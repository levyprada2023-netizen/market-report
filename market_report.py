"""
Market Report Emailer

Runs on demand only. There is no schedule and no internal gating: every time
this script is executed it builds the report and sends it. Trigger it from
the GitHub Actions Run workflow button, a phone shortcut, or any external
scheduler that calls the workflow_dispatch API.

Setup:
  pip install yfinance mplfinance feedparser pandas matplotlib requests weasyprint
  Set MAIL_TO below and put your Resend key in the RESEND_API_KEY env var.

Test run (writes report.html and report.pdf locally, sends nothing):
  python market_report.py --preview
"""

import argparse
import base64
import datetime as dt
import io
import itertools
import time
import json
import logging
import os
import re
import smtplib
import ssl
import sys
from email.message import EmailMessage
from urllib.parse import unquote
from zoneinfo import ZoneInfo

import feedparser
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import mplfinance as mpf
import requests
import yfinance as yf

# ETFs and trusts have no analyst coverage, so yfinance logs 404s for them.
# Those are expected and handled, so keep them out of the run log.
logging.getLogger("yfinance").setLevel(logging.CRITICAL)

# ============================== CONFIG ==============================

# Resend SMTP. Username is the literal word "resend" for every account,
# password is your API key. The key comes from an environment variable so it
# never sits in this file.
SMTP_HOST = "smtp.resend.com"
SMTP_PORT = 465
SMTP_USER = "resend"
SMTP_PASS = os.environ.get("RESEND_API_KEY", "")

MAIL_FROM = "Market Report <onboarding@resend.dev>"
MAIL_TO = os.environ.get("MAIL_TO", "levyprada2023@gmail.com")

LOCAL_TZ = ZoneInfo("America/Edmonton")
MARKET_TZ = ZoneInfo("America/New_York")

# Report times anchored to New York, so they stay correct through every
# time change on either side of the border. Alberta stops changing clocks
# on Nov 1 2026, the US does not, and this handles that automatically.
TARGETS_ET = [
    (16, 10, "Closing report"),      # 10 min after the 4pm ET close
]
WINDOW_MIN = 30   # how far either side of a target a run still counts

# Tradable proxies rather than cash indices, so every row has a real
# extended session. Cash indices like ^GSPC do not trade before the open,
# which made the pre-market column inconsistent row to row.
INDEXES = {
    "SPY": "S&P 500 (SPY)",
    "DIA": "Dow Jones (DIA)",
    "QQQ": "Nasdaq 100 (QQQ)",
    "IWM": "Russell 2000 (IWM)",
    "VIXY": "Volatility (VIXY)",
    "TLT": "20Y Treasuries (TLT)",
}

# Kept for the charts, the technicals and the subject line, not displayed
# in the index table.
SPOT_INDEXES = {
    "^GSPC": "S&P 500 index",
    "^DJI": "Dow Jones index",
    "^RUT": "Russell 2000 index",
    "^VIX": "VIX",
    "^TNX": "US 10Y yield",
}

SECTORS = {
    "XLK": "Technology",
    "XLC": "Comm Services",
    "XLY": "Cons Discretionary",
    "XLP": "Cons Staples",
    "XLF": "Financials",
    "XLV": "Health Care",
    "XLI": "Industrials",
    "XLE": "Energy",
    "XLB": "Materials",
    "XLRE": "Real Estate",
    "XLU": "Utilities",
}

CRYPTO = {
    "BTC-USD": "Bitcoin",
    "ETH-USD": "Ethereum",
}

COMMODITIES = {
    "GC=F": "Gold",
    "SI=F": "Silver",
    "PL=F": "Platinum",
    "HG=F": "Copper",
    "CL=F": "Crude Oil WTI",
    "DX-Y.NYB": "US Dollar Index",
}

# Non US markets. Asia and Europe are closed when the US trades, so these
# show the change on their most recent completed session.
GLOBAL = {
    "^GSPTSE": "TSX, Canada",
    "^GDAXI": "DAX, Germany",
    "^FTSE": "FTSE 100, UK",
    "^STOXX50E": "Euro Stoxx 50",
    "^N225": "Nikkei 225, Japan",
    "^HSI": "Hang Seng, HK",
    "000001.SS": "Shanghai Composite",
    "^KS11": "KOSPI, Korea",
    "^AXJO": "ASX 200, Australia",
}

MEGACAPS = {
    "AAPL": "AAPL", "MSFT": "MSFT", "NVDA": "NVDA", "GOOGL": "GOOGL",
    "AMZN": "AMZN", "META": "META", "AVGO": "AVGO", "TSLA": "TSLA",
    "LLY": "LLY", "COST": "COST", "JPM": "JPM", "XOM": "XOM",
    "WMT": "WMT", "MU": "MU", "AMD": "AMD",
}

FNG_URL = "https://production.dataviz.cnn.io/index/fearandgreed/graphdata"
SYMBOL_NEWS = "https://feeds.finance.yahoo.com/rss/2.0/headline?s={sym}&region=US&lang=en-US"
PORTFOLIO_NEWS_HOURS = 30    # how far back company news counts as today's

# Liquid large caps scanned for movers and moving average proximity.
UNIVERSE = """
AAPL MSFT NVDA GOOGL AMZN META AVGO TSLA LLY JPM XOM WMT COST MU AMD
NFLX ORCL CRM ADBE INTC QCOM TXN AMAT LRCX KLAC ASML ARM PLTR SMCI DELL
COIN MSTR HOOD XYZ PYPL SHOP UBER ABNB DASH SPOT NOW SNOW CRWD PANW ZS
DDOG NET MDB TEAM WDAY INTU IBM CSCO ACN GE CAT DE HON RTX LMT BA
UNH JNJ PFE MRK ABBV TMO ABT DHR ISRG VRTX REGN AMGN GILD BMY CVS
BAC WFC GS MS C SCHW BLK AXP V MA PGR CB SPGI ICE
CVX COP SLB EOG PSX MPC OXY KMI WMB
PG KO PEP PM MO MDLZ CL KMB GIS SYY KR
HD LOW TGT TJX NKE SBUX MCD CMG BKNG MAR RCL
DIS CMCSA T VZ TMUS CHTR WBD
LIN APD SHW FCX NEM NUE
AMT PLD EQIX SPG O
NEE DUK SO D AEP
""".split()

MA_NEAR_PCT = 2.0    # how close to a moving average counts as "near"

# Always checked in the movers section regardless of how much they moved,
# alongside everything in the portfolio.
WATCHLIST = """
MRNA JPM DELL USAR SKHY MU SHOP PLTR INTC RGTI IONQ AMD DIS CVNA CAKE
KO MCD SPY QQQ
""".split()
AI_MODEL = "claude-sonnet-4-6"

# Optional question typed into the Run workflow box. Empty on a plain run.
QUESTION = os.environ.get("REPORT_QUESTION", "").strip()
QUESTION_TICKERS = os.environ.get("REPORT_TICKERS", "").strip()
QUESTION_DEPTH = (os.environ.get("REPORT_DEPTH", "") or "normal").strip().lower()

DEPTH_RULES = {
    "short": "Answer in 3 to 4 sentences, under 90 words. Get to the point.",
    "normal": "Answer in 6 to 10 sentences, under 200 words.",
    "deep": ("Answer thoroughly, 15 to 25 sentences, up to 500 words. Use "
             "short paragraphs separated by <br><br>. Cover the evidence, "
             "what it implies, what argues against it, and what you would "
             "watch next."),
}

# Words that look like tickers but are not, so a question does not send the
# script chasing quotes for AND, THE or CEO.
NOT_TICKERS = set("""
A I AN AS AT BE BY DO GO IF IN IS IT MY NO OF ON OR SO TO UP US WE
AND ARE BUT CAN DID FOR HAS HAD HOW ITS NOT NOW OUT SEE THE WAS WHO WHY YOU
CEO CFO ETF IPO USA GDP CPI PCE FED SEC IRS AI EPS PE ROI YOY QOQ
FROM THIS THAT WITH WHAT WHEN OVER MUCH JUST LIKE MORE MOST WILL
""".split())
STATE_FILE = "state.json"

from positions import load_positions, currency_of

POSITIONS = load_positions()
HOLDINGS = POSITIONS["holdings"]
BOOK_COST = POSITIONS["book"]
OPTIONS = POSITIONS["options"]
POSITIONS_SOURCE = POSITIONS["source"]

try:
    from holdings import CASH, CURRENCY
except Exception:
    CASH, CURRENCY = 0.0, "USD"


CHART_SYMBOL = "^GSPC"
INTRADAY_INTERVAL = "5m"   # "5m" or "15m"
INTRADAY_DAYS = 2          # 2 gives yesterday for context in the morning report
# News sources. RSS where a live feed exists, a light page scrape where the
# publisher has abandoned theirs. Each is capped so no single outlet dominates
# the pool the model triages from.
# Fields: label, fetch method, url, cap, paywalled
# Bloomberg's own RSS carries a useful two sentence summary, which is worth
# feeding the model, but the articles themselves sit behind a subscription.
# Those are marked so they are used for signal and flagged if linked.
NEWS_SOURCES = [
    # label, method, url, cap, paywalled
    # Wire services and broad business desks
    ("Reuters", "rss", "https://news.google.com/rss/search?q=when:1d+site:reuters.com"
     "+markets+OR+economy&hl=en-US&gl=US&ceid=US:en", 9, False),
    ("AP", "rss", "https://news.google.com/rss/search?q=when:1d+site:apnews.com"
     "+business+OR+economy&hl=en-US&gl=US&ceid=US:en", 7, False),
    ("CNBC", "rss", "https://www.cnbc.com/id/100003114/device/rss/rss.html", 8, False),
    ("CNBC Economy", "rss", "https://www.cnbc.com/id/20910258/device/rss/rss.html", 7, False),
    ("Yahoo Finance", "rss", "https://finance.yahoo.com/news/rssindex", 8, False),
    ("Yahoo Latest", "yahoo_page",
     "https://finance.yahoo.com/topic/latest-news/", 10, False),
    ("MarketWatch", "rss",
     "https://feeds.content.dowjones.io/public/rss/mw_topstories", 6, False),
    ("CNN Business", "cnn", "https://www.cnn.com/business", 8, False),
    ("BBC Business", "rss", "https://feeds.bbci.co.uk/news/business/rss.xml", 6, False),
    ("Fortune", "rss", "https://fortune.com/feed/", 5, False),
    ("Seeking Alpha", "rss", "https://seekingalpha.com/market_currents.xml", 6, False),

    # Canadian, since part of the book is listed in Canada
    ("Globe and Mail", "rss",
     "https://www.theglobeandmail.com/arc/outboundfeeds/rss/category/business/", 6, False),
    ("CBC Business", "rss", "https://www.cbc.ca/webfeed/rss/rss-business", 5, False),

    # Asia, which sets the tone before the US opens
    ("SCMP Business", "rss", "https://www.scmp.com/rss/92/feed", 5, False),

    # Official sources, no spin
    ("Federal Reserve", "rss",
     "https://www.federalreserve.gov/feeds/press_all.xml", 4, False),

    # Human curated newsletter. Treated as higher signal than the wires
    # because someone already decided each item was worth writing about.
    ("Short Squeez", "squeez", "https://www.shortsqueez.co", 12, False),

    # Headlines and summaries are free, full articles need a subscription
    ("Bloomberg Markets", "rss",
     "https://feeds.bloomberg.com/markets/news.rss", 7, True),
    ("Bloomberg Economics", "rss",
     "https://feeds.bloomberg.com/economics/news.rss", 5, True),
    ("WSJ Markets", "rss",
     "https://feeds.content.dowjones.io/public/rss/RSSMarketsMain", 6, True),
    ("Financial Times", "rss", "https://news.google.com/rss/search?q=when:1d"
     "+site:ft.com+markets+OR+economy&hl=en-US&gl=US&ceid=US:en", 5, True),
    ("Barron's", "rss", "https://news.google.com/rss/search?q=when:1d"
     "+site:barrons.com&hl=en-US&gl=US&ceid=US:en", 5, True),
]
NEWS_POOL = 130     # headlines gathered, then triaged down by the model
NEWS_PICKS = 10     # how many make the front of the report
CALENDAR_URL = "https://nfs.faireconomy.media/ff_calendar_thisweek.json"

# ============================== DATA ==============================


def session_label():
    """Whether we are currently before, during or after the US session."""
    now = dt.datetime.now(MARKET_TZ)
    t = now.hour * 60 + now.minute
    if now.weekday() >= 5:
        return "weekend"
    if t < 9 * 60 + 30:
        return "pre-market"
    if t <= 16 * 60:
        return "intraday"
    return "after hours"


def get_quotes(symbols):
    """Price everything off the last COMPLETED regular session.

    Indices like the S&P have no extended session, while stocks and ETFs do,
    so quoting live prices mixes two different clocks and produces figures
    that cannot be compared. Every headline number therefore comes from the
    official close. The live price is carried separately as 'ext', which is
    where any pre-market or after hours move shows up.
    """
    symbols = sorted(set(symbols))
    out = {}

    df = yf.download(symbols, period="10d", interval="1d", progress=False,
                     auto_adjust=False, threads=True)
    close, opn = df["Close"], df["Open"]
    if getattr(close, "ndim", 1) == 1:                # single symbol
        close, opn = close.to_frame(symbols[0]), opn.to_frame(symbols[0])

    # fast_info reports the regular session close, not the extended session,
    # so the live price comes from intraday bars fetched with prepost=True.
    # Indices have no extended session and simply return nothing here.
    live = {}
    try:
        ex = yf.download(symbols, period="1d", interval="5m", prepost=True,
                         progress=False, auto_adjust=False, threads=True)
        exc = ex["Close"]
        if getattr(exc, "ndim", 1) == 1:
            exc = exc.to_frame(symbols[0])
        for s in symbols:
            try:
                ser = exc[s].dropna()
                if len(ser):
                    live[s] = float(ser.iloc[-1])
            except Exception:
                pass
    except Exception as e:
        print(f"extended hours prices unavailable: {e}", file=sys.stderr)

    for s in symbols:
        try:
            ser = close[s].dropna()
            if len(ser) < 2:
                continue
            last = float(ser.iloc[-1])
            prev = float(ser.iloc[-2])
            try:
                op = float(opn[s].dropna().reindex(ser.index).iloc[-1])
            except Exception:
                op = prev
            ext = live.get(s)
            out[s] = {
                "last": last,                 # official close, the headline number
                "prev": prev,
                "open": op or prev,
                "pct": (last - prev) / prev * 100.0,
                "from_open": (last - op) / op * 100.0 if op else 0.0,
                "dollar": last - prev,
                "ext": ext,
                "ext_pct": ((ext - last) / last * 100.0)
                           if ext and abs(ext / last - 1) > 0.0002 else None,
                "session": str(ser.index[-1].date()),
            }
        except Exception as e:
            print(f"quote failed {s}: {e}", file=sys.stderr)
    return out


def get_history(symbol, period="9mo"):
    df = yf.download(symbol, period=period, interval="1d",
                     progress=False, auto_adjust=False)
    if hasattr(df.columns, "levels") and df.columns.nlevels > 1:
        df.columns = df.columns.droplevel(1)
    return df


UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/125.0 Safari/537.36")


def _clean(text, limit=260):
    text = re.sub(r"<[^>]+>", " ", text or "")
    text = re.sub(r"&[a-z]+;|&#\d+;", " ", text)
    text = re.sub(r"\s+", " ", text).strip()
    return text[:limit]


def _rss_items(url, cap, source, paywalled=False):
    r = requests.get(url, timeout=25, headers={"User-Agent": UA})
    r.raise_for_status()
    feed = feedparser.parse(r.content)
    out = []
    for e in feed.entries[:cap]:
        title = (e.get("title") or "").strip()
        if not title:
            continue
        # Google News wraps the outlet name onto the end of the title
        title = re.sub(r"\s+-\s+(Reuters|Reuters\.com)\s*$", "", title)
        out.append({"title": title, "link": e.get("link", ""),
                    "source": source, "paywalled": paywalled,
                    "summary": _clean(e.get("summary") or e.get("description"))})
    return out


def _cnn_items(url, cap, source):
    """CNN abandoned their RSS feeds, so read the business page instead."""
    r = requests.get(url, timeout=25, headers={"User-Agent": UA})
    r.raise_for_status()
    html = r.text
    pattern = re.compile(
        r'href="(/\d{4}/\d{2}/\d{2}/[^"]+)"[^>]*>.{0,600}?'
        r'container__headline-text[^>]*>([^<]{15,160})<', re.S)
    seen, out = set(), []
    for href, title in pattern.findall(html):
        title = re.sub(r"\s+", " ", title).strip()
        title = title.replace("&#8217;", "\u2019").replace("&amp;", "&")
        if not title or title in seen:
            continue
        seen.add(title)
        out.append({"title": title, "link": "https://www.cnn.com" + href,
                    "source": source, "paywalled": False, "summary": ""})
        if len(out) >= cap:
            break
    if not out:                      # markup changed, fall back to headlines only
        for title in re.findall(
                r'container__headline-text[^>]*>([^<]{15,160})<', html)[:cap]:
            title = re.sub(r"\s+", " ", title).strip()
            if title and title not in seen:
                seen.add(title)
                out.append({"title": title, "link": url, "source": source,
                            "paywalled": False, "summary": ""})
    return out


def _squeez_items(url, cap, source):
    """Short Squeez runs on beehiiv, which renders posts client side, so the
    posts come out of the JSON payload embedded in the page. Title appears
    before its slug in that payload, so they are matched as a pair rather
    than by list position."""
    r = requests.get(url, timeout=25, headers={"User-Agent": UA})
    r.raise_for_status()
    html = r.text

    def decode(t):
        try:
            t = t.encode("utf-8").decode("unicode_escape")
            t = t.encode("latin-1", "ignore").decode("utf-8", "ignore")
        except Exception:
            pass
        t = re.sub(r"^[^\w$]+", "", t)          # leading emoji the newsletter uses
        return re.sub(r"\s+", " ", t).strip()

    pairs = re.findall(r'"web_title":"(.*?)".{0,600}?"slug":"([a-z0-9\-]+)"',
                       html, re.S)
    out, seen = [], set()
    for title, slug in pairs:
        title = decode(title)
        if not title or slug in seen:
            continue
        # sanity check that the slug really belongs to this title
        key = re.sub(r"[^a-z0-9]", "", title.lower())[:12]
        if key and key not in re.sub(r"[^a-z0-9]", "", slug):
            if len(out) and not slug.startswith(key[:5]):
                pass                              # keep it, beehiiv slugs drift
        seen.add(slug)
        out.append({
            "title": title,
            "link": f"{url.rstrip('/')}/p/{slug}",
            "source": source,
            "paywalled": False,
            "summary": "",
        })
        if len(out) >= cap:
            break
    return out


def _yahoo_page_items(url, cap, source):
    """Yahoo's Latest News stream. Its own RSS feed carries different stories,
    so this is additive rather than duplicated. Each story block holds the
    headline in a tracking attribute and the article link alongside it."""
    r = requests.get(url, timeout=25, headers={"User-Agent": UA})
    r.raise_for_status()
    blocks = re.split(r'<section class="story-item', r.text)[1:]

    out, seen = [], set()
    for b in blocks:
        slk = re.search(r"slk:([^;\"]+)", b)
        href = re.search(r'href="(https://finance\.yahoo\.com/[^"]*?'
                         r'(?:/articles/|/news/)[^"]+)"', b)
        if not (slk and href):
            continue
        title = unquote(slk.group(1)).replace("%20", " ").strip()
        title = re.sub(r"\s+", " ", title)
        key = re.sub(r"[^a-z0-9]", "", title.lower())[:60]
        if not title or key in seen:
            continue
        seen.add(key)
        partner = re.search(r"destpartner:([^;\"]+)", b)
        out.append({
            "title": title,
            "link": href.group(1),
            "source": f"{source}" + (f" ({partner.group(1)})" if partner else ""),
            "paywalled": False,
            "summary": "",
        })
        if len(out) >= cap:
            break
    return out


def get_news(limit=NEWS_POOL):
    """Gather headlines from every source, interleaved so one cannot dominate."""
    buckets = []
    for source, kind, url, cap, paywalled in NEWS_SOURCES:
        try:
            if kind == "cnn":
                items = _cnn_items(url, cap, source)
            elif kind == "yahoo_page":
                items = _yahoo_page_items(url, cap, source)
            elif kind == "squeez":
                items = _squeez_items(url, cap, source)
            else:
                items = _rss_items(url, cap, source, paywalled)
            if items:
                buckets.append(items)
            else:
                print(f"news source empty: {source}", file=sys.stderr)
        except Exception as e:
            print(f"news source failed {source}: {e}", file=sys.stderr)

    merged, seen = [], set()
    for row in itertools.zip_longest(*buckets):
        for item in row:
            if not item:
                continue
            key = re.sub(r"[^a-z0-9]", "", item["title"].lower())[:60]
            if key in seen:
                continue
            seen.add(key)
            merged.append(item)
    return merged[:limit]


def get_fear_greed():
    """CNN Fear and Greed index, current score plus trend."""
    try:
        r = requests.get(FNG_URL, timeout=20,
                         headers={"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64)"})
        f = r.json()["fear_and_greed"]
        return {
            "score": float(f["score"]),
            "rating": str(f["rating"]).title(),
            "prev": float(f["previous_close"]),
            "week": float(f["previous_1_week"]),
            "month": float(f["previous_1_month"]),
            "year": float(f["previous_1_year"]),
        }
    except Exception as e:
        print(f"fear and greed failed: {e}", file=sys.stderr)
        return None


GOOGLE_NEWS_Q = ("https://news.google.com/rss/search?q=%22{q}%22+when:1d"
                 "&hl=en-US&gl=US&ceid=US:en")

# Stop words stripped from a release title before searching for coverage
CAL_NOISE = re.compile(r"\b(m/m|q/q|y/y|prelim|final|revised|index|rate|"
                       r"speaks|data|report)\b", re.I)


def article_body(url, limit=2600):
    """Plain text of an article, empty string if the publisher blocks us."""
    try:
        r = requests.get(url, timeout=20, headers={"User-Agent": UA},
                         allow_redirects=True)
        if r.status_code != 200:
            return ""
        paras = re.findall(r"<p[^>]*>(.*?)</p>", r.text, re.S)
        txt = " ".join(re.sub(r"<[^>]+>", "", p) for p in paras)
        txt = re.sub(r"&[a-z]+;|&#\d+;", " ", txt)
        return re.sub(r"\s+", " ", txt).strip()[:limit]
    except Exception:
        return ""


def verify_releases(pending, max_events=4, per_event=4):
    """Chase down results for releases the calendar feed has not filled in.

    The feed is often slow to publish an actual value, so a release can be
    out and reported everywhere while the feed still shows nothing. This
    searches the last day's coverage for each such event. Wire headlines
    usually carry the figure directly, and article bodies are pulled where
    the publisher allows it. Everything is handed to the model as reported
    coverage, never as a confirmed number.
    """
    found = []
    for ev in pending[:max_events]:
        title = re.sub(r"\s+", " ", CAL_NOISE.sub("", ev["title"])).strip()
        if len(title) < 4:
            continue

        queries = [title]
        short = re.sub(r"^(CB|ISM|UoM|BoC|ECB|Fed)\s+", "", title).strip()
        if short and short != title:
            queries.append(short)

        items, seen = [], set()
        for q in queries:
            try:
                url = GOOGLE_NEWS_Q.format(q=requests.utils.quote(q))
                feed = feedparser.parse(
                    requests.get(url, timeout=25,
                                 headers={"User-Agent": UA}).content)
            except Exception as e:
                print(f"release search failed {q}: {e}", file=sys.stderr)
                continue

            for entry in feed.entries[:8]:
                head = (entry.get("title") or "").strip()
                key = re.sub(r"[^a-z0-9]", "", head.lower())[:50]
                if not head or key in seen:
                    continue
                seen.add(key)
                # a headline carrying a figure is usually the whole answer
                has_number = bool(re.search(r"\d+\.?\d*", head))
                body = article_body(entry.get("link", ""))
                if has_number or re.search(r"\d+\.\d", body or ""):
                    items.append({"headline": head, "text": body[:1400]})
                if len(items) >= per_event:
                    break
            if len(items) >= per_event:
                break

        if items:
            found.append({"event": ev, "coverage": items})
    return found


def get_calendar():
    """US economic events. Returns (today, rest_of_week)."""
    # This feed rate limits, and a 429 returns an HTML error page rather than
    # JSON, so validate the body and back off rather than losing the calendar.
    data = None
    for attempt in range(4):
        try:
            r = requests.get(CALENDAR_URL, timeout=25,
                             headers={"User-Agent": UA})
            body = r.text.strip()
            if r.status_code == 200 and body.startswith("["):
                data = r.json()
                break
            print(f"calendar attempt {attempt + 1}: http {r.status_code}",
                  file=sys.stderr)
        except Exception as e:
            print(f"calendar attempt {attempt + 1} failed: {e}", file=sys.stderr)
        time.sleep(3 * (attempt + 1))
    if data is None:
        print("calendar unavailable after retries", file=sys.stderr)
        return [], []

    now = dt.datetime.now(LOCAL_TZ)
    today = now.date()
    fmt = "%#I:%M %p" if os.name == "nt" else "%-I:%M %p"
    todays, ahead = [], []

    for ev in data:
        if ev.get("country") != "USD":
            continue
        if ev.get("impact") not in ("High", "Medium"):
            continue
        try:
            when = dt.datetime.fromisoformat(ev["date"]).astimezone(LOCAL_TZ)
        except Exception:
            continue
        row = {
            "when": when,
            "day": when.strftime("%a %b %-d") if os.name != "nt" else when.strftime("%a %b %#d"),
            "time": when.strftime(fmt),
            "title": ev.get("title", ""),
            "impact": ev.get("impact", ""),
            "actual": ev.get("actual") or "",
            "forecast": ev.get("forecast") or "",
            "previous": ev.get("previous") or "",
        }
        if when.date() == today:
            todays.append(row)
        elif when.date() > today:
            ahead.append(row)

    todays.sort(key=lambda x: x["when"])
    ahead.sort(key=lambda x: x["when"])
    return todays, ahead

SP500_LIST = "https://en.wikipedia.org/wiki/List_of_S%26P_500_companies"
CAPE_URL = "https://www.multpl.com/shiller-pe"
SP500_PE_URL = "https://www.multpl.com/s-p-500-pe-ratio"

# Breadth proxies. RSP is the equal weight S&P, so RSP against SPY says
# whether the average stock is keeping up with the megacaps.
HEALTH_TICKERS = {
    "RSP": "S&P 500 equal weight",
    "SPY": "S&P 500 cap weight",
    "^SKEW": "CBOE SKEW, tail risk pricing",
    "HYG": "High yield credit",
    "^VIX": "VIX",
}


def sp500_members():
    """Current S&P 500 constituents, read from the public listing."""
    try:
        r = requests.get(SP500_LIST, timeout=30, headers={"User-Agent": UA})
        r.raise_for_status()
        seg = r.text[r.text.find('id="constituents"'):]
        seg = seg[:seg.find("</table>")]
        out = []
        for row in re.split(r"<tr[^>]*>", seg)[2:]:
            cells = re.findall(r"<td[^>]*>(.*?)</td>", row, re.S)
            if not cells:
                continue
            txt = re.sub(r"<[^>]+>", "", cells[0]).strip()
            if re.fullmatch(r"[A-Z][A-Z.\-]{0,6}", txt):
                out.append(txt.replace(".", "-"))
        return list(dict.fromkeys(out))
    except Exception as e:
        print(f"S&P 500 list failed, falling back to universe: {e}",
              file=sys.stderr)
        return list(UNIVERSE)


def multpl_history(url):
    """Full monthly history with today's reading placed against it.

    Hardcoding a long run average would go stale and could simply be wrong,
    so the mean, median, peak and percentile are computed from the actual
    series each run.
    """
    try:
        r = requests.get(url + "/table/by-month", timeout=30,
                         headers={"User-Agent": UA})
        r.raise_for_status()
        rows = re.findall(
            r"<td>([A-Z][a-z]{2} \d{1,2}, \d{4})</td>\s*<td>\s*&#x2002;\s*([\d.]+)",
            r.text)
        if len(rows) < 100:
            return None
        vals = [float(v) for _, v in rows]
        cur = vals[0]
        peak = max(vals)
        trough = min(vals)
        return {
            "current": cur,
            "mean": sum(vals) / len(vals),
            "median": sorted(vals)[len(vals) // 2],
            "peak": peak,
            "peak_date": rows[vals.index(peak)][0],
            "trough": trough,
            "trough_date": rows[vals.index(trough)][0],
            "percentile": sum(1 for v in vals if v < cur) / len(vals) * 100,
            "months": len(vals),
            "since": rows[-1][0],
            "vs_mean": (cur / (sum(vals) / len(vals)) - 1) * 100,
            "vs_peak": (cur / peak - 1) * 100,
        }
    except Exception as e:
        print(f"multpl history failed {url}: {e}", file=sys.stderr)
        return None


def scrape_multpl(url):
    """multpl publishes the current value in a div marked current."""
    try:
        r = requests.get(url, timeout=25, headers={"User-Agent": UA})
        m = re.search(r'id="current"[^>]*>(.*?)</div>', r.text, re.S)
        if not m:
            return None
        txt = re.sub(r"<[^>]+>", " ", m.group(1))
        num = re.search(r"([\d]+\.[\d]+)", txt)
        return float(num.group(1)) if num else None
    except Exception as e:
        print(f"multpl scrape failed {url}: {e}", file=sys.stderr)
        return None


STOCKTWITS = "https://api.stocktwits.com/api/2/streams/symbol/{sym}.json"
APEWISDOM = "https://apewisdom.io/api/v1.0/filter/all-stocks/page/1"


def retail_sentiment(symbols, min_tagged=4):
    """Bull versus bear tagging on StockTwits, per symbol.

    Posters tag their own messages, so this measures the mood of people
    posting about a ticker today. It is a crowd positioning read, not a
    forecast, and small samples mean very little.
    """
    out = {}
    for sym in symbols:
        if "." in sym or "-" in sym:          # non US listings are not covered
            continue
        try:
            r = requests.get(STOCKTWITS.format(sym=sym), timeout=15,
                             headers={"User-Agent": UA})
            if r.status_code != 200:
                continue
            msgs = r.json().get("messages", [])
            bull = bear = 0
            for m in msgs:
                basic = ((m.get("entities") or {}).get("sentiment") or {}).get("basic")
                if basic == "Bullish":
                    bull += 1
                elif basic == "Bearish":
                    bear += 1
            tagged = bull + bear
            if tagged < min_tagged:
                continue
            out[sym] = {
                "bull": bull, "bear": bear, "tagged": tagged,
                "posts": len(msgs),
                "bull_pct": bull / tagged * 100,
            }
        except Exception as e:
            print(f"stocktwits failed {sym}: {e}", file=sys.stderr)
    # StockTwits posters skew bullish on almost everything, so a raw 90%
    # reading says little. What is informative is how a name sits against the
    # crowd's own baseline on the same day.
    if out:
        vals = sorted(v["bull_pct"] for v in out.values())
        mid = vals[len(vals) // 2]
        for v in out.values():
            v["vs_crowd"] = v["bull_pct"] - mid
        for v in out.values():
            v["baseline"] = mid
    return out


def reddit_buzz(limit=15):
    """What retail is talking about, and what is suddenly being talked about.

    The change against 24 hours ago matters more than the raw count, since
    the same megacaps sit at the top of the list every single day.
    """
    try:
        r = requests.get(APEWISDOM, timeout=20, headers={"User-Agent": UA})
        r.raise_for_status()
        rows = []
        for x in r.json().get("results", [])[:60]:
            now = int(x.get("mentions") or 0)
            prior = int(x.get("mentions_24h_ago") or 0)
            rows.append({
                "ticker": x.get("ticker", ""),
                "name": x.get("name", ""),
                "mentions": now,
                "prior": prior,
                "change": ((now / prior - 1) * 100) if prior else None,
                "upvotes": int(x.get("upvotes") or 0),
            })
        return rows[:limit]
    except Exception as e:
        print(f"reddit buzz failed: {e}", file=sys.stderr)
        return []


PC_INDEX = ["SPY", "QQQ", "IWM", "DIA"]
PC_EQUITY = ["NVDA", "AAPL", "TSLA", "AMZN", "META", "MSFT", "AMD", "GOOGL"]


def put_call(symbols, expiries=4):
    """Put to call ratio computed from live option chains.

    CBOE stopped publishing their daily ratios on a free endpoint, so this is
    built from the chains directly. Index options are dominated by hedging and
    normally sit above 1.0, while single stock options are speculative and sit
    well below, so the two are reported separately rather than blended.
    """
    pv = cv = poi = coi = 0.0
    used = []
    for sym in symbols:
        try:
            tk = yf.Ticker(sym)
            for exp in (tk.options or [])[:expiries]:
                ch = tk.option_chain(exp)
                pv += float(ch.puts["volume"].fillna(0).sum())
                cv += float(ch.calls["volume"].fillna(0).sum())
                poi += float(ch.puts["openInterest"].fillna(0).sum())
                coi += float(ch.calls["openInterest"].fillna(0).sum())
            used.append(sym)
        except Exception as e:
            print(f"option chain failed {sym}: {e}", file=sys.stderr)
    if not cv or not coi:
        return None
    return {
        "volume_pc": pv / cv,
        "oi_pc": poi / coi,
        "put_volume": pv,
        "call_volume": cv,
        "symbols": used,
    }


def market_health():
    """Breadth and valuation for the market as a whole, not single names."""
    out = {}

    members = sp500_members()
    out["members"] = len(members)
    try:
        df = yf.download(members, period="1y", interval="1d", progress=False,
                         auto_adjust=False, threads=True)
        c = df["Close"].dropna(axis=1, how="all")
        last, prev = c.iloc[-1], c.iloc[-2]

        adv = int((last > prev).sum())
        dec = int((last < prev).sum())
        unch = int(c.shape[1] - adv - dec)
        sma50 = c.rolling(50, min_periods=40).mean().iloc[-1]
        sma200 = c.rolling(200, min_periods=150).mean().iloc[-1]
        hi52 = c.rolling(252, min_periods=200).max().iloc[-1]
        lo52 = c.rolling(252, min_periods=200).min().iloc[-1]
        n = c.shape[1]

        out.update({
            "counted": n,
            "advancers": adv,
            "decliners": dec,
            "unchanged": unch,
            "ad_ratio": (adv / dec) if dec else None,
            "above50": float((last > sma50).sum()) / n * 100,
            "above200": float((last > sma200).sum()) / n * 100,
            "new_highs": int((last >= hi52 * 0.999).sum()),
            "new_lows": int((last <= lo52 * 1.001).sum()),
            "median_move": float(((last / prev - 1) * 100).median()),
        })
    except Exception as e:
        print(f"breadth failed: {e}", file=sys.stderr)

    try:
        h = yf.download(list(HEALTH_TICKERS), period="6mo", interval="1d",
                        progress=False, auto_adjust=False, threads=True)["Close"]
        def move(sym, days):
            ser = h[sym].dropna()
            return (float(ser.iloc[-1]) / float(ser.iloc[-1 - days]) - 1) * 100
        out["rsp_spy_day"] = move("RSP", 1) - move("SPY", 1)
        out["rsp_spy_month"] = move("RSP", 21) - move("SPY", 21)
        out["rsp_spy_qtr"] = move("RSP", 63) - move("SPY", 63)
        for sym in ("^SKEW", "HYG", "^VIX"):
            ser = h[sym].dropna()
            out[sym] = float(ser.iloc[-1])
            out[sym + "_chg"] = (float(ser.iloc[-1]) / float(ser.iloc[-2]) - 1) * 100
    except Exception as e:
        print(f"health tickers failed: {e}", file=sys.stderr)

    out["pc_index"] = put_call(PC_INDEX)
    out["pc_equity"] = put_call(PC_EQUITY)
    out["cape_hist"] = multpl_history(CAPE_URL)
    out["pe_hist"] = multpl_history(SP500_PE_URL)
    out["cape"] = (out["cape_hist"] or {}).get("current") or scrape_multpl(CAPE_URL)
    out["pe"] = (out["pe_hist"] or {}).get("current") or scrape_multpl(SP500_PE_URL)
    return out


def scan_universe():
    """One batched download, used for both the movers list and the MA scan."""
    tickers = sorted(set(UNIVERSE) | set(WATCHLIST) | set(HOLDINGS))
    df = yf.download(tickers, period="1y", interval="1d", progress=False,
                     auto_adjust=False, threads=True)
    close, vol = df["Close"], df["Volume"]
    close = close.dropna(axis=1, how="all")

    last, prev = close.iloc[-1], close.iloc[-2]
    pct = (last / prev - 1) * 100
    rvol = vol.iloc[-1] / vol.iloc[-21:-1].mean()

    rows = []
    for sym in close.columns:
        try:
            px = float(last[sym])
            if px != px:
                continue
            sma = {n: float(close[sym].rolling(n).mean().iloc[-1])
                   for n in (20, 50, 200)}
            rows.append({
                "sym": sym,
                "price": px,
                "pct": float(pct[sym]),
                "rvol": float(rvol[sym]) if rvol[sym] == rvol[sym] else 0.0,
                "sma": sma,
            })
        except Exception:
            continue
    return rows


def hot_stocks(rows, n=8):
    """Biggest movers, plus everything on the watchlist and in the portfolio."""
    tracked = set(WATCHLIST) | set(HOLDINGS)

    movers = [r for r in rows if abs(r["pct"]) >= 1.5 and r["sym"] not in tracked]
    movers.sort(key=lambda r: abs(r["pct"]) * (1 + min(r["rvol"], 4) / 4),
                reverse=True)
    for r in movers:
        r["why"] = "unusual move"

    watched = [r for r in rows if r["sym"] in tracked]
    watched.sort(key=lambda r: -abs(r["pct"]))
    for r in watched:
        r["why"] = ("held and watched" if r["sym"] in HOLDINGS
                    and r["sym"] in WATCHLIST else
                    "held" if r["sym"] in HOLDINGS else "watchlist")

    picks = movers[:n] + watched
    # headlines only for the ones that actually moved, to keep the run quick
    for p in sorted(picks, key=lambda r: -abs(r["pct"]))[:10]:
        p["news"] = symbol_news(p["sym"])
    return picks


def symbol_news(sym, limit=2, max_age_hours=None):
    """Recent headlines for one ticker. max_age_hours filters out stale items,
    which matters for thinly covered names whose feeds go months back."""
    try:
        r = requests.get(SYMBOL_NEWS.format(sym=sym), timeout=20,
                         headers={"User-Agent": UA})
        feed = feedparser.parse(r.content)
    except Exception as e:
        print(f"symbol news failed {sym}: {e}", file=sys.stderr)
        return []

    now = time.time()
    out = []
    for e in feed.entries:
        p = e.get("published_parsed")
        age = (now - time.mktime(p)) / 3600 if p else None
        if max_age_hours is not None:
            if age is None or age > max_age_hours:
                continue
        out.append({"title": (e.get("title") or "").strip(),
                    "link": e.get("link", ""),
                    "age_hours": age})
        if len(out) >= limit:
            break
    return out


def portfolio_news(max_age_hours=PORTFOLIO_NEWS_HOURS, per_symbol=2):
    """News on the things actually owned or watched, newest first.

    Everything else in the report is about the market. This is about the
    specific companies whose share price sits in the account, so it gets its
    own section rather than competing with wire copy for a slot.
    """
    held = set(HOLDINGS)
    watched = set(WATCHLIST) - held
    rows, seen = [], set()

    for sym in sorted(held) + sorted(watched):
        for item in symbol_news(sym, limit=per_symbol,
                                max_age_hours=max_age_hours):
            key = re.sub(r"[^a-z0-9]", "", item["title"].lower())[:60]
            if not key or key in seen:
                continue
            seen.add(key)
            rows.append({**item, "sym": sym,
                         "held": sym in held})
    rows.sort(key=lambda r: (r["age_hours"] if r["age_hours"] is not None else 999))
    return rows


def near_moving_averages(rows, tol=MA_NEAR_PCT):
    """Names sitting within tol percent of their 20, 50 or 200 day average."""
    out = []
    for r in rows:
        for n in (200, 50, 20):
            avg = r["sma"].get(n)
            if not avg or avg != avg:
                continue
            gap = (r["price"] / avg - 1) * 100
            if abs(gap) <= tol:
                out.append({
                    "sym": r["sym"],
                    "price": r["price"],
                    "pct": r["pct"],
                    "ma": n,
                    "gap": gap,
                    "side": "above" if gap >= 0 else "below",
                })
                break
    out.sort(key=lambda x: (-x["ma"], abs(x["gap"])))
    return out


def extract_tickers(text, explicit=""):
    """Pull tickers out of a free text question.

    Anything after a dollar sign is taken as written. Bare uppercase words
    are candidates, filtered against a stop list and then confirmed by
    checking each one actually prices, so a typo does not become a section.
    """
    found = []
    for t in re.findall(r"\$([A-Za-z][A-Za-z.\-]{0,6})", text or ""):
        found.append(t.upper())
    for t in re.findall(r"\b([A-Z][A-Z.\-]{0,5})\b", text or ""):
        if t not in NOT_TICKERS:
            found.append(t)
    for t in re.split(r"[,\s]+", explicit or ""):
        t = t.strip().upper()
        if t:
            found.append(t)

    # anything already known to us needs no verification
    known = set(HOLDINGS) | set(WATCHLIST) | set(UNIVERSE)
    out, unverified = [], []
    for t in dict.fromkeys(found):
        (out if t in known else unverified).append(t)

    for t in unverified[:8]:
        try:
            d = yf.download(t, period="5d", interval="1d", progress=False,
                            auto_adjust=False)
            if len(d.get("Close", []).dropna()):
                out.append(t)
        except Exception:
            continue
    return list(dict.fromkeys(out))[:10]


def question_context(tickers):
    """Everything worth knowing about the names a question mentions."""
    if not tickers:
        return ""

    quotes = get_quotes(tickers)
    fundamentals = get_fundamentals(tickers)
    analysts = get_analysts(tickers)
    earnings = get_earnings(tickers, ahead_days=45, back_days=10)
    hist = get_earnings_history(tickers)

    lines = ["DATA ON THE TICKERS IN HIS QUESTION. Use these figures rather "
             "than anything you recall, and say so if something he asked "
             "about is not covered here."]

    for t in tickers:
        q = quotes.get(t)
        if not q:
            lines.append(f"\n{t}: no price data found")
            continue
        bits = [f"\n{t}: close {q['last']:,.2f}, {q['pct']:+.2f}% "
                f"({q['dollar']:+,.2f}) on the session"]
        if q.get("ext_pct") is not None:
            bits.append(f"; {q['ext']:,.2f} ({q['ext_pct']:+.2f}%) in the "
                        "extended session")
        f = fundamentals.get(t)
        if f:
            bits.append(
                f". Market cap {fmt((f['mcap'] or 0) / 1e9, 1, 'B')}, "
                f"trailing PE {fmt(f['pe'])}, forward PE {fmt(f['fwd_pe'])}, "
                f"PS {fmt(f['ps'])}, PEG {fmt(f['peg'], 2)}, revenue growth "
                f"{fmt(f['rev_growth'], 0, '%')}, margin "
                f"{fmt(f['margin'], 0, '%')}")
            if f.get("short_pct"):
                bits.append(f", short interest {f['short_pct']:.1f}% of float")
        a = analysts.get(t)
        if a:
            bits.append(f". Analyst mean target {a['mean']:,.2f} "
                        f"({a['upside']:+.1f}% from here), rating "
                        f"{a['rating'] or 'na'}, {a['count'] or '?'} analysts")
        h = hist.get(t)
        if h:
            bits.append(f". Beat estimates in {h['beats']} of the last "
                        f"{h['of']} quarters, last surprise "
                        f"{h['rows'][-1]['surprise']:+.1f}%")
        e = next((x for x in earnings if x["sym"] == t), None)
        if e:
            bits.append(f". Earnings {'reported' if e['reported'] else 'due'} "
                        f"{e['date'].strftime('%b %d')}")
        if t in HOLDINGS:
            bits.append(f". HE OWNS {HOLDINGS[t]:,.0f} shares")
        elif t in WATCHLIST:
            bits.append(". On his watchlist")
        lines.append("".join(bits))

        news = symbol_news(t, limit=5, max_age_hours=72)
        for n in news:
            lines.append(f"    NEWS: {n['title']}")

    return "\n".join(lines)


def fallback_summary(quotes, fng, movers, cal_today, port):
    """Plain summary used when no Anthropic key is configured."""
    def p(sym):
        return quotes.get(sym, {}).get("pct", 0)

    def word(v):
        if v > 0.75:
            return "up firmly"
        if v > 0.1:
            return "up"
        if v < -0.75:
            return "down firmly"
        if v < -0.1:
            return "down"
        return "roughly flat"

    bits = [f"Shares finished the day {word(p('SPY'))}. The S&P 500, which "
            f"tracks 500 big US companies, moved {p('SPY'):+.2f} percent, and "
            f"the tech heavy Nasdaq {p('QQQ'):+.2f} percent."]
    if abs(p("GC=F")) > 0.5 or abs(p("BTC-USD")) > 1.5:
        bits.append(f"Gold moved {p('GC=F'):+.2f} percent and Bitcoin "
                    f"{p('BTC-USD'):+.2f} percent.")
    if port:
        bits.append(f"Your account is {port['day_pl']:+,.0f} on the day, "
                    f"{port['day_pct']:+.2f} percent.")
    if cal_today:
        n = len(cal_today)
        bits.append(f"There {'is' if n == 1 else 'are'} {n} economic "
                    f"report{'s' if n != 1 else ''} on the calendar today.")
    return " ".join(bits)


AI_SCHEMA = """You are writing a daily market report for a couple who invest
together with a 20 year horizon. One of them follows markets closely, the
other does not. Write so the one who does not can read the whole thing in a
few minutes and understand it completely.

HOW TO WRITE. This matters as much as what you say.
- Plain English at a high school reading level. Short sentences.
- Explain any term the moment you use it, in a few words: "the VIX, which
  measures how much fear is priced into the market, rose to 15.8".
- No jargon without a plain translation. Never write breadth, multiple
  compression, risk on, rotation, hawkish, or dovish without saying what it
  means in ordinary words.
- Say what a number means, not just what it is. "58 percent of stocks are
  above their 50 day average, so a bit more than half are doing well" beats
  "breadth is 58 percent".
- Be brief. Respect the word limits below. Cut every sentence that does not
  tell him something he can use.
- No filler openers. Start with the point.

Return ONLY a JSON object, no markdown fences, with these keys:

"summary": string. 3 to 4 short sentences, under 90 words. What happened
  today and why it matters. Cover stocks, then anything unusual in gold,
  bitcoin or overseas, then what is coming next. Specific numbers, plainly
  explained. This is the part read over coffee.

"portfolio_analysis": string, or "" if no portfolio data. 4 to 6 short
  sentences, under 130 words. How much the account made or lost today in
  dollars, which one or two holdings caused it, and anything that needs
  attention such as earnings coming up or a position that has grown very
  large. End with one plain sentence on what a long term holder might do,
  including doing nothing, which is often right. Name tickers.

"technical_analysis": string. 3 to 5 short sentences, under 110 words. What
  the charts show, described the way you would to someone who has never read
  a chart. Whether the price is trending up or down, whether it is above or
  below its long term average and what that means, and whether trading volume
  supported the move. Then one sentence on what to watch next and what would
  change the picture.

"macro_analysis": string. 5 to 7 short sentences, under 160 words. The
  economy and the news. What today's data means for jobs, prices and interest
  rates. Explain each figure in ordinary words. Connect two things a casual
  reader would miss. Say whether the overall picture leans positive or
  negative and why. Finish with what would change your view.

"health_analysis": string. 4 to 6 short sentences, under 140 words. Whether
  the market as a whole is healthy. Are most stocks rising or only a few of
  the biggest. How expensive shares are compared with history, using the
  percentile supplied, and be honest that expensive markets say a lot about
  the next ten years and almost nothing about the next twelve months. Finish
  with which part of the cycle this looks like.

"answer": string. ONLY if a question was supplied in the data block under
  HIS QUESTION, otherwise return "". Answer that question directly and first,
  before anything else. Follow the length rule given with the question. Same
  plain English rules as everything else. Use the data supplied on the
  tickers he mentioned. If the data does not settle it, say what you can
  support and what you cannot rather than filling the gap. He is asking
  because he wants your actual read, so give one. Do not lecture him about
  his strategy, do not comment on whether the question is consistent with
  anything he has said before, and do not append warnings he did not ask
  for. Answer the question he asked.

"ticker_notes": array. ONLY if the data block lists DEEP DIVE TICKERS,
  otherwise return []. One object per ticker, each
  {"ticker": string, "note": string, "verdict": string}.
  "note" is 4 to 7 short sentences, under 140 words, vetting that name using
  the data supplied: what it did, what it costs against its growth, what
  analysts think, its earnings record, anything in the recent news, and how
  it sits for a 20 year holder. Plain English.
  "verdict" is one short phrase under 12 words giving your actual read, for
  example "cheap for the growth, earnings risk in November" or "priced for
  perfection". Be specific rather than balanced for its own sake.
  Do this for every deep dive ticker, whether or not a question was also
  asked. The two are separate requests.

"lean": string, exactly one of "bullish", "leaning bullish", "neutral",
  "leaning bearish", "bearish". Your overall near term read.

"lean_reason": string, one plain sentence, under 18 words.

"news_picks": array of exactly 10 objects, each
  {"title": string, "why": string, "tone": string, "tickers": string}.
  Pick from the market headlines OR from the company news on his own
  positions. Copy each title exactly, character for character, with no source
  name in brackets, or the link will break.
  "why" is ONE short sentence, under 25 words, in plain English, saying why it
  matters to him specifically.
  "tone" is exactly one of "high bullish", "lean bullish", "neutral",
  "lean bearish", "high bearish", judged on what the story means for prices,
  not the mood of the writing. Reserve "high" for something that genuinely
  changes the picture. Most stories are "lean" or "neutral".
  "tickers" is a short comma separated list of affected tickers he holds or
  watches, or an empty string.
  Rank them most important first.

ECONOMIC DATA RULE. A release has a result only if the data block marks it
RELEASED and gives an actual value. Anything marked otherwise has no result:
you may say what is expected and when it is due, but never say it came in at
a number, rose, fell, missed or beat. If the coverage block supplies a figure
for a release the feed left blank, you may use that figure, but say it came
from press coverage. Never invent a consensus number that was not supplied.

NUMBERS RULE, this matters more than anything else above. Every number you
write must appear verbatim in the MARKET DATA block. Do not estimate a level
from the chart images, do not convert a percentage into a level, do not recall
a figure from memory, and do not describe anything as elevated, cheap,
extended or historically high unless the data block gives you the comparison.
The charts are for reading shape and direction only, never for reading values
off an axis. If you want to cite a number you have not been given, leave it
out and describe the direction instead.

Do not use hyphens as punctuation anywhere in your output."""


def ai_brief(payload, images, quotes, fng, movers, cal_today, port):
    """One API call returning summary, chart read, news picks and considerations."""
    blank = {
        "summary": fallback_summary(quotes, fng, movers, cal_today, port),
        "portfolio_analysis": "", "technical_analysis": "",
        "macro_analysis": "", "health_analysis": "", "answer": "",
        "ticker_notes": [],
        "lean": "", "lean_reason": "", "news_picks": [],
    }
    key = os.environ.get("ANTHROPIC_API_KEY", "")
    if not key:
        return blank, False

    content = []
    for img in images:
        content.append({
            "type": "image",
            "source": {"type": "base64", "media_type": "image/png",
                       "data": base64.b64encode(img).decode()},
        })
    content.append({"type": "text",
                    "text": f"{AI_SCHEMA}\n\nMARKET DATA:\n{payload}"})

    try:
        r = requests.post(
            "https://api.anthropic.com/v1/messages",
            headers={"x-api-key": key,
                     "anthropic-version": "2023-06-01",
                     "content-type": "application/json"},
            json={"model": AI_MODEL, "max_tokens": 4000,
                  "messages": [{"role": "user", "content": content}]},
            timeout=120)
        r.raise_for_status()
        text = "".join(b.get("text", "") for b in r.json()["content"]
                       if b.get("type") == "text").strip()
        text = re.sub(r"^```(?:json)?|```$", "", text, flags=re.M).strip()
        data = json.loads(text)
        out = dict(blank)
        for k in blank:
            if data.get(k):
                out[k] = data[k]
        return out, True
    except Exception as e:
        print(f"ai brief failed, using fallback: {e}", file=sys.stderr)
        return blank, False


def intraday_facts(df):
    """Session volume facts, so the chart never has to be read for numbers.

    The two session chart puts the prior close auction right beside today's
    open, which is easy to misread as an opening spike. These figures state
    plainly which session each volume event belongs to.
    """
    try:
        day = df.index.date
        days = sorted(set(day))
        if len(days) < 1:
            return None
        today = df[[d == days[-1] for d in day]]
        prior = df[[d == days[0] for d in day]] if len(days) > 1 else None

        out = {
            "today_date": str(days[-1]),
            "today_bars": len(today),
            "today_volume": float(today["Volume"].sum()),
            "today_open_volume": float(today["Volume"].head(6).sum()),
            "today_max_bar": float(today["Volume"].max()),
            "today_max_time": str(today["Volume"].idxmax())[11:16],
            "today_high": float(today["High"].max()),
            "today_low": float(today["Low"].min()),
        }
        if prior is not None and len(prior):
            out.update({
                "prior_date": str(days[0]),
                "prior_volume": float(prior["Volume"].sum()),
                "prior_close_auction": float(prior["Volume"].tail(2).sum()),
                "prior_max_bar": float(prior["Volume"].max()),
                "prior_max_time": str(prior["Volume"].idxmax())[11:16],
            })
        return out
    except Exception as e:
        print(f"intraday facts failed: {e}", file=sys.stderr)
        return None


def index_technicals(symbol="^GSPC"):
    """Actual distance from the key averages, so nothing is eyeballed."""
    try:
        df = get_history(symbol, period="2y")
        c = df["Close"]
        px = float(c.iloc[-1])
        out = {"price": px}
        for n in (20, 50, 200):
            avg = float(c.rolling(n).mean().iloc[-1])
            out[f"sma{n}"] = avg
            out[f"gap{n}"] = (px / avg - 1) * 100
        hi = float(c.rolling(252).max().iloc[-1])
        out["from_high"] = (px / hi - 1) * 100
        return out
    except Exception as e:
        print(f"index technicals failed: {e}", file=sys.stderr)
        return None


def summary_payload(quotes, fng, movers, near_ma, cal_today, cal_ahead,
                    news, port, analysts, earnings, prev_state, tech=None,
                    my_news=None, fundamentals=None, earn_hist=None,
                    shorted=None, intraday=None, health=None,
                    sentiment=None, buzz=None, verified=None,
                    q_context="", d_tickers=None, e_results=None,
                    e_coverage=None, today_cal=None, tracked=None):
    """Compact text block handed to the model."""
    def line(names):
        return "; ".join(
            f"{lab} at {quotes[s]['last']:,.2f} ({quotes[s]['pct']:+.2f}%)"
            for s, lab in names.items() if s in quotes)

    parts = []
    if QUESTION:
        parts.append(
            "HIS QUESTION, answer this first in the answer field:\n"
            f"  {QUESTION}\n"
            f"Length: {DEPTH_RULES.get(QUESTION_DEPTH, DEPTH_RULES['normal'])}")
    if d_tickers:
        parts.append(
            "DEEP DIVE TICKERS, he asked for these to be vetted individually: "
            + ", ".join(d_tickers)
            + ". Produce a ticker_notes entry for each of them. This is a "
            "separate request from any question above and must be answered "
            "even if a question was also asked.")
    if q_context:
        parts.append(q_context)
    parts += [
        f"US markets, tradable index funds: {line(INDEXES)}",
        f"US cash indices and rates: {line(SPOT_INDEXES)}",
        f"Sectors: {line(SECTORS)}",
        f"Crypto: {line(CRYPTO)}",
        f"Commodities and dollar: {line(COMMODITIES)}",
        f"Global: {line(GLOBAL)}",
    ]
    if tech:
        parts.append(
            f"S&P 500 technicals: price {tech['price']:,.2f}; "
            f"20d avg {tech['sma20']:,.2f} ({tech['gap20']:+.2f}%); "
            f"50d avg {tech['sma50']:,.2f} ({tech['gap50']:+.2f}%); "
            f"200d avg {tech['sma200']:,.2f} ({tech['gap200']:+.2f}%); "
            f"{tech['from_high']:+.2f}% from the 52 week closing high")
    if intraday:
        i = intraday
        block = [
            "INTRADAY SESSION FACTS. The 5 minute chart shows TWO sessions "
            "side by side, separated by a blue vertical line and with the "
            "older one shaded. The tall volume bar just LEFT of that line is "
            f"the closing auction of {i.get('prior_date', 'the prior session')}, "
            "NOT an opening spike on the current session. Use these figures "
            "rather than reading bar heights off the picture.",
            f"Current session {i['today_date']}: total volume "
            f"{i['today_volume']:,.0f}; first 30 minutes {i['today_open_volume']:,.0f}; "
            f"largest single bar {i['today_max_bar']:,.0f} at {i['today_max_time']}; "
            f"range {i['today_low']:,.2f} to {i['today_high']:,.2f}",
        ]
        if i.get("prior_date"):
            block.append(
                f"Prior session {i['prior_date']}: total volume "
                f"{i['prior_volume']:,.0f}; closing auction "
                f"{i['prior_close_auction']:,.0f}; largest single bar "
                f"{i['prior_max_bar']:,.0f} at {i['prior_max_time']}")
            if i["today_volume"] and i["prior_volume"]:
                block.append(
                    "Current session volume is "
                    f"{i['today_volume'] / i['prior_volume'] * 100:.0f}% of the "
                    "prior session's total")
        parts.append("\n".join(block))
    if health and health.get("counted"):
        h = health
        parts.append(
            "MARKET HEALTH, measured across all "
            f"{h['counted']} S&P 500 members rather than the index alone:\n"
            f"Advancers {h['advancers']} vs decliners {h['decliners']}"
            + (f" (ratio {h['ad_ratio']:.2f})" if h.get("ad_ratio") else "")
            + f"; median stock {h['median_move']:+.2f}%; "
            f"{h['above50']:.0f}% above their 50 day average; "
            f"{h['above200']:.0f}% above their 200 day; "
            f"{h['new_highs']} new 52 week highs vs {h['new_lows']} new lows.\n"
            + (f"Equal weight vs cap weight (RSP minus SPY): today "
               f"{h['rsp_spy_day']:+.2f}%, past month {h['rsp_spy_month']:+.2f}%, "
               f"past quarter {h['rsp_spy_qtr']:+.2f}%. Negative means the "
               "average stock is lagging the megacaps.\n"
               if h.get("rsp_spy_month") is not None else "")
            + (f"Breadth reading: {breadth_verdict(h['above50'], h['above200'])}\n"
               if h.get("above50") is not None else "")
            + (("Valuation with full history: Shiller CAPE "
                f"{h['cape_hist']['current']:.1f} versus a long run mean of "
                f"{h['cape_hist']['mean']:.1f} and median "
                f"{h['cape_hist']['median']:.1f}; that is "
                f"{h['cape_hist']['vs_mean']:+.0f}% against the mean and sits "
                f"in the {h['cape_hist']['percentile']:.0f}th percentile of "
                f"{h['cape_hist']['months']:,} months since "
                f"{h['cape_hist']['since']}; the all time peak was "
                f"{h['cape_hist']['peak']:.1f} in "
                f"{h['cape_hist']['peak_date']}, so today is "
                f"{abs(h['cape_hist']['vs_peak']):.0f}% "
                f"{'below' if h['cape_hist']['vs_peak'] < 0 else 'above'} it")
               if h.get("cape_hist") else "")
            + ((f". S&P 500 trailing P/E {h['pe_hist']['current']:.1f} versus "
                f"mean {h['pe_hist']['mean']:.1f}, "
                f"{h['pe_hist']['percentile']:.0f}th percentile")
               if h.get("pe_hist") else "")
            + ((f".\nPut to call: index options volume "
                f"{h['pc_index']['volume_pc']:.2f}, open interest "
                f"{h['pc_index']['oi_pc']:.2f}")
               if h.get("pc_index") else "")
            + ((f"; single stock volume {h['pc_equity']['volume_pc']:.2f}. "
                "Index options run higher because they are hedges, single "
                "stock options run lower because they are speculation")
               if h.get("pc_equity") else "")
            + (f".\nRisk pricing: CBOE SKEW {h['^SKEW']:.1f} "
               f"({h['^SKEW_chg']:+.1f}%), VIX {h['^VIX']:.2f} "
               f"({h['^VIX_chg']:+.1f}%), HYG high yield credit "
               f"{h['HYG_chg']:+.2f}%." if h.get("^SKEW") else ""))
    if sentiment:
        base = next(iter(sentiment.values()))["baseline"]
        ranked = sorted(sentiment.items(), key=lambda kv: -kv[1]["vs_crowd"])
        parts.append(
            "RETAIL POSITIONING from StockTwits self tagged posts. Posters skew "
            f"bullish on nearly everything, so today's median across his names "
            f"is {base:.0f}% bullish. Judge each name by its distance from that "
            "baseline, not the raw figure, and ignore small samples. Most "
            "bullish: " + "; ".join(
                f"{k} {v['bull_pct']:.0f}% ({v['vs_crowd']:+.0f} vs baseline, "
                f"{v['tagged']} tagged)" for k, v in ranked[:6])
            + ". Least bullish: " + "; ".join(
                f"{k} {v['bull_pct']:.0f}% ({v['vs_crowd']:+.0f}, {v['tagged']} "
                "tagged)" for k, v in ranked[-6:]))
    if buzz:
        spikes = [x for x in buzz if x["change"] and x["change"] > 80]
        parts.append("REDDIT ATTENTION, mentions and change since 24h ago: "
                     + "; ".join(
                         f"{x['ticker']} {x['mentions']}"
                         + (f" ({x['change']:+.0f}%)" if x["change"] is not None else "")
                         for x in buzz[:12])
                     + (". Sudden jumps worth noting: "
                        + ", ".join(f"{x['ticker']} {x['change']:+.0f}%"
                                    for x in spikes) if spikes else ""))
    if fng:
        parts.append(f"CNN Fear and Greed: {fng['score']:.0f} ({fng['rating']}), "
                     f"week ago {fng['week']:.0f}, month ago {fng['month']:.0f}")
    if port:
        by_weight = sorted(port["rows"], key=lambda r: -r["value"])
        total = sum(r["value"] for r in port["rows"]) or 1
        top5 = sum(r["value"] for r in by_weight[:5]) / total * 100
        parts.append(
            f"PORTFOLIO: total {CURRENCY} {port['value']:,.0f}, today "
            f"{port['day_pl']:+,.0f} ({port['day_pct']:+.2f}%). "
            + ("Total gain since purchase " + format(port["total_gain"], "+,.0f") + ". "
               if port["total_gain"] is not None else "")
            + f"{len(port['rows'])} positions. Top 5 are {top5:.0f}% of the book.")
        if len(port.get("accounts", [])) > 1:
            parts.append("By account, each in its own currency: " + "; ".join(
                f"{a['cur']} {a['value']:,.0f}, today {a['day_pl']:+,.0f}, "
                + (f"gain since purchase {a['gain']:+,.0f} ({a['gain_pct']:+.2f}%)"
                   if a["gain"] is not None else "gain unknown")
                for a in port["accounts"]))
        parts.append("Position weights and returns: " + "; ".join(
            f"{r['sym']} {r['value'] / total * 100:.1f}% of book, "
            f"{CURRENCY} {r['value']:,.0f}, today {r['pct']:+.2f}% "
            f"({r['moved']:+,.0f})"
            + (f", since purchase {r['gain_pct']:+.1f}%"
               if r.get("gain_pct") is not None else "")
            for r in by_weight))
        if port.get("options"):
            parts.append("Option positions held: " + "; ".join(
                f"{o['symbol']} qty {o['qty']:,.0f}" for o in port["options"]))
    if analysts:
        parts.append("Analyst targets: " + "; ".join(
            f"{s} price {a['price']:,.2f} vs mean target {a['mean']:,.2f} "
            f"({a['upside']:+.1f}%), {a['rating'] or 'na'}, {a['count'] or '?'} analysts"
            for s, a in list(analysts.items())[:14]))
    if e_results:
        lines2 = ["EARNINGS RESULTS ALREADY OUT. These are actual reported "
                  "figures against consensus. Say plainly whether each beat or "
                  "missed and by how much. If the coverage lines mention "
                  "guidance or an outlook, report that too, and say it came "
                  "from press coverage."]
        for r in sorted(e_results.values(),
                        key=lambda x: x.get("days_ago", 99)):
            if not r.get("reported"):
                continue
            when = ("TODAY" if r.get("days_ago") == 0 else
                    f"{r.get('days_ago', '?')} days ago")
            if r.get("eps") is not None:
                lines2.append(
                    f"  {r['sym']}{' (HELD)' if r['held'] else ''} "
                    f"{r.get('quarter', '')}, reported {when}: EPS "
                    f"{r['eps']:,.2f} vs consensus {r['estimate']:,.2f}, "
                    f"{'BEAT' if r['beat'] else 'MISS'} by "
                    f"{r['surprise_pct']:+.1f}%")
            else:
                lines2.append(
                    f"  {r['sym']}{' (HELD)' if r['held'] else ''} reported "
                    f"{when}. No vendor consensus yet, so read the figures "
                    "out of the press release below rather than guessing a "
                    "beat or miss")
            for h in (e_coverage or {}).get(r["sym"], []):
                lines2.append(f"      COVERAGE: {h}")
            f_ = r.get("filing")
            if f_:
                lines2.append(f"      PRESS RELEASE filed {f_['filed']}: "
                              f"{f_['text'][:2200]}")
                for g in f_.get("guidance", [])[:5]:
                    lines2.append(f"      GUIDANCE LINE: {g[:220]}")
        parts.append("\n".join(lines2))
    if today_cal and tracked:
        pend = [(s_, today_cal[s_.split(".")[0]]) for s_ in tracked
                if s_.split(".")[0] in today_cal
                and not (e_results or {}).get(s_, {}).get("reported")]
        if pend:
            parts.append(
                "REPORTING TODAY BUT NOT OUT YET. Do not describe these as "
                "having reported, and do not invent a result: " + "; ".join(
                    f"{s_}{' (held)' if s_ in HOLDINGS else ''} {i['when']}, "
                    f"consensus {i['forecast'] or 'na'}" for s_, i in pend))
    if earnings:
        parts.append("Earnings around now: " + "; ".join(
            f"{e['sym']}{' (held)' if e['held'] else ''} "
            f"{'reported' if e['reported'] else 'reports'} "
            f"{e['date'].strftime('%b %d')}" for e in earnings[:14]))
    if fundamentals:
        held = [x for x in fundamentals if x in HOLDINGS]
        parts.append("Valuation on his holdings: " + "; ".join(
            f"{s_} PE {fundamentals[s_]['pe']:.0f}" if fundamentals[s_].get("pe")
            else f"{s_} PE n/a"
            for s_ in held[:16]))
        parts.append("Full valuation detail: " + "; ".join(
            f"{s_} fwdPE {fmt(fundamentals[s_]['fwd_pe'])} "
            f"PS {fmt(fundamentals[s_]['ps'])} PEG {fmt(fundamentals[s_]['peg'], 2)} "
            f"revgr {fmt(fundamentals[s_]['rev_growth'], 0, '%')}"
            for s_ in held[:14]))
    if earn_hist:
        parts.append("Earnings record, beats out of last four quarters: "
                     + "; ".join(f"{s_} {v['beats']}/{v['of']}, last surprise "
                                 f"{v['rows'][-1]['surprise']:+.1f}%"
                                 for s_, v in list(earn_hist.items())[:14]))
    if shorted:
        parts.append("Heavily shorted names he owns or watches: " + "; ".join(
            f"{r['sym']} {r['short_pct']:.1f}% of float, "
            f"{fmt(r['short_ratio'], 1)} days to cover" for r in shorted[:10]))
    if my_news:
        parts.append(
            "COMPANY NEWS ON HIS OWN POSITIONS in the last "
            f"{PORTFOLIO_NEWS_HOURS} hours. This is the highest value news in "
            "the report because it moves money he actually has at risk. Work "
            "it into the portfolio analysis, and pull anything genuinely "
            "significant into news_picks:\n" + "\n".join(
                f"- {r['sym']}{' (held)' if r['held'] else ' (watchlist)'} "
                f"{r['title']}" for r in my_news[:30]))
    if movers:
        parts.append("Biggest movers: " + "; ".join(
            f"{m['sym']} {m['pct']:+.1f}% on {m['rvol']:.1f}x volume"
            + (" | " + m["news"][0]["title"] if m.get("news") else "")
            for m in movers))
    if near_ma:
        parts.append("Near key moving averages: " + "; ".join(
            f"{r['sym']} {r['gap']:+.1f}% vs {r['ma']}d" for r in near_ma[:10]))
    if cal_today:
        released, pending = [], []
        for c in cal_today:
            if c.get("actual"):
                released.append(
                    f"{c['title']} RELEASED: actual {c['actual']}, forecast "
                    f"{c['forecast'] or 'na'}, prior {c['previous'] or 'na'}")
            else:
                pending.append(
                    f"{c['title']} NOT YET RELEASED at {c['time']} MT: forecast "
                    f"{c['forecast'] or 'na'}, prior {c['previous'] or 'na'}")
        if released:
            parts.append("Today's US data already OUT: " + "; ".join(released))
        if pending:
            parts.append(
                "Today's US data with NO RESULT IN THE CALENDAR FEED. The "
                "numbers below are FORECASTS, not results. Do not report a "
                "forecast as though it were released: " + "; ".join(pending))
    if verified:
        block = [
            "COVERAGE OF RELEASES THE FEED HAS NOT FILLED IN. The calendar "
            "feed lags, so a release can be out and widely reported while the "
            "feed still shows nothing. Below is news coverage from the last "
            "day for each such release. If the coverage states an actual "
            "figure, use it and say it came from press coverage rather than "
            "the calendar. If two sources disagree, say so. If the coverage "
            "does not clearly state a result, treat the release as still "
            "pending. Never average, round or infer a figure that is not "
            "written here."]
        for v in verified:
            ev = v["event"]
            block.append(
                f"\n{ev['title']} (forecast {ev['forecast'] or 'na'}, prior "
                f"{ev['previous'] or 'na'}):")
            for c in v["coverage"]:
                block.append(f"  HEADLINE: {c['headline']}")
                if c.get("text"):
                    block.append(f"  ARTICLE: {c['text'][:900]}")
        parts.append("\n".join(block))
    if cal_ahead:
        parts.append("Rest of week: " + "; ".join(
            f"{c['day']} {c['title']}" for c in cal_ahead[:10]))
    if prev_state.get("summary"):
        parts.append("YESTERDAY'S REPORT (note what has changed since this "
                     "where it is relevant, do not simply repeat it): "
                     f"{prev_state['summary']}")
    lines = []
    for n in news:
        tag = f"[{n['source']}{' PAYWALLED' if n.get('paywalled') else ''}]"
        lines.append(f"- {tag} {n['title']}"
                     + (f"\n    {n['summary']}" if n.get("summary") else ""))
    parts.append(
        "HEADLINES from twenty one outlets, some with a summary line beneath. "
        "Use all of them to inform your macro analysis.\n\n"
        "HOW TO RANK THEM when choosing news_picks:\n"
        "1. Anything that moves the whole market comes first, whatever the "
        "source. That means the Fed and Chair Warsh, FOMC decisions and "
        "minutes, Treasury Secretary Bessent, the President, tariffs and "
        "trade policy, wars and geopolitical shocks, and scheduled economic "
        "data such as CPI, PCE, GDP, payrolls and claims.\n"
        "2. Items marked [Short Squeez] are from a human curated newsletter "
        "where an editor already judged the story worth writing about, so "
        "weight them above an equivalent wire headline. They are not market "
        "moving on their own, so they never outrank category 1.\n"
        "3. Company news that touches what he holds or watches.\n"
        "4. Everything else on merit.\n\n"
        "Items marked PAYWALLED need a subscription, so only pick one if it "
        "is clearly more important than a free alternative. Skip clickbait, "
        "listicles and prediction teasers. Give ten, ranked by importance:\n"
        + "\n".join(lines))
    return "\n\n".join(parts)


def get_analysts(symbols):
    """Analyst mean target, rating and count for each symbol."""
    out = {}
    for s in symbols:
        try:
            tk = yf.Ticker(s)
            pt = tk.analyst_price_targets or {}
            info = tk.info or {}
            cur = pt.get("current") or info.get("currentPrice")
            mean = pt.get("mean")
            if not cur or not mean:
                continue
            out[s] = {
                "price": float(cur),
                "mean": float(mean),
                "high": float(pt["high"]) if pt.get("high") else None,
                "low": float(pt["low"]) if pt.get("low") else None,
                "upside": (float(mean) / float(cur) - 1) * 100,
                "rating": str(info.get("recommendationKey") or "").replace("_", " "),
                "count": info.get("numberOfAnalystOpinions"),
            }
        except Exception as e:
            print(f"analysts failed {s}: {e}", file=sys.stderr)
    return out


def get_fundamentals(symbols):
    """Valuation and short interest for each symbol."""
    out = {}
    for sym in symbols:
        try:
            i = yf.Ticker(sym).info or {}
            mcap = i.get("marketCap") or 0
            spf = i.get("shortPercentOfFloat")
            out[sym] = {
                "pe": i.get("trailingPE"),
                "fwd_pe": i.get("forwardPE"),
                "ps": i.get("priceToSalesTrailing12Months"),
                "peg": i.get("trailingPegRatio") or i.get("pegRatio"),
                "pb": i.get("priceToBook"),
                "ev_ebitda": i.get("enterpriseToEbitda"),
                "short_pct": (spf * 100) if spf else None,
                "short_ratio": i.get("shortRatio"),
                "shares_short": i.get("sharesShort"),
                "short_prior": i.get("sharesShortPriorMonth"),
                "mcap": mcap,
                "rev_growth": (i.get("revenueGrowth") or 0) * 100 or None,
                "margin": (i.get("profitMargins") or 0) * 100 or None,
            }
        except Exception as e:
            print(f"fundamentals failed {sym}: {e}", file=sys.stderr)
    return out


def get_earnings_history(symbols, quarters=4):
    """How each name has actually done against estimates recently."""
    out = {}
    for sym in symbols:
        try:
            eh = yf.Ticker(sym).earnings_history
            if eh is None or not len(eh):
                continue
            rows = []
            for idx, r in eh.tail(quarters).iterrows():
                try:
                    rows.append({
                        "quarter": str(idx)[:10],
                        "actual": float(r["epsActual"]),
                        "estimate": float(r["epsEstimate"]),
                        "surprise": float(r["surprisePercent"]) * 100,
                    })
                except Exception:
                    continue
            if rows:
                beats = sum(1 for r in rows if r["surprise"] > 0)
                out[sym] = {"rows": rows, "beats": beats, "of": len(rows)}
        except Exception as e:
            print(f"earnings history failed {sym}: {e}", file=sys.stderr)
    return out


EARN_KW = re.compile(
    r"\b(beat|beats|miss|missed|misses|topped|exceed\w*|surpass\w*|"
    r"guidance|outlook|forecast|raise[sd]?|lower\w*|cut|record|"
    r"earnings|revenue|EPS|profit|results|quarter)\b", re.I)


def company_name(sym):
    """Search by company name, since a bare ticker matches poorly."""
    try:
        info = yf.Ticker(sym).info or {}
        nm = info.get("shortName") or info.get("longName") or ""
        nm = re.sub(r"\b(Inc|Corp|Corporation|Ltd|Limited|plc|Co|Company|"
                    r"Holdings|Group|The|Class [A-C]|Technologies|"
                    r"Incorporated)\b\.?", "", nm, flags=re.I)
        return re.sub(r"[,.]+", " ", nm).strip() or sym
    except Exception:
        return sym


NASDAQ_H = {"User-Agent": UA, "Accept": "application/json"}
NASDAQ_CAL = "https://api.nasdaq.com/api/calendar/earnings?date={date}"
NASDAQ_SURPRISE = "https://api.nasdaq.com/api/company/{sym}/earnings-surprise"
SEC_H = {"User-Agent": "market-report " + MAIL_TO}
SEC_TICKERS = "https://www.sec.gov/files/company_tickers.json"
_CIK_CACHE = {}

TIME_LABEL = {
    "time-pre-market": "before the open",
    "time-after-hours": "after the close",
    "time-not-supplied": "time not given",
}


def earnings_calendar_day(day):
    """Who reports on a given day, and whether before the open or after the
    close. yfinance gives a date but never the time, which is the difference
    between a result being out already and being hours away."""
    out = {}
    try:
        r = requests.get(NASDAQ_CAL.format(date=day.isoformat()), timeout=25,
                         headers=NASDAQ_H)
        rows = ((r.json().get("data") or {}).get("rows")) or []
        for x in rows:
            sym = (x.get("symbol") or "").upper()
            if not sym:
                continue
            out[sym] = {
                "when": TIME_LABEL.get(x.get("time"), x.get("time") or ""),
                "raw_time": x.get("time") or "",
                "forecast": x.get("epsForecast") or "",
                "last_year": x.get("lastYearEPS") or "",
                "name": x.get("name") or "",
                "date": day,
            }
    except Exception as e:
        print(f"nasdaq calendar failed {day}: {e}", file=sys.stderr)
    return out


SEC_H = {"User-Agent": f"market report {MAIL_TO}"}
SEC_TICKERS = "https://www.sec.gov/files/company_tickers.json"
_CIK_CACHE = {}


def sec_cik(sym):
    """Ticker to SEC CIK. The map is fetched once and reused."""
    if not _CIK_CACHE:
        try:
            data = requests.get(SEC_TICKERS, timeout=25, headers=SEC_H).json()
            for v in data.values():
                _CIK_CACHE[v["ticker"].upper()] = str(v["cik_str"]).zfill(10)
        except Exception as e:
            print(f"SEC ticker map failed: {e}", file=sys.stderr)
            _CIK_CACHE["__failed__"] = True
    return _CIK_CACHE.get(sym.split(".")[0].upper())


def sec_earnings_release(sym, back_days=6):
    """The earnings press release straight from the filing.

    A company files an Item 2.02 8-K within minutes of reporting, long before
    any data vendor updates. This is the only source that has the numbers on
    the same afternoon, and it is also the only one carrying guidance.
    """
    cik = sec_cik(sym)
    if not cik:
        return None
    today = dt.datetime.now(MARKET_TZ).date()
    try:
        sub = requests.get(f"https://data.sec.gov/submissions/CIK{cik}.json",
                           timeout=25, headers=SEC_H).json()
        rec = sub["filings"]["recent"]
    except Exception as e:
        print(f"SEC submissions failed {sym}: {e}", file=sys.stderr)
        return None

    for i, form in enumerate(rec.get("form", [])[:40]):
        if form != "8-K":
            continue
        if "2.02" not in (rec.get("items", [""] * 40)[i] or ""):
            continue
        try:
            filed = dt.date.fromisoformat(rec["filingDate"][i])
        except Exception:
            continue
        if not (0 <= (today - filed).days <= back_days):
            continue

        acc = rec["accessionNumber"][i].replace("-", "")
        base = (f"https://www.sec.gov/Archives/edgar/data/{int(cik)}/{acc}")
        try:
            files = [f["name"] for f in
                     requests.get(base + "/index.json", timeout=25,
                                  headers=SEC_H).json()["directory"]["item"]]
        except Exception:
            continue

        # the press release is the exhibit, not the cover page. Filenames vary
        # wildly, so match on 99 anywhere and fall back to the biggest html.
        cands = [f for f in files
                 if f.lower().endswith((".htm", ".html"))
                 and "99" in f
                 and "index" not in f.lower()]
        if not cands:
            cands = [f for f in files if f.lower().endswith((".htm", ".html"))
                     and not re.match(r"^(R\d+|.*index)", f, re.I)]
        for name in cands:
            try:
                html = requests.get(f"{base}/{name}", timeout=25,
                                    headers=SEC_H).text
            except Exception:
                continue
            txt = re.sub(r"<[^>]+>", " ", html)
            txt = re.sub(r"&[a-z#0-9]+;", " ", txt)
            txt = re.sub(r"\s+", " ", txt).strip()
            if len(txt) < 900 or not re.search(r"\d", txt):
                continue
            # split on sentence ends only, never on the decimal point inside
            # a figure, or "$192.0 billion" becomes two useless fragments
            sentences = re.split(r"(?<=[a-z0-9%\)])\.\s+(?=[A-Z(])",
                                 txt[:14000])
            guide = []
            for x in sentences:
                x = x.strip()
                # skip the EDGAR document header that precedes the release
                x = re.sub(r"^EX-\d+\.?\d*\s+\d+\s+\S+\.htm\s+EX-\d+\.?\d*"
                           r"\s+Document\s+Exhibit\s+\d+\.?\d*\s*", "", x, flags=re.I)
                if len(x) < 30 or x.lower().startswith("ex-"):
                    continue
                if re.search(r"\b(guidance|outlook|raising|lowering|"
                             r"expects?|forecast)\b", x, re.I):
                    guide.append(x)
                if len(guide) >= 6:
                    break

            # headline figures for the table, straight from the release
            def grab(pattern):
                m2 = re.search(pattern, txt[:6000], re.I)
                return m2.group(1).strip() if m2 else None

            metrics = {
                "revenue": grab(r"revenue of \$?([\d.,]+\s*(?:billion|million))"),
                "eps": grab(r"(?:diluted )?(?:earnings per share|EPS)[^$]{0,40}"
                            r"\$([\d.]+)"),
                "non_gaap_eps": grab(r"non-?GAAP diluted EPS of \$([\d.]+)"),
            }
            return {
                "filed": filed,
                "days_ago": (today - filed).days,
                "url": f"{base}/{name}",
                "text": re.sub(r"^EX-\d+\.?\d*\s+\d+\s+\S+\.htm\s+EX-\d+\.?\d*"
                               r"\s+Document\s+Exhibit\s+\d+\.?\d*\s*", "",
                               txt, flags=re.I)[:5000],
                "guidance": guide,
                "metrics": {k: v for k, v in metrics.items() if v},
            }
    return None


def earnings_results(symbols, back_days=6):
    """Actual reported EPS against consensus, for anything that has already
    reported recently. yfinance lags by a full quarter here, so a company
    that reported this morning shows nothing in its earnings history."""
    today = dt.datetime.now(MARKET_TZ).date()
    out = {}
    for sym in symbols:
        base = sym.split(".")[0]          # CM.TO reports under CM
        try:
            r = requests.get(NASDAQ_SURPRISE.format(sym=base), timeout=20,
                             headers=NASDAQ_H)
            rows = ((r.json().get("data") or {})
                    .get("earningsSurpriseTable") or {}).get("rows") or []
        except Exception as e:
            print(f"earnings surprise failed {sym}: {e}", file=sys.stderr)
            continue
        for x in rows:
            try:
                d = dt.datetime.strptime(x["dateReported"], "%m/%d/%Y").date()
            except Exception:
                continue
            days = (today - d).days
            if 0 <= days <= back_days:
                try:
                    eps = float(x.get("eps"))
                    est = float(x.get("consensusForecast"))
                except Exception:
                    continue
                out[sym] = {
                    "sym": sym,
                    "name": "",
                    "date": d,
                    "days_ago": days,
                    "quarter": x.get("fiscalQtrEnd", ""),
                    "eps": eps,
                    "estimate": est,
                    "surprise_pct": float(x.get("percentageSurprise") or 0),
                    "beat": eps > est,
                    "held": sym in HOLDINGS,
                }
                break
    return out


def merge_earnings_sources(symbols, today_cal, back_days=6):
    """Combine the vendor numbers with the filings.

    Nasdaq gives a clean EPS against consensus but lags by hours, so a
    company reporting at the bell shows nothing there until the next day.
    The SEC filing appears within minutes and carries guidance. Whichever
    exists is used, and when both do they sit side by side.
    """
    vendor = earnings_results(symbols, back_days=back_days)
    today = dt.datetime.now(MARKET_TZ).date()

    # Candidates come from three places, because no single one is complete.
    # A company reporting after the close is not on today's calendar the next
    # morning, and the vendor can lag it by more than a day, so the recent
    # calendar days are swept as well.
    candidates = set(vendor)
    cal_by_sym = dict(today_cal)
    for back in range(0, back_days + 1):
        day = today - dt.timedelta(days=back)
        if day.weekday() >= 5:
            continue
        day_cal = today_cal if back == 0 else earnings_calendar_day(day)
        for base, info in day_cal.items():
            for sym in symbols:
                if sym.split(".")[0] == base:
                    candidates.add(sym)
                    cal_by_sym.setdefault(base, info)
    today_cal = cal_by_sym

    out = {}
    for sym in sorted(candidates):
        row = dict(vendor.get(sym) or {})
        row.setdefault("sym", sym)
        row.setdefault("held", sym in HOLDINGS)
        info = today_cal.get(sym.split(".")[0])
        if info:
            row["when"] = info["when"]
            row["raw_time"] = info["raw_time"]
            row["name"] = info.get("name") or row.get("name") or sym
            row["scheduled_today"] = True
            row.setdefault("estimate_str", info.get("forecast", ""))
        filing = sec_earnings_release(sym, back_days=back_days)
        if filing:
            row["filing"] = filing
            row.setdefault("date", filing["filed"])
            row.setdefault("days_ago", filing["days_ago"])
        if row.get("eps") is not None or filing:
            row["reported"] = True
        out[sym] = row
    return out


def earnings_coverage(results, per_name=3):
    """Guidance is not in any API, so it comes from the coverage. Searched by
    company name because a bare ticker returns too much unrelated noise."""
    found = {}
    for sym, r in list(results.items())[:8]:
        name = r.get("name") or sym
        for term in (f"{name} earnings guidance", f"{name} quarterly results"):
            try:
                url = GOOGLE_NEWS_Q.replace("when:1d", "when:3d").format(
                    q=requests.utils.quote(term))
                entries = feedparser.parse(
                    requests.get(url, timeout=25,
                                 headers={"User-Agent": UA}).content).entries
            except Exception:
                continue
            items = []
            for e in entries[:6]:
                head = (e.get("title") or "").strip()
                if head:
                    items.append(head)
                if len(items) >= per_name:
                    break
            if items:
                found[sym] = items
                break
    return found


def heavily_shorted(fundamentals, min_pct=5.0, min_mcap=2e9):
    """Medium and large caps carrying an unusual short position."""
    out = []
    for sym, f in fundamentals.items():
        if not f.get("short_pct") or f["short_pct"] < min_pct:
            continue
        if (f.get("mcap") or 0) < min_mcap:
            continue
        trend = None
        if f.get("shares_short") and f.get("short_prior"):
            trend = (f["shares_short"] / f["short_prior"] - 1) * 100
        out.append({**f, "sym": sym, "trend": trend})
    out.sort(key=lambda r: -r["short_pct"])
    return out


def get_earnings(symbols, ahead_days=21, back_days=5):
    """Earnings dates around now, both just reported and coming up."""
    today = dt.datetime.now(MARKET_TZ).date()
    out = []
    for s in symbols:
        try:
            cal = yf.Ticker(s).calendar or {}
            dates = cal.get("Earnings Date") or []
            if not isinstance(dates, list):
                dates = [dates]
            for d in dates:
                if not isinstance(d, dt.date):
                    continue
                days = (d - today).days
                if -back_days <= days <= ahead_days:
                    out.append({
                        "sym": s, "date": d, "days": days,
                        "reported": days < 0,
                        "held": s in HOLDINGS,
                    })
                    break
        except Exception as e:
            print(f"earnings failed {s}: {e}", file=sys.stderr)
    out.sort(key=lambda x: x["date"])
    return out


def fx_rates(symbols):
    """USD per unit of each foreign currency the holdings trade in."""
    needed = {currency_of(s) for s in symbols} - {"USD"}
    rates = {"USD": 1.0}
    for cur in needed:
        try:
            fi = yf.Ticker(f"{cur}=X").fast_info
            rate = float(fi["lastPrice"])          # units of cur per 1 USD
            rates[cur] = 1.0 / rate if rate else 1.0
        except Exception as e:
            print(f"fx failed {cur}, treating as 1:1: {e}", file=sys.stderr)
            rates[cur] = 1.0
    return rates


def portfolio_view(quotes):
    """Value the holdings, split by listing currency so the totals reconcile
    against a broker that keeps USD and CAD as separate accounts."""
    if not HOLDINGS:
        return None
    rates = fx_rates(HOLDINGS.keys())
    rows, missing = [], []
    books = {}          # per currency subtotals, in that currency

    for sym, shares in HOLDINGS.items():
        q = quotes.get(sym)
        if not q:
            missing.append(sym)
            continue
        cur = currency_of(sym)
        fx = rates.get(cur, 1.0)
        native_val = q["last"] * shares
        native_moved = (q["last"] - q["prev"]) * shares
        book = BOOK_COST.get(sym)
        native_cost = book * shares if book else None

        b = books.setdefault(cur, {"value": 0.0, "moved": 0.0, "cost": 0.0,
                                   "has_cost": False, "fx": fx, "n": 0})
        b["value"] += native_val
        b["moved"] += native_moved
        b["n"] += 1
        if native_cost is not None:
            b["cost"] += native_cost
            b["has_cost"] = True

        rows.append({
            "sym": sym, "shares": shares, "price": q["last"],
            "pct": q["pct"], "cur": cur,
            "value": native_val * fx,          # reporting currency
            "moved": native_moved * fx,
            "native_value": native_val,
            "native_gain": (native_val - native_cost) if native_cost is not None else None,
            "gain": ((native_val - native_cost) * fx) if native_cost is not None else None,
            "gain_pct": (q["last"] / book - 1) * 100 if book else None,
            "ext": q.get("ext"),
            "ext_pct": q.get("ext_pct"),
        })

    if not rows:
        return None
    if missing:
        print(f"no quote for: {', '.join(missing)}", file=sys.stderr)

    value = sum(b["value"] * b["fx"] for b in books.values())
    day_pl = sum(b["moved"] * b["fx"] for b in books.values())
    cost = sum(b["cost"] * b["fx"] for b in books.values() if b["has_cost"])
    prev_value = value - day_pl

    accounts = []
    for cur in sorted(books, key=lambda c: -books[c]["value"]):
        b = books[cur]
        prev = b["value"] - b["moved"]
        accounts.append({
            "cur": cur,
            "positions": b["n"],
            "value": b["value"],
            "day_pl": b["moved"],
            "day_pct": (b["moved"] / prev * 100) if prev else 0.0,
            "gain": (b["value"] - b["cost"]) if b["has_cost"] else None,
            "gain_pct": ((b["value"] / b["cost"] - 1) * 100
                         if b["has_cost"] and b["cost"] else None),
            "fx": b["fx"],
        })

    return {
        "rows": rows,
        "accounts": accounts,
        "value": value + CASH,
        "day_pl": day_pl,
        "day_pct": (day_pl / prev_value * 100) if prev_value else 0.0,
        "total_gain": (value - cost) if cost else None,
        "missing": missing,
        "options": OPTIONS,
        "source": POSITIONS_SOURCE,
        "fx": {k: v for k, v in rates.items() if k != "USD"},
    }


def read_state():
    try:
        with open(STATE_FILE, encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return {}


def write_state(state):
    try:
        with open(STATE_FILE, "w", encoding="utf-8") as f:
            json.dump(state, f, indent=1)
    except Exception as e:
        print(f"state write failed: {e}", file=sys.stderr)


# ============================== IMAGES ==============================


def color_for(pct):
    if pct >= 2.0:
        return "#0b6e3d"
    if pct >= 1.0:
        return "#1a8b52"
    if pct >= 0.25:
        return "#3aa76d"
    if pct > -0.25:
        return "#6b7280"
    if pct > -1.0:
        return "#d1584f"
    if pct > -2.0:
        return "#b3352c"
    return "#8c1f18"


def build_heatmap(sector_q, mega_q):
    """Grid heatmap: sectors on top, mega caps below."""
    fig = plt.figure(figsize=(11, 7), dpi=110)
    fig.patch.set_facecolor("#111418")

    def draw_block(ax, items, title, cols):
        ax.set_facecolor("#111418")
        ax.set_title(title, color="#e5e7eb", fontsize=13,
                     loc="left", pad=10, fontweight="bold")
        rows = -(-len(items) // cols)
        for i, (label, pct) in enumerate(items):
            r, c = divmod(i, cols)
            x, y = c, rows - r - 1
            ax.add_patch(plt.Rectangle((x + .02, y + .02), .96, .96,
                                       facecolor=color_for(pct),
                                       edgecolor="#111418", linewidth=2))
            ax.text(x + .5, y + .62, label, ha="center", va="center",
                    color="white", fontsize=11, fontweight="bold")
            ax.text(x + .5, y + .32, f"{pct:+.2f}%", ha="center", va="center",
                    color="white", fontsize=12)
        ax.set_xlim(0, cols)
        ax.set_ylim(0, rows)
        ax.axis("off")

    ax1 = fig.add_axes([0.02, 0.60, 0.96, 0.33])
    ax2 = fig.add_axes([0.02, 0.04, 0.96, 0.50])
    draw_block(ax1, sector_q, "Sectors", 6)
    draw_block(ax2, mega_q, "Mega caps", 5)

    buf = io.BytesIO()
    fig.savefig(buf, format="png", facecolor=fig.get_facecolor())
    plt.close(fig)
    return buf.getvalue()


def get_intraday(symbol, interval=INTRADAY_INTERVAL, days=INTRADAY_DAYS):
    df = yf.download(symbol, period=f"{days}d", interval=interval,
                     progress=False, auto_adjust=False, prepost=False)
    if hasattr(df.columns, "levels") and df.columns.nlevels > 1:
        df.columns = df.columns.droplevel(1)
    df.index = df.index.tz_convert(MARKET_TZ)
    return df


def build_chart(df, prev_close=None):
    """Intraday candles with VWAP and a prior close reference line.

    Two sessions are shown so the morning has context, but they are plotted
    as one continuous series. Without a hard visual break the previous
    session's closing auction volume sits right next to today's open and
    reads as an opening spike, so the prior session is shaded and both
    sessions are labelled.
    """
    style = mpf.make_mpf_style(
        base_mpf_style="nightclouds",
        rc={"font.size": 9},
        marketcolors=mpf.make_marketcolors(
            up="#3fb950", down="#f85149", edge="inherit",
            wick="inherit", volume="in"))

    tp = (df["High"] + df["Low"] + df["Close"]) / 3
    day = df.index.date
    cum_pv = (tp * df["Volume"]).groupby(day).cumsum()
    cum_v = df["Volume"].groupby(day).cumsum().replace(0, float("nan"))
    vwap = cum_pv / cum_v

    adds = [mpf.make_addplot(vwap, color="#f0b429", width=1.1)]

    hlines = None
    if prev_close:
        hlines = dict(hlines=[float(prev_close)], colors=["#c9d1d9"],
                      linestyle="--", linewidths=1.2)

    days_seen = sorted(set(day))
    label = f"S&P 500 intraday, {INTRADAY_INTERVAL} candles"
    sub = "gold line is VWAP"
    if prev_close:
        sub += ", dashed line is prior close"

    fig, axes = mpf.plot(df, type="candle", style=style, volume=True,
                         addplot=adds, hlines=hlines,
                         figsize=(11, 6.4), returnfig=True,
                         tight_layout=True)

    # shade and label each session so the boundary cannot be misread
    if len(days_seen) > 1:
        positions = list(range(len(df)))
        split = next(i for i, d in enumerate(day) if d == days_seen[-1])
        for ax in axes[:2] + axes[2:3]:
            try:
                ax.axvspan(positions[0] - 0.5, split - 0.5,
                           color="#ffffff", alpha=0.045, zorder=0)
                ax.axvline(split - 0.5, color="#79c0ff", linewidth=1.6,
                           linestyle="-", alpha=0.9, zorder=3)
            except Exception:
                pass
        price_ax = axes[0]
        top = price_ax.get_ylim()[1]
        price_ax.text(split / 2, top, f"PRIOR SESSION {days_seen[0]}",
                      color="#8b949e", fontsize=8, ha="center", va="top",
                      fontweight="bold")
        price_ax.text((split + len(df)) / 2, top, f"TODAY {days_seen[-1]}",
                      color="#79c0ff", fontsize=8, ha="center", va="top",
                      fontweight="bold")
        sub += ". Shaded area and blue line separate the two sessions"

    fig.suptitle(label, color="#e6edf3", fontsize=13,
                 fontweight="bold", y=1.02)
    fig.text(0.5, 0.975, sub, color="#8b949e", fontsize=9, ha="center")

    buf = io.BytesIO()
    fig.savefig(buf, format="png", dpi=110, bbox_inches="tight",
                facecolor=fig.get_facecolor())
    plt.close(fig)
    return buf.getvalue()


def build_daily_chart(df, bars=140):
    """Daily candles with 20 / 50 / 200 SMA and volume, for trend context."""
    style = mpf.make_mpf_style(
        base_mpf_style="nightclouds",
        rc={"font.size": 9},
        marketcolors=mpf.make_marketcolors(
            up="#3fb950", down="#f85149", edge="inherit",
            wick="inherit", volume="in"))

    # averages are computed on the full history, then sliced, so the
    # 200 SMA is valid even though only the last 140 bars are shown
    smas = {20: "#58a6ff", 50: "#f0b429", 200: "#d2a8ff"}
    view = df.tail(bars)
    adds = [mpf.make_addplot(df["Close"].rolling(n).mean().tail(bars),
                             color=c, width=1.1)
            for n, c in smas.items()]

    fig, _ = mpf.plot(view, type="candle", style=style, volume=True,
                      addplot=adds, figsize=(11, 6.2),
                      returnfig=True, tight_layout=True)
    fig.suptitle("S&P 500 daily", color="#e6edf3", fontsize=13,
                 fontweight="bold", y=1.02)
    fig.text(0.5, 0.975, "20 SMA blue, 50 SMA gold, 200 SMA purple",
             color="#8b949e", fontsize=9, ha="center")

    buf = io.BytesIO()
    fig.savefig(buf, format="png", dpi=110, bbox_inches="tight",
                facecolor=fig.get_facecolor())
    plt.close(fig)
    return buf.getvalue()

# ============================== HTML ==============================


CSS = """
.wrap{background:#0d1117;color:#e6edf3;font-family:-apple-system,Segoe UI,Arial,sans-serif;
     padding:18px;}
.wrap h2{font-size:16px;margin:26px 0 8px;color:#e6edf3;border-bottom:1px solid #30363d;
     padding-bottom:6px;}
.wrap table{border-collapse:collapse;width:100%;font-size:14px;color:#e6edf3;}
.wrap td,.wrap th{padding:7px 8px;text-align:left;border-bottom:1px solid #21262d;
     color:#e6edf3;}
.wrap th{color:#8b949e;font-weight:600;font-size:12px;text-transform:uppercase;}
.wrap p{color:#e6edf3;}
.num{text-align:right;font-variant-numeric:tabular-nums;}
.up{color:#3fb950 !important;font-weight:600;}
.dn{color:#f85149 !important;font-weight:600;}
.flat{color:#8b949e !important;}
.wrap img{width:100%;border-radius:8px;margin-top:6px;}
.wrap a{color:#79c0ff !important;text-decoration:none;}
.small{color:#8b949e !important;font-size:12px;}
.hdr{font-size:20px;font-weight:700;color:#e6edf3;}
.hi{color:#f0b429 !important;font-size:11px;font-weight:600;}
.lede{background:#161b22;color:#e6edf3;border-left:3px solid #58a6ff;border-radius:6px;
      padding:14px 16px;margin:14px 0 6px;font-size:15px;line-height:1.55;}
.think{background:#161b22;color:#e6edf3;border-left:3px solid #f0b429;border-radius:6px;
      padding:14px 16px;margin:6px 0;font-size:14px;line-height:1.55;}
details{margin-top:8px;} summary{cursor:pointer;color:#8b949e;}
"""


def cls(p):
    return "up" if p > 0.05 else ("dn" if p < -0.05 else "flat")


def ext_cell(q):
    if q.get("ext_pct") is None:
        return "<td class='num small'>-</td>"
    return (f"<td class='num small {cls(q['ext_pct'])}'>"
            f"{q['ext']:,.2f} ({q['ext_pct']:+.2f}%)</td>")


def quote_rows(names, quotes):
    out = []
    for sym, label in names.items():
        q = quotes.get(sym)
        if not q:
            continue
        out.append(
            f"<tr><td>{label}</td>"
            f"<td class='num'>{q['last']:,.2f}</td>"
            f"<td class='num {cls(q['dollar'])}'>{q['dollar']:+,.2f}</td>"
            f"<td class='num {cls(q['pct'])}'>{q['pct']:+.2f}%</td>"
            + ext_cell(q) + "</tr>")
    return "".join(out)


def simple_table(names, quotes, head="Market", sort=False):
    items = list(names.items())
    if sort:
        items.sort(key=lambda kv: quotes.get(kv[0], {}).get("pct", 0), reverse=True)
    rows = "".join(
        f"<tr><td>{lab}</td><td class='num'>{quotes[s]['last']:,.2f}</td>"
        f"<td class='num {cls(quotes[s]['dollar'])}'>{quotes[s]['dollar']:+,.2f}</td>"
        f"<td class='num {cls(quotes[s]['pct'])}'>{quotes[s]['pct']:+.2f}%</td>"
        + ext_cell(quotes[s]) + "</tr>"
        for s, lab in items if s in quotes)
    return (f"<table><tr><th>{head}</th><th class='num'>Close</th>"
            f"<th class='num'>Change</th><th class='num'>%</th>"
            f"<th class='num'>{session_label().title()}</th></tr>{rows}</table>")


def retail_block(sentiment, buzz):
    """What retail is saying, kept clearly separate from the hard data."""
    if not sentiment and not buzz:
        return ""

    body = ""
    if sentiment:
        ranked = sorted(sentiment.items(), key=lambda kv: -kv[1]["vs_crowd"])
        base = next(iter(sentiment.values()))["baseline"]
        top, bottom = ranked[:6], ranked[-6:]

        def rows(items):
            return "".join(
                f"<tr><td><b>{sym}</b>"
                + ("<span class='small'> held</span>" if sym in HOLDINGS else "")
                + f"</td><td class='num'>{v['bull_pct']:.0f}%</td>"
                f"<td class='num {cls(v['vs_crowd'])}'>{v['vs_crowd']:+.0f}</td>"
                f"<td class='num small'>{v['tagged']}</td></tr>"
                for sym, v in items)

        body += (
            "<p class='small' style='margin:12px 0 2px;color:#e6edf3;"
            "font-weight:600'>Most bullish against the crowd baseline</p>"
            "<table><tr><th>Ticker</th><th class='num'>Bullish</th>"
            "<th class='num'>vs baseline</th><th class='num'>Tagged</th></tr>"
            + rows(top) + "</table>"
            "<p class='small' style='margin:16px 0 2px;color:#e6edf3;"
            "font-weight:600'>Least bullish against the crowd baseline</p>"
            "<table><tr><th>Ticker</th><th class='num'>Bullish</th>"
            "<th class='num'>vs baseline</th><th class='num'>Tagged</th></tr>"
            + rows(bottom) + "</table>"
            f"<p class='small'>StockTwits posters tag their own messages and "
            f"skew bullish on nearly everything, so the raw percentage means "
            f"little on its own. Today's median across your names is "
            f"{base:.0f}% bullish, and the middle column is each name's "
            f"distance from that. Tagged is the sample size, so anything in "
            f"single digits is noise.</p>")

    if buzz:
        held = set(HOLDINGS) | set(WATCHLIST)
        rows = "".join(
            f"<tr><td><b>{x['ticker']}</b>"
            + ("<span class='small'> yours</span>" if x["ticker"] in held else "")
            + f"</td><td class='num'>{x['mentions']:,}</td>"
            f"<td class='num {cls(x['change'] or 0)}'>"
            f"{format(x['change'], '+.0f') + '%' if x['change'] is not None else '-'}"
            f"</td><td class='num small'>{x['upvotes']:,}</td></tr>"
            for x in buzz)
        body += ("<p class='small' style='margin:16px 0 2px;color:#e6edf3;"
                 "font-weight:600'>Most discussed on Reddit</p><table>"
                 "<tr><th>Ticker</th><th class='num'>Mentions</th>"
                 "<th class='num'>vs 24h</th><th class='num'>Upvotes</th></tr>"
                 + rows + "</table>"
                 "<p class='small'>The change column matters more than the "
                 "count, since the same megacaps top this list every day. A "
                 "large jump means something happened.</p>")

    return ("<h2 id='retail'>What retail is saying</h2>"
            "<p class='small'>Crowd positioning, not analysis. Useful for "
            "spotting where attention has moved, and occasionally as a "
            "contrarian signal at extremes.</p>" + body)


def gauge_bar(pct, good_high=True):
    pct = max(0.0, min(100.0, float(pct)))
    val = pct if good_high else 100 - pct
    col = ("#3fb950" if val >= 65 else "#8b949e" if val >= 35 else "#f85149")
    return (f"<div style='background:#21262d;border-radius:5px;height:8px;"
            f"margin:5px 0 2px;'><div style='background:{col};width:{pct:.0f}%;"
            f"height:8px;border-radius:5px'></div></div>")


def breadth_verdict(above50, above200):
    """Plain reading of what the two breadth figures mean together."""
    if above50 >= 70 and above200 >= 70:
        return ("Broad participation. Most stocks are in an uptrend on both "
                "horizons, which is the healthiest configuration.")
    if above50 < 40 and above200 >= 60:
        return ("Short term pullback inside a longer uptrend. The 50 day "
                "figure has cracked while the 200 day is intact, which is "
                "what an ordinary correction looks like.")
    if above50 >= 60 and above200 < 45:
        return ("Early recovery. Stocks are bouncing off lows but most have "
                "not yet repaired the longer trend.")
    if above50 < 40 and above200 < 40:
        return ("Broad weakness on both horizons. This configuration shows up "
                "in genuine downtrends, not routine pullbacks.")
    if above200 - above50 > 20:
        return ("The average stock is losing short term momentum while the "
                "long trend holds. Worth watching rather than acting on.")
    return ("Mixed. Neither figure is at an extreme, so breadth is not saying "
            "much either way right now.")


def ordinal(v):
    """42.0 becomes 42nd. Kept out of the f-string so this stays valid on
    Python 3.11, where nested double quotes inside an f-string are illegal."""
    n = int(round(float(v)))
    if 10 <= n % 100 <= 20:
        suffix = "th"
    else:
        suffix = {1: "st", 2: "nd", 3: "rd"}.get(n % 10, "th")
    return f"{n}{suffix}"


def hist_row(label, h, dp=1):
    """One valuation line with its own history alongside it."""
    if not h:
        return ""
    return (f"<tr><td>{label}</td>"
            f"<td class='num'><b>{h['current']:,.{dp}f}</b></td>"
            f"<td class='num'>{h['mean']:,.{dp}f}</td>"
            f"<td class='num'>{h['median']:,.{dp}f}</td>"
            f"<td class='num'>{h['peak']:,.{dp}f}</td>"
            f"<td class='small'>{h['peak_date']}</td>"
            f"<td class='num {cls(h['percentile'] - 50)}'>"
            f"{ordinal(h['percentile'])}</td></tr>")


def health_block(h):
    """Market wide breadth, valuation and risk pricing, with context."""
    if not h:
        return ""

    def row(label, value, note=""):
        return (f"<tr><td>{label}</td><td class='num'>{value}</td>"
                f"<td class='small'>{note}</td></tr>")

    breadth = ""
    if h.get("counted"):
        ad = h.get("ad_ratio")
        breadth = (
            "<p class='small' style='margin:12px 0 2px;color:#e6edf3;"
            f"font-weight:600'>Breadth, all {h['counted']} S&amp;P 500 members</p>"
            + gauge_bar(h["above50"])
            + f"<p class='small'>{h['above50']:.0f}% above their 50 day "
              f"average, {h['above200']:.0f}% above their 200 day</p>"
            + "<table>"
            + row("Advancers vs decliners",
                  f"{h['advancers']} to {h['decliners']}",
                  f"ratio {ad:.2f}" if ad else "")
            + row("Median stock move", f"{h['median_move']:+.2f}%",
                  "the typical stock, not the index")
            + row("New 52 week highs", h["new_highs"],
                  "expansion is healthy, contraction while the index rises is not")
            + row("New 52 week lows", h["new_lows"], "")
            + row("Above 50 day average", f"{h['above50']:.0f}%",
                  "short term trend, roughly ten weeks")
            + row("Above 200 day average", f"{h['above200']:.0f}%",
                  "long term trend, roughly a year")
            + "</table>"
            + "<p class='small'><b>What the two averages mean together.</b> "
              "The 50 day is the short trend and the 200 day is the long one. "
              "When most stocks sit above both, the rally is broad. When the "
              "50 day figure falls hard while the 200 day holds, it is usually "
              "a pullback inside an uptrend. When both fall below 40 percent, "
              "the damage is structural rather than cosmetic. "
              + breadth_verdict(h["above50"], h["above200"]) + "</p>")

    lead = ""
    if h.get("rsp_spy_month") is not None:
        d, mo, q = h["rsp_spy_day"], h["rsp_spy_month"], h["rsp_spy_qtr"]
        lead = ("<p class='small' style='margin:16px 0 2px;color:#e6edf3;"
                "font-weight:600'>Equal weight versus cap weight</p><table>"
                + row("Today", f"<span class='{cls(d)}'>{d:+.2f}%</span>", "")
                + row("Past month", f"<span class='{cls(mo)}'>{mo:+.2f}%</span>", "")
                + row("Past quarter", f"<span class='{cls(q)}'>{q:+.2f}%</span>", "")
                + "</table><p class='small'>RSP against SPY. Negative means the "
                  "average stock is lagging the megacaps, so the index is being "
                  "carried by a narrowing group.</p>")

    val = ""
    ch, ph = h.get("cape_hist"), h.get("pe_hist")
    if ch or ph:
        span = ch or ph
        val = ("<p class='small' style='margin:16px 0 2px;color:#e6edf3;"
               "font-weight:600'>Market valuation against its own history</p>"
               "<table><tr><th>Measure</th><th class='num'>Now</th>"
               "<th class='num'>Mean</th><th class='num'>Median</th>"
               "<th class='num'>Peak</th><th>Peak date</th>"
               "<th class='num'>Percentile</th></tr>"
               + hist_row("Shiller CAPE", ch)
               + hist_row("S&amp;P 500 P/E", ph)
               + "</table>")
        if ch:
            val += (f"<p class='small'>CAPE uses ten years of inflation "
                    f"adjusted earnings, which smooths out the cycle. Today's "
                    f"{ch['current']:.1f} is {ch['vs_mean']:+.0f}% against the "
                    f"long run mean of {ch['mean']:.1f}, sits in the "
                    f"{ch['percentile']:.0f}th percentile of "
                    f"{ch['months']:,} months going back to {ch['since']}, and "
                    f"is {abs(ch['vs_peak']):.0f}% "
                    f"{'below' if ch['vs_peak'] < 0 else 'above'} the all time "
                    f"peak of {ch['peak']:.1f} set in {ch['peak_date']}. "
                    "High readings have historically meant weaker returns over "
                    "the following decade, but they are close to useless for "
                    "timing anything inside a year.</p>")

    pc = ""
    if h.get("pc_index") or h.get("pc_equity"):
        i, e = h.get("pc_index"), h.get("pc_equity")
        pc = ("<p class='small' style='margin:16px 0 2px;color:#e6edf3;"
              "font-weight:600'>Put to call ratios</p><table>"
              + (row("Index options, volume", f"{i['volume_pc']:.2f}",
                     "SPY, QQQ, IWM, DIA. Above 1.2 is defensive, below 0.8 "
                     "is complacent") if i else "")
              + (row("Index options, open interest", f"{i['oi_pc']:.2f}",
                     "standing positioning rather than today's flow") if i else "")
              + (row("Single stock, volume", f"{e['volume_pc']:.2f}",
                     "large caps. Normally well below the index figure, since "
                     "these are speculative rather than hedges") if e else "")
              + "</table><p class='small'>Computed from live option chains "
                "across the nearest four expiries, since CBOE no longer "
                "publishes its daily ratios on a free endpoint. Directionally "
                "sound, not identical to the official CBOE series.</p>")

    risk = ""
    if h.get("^SKEW"):
        risk = ("<p class='small' style='margin:16px 0 2px;color:#e6edf3;"
                "font-weight:600'>Risk pricing</p><table>"
                + row("CBOE SKEW", f"{h['^SKEW']:.1f}",
                      "above 145 means the options market is paying up for "
                      "crash protection")
                + row("VIX", f"{h['^VIX']:.2f}",
                      f"{h['^VIX_chg']:+.1f}% on the day. Below 15 is calm, "
                      "above 25 is stressed")
                + row("High yield credit (HYG)", f"{h['HYG']:.2f}",
                      f"{h['HYG_chg']:+.2f}% on the day, credit usually cracks "
                      "before equities")
                + "</table>")

    return ("<h2 id='health'>Market health</h2>" + breadth + lead + val
            + pc + risk)


def fng_block(f):
    if not f:
        return ""
    if f["score"] >= 75:
        col = "#3fb950"
    elif f["score"] >= 55:
        col = "#56b36b"
    elif f["score"] >= 45:
        col = "#8b949e"
    elif f["score"] >= 25:
        col = "#e8935b"
    else:
        col = "#f85149"
    pos = max(0, min(100, f["score"]))
    bar = (f"<div style='background:#21262d;border-radius:6px;height:10px;"
           f"margin:10px 0 4px;position:relative'>"
           f"<div style='background:{col};width:{pos:.0f}%;height:10px;"
           f"border-radius:6px'></div></div>"
           f"<div class='small'>0 extreme fear, 100 extreme greed</div>")
    return ("<h2>CNN Fear and Greed</h2>"
            f"<div style='font-size:26px;font-weight:700;color:{col}'>"
            f"{f['score']:.0f} <span style='font-size:15px'>{f['rating']}</span></div>"
            f"{bar}<table>"
            f"<tr><th>Prev close</th><th>1 week ago</th><th>1 month ago</th><th>1 year ago</th></tr>"
            f"<tr><td>{f['prev']:.0f}</td><td>{f['week']:.0f}</td>"
            f"<td>{f['month']:.0f}</td><td>{f['year']:.0f}</td></tr></table>")


DUE_TAG = "<span class='small'>due</span>"


def cal_table(rows, show_day=False):
    if not rows:
        return "<p class='small'>Nothing scheduled at medium or high impact.</p>"
    day_h = "<th>Day</th>" if show_day else ""
    out = "".join(
        (f"<tr>{'<td>' + c['day'] + '</td>' if show_day else ''}"
         f"<td>{c['time']}</td>"
         f"<td>{c['title']}"
         f"{' <span class=hi>high</span>' if c['impact'] == 'High' else ''}</td>"
         f"<td class='num'>{c['actual'] or DUE_TAG}</td>"
         f"<td class='num'>{c['forecast'] or '-'}</td>"
         f"<td class='num'>{c['previous'] or '-'}</td></tr>")
        for c in rows)
    return (f"<table><tr>{day_h}<th>Time MT</th><th>Event</th>"
            f"<th class='num'>Actual</th><th class='num'>Forecast</th>"
            f"<th class='num'>Prior</th></tr>{out}</table>")


def _mover_rows(rows):
    cards = []
    for m in rows:
        heads = "".join(
            f"<div class='small' style='margin-top:3px'>"
            f"<a href='{n['link']}'>{n['title']}</a></div>"
            for n in m.get("news", []))
        cards.append(
            f"<tr><td style='width:70px'><b>{m['sym']}</b></td>"
            f"<td class='num' style='width:80px'>{m['price']:,.2f}</td>"
            f"<td class='num {cls(m['pct'])}' style='width:70px'>{m['pct']:+.2f}%</td>"
            f"<td class='num small' style='width:60px'>{m['rvol']:.1f}x</td>"
            f"<td>{heads or '<span class=small>no fresh headlines</span>'}</td></tr>")
    return "".join(cards)


def movers_block(movers):
    if not movers:
        return ""
    tracked = set(WATCHLIST) | set(HOLDINGS)
    moving = [m for m in movers if m["sym"] not in tracked]
    watched = [m for m in movers if m["sym"] in tracked]
    head = ("<tr><th>Ticker</th><th class='num'>Price</th><th class='num'>Change</th>"
            "<th class='num'>Volume</th><th>Why</th></tr>")
    out = ""
    if moving:
        out += (f"<h2 id='movers'>Stocks getting attention</h2><table>{head}"
                + _mover_rows(moving) + "</table>")
    if watched:
        out += (f"<h2 id='watchlist'>Your watchlist and holdings</h2><table>{head}"
                + _mover_rows(watched) + "</table>")
    return out + ("<p class='small'>Volume column is today against the 20 day "
                  "average. Above 1.5x means unusual participation.</p>")


def ma_block(near):
    if not near:
        return ""
    rows = "".join(
        f"<tr><td><b>{r['sym']}</b></td>"
        f"<td class='num'>{r['price']:,.2f}</td>"
        f"<td class='num {cls(r['pct'])}'>{r['pct']:+.2f}%</td>"
        f"<td>{r['ma']} day</td>"
        f"<td class='num {cls(r['gap'])}'>{r['gap']:+.2f}%</td>"
        f"<td class='small'>{r['side']}</td></tr>" for r in near[:18])
    return ("<h2>Sitting on a moving average</h2><table>"
            "<tr><th>Ticker</th><th class='num'>Price</th><th class='num'>Today</th>"
            "<th>Average</th><th class='num'>Distance</th><th>Side</th></tr>"
            + rows + "</table>"
            f"<p class='small'>Names within {MA_NEAR_PCT:.0f} percent of their 20, 50 "
            "or 200 day average, longest average first. These are the levels where "
            "price often pauses or turns.</p>")


PDF_CSS = """
@page { size: A4; margin: 14mm 12mm; background: #0d1117; }
.wrap { padding: 0 !important; }
h2 { page-break-after: avoid; }
table { page-break-inside: auto; }
tr { page-break-inside: avoid; }
img { max-width: 100%; page-break-inside: avoid; }
a { text-decoration: none; }
"""


TONE_STYLE = {
    "high bullish": ("#0b6e3d", "#ffffff", "HIGH BULLISH"),
    "lean bullish": ("#1f6f43", "#d6f5e2", "lean bullish"),
    "neutral":      ("#30363d", "#8b949e", "neutral"),
    "lean bearish": ("#8c3b34", "#ffdedb", "lean bearish"),
    "high bearish": ("#8c1f18", "#ffffff", "HIGH BEARISH"),
}


def tone_stamp(tone):
    if not tone:
        return ""
    bg, fg, label = TONE_STYLE.get(str(tone).strip().lower(),
                                   TONE_STYLE["neutral"])
    return (f"<span style=\"display:inline-block;background:{bg};color:{fg};"
            f"font-size:10px;font-weight:700;letter-spacing:0.4px;"
            f"padding:2px 7px;border-radius:9px;white-space:nowrap\">"
            f"{label}</span>")


LEAN_COLORS = {
    "bullish": "#3fb950", "leaning bullish": "#56b36b", "neutral": "#8b949e",
    "leaning bearish": "#e8935b", "bearish": "#f85149",
}


def answer_box(question, text, tickers):
    """The reply to whatever was typed into the Run workflow box."""
    if not text:
        return ""
    tags = ""
    if tickers:
        tags = ("<div class='small' style='margin-top:8px;color:#8b949e'>"
                "Pulled live data on " + ", ".join(tickers) + "</div>")
    return (f"<h2 id='answer' style='border-bottom:1px solid #30363d'>You asked</h2>"
            f"<div style=\"background:#1b2432;color:#c9d1d9;border-left:3px solid "
            f"#e3b341;border-radius:6px;padding:10px 14px;margin:6px 0 0;"
            f"font-size:14px;font-style:italic\">{question}</div>"
            f"<div style=\"background:#161b22;color:#e6edf3;border-left:3px solid "
            f"#e3b341;border-radius:6px;padding:14px 16px;margin:8px 0 4px;"
            f"font-size:15px;line-height:1.6\">{text}{tags}</div>")


def ticker_notes_block(notes, tickers):
    """Per name write ups for the deep dive field, separate from the answer."""
    if not notes:
        return ""
    cards = ""
    for n in notes:
        t = (n.get("ticker") or "").upper()
        verdict = n.get("verdict", "")
        cards += (
            f"<div style=\"background:#161b22;border-left:3px solid #a371f7;"
            f"border-radius:6px;padding:12px 16px;margin:8px 0\">"
            f"<div style='font-size:15px;font-weight:700;color:#e6edf3'>{t}"
            + (f"<span class='small' style='margin-left:8px;color:#a371f7'>"
               f"{verdict}</span>" if verdict else "")
            + ("<span class='small' style='margin-left:8px'>held</span>"
               if t in HOLDINGS else "")
            + f"</div><div style='color:#e6edf3;font-size:14px;line-height:1.6;"
              f"margin-top:6px'>{n.get('note','')}</div></div>")
    return (f"<h2 id='deepdive'>Deep dive</h2>"
            f"<p class='small'>You asked for these to be vetted: "
            f"{', '.join(tickers)}. Live prices, valuation, analyst targets, "
            f"earnings record and recent news were pulled for each.</p>"
            + cards)


def analysis_box(title, text, accent):
    """One AI written section, visually distinct from the data tables."""
    if not text:
        return ""
    return (f"<h2>{title}</h2>"
            f"<div style=\"background:#161b22;color:#e6edf3;border-left:3px solid "
            f"{accent};border-radius:6px;padding:14px 16px;margin:6px 0 4px;"
            f"font-size:14px;line-height:1.6\">{text}</div>")


def lean_badge(lean, reason):
    if not lean:
        return ""
    col = LEAN_COLORS.get(lean.lower(), "#8b949e")
    return (f"<div style='margin:12px 0 2px'>"
            f"<span style=\"display:inline-block;background:{col};color:#0d1117;"
            f"font-weight:700;font-size:13px;padding:4px 12px;border-radius:12px\">"
            f"{lean.upper()}</span>"
            f"<span class='small' style='margin-left:10px;color:#8b949e'>"
            f"{reason}</span></div>")


def portfolio_block(port, ai_note):
    if not port:
        return ""
    col = "up" if port["day_pl"] > 0 else ("dn" if port["day_pl"] < 0 else "flat")

    # per currency subtotals, so the figures reconcile against the broker
    acc = ""
    if len(port.get("accounts", [])) > 1:
        arows = "".join(
            f"<tr><td><b>{a['cur']}</b> account</td>"
            f"<td class='num small'>{a['positions']}</td>"
            f"<td class='num'>{a['cur']} {a['value']:,.0f}</td>"
            f"<td class='num {cls(a['day_pl'])}'>{a['day_pl']:+,.0f}</td>"
            f"<td class='num {cls(a['day_pct'])}'>{a['day_pct']:+.2f}%</td>"
            f"<td class='num {cls(a['gain'] or 0)}'>"
            f"{format(a['gain'], '+,.0f') if a['gain'] is not None else '-'}</td>"
            f"<td class='num {cls(a['gain_pct'] or 0)}'>"
            f"{format(a['gain_pct'], '+.2f') + '%' if a['gain_pct'] is not None else '-'}"
            f"</td></tr>" for a in port["accounts"])
        acc = ("<p class='small' style='margin:16px 0 2px;color:#e6edf3;"
               "font-weight:600'>By account, each in its own currency</p><table>"
               "<tr><th>Account</th><th class='num'>Pos</th><th class='num'>Value</th>"
               "<th class='num'>Day</th><th class='num'>Day %</th>"
               "<th class='num'>Gain</th><th class='num'>Gain %</th></tr>"
               + arows + "</table>"
               "<p class='small'>These match what your broker shows per account. "
               "The combined figure above converts everything into "
               f"{CURRENCY}, so a losing position in another currency pulls it "
               "down even when the account you are looking at is up.</p>")

    rows = "".join(
        f"<tr><td><b>{r['sym']}</b>"
        f"{'' if r['cur'] == CURRENCY else chr(32) + '<span class=small>' + r['cur'] + '</span>'}"
        f"</td>"
        f"<td class='num'>{r['shares']:,.0f}</td>"
        f"<td class='num'>{r['price']:,.2f}</td>"
        f"<td class='num {cls(r['pct'])}'>{r['pct']:+.2f}%</td>"
        f"<td class='num'>{r['value']:,.0f}</td>"
        f"<td class='num {cls(r['moved'])}'>{r['moved']:+,.0f}</td>"
        f"<td class='num {cls(r['gain'] or 0)}'>"
        f"{format(r['gain'], '+,.0f') if r['gain'] is not None else '-'}</td>"
        f"<td class='num {cls(r['gain_pct'] or 0)}'>"
        f"{format(r['gain_pct'], '+.1f') + '%' if r['gain_pct'] is not None else '-'}</td>"
        + (f"<td class='num small {cls(r['ext_pct'])}'>{r['ext_pct']:+.2f}%</td>"
           if r.get("ext_pct") is not None else "<td class='num small'>-</td>")
        + "</tr>"
        for r in sorted(port["rows"], key=lambda r: -abs(r["moved"])))

    total_gain = ("<div class='small'>Total gain since purchase: "
                  f"{port['total_gain']:+,.0f} {CURRENCY} across all accounts</div>"
                  if port["total_gain"] is not None else "")

    opts = ""
    if port.get("options"):
        orows = "".join(
            f"<tr><td><b>{o['symbol']}</b></td><td class='num'>{o['qty']:,.0f}</td>"
            f"<td class='num'>{o['value']:,.0f}</td></tr>" if o.get("value") else
            f"<tr><td><b>{o['symbol']}</b></td><td class='num'>{o['qty']:,.0f}</td>"
            f"<td class='num'>-</td></tr>"
            for o in port["options"])
        opts = ("<p class='small' style='margin-top:14px'>Option positions, "
                "valued from your export rather than live</p><table>"
                "<tr><th>Contract</th><th class='num'>Qty</th>"
                "<th class='num'>Value</th></tr>" + orows + "</table>")

    footnotes = []
    if port.get("fx"):
        footnotes.append("Converted at " + ", ".join(
            f"1 {c} = {r:.4f} {CURRENCY}" for c, r in port["fx"].items()))
    if port.get("missing"):
        footnotes.append("No quote found for " + ", ".join(port["missing"]))
    footnotes.append(f"Positions read from {port.get('source', 'config')}")
    foot = "<p class='small'>" + ". ".join(footnotes) + ".</p>"

    return (f"<h2>Your portfolio</h2>"
            f"<div style='font-size:24px;font-weight:700'>"
            f"{CURRENCY} {port['value']:,.0f}</div>"
            f"<div class='{col}' style='font-size:16px;font-weight:600'>"
            f"{port['day_pl']:+,.0f} today ({port['day_pct']:+.2f}%)</div>"
            f"{total_gain}{acc}"
            f"<p class='small' style='margin:16px 0 2px;color:#e6edf3;"
            f"font-weight:600'>Positions, by size of today's move</p><table>"
            f"<tr><th>Ticker</th><th class='num'>Shares</th><th class='num'>Close</th>"
            f"<th class='num'>Day %</th><th class='num'>Value {CURRENCY}</th>"
            f"<th class='num'>Day P/L</th><th class='num'>Gain {CURRENCY}</th>"
            f"<th class='num'>Gain %</th>"
            f"<th class='num'>{session_label().title()}</th></tr>"
            f"{rows}</table>{opts}{foot}")


def fmt(v, dp=1, suffix=""):
    if v is None or v != v:
        return "-"
    try:
        return f"{float(v):,.{dp}f}{suffix}"
    except Exception:
        return "-"


def valuation_block(fundamentals, earn_hist, port):
    """Valuation and quality for what he owns, plus how each has delivered."""
    if not fundamentals:
        return ""
    held = set(HOLDINGS)
    order = ([s for s in fundamentals if s in held]
             + [s for s in fundamentals if s not in held])
    rows = ""
    for sym in order:
        f = fundamentals[sym]
        eh = earn_hist.get(sym)
        beat = (f"{eh['beats']}/{eh['of']}" if eh else "-")
        last = (f"{eh['rows'][-1]['surprise']:+.1f}%" if eh and eh["rows"] else "-")
        rows += (
            f"<tr><td><b>{sym}</b>"
            + ("<span class='small'> held</span>" if sym in held else "")
            + f"</td><td class='num'>{fmt(f['mcap'] / 1e9, 1, 'B') if f['mcap'] else '-'}</td>"
            f"<td class='num'>{fmt(f['pe'])}</td>"
            f"<td class='num'>{fmt(f['fwd_pe'])}</td>"
            f"<td class='num'>{fmt(f['ps'])}</td>"
            f"<td class='num'>{fmt(f['peg'], 2)}</td>"
            f"<td class='num'>{fmt(f['rev_growth'], 0, '%')}</td>"
            f"<td class='num'>{fmt(f['margin'], 0, '%')}</td>"
            f"<td class='num small'>{beat}</td>"
            f"<td class='num small'>{last}</td></tr>")
    return ("<h2 id='valuation'>Valuation and earnings record</h2><table>"
            "<tr><th>Ticker</th><th class='num'>Mkt cap</th><th class='num'>P/E</th>"
            "<th class='num'>Fwd P/E</th><th class='num'>P/S</th>"
            "<th class='num'>PEG</th><th class='num'>Rev gr</th>"
            "<th class='num'>Margin</th><th class='num'>Beats</th>"
            "<th class='num'>Last surp</th></tr>" + rows + "</table>"
            "<p class='small'>Beats is how many of the last four quarters came "
            "in above the estimate. Last surp is the most recent quarter's "
            "surprise. Forward P/E below trailing means analysts expect earnings "
            "to grow. PEG under 1 means the multiple is low relative to that "
            "growth, though the growth estimate behind it can be wrong.</p>")


def short_interest_block(shorted, fundamentals):
    """Medium and large caps carrying an unusual short position."""
    if not shorted:
        return ""
    held = set(HOLDINGS)
    rows = "".join(
        f"<tr><td><b>{r['sym']}</b>"
        + ("<span class='small'> held</span>" if r["sym"] in held else "")
        + f"</td><td class='num'>{fmt(r['mcap'] / 1e9, 1, 'B')}</td>"
        f"<td class='num {cls(r['short_pct'] - 8)}'>{fmt(r['short_pct'], 1, '%')}</td>"
        f"<td class='num'>{fmt(r['short_ratio'], 1)}</td>"
        f"<td class='num small {cls(r['trend'] or 0)}'>"
        f"{fmt(r['trend'], 0, '%') if r['trend'] is not None else '-'}</td></tr>"
        for r in shorted)
    return ("<h2 id='shorts'>Heavily shorted names</h2><table>"
            "<tr><th>Ticker</th><th class='num'>Mkt cap</th>"
            "<th class='num'>Short % float</th><th class='num'>Days to cover</th>"
            "<th class='num'>vs last month</th></tr>" + rows + "</table>"
            "<p class='small'>From your holdings and watchlist, filtered to "
            "names above 2 billion market cap with more than 5 percent of float "
            "sold short. Days to cover is short interest divided by average "
            "volume. A rising figure means shorts are adding, a falling one "
            "means they are covering.</p>")


def analyst_block(analysts):
    if not analysts:
        return ""
    items = sorted(analysts.items(), key=lambda kv: -kv[1]["upside"])
    rows = "".join(
        f"<tr><td><b>{s}</b></td>"
        f"<td class='num'>{a['price']:,.2f}</td>"
        f"<td class='num'>{a['mean']:,.2f}</td>"
        f"<td class='num {cls(a['upside'])}'>{a['upside']:+.1f}%</td>"
        f"<td class='num small'>{a['low']:,.0f} to {a['high']:,.0f}</td>"
        f"<td class='small'>{a['rating'] or 'na'}</td>"
        f"<td class='num small'>{a['count'] or '?'}</td></tr>"
        for s, a in items)
    return ("<h2>Analyst targets</h2><table>"
            "<tr><th>Ticker</th><th class='num'>Price</th><th class='num'>Mean target</th>"
            "<th class='num'>Implied</th><th class='num'>Low to high</th>"
            "<th>Rating</th><th class='num'>Analysts</th></tr>"
            + rows + "</table>"
            "<p class='small'>Targets are what sell side analysts publish, usually on a "
            "12 month view. They cluster around current price and move after it, so they "
            "describe consensus rather than predict it.</p>")


def earnings_today(symbols, today_cal, results, back_days=2):
    """Fill the gap the data vendors leave.

    A company that reports at 4:05pm is in its own SEC filing by 4:10 and in
    a vendor feed the next morning. So anything scheduled today, or held and
    filing in the last couple of days, gets read straight from the filing,
    which also carries the guidance.
    """
    out = {}
    for sym in symbols:
        if sym in results:
            continue
        base = sym.split(".")[0]
        if base not in today_cal and sym not in HOLDINGS:
            continue
        rel = sec_earnings_release(sym, back_days=back_days)
        if not rel:
            continue
        info = today_cal.get(base, {})
        out[sym] = {
            "sym": sym,
            "filed": rel["filed"],
            "days_ago": rel["days_ago"],
            "when": info.get("when", ""),
            "forecast": info.get("forecast", ""),
            "text": rel["text"],
            "guidance": rel.get("guidance") or [],
            "url": rel["url"],
            "held": sym in HOLDINGS,
        }
    return out


def results_block(results, coverage, today_cal, tracked):
    """What actually came out, separated from what is merely scheduled."""
    reported, due = "", ""

    if results:
        rows = ""
        for r in sorted(results.values(),
                        key=lambda x: x.get("days_ago", 99)):
            if not r.get("reported"):
                continue
            has_eps = r.get("eps") is not None
            fil = r.get("filing") or {}
            met = fil.get("metrics") or {}
            verdict = ("BEAT" if r.get("beat") else "MISS") if has_eps else "FILED"
            if not has_eps and met.get("eps") and r.get("estimate_str"):
                try:
                    got = float(met["eps"])
                    exp = float(str(r["estimate_str"]).replace("$", "")
                                .replace("(", "-").replace(")", ""))
                    verdict = "BEAT" if got > exp else "MISS"
                    r["beat"] = got > exp
                    has_eps = True
                    r["eps"] = got
                    r["estimate"] = exp
                    r["surprise_pct"] = (got / exp - 1) * 100 if exp else 0.0
                except Exception:
                    pass
            col = ("#30363d" if not has_eps
                   else "#0b6e3d" if r["beat"] else "#8c1f18")
            extra = ""
            if met.get("revenue"):
                extra += (f"<div class='small' style='margin-top:3px'>"
                          f"Revenue ${met['revenue']}"
                          + (f", non GAAP EPS ${met['non_gaap_eps']}"
                             if met.get("non_gaap_eps") else "") + "</div>")
            shown = 0
            for g in (fil.get("guidance") or []):
                if re.search(r"\bprovides guidance\b|announces financial "
                             r"results|forward-looking", g, re.I):
                    continue
                if not re.search(r"\b(raising|raised|lowering|lowered|"
                                 r"guidance of|outlook (?:to|by)|now expects?|"
                                 r"expects? full)\b", g, re.I):
                    continue
                extra += (f"<div class='small' style='margin-top:3px;"
                          f"color:#f0b429'>{g[:240]}</div>")
                shown += 1
                if shown >= 2:
                    break
            if fil.get("url"):
                extra += (f"<div class='small' style='margin-top:3px'>"
                          f"<a href='{fil['url']}'>Read the release</a></div>")
            heads = extra + "".join(
                f"<div class='small' style='margin-top:3px'>{h}</div>"
                for h in coverage.get(r["sym"], []))
            d_ago = r.get("days_ago", 0)
            when = ("today" if d_ago == 0 else "yesterday" if d_ago == 1
                    else f"{d_ago} days ago")
            if r.get("when"):
                when += f", {r['when']}"
            rows += (
                f"<tr><td><b>{r['sym']}</b>"
                + ("<span class='small'> held</span>" if r["held"] else "")
                + f"</td><td class='small'>{r.get('quarter', '')}</td>"
                f"<td class='small'>{when}</td>"
                + (f"<td class='num'>{r['eps']:,.2f}</td>"
                   f"<td class='num'>{r['estimate']:,.2f}</td>" if has_eps
                   else "<td class='num small'>see release</td>"
                        "<td class='num small'>-</td>")
                +
                f"<td class='num'><span style=\"background:{col};color:#fff;"
                f"font-size:10px;font-weight:700;padding:2px 7px;"
                f"border-radius:9px\">{verdict}"
                + (f" {r['surprise_pct']:+.1f}%" if has_eps else "")
                + "</span></td>"
                f"<td>{heads or '<span class=small>no coverage found</span>'}"
                f"</td></tr>")
        reported = ("<p class='small' style='margin:12px 0 2px;color:#e6edf3;"
                    "font-weight:600'>Already reported</p><table>"
                    "<tr><th>Ticker</th><th>Quarter</th><th>Reported</th>"
                    "<th class='num'>EPS</th><th class='num'>Expected</th>"
                    "<th class='num'>Result</th><th>Coverage, including any "
                    "guidance</th></tr>" + rows + "</table>")

    pending = []
    for sym in tracked:
        base = sym.split(".")[0]
        info = today_cal.get(base)
        if info and sym not in results:
            pending.append((sym, info))
    if pending:
        rows = "".join(
            f"<tr><td><b>{sym}</b>"
            + ("<span class='small'> held</span>" if sym in HOLDINGS else "")
            + f"</td><td class='small'>{i['when']}</td>"
            f"<td class='num'>{i['forecast'] or '-'}</td>"
            f"<td class='num small'>{i['last_year'] or '-'}</td></tr>"
            for sym, i in pending)
        due = ("<p class='small' style='margin:16px 0 2px;color:#e6edf3;"
               "font-weight:600'>Reporting today, result not out yet</p><table>"
               "<tr><th>Ticker</th><th>When</th><th class='num'>Expected EPS</th>"
               "<th class='num'>Year ago</th></tr>" + rows + "</table>"
               "<p class='small'>After the close means the numbers land once "
               "trading ends, so today's share price does not reflect them.</p>")

    if not reported and not due:
        return ""
    return ("<h2 id='results'>Earnings results</h2>" + reported + due)


def earnings_block(earnings):
    if not earnings:
        return ""

    def when(e):
        if e["days"] == 0:
            return "today"
        if e["days"] < 0:
            n = -e["days"]
            return f"{n} day{'s' if n != 1 else ''} ago"
        return f"in {e['days']} day{'s' if e['days'] != 1 else ''}"

    upcoming = [e for e in earnings if not e.get("reported")]
    if not upcoming:
        return ""
    rows = "".join(
        f"<tr><td><b>{e['sym']}</b>"
        + ("<span class='small'> held</span>" if e["held"] else "")
        + f"</td><td>{e['date'].strftime('%a %b %d')}</td>"
        f"<td class='num small'>{when(e)}</td></tr>"
        for e in upcoming)
    return ("<h2 id='earnings'>Earnings coming up</h2><table>"
            "<tr><th>Ticker</th><th>Date</th><th class='num'>When</th></tr>"
            + rows + "</table>"
            "<p class='small'>Anything already reported appears above with its "
            "actual figures instead.</p>")


def match_link(title, news):
    """Find the original article URL for a title the model handed back."""
    def norm(t):
        return re.sub(r"[^a-z0-9]", "", (t or "").lower())

    title = re.sub(r"^\s*\[[^\]]{1,30}\]\s*", "", title or "")
    want = norm(title)
    if not want:
        return None
    for n in news:                       # exact match after normalising
        if norm(n["title"]) == want:
            return n["link"]
    for n in news:                       # model trimmed or extended it
        got = norm(n["title"])
        if got and (got.startswith(want[:40]) or want.startswith(got[:40])):
            return n["link"]
    for n in news:                       # last resort, strong prefix overlap
        got = norm(n["title"])
        if got and want[:25] and (want[:25] in got or got[:25] in want):
            return n["link"]
    return None


def portfolio_news_block(rows, earnings, limit=18):
    """Company news on what he actually owns, kept apart from market news."""
    if not rows and not earnings:
        return ""

    def ago(h):
        if h is None:
            return ""
        if h < 1:
            return "just now"
        if h < 24:
            return f"{h:.0f}h ago"
        return f"{h / 24:.0f}d ago"

    body = ""
    if rows:
        held = [r for r in rows if r["held"]][:limit]
        watch = [r for r in rows if not r["held"]][:8]

        def table(items):
            return "<table>" + "".join(
                f"<tr><td style='width:64px'><b>{r['sym']}</b></td>"
                f"<td><a href='{r['link']}'>{r['title']}</a>"
                f"<span class='small'> \u00b7 {ago(r['age_hours'])}</span></td></tr>"
                for r in items) + "</table>"

        if held:
            body += ("<p class='small' style='margin:12px 0 2px;color:#e6edf3;"
                     "font-weight:600'>On what you own</p>" + table(held))
        if watch:
            body += ("<p class='small' style='margin:16px 0 2px;color:#e6edf3;"
                     "font-weight:600'>On your watchlist</p>" + table(watch))

    return (f"<h2 id='mynews'>News on your positions</h2>"
            f"<p class='small'>Company specific stories from the last "
            f"{PORTFOLIO_NEWS_HOURS} hours, newest first.</p>"
            + body + earnings_block(earnings))


def news_block(picks, news, my_news=None):
    """Render the model's picks. It can choose from the market pool or from
    company news on his own positions, so both are searched for the link."""
    pool = list(news) + [
        {"title": r["title"], "link": r["link"],
         "source": f"{r['sym']} news", "paywalled": False}
        for r in (my_news or [])]
    news = pool
    if picks:
        rows = ""
        for p in picks:
            title = re.sub(r"^\s*\[[^\]]{1,30}\]\s*", "", p.get("title", ""))
            link = match_link(title, news)
            entry = next((n for n in news if n["link"] == link and link), None)
            src = entry["source"] if entry else ""
            if entry and entry.get("paywalled"):
                src += ", subscription"
            head = (f"<a href='{link}' style='color:#79c0ff;text-decoration:none'>"
                    f"<b>{title}</b></a>") if link else f"<b>{title}</b>"
            tag = (f"<span class='small' style='color:#8b949e'> &middot; {src}</span>"
                   if src else "")
            tick = p.get("tickers", "")
            tick_tag = (f"<span class='small' style='color:#f0b429'> "
                        f"&middot; {tick}</span>" if tick else "")
            rows += (f"<tr><td style='width:96px;vertical-align:top'>"
                     f"{tone_stamp(p.get('tone'))}</td>"
                     f"<td>{head}{tag}{tick_tag}"
                     f"<div class='small' style='margin-top:3px'>"
                     f"{p.get('why','')}</div></td></tr>")
        return ("<h2>What actually matters today</h2><table>" + rows + "</table>"
                "<p class='small'>The stamp is the story's likely direction for "
                "markets, not the tone of the writing. Ranked most important "
                "first.</p>")
    # No picks came back, usually because no Anthropic key is set. The full
    # pool already prints at the end of the report, so do not repeat it here.
    return ("<h2>What actually matters today</h2>"
            "<p class='small'>No selection was made this run. Every headline "
            "gathered is listed at the end of the report.</p>")


NAV = [
    ("brief", "Brief"), ("answer", "Your question"), ("deepdive", "Deep dive"),
    ("portfolio", "Portfolio"), ("results", "Earnings results"), ("charts", "Charts"),
    ("results", "Earnings"), ("mynews", "Your news"), ("macro", "Macro"), ("news", "Top news"),
    ("movers", "Movers"),
    ("numbers", "The numbers"), ("health", "Market health"),
    ("valuation", "Valuation"),
    ("shorts", "Shorts"), ("allnews", "Every headline"),
]


def nav_bar():
    links = " &nbsp;|&nbsp; ".join(
        f"<a href='#{a}' style='color:#79c0ff;text-decoration:none'>{lab}</a>"
        for a, lab in NAV)
    return (f"<div style=\"background:#161b22;border-radius:6px;padding:10px 14px;"
            f"margin:10px 0 4px;font-size:13px;color:#8b949e\">{links}</div>")


def all_news_block(news):
    by_source = {}
    for n in news:
        by_source.setdefault(n["source"], []).append(n)
    out = ""
    for source in sorted(by_source):
        rows = "".join(
            f"<tr><td><a href='{n['link']}'>{n['title']}</a>"
            + ("<span class='small'> &middot; subscription</span>"
               if n.get("paywalled") else "")
            + (f"<div class='small' style='margin-top:2px'>{n['summary']}</div>"
               if n.get("summary") else "")
            + "</td></tr>" for n in by_source[source])
        out += (f"<p class='small' style='margin:16px 0 2px;color:#e6edf3;"
                f"font-weight:600'>{source}</p><table>{rows}</table>")
    return (f"<h2 id='allnews'>Every headline gathered</h2>"
            f"<p class='small'>{len(news)} stories from {len(by_source)} outlets, "
            f"grouped by source. The ten above were selected from these.</p>{out}")


def build_html(slot, quotes, news, cal_today, cal_ahead, fng, movers,
               near_ma, brief, ai_used, port, analysts, earnings,
               my_news=None, fundamentals=None, earn_hist=None, shorted=None,
               health=None, sentiment=None, buzz=None, q_tickers=None,
               d_tickers=None, e_results=None, e_coverage=None,
               today_cal=None, tracked=None, for_pdf=False):
    now = dt.datetime.now(LOCAL_TZ)

    lede = ("<div class='lede' style=\"background:#161b22;color:#e6edf3;"
            "border-left:3px solid #58a6ff;border-radius:6px;padding:14px 16px;"
            "margin:14px 0 6px;font-size:15px;line-height:1.55\">"
            f"{brief['summary']}</div>")

    header = (f"<div class='hdr' id='brief'>{slot}</div>"
              f"<div class='small'>{now.strftime('%A %B %d, %Y at %I:%M %p')} MT</div>"
              f"{nav_bar() if for_pdf else ''}{lede}"
              f"{lean_badge(brief.get('lean'), brief.get('lean_reason'))}"
              f"<div class='small' style='margin-bottom:4px'>"
              f"{'Analysis written by Claude. Not advice, and it does not know your plan or tax position.' if ai_used else 'Auto generated summary. Add an Anthropic key for full analysis.'}"
              f"</div>"
              + answer_box(QUESTION, brief.get("answer"), q_tickers or [])
              + ticker_notes_block(brief.get("ticker_notes"), d_tickers or []))

    sec_portfolio = ("<a id='portfolio'></a>" + portfolio_block(port, None)
                     + analysis_box("Portfolio analysis",
                                    brief.get("portfolio_analysis"), "#3fb950")
                     + results_block(e_results or {}, e_coverage or {},
                                     today_cal or {}, tracked or [])
                     + portfolio_news_block(my_news or [], earnings))

    sec_charts = ("<h2 id='charts'>S&amp;P 500 intraday</h2><img src='cid:chart'>"
                  "<h2>S&amp;P 500 daily</h2><img src='cid:daily'>"
                  + analysis_box("Technical analysis",
                                 brief.get("technical_analysis"), "#a371f7"))

    sec_macro = ("<a id='macro'></a>"
                 + analysis_box("Macro and news analysis",
                                brief.get("macro_analysis"), "#f0b429")
                 + "<a id='news'></a>"
                 + news_block(brief.get("news_picks"), news, my_news)
                 + "<h2>US economic data today</h2>" + cal_table(cal_today)
                 + "<h2>Coming up this week</h2>" + cal_table(cal_ahead, show_day=True))

    idx = ("<h2 id='numbers'>US markets</h2><table>"
           "<tr><th>Market</th><th class='num'>Close</th>"
           "<th class='num'>Change</th><th class='num'>%</th>"
           f"<th class='num'>{session_label().title()}</th></tr>"
           + quote_rows(INDEXES, quotes) + "</table>"
           "<p class='small'>These are the tradable funds that track each index, "
           "so every row has a real extended session and the pre-market column "
           "means the same thing on every line. Cash indices do not trade before "
           "the open, which is why they are shown separately below.</p>"
           "<p class='small' style='margin:16px 0 2px;color:#e6edf3;"
           "font-weight:600'>Cash indices and rates, regular session only</p>"
           "<table><tr><th>Index</th><th class='num'>Close</th>"
           "<th class='num'>Change</th><th class='num'>%</th></tr>"
           + "".join(
               f"<tr><td>{lab}</td><td class='num'>{quotes[sym]['last']:,.2f}</td>"
               f"<td class='num {cls(quotes[sym]['dollar'])}'>"
               f"{quotes[sym]['dollar']:+,.2f}</td>"
               f"<td class='num {cls(quotes[sym]['pct'])}'>"
               f"{quotes[sym]['pct']:+.2f}%</td></tr>"
               for sym, lab in SPOT_INDEXES.items() if sym in quotes)
           + "</table>")
    sec_market = (idx
                  + "<h2>Sectors, best to worst</h2>"
                  + simple_table(SECTORS, quotes, "Sector", sort=True)
                  + analysis_box("Market health analysis",
                                 brief.get("health_analysis"), "#58a6ff")
                  + health_block(health or {})
                  + retail_block(sentiment or {}, buzz or [])
                  + fng_block(fng)
                  + "<h2>Heat map</h2><img src='cid:heatmap'>"
                  + movers_block(movers) + ma_block(near_ma)
                  + analyst_block(analysts)
                  + valuation_block(fundamentals or {}, earn_hist or {}, port)
                  + short_interest_block(shorted or [], fundamentals or {})
                  + "<h2>Crypto</h2>" + simple_table(CRYPTO, quotes, "Coin")
                  + "<h2>Metals, energy and the dollar</h2>"
                  + simple_table(COMMODITIES, quotes, "Contract")
                  + "<h2>Global markets</h2>" + simple_table(GLOBAL, quotes, "Index")
                  + "<p class='small'>Asia and Europe are closed during US hours, "
                    "so these reflect their most recent completed session.</p>")

    rule = "<div style='border-top:2px solid #30363d;margin:34px 0 0'></div>"

    return (f"<html><head><meta charset='utf-8'>"
            f"<meta name='color-scheme' content='dark'>"
            f"<meta name='supported-color-schemes' content='dark'>"
            f"<style>{PDF_CSS if for_pdf else ''}{CSS}</style></head>"
            f"<body style='margin:0;padding:0;background:#0d1117'>"
            f"<div class='wrap' style=\"background:#0d1117;color:#e6edf3;padding:18px;"
            f"font-family:-apple-system,Segoe UI,Arial,sans-serif\">"
            f"{header}{sec_portfolio}{sec_charts}{sec_macro}"
            f"{rule}{sec_market}{rule}{all_news_block(news)}"
            f"<p class='small'>Generated automatically. Prices and analyst data from "
            f"Yahoo Finance, sentiment from CNN, calendar from Forex Factory.</p>"
            f"</div></body></html>")


def build_pdf(html, images):
    """Render the report to a PDF with the chart images embedded."""
    try:
        from weasyprint import HTML
    except Exception as e:
        print(f"weasyprint unavailable, skipping PDF: {e}", file=sys.stderr)
        return None
    try:
        doc = html
        for cid, data in images.items():
            b64 = base64.b64encode(data).decode()
            doc = doc.replace(f"cid:{cid}", f"data:image/png;base64,{b64}")
        return HTML(string=doc).write_pdf()
    except Exception as e:
        print(f"pdf build failed: {e}", file=sys.stderr)
        return None


# ============================== SEND ==============================


def send_email(subject, html, images, pdf=None, pdf_name="market-report.pdf"):
    msg = EmailMessage()
    msg["Subject"] = subject
    msg["From"] = MAIL_FROM
    msg["To"] = MAIL_TO
    msg.set_content("This report needs an HTML capable mail client.")
    msg.add_alternative(html, subtype="html")
    part = msg.get_payload()[-1]
    for cid, data in images.items():
        part.add_related(data, maintype="image", subtype="png", cid=f"<{cid}>")
    if not SMTP_PASS:
        raise SystemExit("RESEND_API_KEY is not set")
    if pdf:
        msg.add_attachment(pdf, maintype="application", subtype="pdf",
                           filename=pdf_name)
    ctx = ssl.create_default_context()
    with smtplib.SMTP_SSL(SMTP_HOST, SMTP_PORT, context=ctx) as s:
        s.login(SMTP_USER, SMTP_PASS)
        s.send_message(msg)


def slot_name():
    """Label for the report, based on where we are in the New York session."""
    now = dt.datetime.now(MARKET_TZ)
    t = now.hour * 60 + now.minute
    if t < 9 * 60 + 30:
        return "Pre-market report"
    if t <= 16 * 60:
        return "Midday report"
    return "Closing report"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--preview", action="store_true",
                    help="write report.html and images locally, send nothing")
    ap.add_argument("--force", action="store_true",
                    help="kept for compatibility, every run sends regardless")
    ap.add_argument("--weekly", action="store_true",
                    help="weekend edition, wider lookback and no time gate")
    args = ap.parse_args()

    # No gating. Every manual press and every cron fires a report.
    prev_state = read_state()

    symbols = (list(INDEXES) + list(SPOT_INDEXES) + list(SECTORS)
               + list(MEGACAPS) + list(CRYPTO) + list(COMMODITIES)
               + list(GLOBAL) + list(HOLDINGS))
    quotes = get_quotes(sorted(set(symbols)))

    sector_items = sorted(
        [(lab, quotes[s]["pct"]) for s, lab in SECTORS.items() if s in quotes],
        key=lambda x: -x[1])
    mega_items = sorted(
        [(lab, quotes[s]["pct"]) for s, lab in MEGACAPS.items() if s in quotes],
        key=lambda x: -x[1])

    heat = build_heatmap(sector_items, mega_items)
    intraday_df = get_intraday(CHART_SYMBOL)
    intraday = intraday_facts(intraday_df)
    chart = build_chart(intraday_df, quotes.get(CHART_SYMBOL, {}).get("prev"))
    daily = build_daily_chart(get_history(CHART_SYMBOL, period="2y"))

    news = get_news(limit=NEWS_POOL)
    cal_today, cal_ahead = get_calendar()
    verified = verify_releases([c for c in cal_today if not c.get("actual")])
    fng = get_fear_greed()

    health = market_health()
    sentiment = retail_sentiment(sorted(set(list(HOLDINGS) + list(WATCHLIST))))
    buzz = reddit_buzz()
    scan = scan_universe()
    movers = hot_stocks(scan)
    near_ma = near_moving_averages(scan)

    port = portfolio_view(quotes)

    # analyst coverage for what you own plus whatever is moving today
    watch = list(HOLDINGS) + list(WATCHLIST) + [m["sym"] for m in movers]
    watch = sorted(set(watch))
    analysts = get_analysts(watch[:24])
    earnings = get_earnings(watch)
    my_news = portfolio_news()
    tracked_syms = sorted(set(list(HOLDINGS) + list(WATCHLIST)))
    today_cal = earnings_calendar_day(dt.datetime.now(MARKET_TZ).date())
    e_results = merge_earnings_sources(tracked_syms, today_cal)
    e_coverage = earnings_coverage(e_results)
    fundamentals = get_fundamentals(watch)
    earn_hist = get_earnings_history(watch)
    shorted = heavily_shorted(fundamentals)

    today_key = dt.datetime.now(MARKET_TZ).date().isoformat()
    prev_today = prev_state if prev_state.get("date") == today_key else {}

    # Two independent inputs. The question field gets an answer, the ticker
    # field gets a per name write up. Filling one must never suppress the other.
    q_tickers = extract_tickers(QUESTION, "") if QUESTION else []
    d_tickers = extract_tickers("", QUESTION_TICKERS) if QUESTION_TICKERS else []
    all_q = list(dict.fromkeys(q_tickers + d_tickers))
    q_context = question_context(all_q) if all_q else ""
    if QUESTION:
        print(f"question: {QUESTION[:80]}")
        print(f"  tickers from question: {', '.join(q_tickers) or 'none'}")
    if d_tickers:
        print(f"deep dive tickers: {', '.join(d_tickers)}")

    tech = index_technicals(CHART_SYMBOL)
    payload = summary_payload(quotes, fng, movers, near_ma, cal_today,
                              cal_ahead, news, port, analysts, earnings,
                              prev_today, tech, my_news, fundamentals,
                              earn_hist, shorted, intraday, health,
                              sentiment, buzz, verified, q_context,
                              d_tickers, e_results, e_coverage, today_cal,
                              tracked_syms)
    brief, ai_used = ai_brief(payload, [chart, daily], quotes, fng, movers,
                              cal_today, port)

    slot = ("Weekend review" if args.weekly
            else ("Your question, plus the daily report" if QUESTION
                  else (slot_name() or "Market report")))
    html = build_html(slot, quotes, news, cal_today, cal_ahead, fng, movers,
                      near_ma, brief, ai_used, port, analysts, earnings,
                      my_news, fundamentals, earn_hist, shorted, health,
                      sentiment, buzz, q_tickers, d_tickers, e_results,
                      e_coverage, today_cal, tracked_syms)

    spx = quotes.get("SPY", {}).get("pct", 0)
    qqq = quotes.get("QQQ", {}).get("pct", 0)
    subject = f"{slot}: SPY {spx:+.2f}%, QQQ {qqq:+.2f}%"
    if QUESTION:
        subject = "Re: " + (QUESTION[:60] + ("..." if len(QUESTION) > 60 else ""))
    if port:
        subject += f", you {port['day_pl']:+,.0f}"

    if args.preview:
        with open("report.html", "w", encoding="utf-8") as f:
            f.write(html.replace("cid:heatmap", "heatmap.png")
                        .replace("cid:chart", "chart.png")
                        .replace("cid:daily", "daily.png"))
        open("heatmap.png", "wb").write(heat)
        open("chart.png", "wb").write(chart)
        open("daily.png", "wb").write(daily)
        pdf_html = build_html(slot, quotes, news, cal_today, cal_ahead, fng,
                              movers, near_ma, brief, ai_used, port, analysts,
                              earnings, my_news, fundamentals, earn_hist,
                              shorted, health, sentiment, buzz, q_tickers,
                              d_tickers, e_results, e_coverage, today_cal,
                              tracked_syms,
                              for_pdf=True)
        pdf = build_pdf(pdf_html, {"heatmap": heat, "chart": chart,
                                   "daily": daily})
        if pdf:
            open("report.pdf", "wb").write(pdf)
        print("wrote report.html, report.pdf, heatmap.png, chart.png, daily.png")
        print("ai used:", ai_used)
        print("subject:", subject)
        return

    images = {"heatmap": heat, "chart": chart, "daily": daily}
    pdf_html = build_html(slot, quotes, news, cal_today, cal_ahead, fng, movers,
                          near_ma, brief, ai_used, port, analysts, earnings,
                          my_news, fundamentals, earn_hist, shorted, health,
                          sentiment, buzz, q_tickers, d_tickers, e_results,
                          e_coverage, today_cal, tracked_syms, for_pdf=True)
    pdf = build_pdf(pdf_html, images)
    stamp = dt.datetime.now(LOCAL_TZ).strftime("%Y-%m-%d")
    send_email(subject, html, images, pdf, f"market-report-{stamp}.pdf")
    write_state({"date": today_key, "slot": slot, "sent": True,
                 "sent_at": dt.datetime.now(MARKET_TZ).isoformat(timespec="minutes"),
                 "summary": brief["summary"],
                 "spx": quotes.get("^GSPC", {}).get("last")})
    print("sent:", subject)


if __name__ == "__main__":
    main()
