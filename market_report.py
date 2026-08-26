"""
Market Report Emailer
Sends a market synopsis by email three times a day.

Setup:
  pip install yfinance mplfinance feedparser pandas matplotlib requests
  Set MAIL_TO below and put your Resend key in the RESEND_API_KEY env var.

Test run (writes report.html locally, sends nothing):
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
    if getattr(close, "ndim", 1) == 1:                 # single symbol
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
    if not out:                     # markup changed, fall back to headlines only
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
                pass                                # keep it, beehiiv slugs drift
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
        "macro_analysis": "", "health_analysis": "", "lean": "",
        "lean_reason": "", "news_picks": [],
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
        text = re.sub(r"^```(?:json)?|
