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

INDEXES = {
    "^GSPC": "S&P 500",
    "^DJI": "Dow Jones",
    "QQQ": "Nasdaq 100 (QQQ)",
    "^RUT": "Russell 2000",
    "^VIX": "VIX",
    "^TNX": "US 10Y Yield",
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
    if getattr(close, "ndim", 1) == 1:                # single symbol
        close, opn = close.to_frame(symbols[0]), opn.to_frame(symbols[0])

    live = {}
    try:
        tk = yf.Tickers(" ".join(symbols))
        for s in symbols:
            try:
                live[s] = float(tk.tickers[s].fast_info["lastPrice"])
            except Exception:
                pass
    except Exception as e:
        print(f"live quotes unavailable: {e}", file=sys.stderr)

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
                           if ext and abs(ext - last) > 1e-9 else None,
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


def get_calendar():
    """US economic events. Returns (today, rest_of_week)."""
    try:
        r = requests.get(CALENDAR_URL, timeout=20,
                         headers={"User-Agent": "Mozilla/5.0"})
        data = r.json()
    except Exception as e:
        print(f"calendar failed: {e}", file=sys.stderr)
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

    bits = [f"The S&P 500 is {word(p('^GSPC'))} {abs(p('^GSPC')):.2f} percent, "
            f"the Nasdaq 100 {word(p('QQQ'))} {abs(p('QQQ')):.2f} percent and "
            f"the Dow {word(p('^DJI'))} {abs(p('^DJI')):.2f} percent."]
    bits.append(f"Gold is {word(p('GC=F'))} {abs(p('GC=F')):.2f} percent and "
                f"Bitcoin {word(p('BTC-USD'))} {abs(p('BTC-USD')):.2f} percent.")
    if fng:
        bits.append(f"CNN Fear and Greed sits at {fng['score']:.0f}, {fng['rating'].lower()}.")
    if port:
        bits.append(f"The portfolio is {word(port['day_pct'])} "
                    f"{abs(port['day_pct']):.2f} percent, "
                    f"{port['day_pl']:+,.0f} on the day.")
    if movers:
        names = ", ".join(f"{m['sym']} {m['pct']:+.1f}%" for m in movers[:3])
        bits.append(f"Biggest movers: {names}.")
    if cal_today:
        n = len(cal_today)
        bits.append(f"{n} US data release{'s' if n != 1 else ''} on today's calendar.")
    return " ".join(bits)


AI_SCHEMA = """You are writing a market report for a 46 year old investor with a
20 year time horizon. He is financially literate, understands options, leverage
and technical analysis, and does not need concepts explained. He wants your
actual read, not hedged neutrality. Write for someone who can handle a direct
opinion and will make his own decision.

Return ONLY a JSON object, no markdown fences, with these keys:

"summary": string. 4 to 6 sentences. The whole day in plain English, written so
  his wife could read it over coffee and understand where things stand. What US
  equities did and why, bonds, gold and Bitcoin, anything notable overseas, the
  sentiment reading, the biggest single stock story, what is coming. Specific
  numbers. Calm and factual. This one is a briefing, not analysis.

"portfolio_analysis": string, or "" if no portfolio data was supplied. 5 to 8
  sentences. Assess the health of the book against a 20 year horizon. Cover:
  what drove today in dollars, concentration and whether any position has grown
  into an outsized share, sector tilt, which positions are working and which
  are dragging, how the holdings sit against analyst targets, and any earnings
  coming that matter to him specifically. Then give your actual view on what a
  20 year holder might do from here, including doing nothing, which is often
  the right answer. Be concrete. Name tickers. If you think something looks
  stretched or something looks like an opportunity, say so plainly and say why.
  Do not recommend day trading or short dated options.

"technical_analysis": string. 5 to 8 sentences. Read both attached charts. The
  first is the intraday 5 minute S&P with VWAP in gold and prior close dashed.
  The second is the daily S&P with 20, 50 and 200 day averages. Cover the shape
  of the session, whether price held above or below VWAP and what that says
  about who was in control, where price sits against each daily average, the
  trend structure, whether volume confirmed or contradicted the move, and any
  divergence worth noting. Then give your forecast: what setup is in play, what
  would confirm it and what would invalidate it. Frame it as scenarios with
  your lean, not a certainty. Reference actual levels from the data block.

"macro_analysis": string. 6 to 10 sentences. This is the deep one. Work through
  the economic data released today, what is coming this week, and the headlines
  supplied. Go past summary into implication: what the data says about growth,
  inflation and the rate path, how the bond market is positioned versus the
  equity market, what the sector rotation reveals about what money is doing,
  what the sentiment reading means in context, and where the risks sit. Draw
  connections between separate data points that a casual reader would miss.
  State your bullish or bearish lean and the reasoning behind it. Acknowledge
  what would change your mind.

"lean": string, exactly one of "bullish", "leaning bullish", "neutral",
  "leaning bearish", "bearish". Your overall near term read.

"lean_reason": string, one sentence, under 20 words, on why.

"news_picks": array of exactly 10 objects, each {"title": string, "why": string}.
  Pick the headlines that genuinely matter to a long term investor from the
  list supplied. Copy each title exactly as given, character for character, and
  do NOT include the source name in square brackets, or the link will break.
  "why" is one sentence on why it matters to him. Rank them most important
  first. Prefer stories with real economic or company substance over opinion
  pieces, stock picking listicles, and anything phrased as a prediction or a
  teaser. Spread the picks across outlets rather than taking several from one.
  Cover different ground with each pick: macro, rates, a major company, the
  sector he is exposed to, and anything overseas that matters.

NUMBERS RULE, this matters more than anything else above. Every number you
write must appear verbatim in the MARKET DATA block. Do not estimate a level
from the chart images, do not convert a percentage into a level, do not recall
a figure from memory, and do not describe anything as elevated, cheap, extended
or historically high unless the data block gives you the comparison. The charts
are for reading shape and direction only, never for reading values off an axis.
If you want to cite a number you have not been given, leave it out and describe
the direction instead.

Do not use hyphens as punctuation anywhere in your output."""


def ai_brief(payload, images, quotes, fng, movers, cal_today, port):
    """One API call returning summary, chart read, news picks and considerations."""
    blank = {
        "summary": fallback_summary(quotes, fng, movers, cal_today, port),
        "portfolio_analysis": "", "technical_analysis": "",
        "macro_analysis": "", "lean": "", "lean_reason": "",
        "news_picks": [],
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
                    my_news=None):
    """Compact text block handed to the model."""
    def line(names):
        return "; ".join(
            f"{lab} at {quotes[s]['last']:,.2f} ({quotes[s]['pct']:+.2f}%)"
            for s, lab in names.items() if s in quotes)

    parts = [
        f"US indices: {line(INDEXES)}",
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
    if earnings:
        parts.append("Earnings around now: " + "; ".join(
            f"{e['sym']}{' (held)' if e['held'] else ''} "
            f"{'reported' if e['reported'] else 'reports'} "
            f"{e['date'].strftime('%b %d')}" for e in earnings[:14]))
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
        parts.append("Today's US data: " + "; ".join(
            f"{c['title']} actual {c['actual'] or 'pending'} vs forecast {c['forecast'] or 'na'}"
            for c in cal_today))
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
        "HEADLINES from Yahoo Finance, CNBC, Reuters, CNN Business and "
        "Bloomberg, some with a summary line beneath. Use all of them to "
        "inform your macro analysis. When choosing news_picks, prefer stories "
        "the reader can actually open: items marked PAYWALLED need a "
        "subscription, so only pick one if it is clearly more important than "
        "the free alternatives. Judge on merit, not outlet, and skip "
        "clickbait, listicles and prediction teasers. Fewer than four picks is "
        "fine if fewer than four matter:\n" + "\n".join(lines))
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
    """Intraday candles with VWAP and a prior close reference line."""
    style = mpf.make_mpf_style(
        base_mpf_style="nightclouds",
        rc={"font.size": 9},
        marketcolors=mpf.make_marketcolors(
            up="#3fb950", down="#f85149", edge="inherit",
            wick="inherit", volume="in"))

    # session VWAP, reset each trading day
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

    # vertical divider at the first bar of the most recent session
    days_seen = sorted(set(day))
    vlines = None
    if len(days_seen) > 1:
        first_today = df.index[[d == days_seen[-1] for d in day]][0]
        vlines = dict(vlines=[first_today], colors=["#484f58"],
                      linestyle="-", linewidths=1.0)

    label = f"S&P 500 intraday, {INTRADAY_INTERVAL} candles"
    sub = "gold line is VWAP"
    if prev_close:
        sub += ", dashed line is prior close"

    fig, _ = mpf.plot(df, type="candle", style=style, volume=True,
                      addplot=adds, hlines=hlines, vlines=vlines,
                      figsize=(11, 6.2), returnfig=True,
                      tight_layout=True)
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


def cal_table(rows, show_day=False):
    if not rows:
        return "<p class='small'>Nothing scheduled at medium or high impact.</p>"
    day_h = "<th>Day</th>" if show_day else ""
    out = "".join(
        (f"<tr>{'<td>' + c['day'] + '</td>' if show_day else ''}"
         f"<td>{c['time']}</td>"
         f"<td>{c['title']}"
         f"{' <span class=hi>high</span>' if c['impact'] == 'High' else ''}</td>"
         f"<td class='num'>{c['actual'] or '-'}</td>"
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


LEAN_COLORS = {
    "bullish": "#3fb950", "leaning bullish": "#56b36b", "neutral": "#8b949e",
    "leaning bearish": "#e8935b", "bearish": "#f85149",
}


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

    rows = "".join(
        f"<tr><td><b>{e['sym']}</b>"
        + ("<span class='small'> held</span>" if e["held"] else "")
        + f"</td><td>{e['date'].strftime('%a %b %d')}</td>"
        f"<td class='num small'>{when(e)}</td>"
        f"<td class='small'>{'reported' if e['reported'] else 'upcoming'}</td></tr>"
        for e in earnings)
    return ("<h2 id='earnings'>Earnings, just reported and coming up</h2><table>"
            "<tr><th>Ticker</th><th>Date</th><th class='num'>When</th>"
            "<th>Status</th></tr>" + rows + "</table>")


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


def news_block(picks, news):
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
            rows += (f"<tr><td>{head}{tag}"
                     f"<div class='small' style='margin-top:3px'>"
                     f"{p.get('why','')}</div></td></tr>")
        return "<h2>What actually matters today</h2><table>" + rows + "</table>"
    return ("<h2>Headlines</h2><table>" + "".join(
        f"<tr><td><a href='{n['link']}'>{n['title']}</a></td></tr>" for n in news)
        + "</table>")


NAV = [
    ("brief", "Brief"), ("portfolio", "Portfolio"), ("charts", "Charts"),
    ("mynews", "Your news"), ("macro", "Macro"), ("news", "Top news"),
    ("movers", "Movers"),
    ("numbers", "The numbers"), ("allnews", "Every headline"),
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
               my_news=None, for_pdf=False):
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
              f"</div>")

    sec_portfolio = ("<a id='portfolio'></a>" + portfolio_block(port, None)
                     + analysis_box("Portfolio analysis",
                                    brief.get("portfolio_analysis"), "#3fb950")
                     + portfolio_news_block(my_news or [], earnings))

    sec_charts = ("<h2 id='charts'>S&amp;P 500 intraday</h2><img src='cid:chart'>"
                  "<h2>S&amp;P 500 daily</h2><img src='cid:daily'>"
                  + analysis_box("Technical analysis",
                                 brief.get("technical_analysis"), "#a371f7"))

    sec_macro = ("<a id='macro'></a>"
                 + analysis_box("Macro and news analysis",
                                brief.get("macro_analysis"), "#f0b429")
                 + "<a id='news'></a>"
                 + news_block(brief.get("news_picks"), news)
                 + "<h2>US economic data today</h2>" + cal_table(cal_today)
                 + "<h2>Coming up this week</h2>" + cal_table(cal_ahead, show_day=True))

    idx = ("<h2 id='numbers'>US indices and rates</h2><table>"
           "<tr><th>Market</th><th class='num'>Close</th>"
           "<th class='num'>Change</th><th class='num'>%</th>"
           f"<th class='num'>{session_label().title()}</th></tr>"
           + quote_rows(INDEXES, quotes) + "</table>"
           "<p class='small'>All figures are the official close from the last "
           "completed session, so indices and stocks are on the same clock. The "
           "final column shows where the live price sits now, which is where any "
           "pre-market or after hours move appears.</p>")
    sec_market = (idx
                  + "<h2>Sectors, best to worst</h2>"
                  + simple_table(SECTORS, quotes, "Sector", sort=True)
                  + fng_block(fng)
                  + "<h2>Heat map</h2><img src='cid:heatmap'>"
                  + movers_block(movers) + ma_block(near_ma)
                  + analyst_block(analysts)
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
    """Which report is due, based on New York time. None if no run is due."""
    now = dt.datetime.now(MARKET_TZ)
    for h, m, label in TARGETS_ET:
        target = now.replace(hour=h, minute=m, second=0, microsecond=0)
        if abs((now - target).total_seconds()) <= WINDOW_MIN * 60:
            return label
    return None


def market_traded_today():
    """True if the US market has a bar for today. Catches weekends and holidays."""
    try:
        df = yf.download("SPY", period="5d", interval="1d",
                         progress=False, auto_adjust=False)
        last = df.index[-1].date()
        return last == dt.datetime.now(MARKET_TZ).date()
    except Exception as e:
        print(f"market day check failed, running anyway: {e}", file=sys.stderr)
        return True


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--preview", action="store_true",
                    help="write report.html and images locally, send nothing")
    ap.add_argument("--force", action="store_true",
                    help="send even if no report is currently due")
    ap.add_argument("--weekly", action="store_true",
                    help="weekend edition, wider lookback and no time gate")
    args = ap.parse_args()

    if not (args.preview or args.force or args.weekly):
        if slot_name() is None:
            print("no report due right now, exiting")
            return
        if not market_traded_today():
            print("market closed today, exiting")
            return

    symbols = (list(INDEXES) + list(SECTORS) + list(MEGACAPS)
               + list(CRYPTO) + list(COMMODITIES) + list(GLOBAL)
               + list(HOLDINGS))
    quotes = get_quotes(sorted(set(symbols)))

    sector_items = sorted(
        [(lab, quotes[s]["pct"]) for s, lab in SECTORS.items() if s in quotes],
        key=lambda x: -x[1])
    mega_items = sorted(
        [(lab, quotes[s]["pct"]) for s, lab in MEGACAPS.items() if s in quotes],
        key=lambda x: -x[1])

    heat = build_heatmap(sector_items, mega_items)
    chart = build_chart(get_intraday(CHART_SYMBOL),
                        quotes.get(CHART_SYMBOL, {}).get("prev"))
    daily = build_daily_chart(get_history(CHART_SYMBOL, period="2y"))

    news = get_news(limit=NEWS_POOL)
    cal_today, cal_ahead = get_calendar()
    fng = get_fear_greed()

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

    prev = read_state()
    today_key = dt.datetime.now(MARKET_TZ).date().isoformat()
    prev_today = prev if prev.get("date") == today_key else {}

    tech = index_technicals(CHART_SYMBOL)
    payload = summary_payload(quotes, fng, movers, near_ma, cal_today,
                              cal_ahead, news, port, analysts, earnings,
                              prev_today, tech, my_news)
    brief, ai_used = ai_brief(payload, [chart, daily], quotes, fng, movers,
                              cal_today, port)

    slot = "Weekend review" if args.weekly else (slot_name() or "Market report")
    html = build_html(slot, quotes, news, cal_today, cal_ahead, fng, movers,
                      near_ma, brief, ai_used, port, analysts, earnings,
                      my_news)

    spx = quotes.get("^GSPC", {}).get("pct", 0)
    qqq = quotes.get("QQQ", {}).get("pct", 0)
    subject = f"{slot}: SPX {spx:+.2f}%, QQQ {qqq:+.2f}%"
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
                              earnings, my_news, for_pdf=True)
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
                          my_news, for_pdf=True)
    pdf = build_pdf(pdf_html, images)
    stamp = dt.datetime.now(LOCAL_TZ).strftime("%Y-%m-%d")
    send_email(subject, html, images, pdf, f"market-report-{stamp}.pdf")
    write_state({"date": today_key, "slot": slot,
                 "summary": brief["summary"],
                 "spx": quotes.get("^GSPC", {}).get("last")})
    print("sent:", subject)


if __name__ == "__main__":
    main()
