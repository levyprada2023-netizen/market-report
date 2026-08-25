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
import json
import os
import re
import smtplib
import ssl
import sys
from email.message import EmailMessage
from zoneinfo import ZoneInfo

import feedparser
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import mplfinance as mpf
import requests
import yfinance as yf

# ============================== CONFIG ==============================

# Resend SMTP. Username is the literal word "resend" for every account,
# password is your API key. The key comes from an environment variable so it
# never sits in this file.
SMTP_HOST = "smtp.resend.com"
SMTP_PORT = 465
SMTP_USER = "resend"
SMTP_PASS = os.environ.get("RESEND_API_KEY", "")

MAIL_FROM = "Market Report <onboarding@resend.dev>"
MAIL_TO = "levyprada2023@gmail.com"            # where the report goes

LOCAL_TZ = ZoneInfo("America/Edmonton")
MARKET_TZ = ZoneInfo("America/New_York")

# Report times anchored to New York, so they stay correct through every
# time change on either side of the border. Alberta stops changing clocks
# on Nov 1 2026, the US does not, and this handles that automatically.
TARGETS_ET = [
    (10, 0, "Morning open report"),    # 30 min after the open
    (12, 30, "Midday report"),
    (15, 0, "Closing report"),         # 1 hour before the close
]
WINDOW_MIN = 25   # how far either side of a target a run still counts

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

# Liquid large caps scanned for movers and moving average proximity.
UNIVERSE = """
AAPL MSFT NVDA GOOGL AMZN META AVGO TSLA LLY JPM XOM WMT COST MU AMD
NFLX ORCL CRM ADBE INTC QCOM TXN AMAT LRCX KLAC ASML ARM PLTR SMCI DELL
COIN MSTR HOOD XYZ PYPL SHOP UBER ABNB DASH SPOT NOW SNOW CRWD PANW ZS
DDOG NET MDB TEAM WDAY INTU IBM CSCO ACN GE CAT DE HON RTX LMT BA
UNH JNJ PFE MRK ABBV TMO ABT DHR ISRG VRTX REGN AMGN GILD BMY CVS
BAC WFC GS MS C SCHW BLK AXP V MA PGR CB SPGI ICE MRNA
CVX COP SLB EOG PSX MPC OXY KMI WMB
PG KO PEP PM MO MDLZ CL KMB GIS SYY KR
HD LOW TGT TJX NKE SBUX MCD CMG BKNG MAR RCL
DIS CMCSA T VZ TMUS CHTR WBD
LIN APD SHW FCX NEM NUE
AMT PLD EQIX SPG O
NEE DUK SO D AEP
""".split()

MA_NEAR_PCT = 2.0    # how close to a moving average counts as "near"
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
NEWS_FEED = "https://finance.yahoo.com/news/rssindex"
NEWS_POOL = 30      # headlines gathered, then triaged down by the model
CALENDAR_URL = "https://nfs.faireconomy.media/ff_calendar_thisweek.json"

# ============================== DATA ==============================


def get_quotes(symbols):
    """Return {symbol: {'last':float,'prev':float,'pct':float,'open':float}}"""
    out = {}
    tk = yf.Tickers(" ".join(symbols))
    for s in symbols:
        try:
            fi = tk.tickers[s].fast_info
            last = float(fi["lastPrice"])
            prev = float(fi["previousClose"])
            op = float(fi.get("open") or prev)
            out[s] = {
                "last": last,
                "prev": prev,
                "open": op,
                "pct": (last - prev) / prev * 100.0,
                "from_open": (last - op) / op * 100.0,
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


def get_news(limit=8):
    feed = feedparser.parse(NEWS_FEED)
    items = []
    for e in feed.entries[:limit]:
        items.append({
            "title": e.get("title", ""),
            "link": e.get("link", ""),
            "source": e.get("source", {}).get("title", "Yahoo Finance"),
        })
    return items


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
    df = yf.download(UNIVERSE, period="1y", interval="1d", progress=False,
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


def hot_stocks(rows, n=6):
    """Biggest movers, weighted toward names also trading unusual volume."""
    scored = [r for r in rows if abs(r["pct"]) >= 1.5]
    scored.sort(key=lambda r: abs(r["pct"]) * (1 + min(r["rvol"], 4) / 4),
                reverse=True)
    picks = scored[:n]
    for p in picks:
        p["news"] = symbol_news(p["sym"])
    return picks


def symbol_news(sym, limit=2):
    try:
        feed = feedparser.parse(SYMBOL_NEWS.format(sym=sym))
        return [{"title": e.get("title", ""), "link": e.get("link", "")}
                for e in feed.entries[:limit]]
    except Exception:
        return []


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


AI_SCHEMA = """Return ONLY a JSON object, no markdown fences, with these keys:

"summary": string. 4 to 6 sentences of plain English for a married couple who
  are long term investors. What US equities did and why, how bonds, gold and
  Bitcoin behaved, anything notable overseas, the sentiment reading, the single
  most important stock story, what is coming on the calendar. Use specific
  numbers. Factual and calm. No advice, no predictions.

"portfolio_note": string, or "" if no portfolio data was supplied. 2 to 3
  sentences on what their own holdings did today in dollars, which positions
  drove it, and any holding with earnings coming up. Factual only.

"chart_read": string. 2 to 4 sentences reading the two attached charts. The
  first is the intraday 5 minute S&P with VWAP in gold and prior close dashed.
  The second is the daily S&P with 20, 50 and 200 day averages. Describe the
  shape of the session, whether price held above or below VWAP, where price
  sits against the daily averages, and whether volume backed the move.

"news_picks": array of up to 4 objects, each {"title": string, "why": string}.
  Pick only the headlines that genuinely matter to a long term investor from
  the list supplied. Copy the title exactly as given. "why" is one short
  sentence on why it matters.

"considerations": string. 3 to 5 sentences. This is the only place you may be
  interpretive. Note what a long term investor might reasonably watch or think
  about given today's data: valuation stretch or compression, sentiment
  extremes, positions sitting at technical levels, upcoming catalysts, how
  analyst targets compare to current prices. Frame everything as observations
  and questions rather than instructions. Never say buy, sell, trim or add.
  Never predict a price. Acknowledge uncertainty where it exists.

Do not use hyphens as punctuation anywhere in your output."""


def ai_brief(payload, images, quotes, fng, movers, cal_today, port):
    """One API call returning summary, chart read, news picks and considerations."""
    blank = {
        "summary": fallback_summary(quotes, fng, movers, cal_today, port),
        "portfolio_note": "", "chart_read": "", "news_picks": [],
        "considerations": "",
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
            json={"model": AI_MODEL, "max_tokens": 2000,
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


def summary_payload(quotes, fng, movers, near_ma, cal_today, cal_ahead,
                    news, port, analysts, earnings, prev_state):
    """Compact text block handed to the model."""
    def line(names):
        return "; ".join(
            f"{lab} {quotes[s]['pct']:+.2f}%" for s, lab in names.items()
            if s in quotes)

    parts = [
        f"US indices: {line(INDEXES)}",
        f"Sectors: {line(SECTORS)}",
        f"Crypto: {line(CRYPTO)}",
        f"Commodities and dollar: {line(COMMODITIES)}",
        f"Global: {line(GLOBAL)}",
    ]
    if fng:
        parts.append(f"CNN Fear and Greed: {fng['score']:.0f} ({fng['rating']}), "
                     f"week ago {fng['week']:.0f}, month ago {fng['month']:.0f}")
    if port:
        parts.append(
            f"PORTFOLIO: total {CURRENCY} {port['value']:,.0f}, today "
            f"{port['day_pl']:+,.0f} ({port['day_pct']:+.2f}%). "
            + ("Total gain " + format(port["total_gain"], "+,.0f") + ". "
               if port["total_gain"] is not None else "")
            + "Positions by dollar impact today: "
            + "; ".join(f"{r['sym']} {r['moved']:+,.0f} ({r['pct']:+.2f}%)"
                        for r in sorted(port["rows"],
                                        key=lambda r: -abs(r["moved"]))[:10]))
    if analysts:
        parts.append("Analyst targets: " + "; ".join(
            f"{s} price {a['price']:,.2f} vs mean target {a['mean']:,.2f} "
            f"({a['upside']:+.1f}%), {a['rating'] or 'na'}, {a['count'] or '?'} analysts"
            for s, a in list(analysts.items())[:14]))
    if earnings:
        parts.append("Earnings coming up: " + "; ".join(
            f"{e['sym']} on {e['date'].strftime('%b %d')} ({e['days']}d)"
            for e in earnings[:10]))
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
        parts.append("EARLIER REPORT TODAY (say what changed since this, do not "
                     f"repeat it): {prev_state['summary']}")
    parts.append("HEADLINES, pick the ones that matter:\n" + "\n".join(
        f"- {n['title']}" for n in news))
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


def get_earnings(symbols, within_days=21):
    """Upcoming earnings dates inside the window."""
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
                if 0 <= days <= within_days:
                    out.append({"sym": s, "date": d, "days": days})
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
    """Value the holdings and rank positions by today's dollar impact."""
    if not HOLDINGS:
        return None
    rates = fx_rates(HOLDINGS.keys())
    rows, value, day_pl, cost_basis, missing = [], 0.0, 0.0, 0.0, []
    for sym, shares in HOLDINGS.items():
        q = quotes.get(sym)
        if not q:
            missing.append(sym)
            continue
        cur = currency_of(sym)
        fx = rates.get(cur, 1.0)
        val = q["last"] * shares * fx
        moved = (q["last"] - q["prev"]) * shares * fx
        value += val
        day_pl += moved
        book = BOOK_COST.get(sym)
        if book:
            cost_basis += book * shares * fx
        rows.append({
            "sym": sym, "shares": shares, "price": q["last"],
            "pct": q["pct"], "value": val, "moved": moved,
            "cur": cur,
            "gain_pct": (q["last"] / book - 1) * 100 if book else None,
        })
    if not rows:
        return None
    if missing:
        print(f"no quote for: {', '.join(missing)}", file=sys.stderr)
    prev_value = value - day_pl
    return {
        "rows": rows,
        "value": value + CASH,
        "day_pl": day_pl,
        "day_pct": (day_pl / prev_value * 100) if prev_value else 0.0,
        "total_gain": (value - cost_basis) if cost_basis else None,
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


def quote_rows(names, quotes):
    out = []
    for sym, label in names.items():
        q = quotes.get(sym)
        if not q:
            continue
        out.append(
            f"<tr><td>{label}</td>"
            f"<td class='num'>{q['last']:,.2f}</td>"
            f"<td class='num {cls(q['pct'])}'>{q['pct']:+.2f}%</td>"
            f"<td class='num {cls(q['from_open'])}'>{q['from_open']:+.2f}%</td></tr>")
    return "".join(out)


def simple_table(names, quotes, head="Market", sort=False):
    items = list(names.items())
    if sort:
        items.sort(key=lambda kv: quotes.get(kv[0], {}).get("pct", 0), reverse=True)
    rows = "".join(
        f"<tr><td>{lab}</td><td class='num'>{quotes[s]['last']:,.2f}</td>"
        f"<td class='num {cls(quotes[s]['pct'])}'>{quotes[s]['pct']:+.2f}%</td></tr>"
        for s, lab in items if s in quotes)
    return (f"<table><tr><th>{head}</th><th class='num'>Last</th>"
            f"<th class='num'>Change</th></tr>{rows}</table>")


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


def movers_block(movers):
    if not movers:
        return ""
    cards = []
    for m in movers:
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
    return ("<h2>Stocks getting attention</h2><table>"
            "<tr><th>Ticker</th><th class='num'>Price</th><th class='num'>Change</th>"
            "<th class='num'>Volume</th><th>Why</th></tr>"
            + "".join(cards) + "</table>"
            "<p class='small'>Volume column is today against the 20 day average. "
            "Above 1.5x means unusual participation.</p>")


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


def portfolio_block(port, ai_note):
    if not port:
        return ""
    col = "up" if port["day_pl"] > 0 else ("dn" if port["day_pl"] < 0 else "flat")
    rows = "".join(
        f"<tr><td><b>{r['sym']}</b></td>"
        f"<td class='num'>{r['shares']:,.0f}</td>"
        f"<td class='num'>{r['price']:,.2f}</td>"
        f"<td class='num {cls(r['pct'])}'>{r['pct']:+.2f}%</td>"
        f"<td class='num'>{r['value']:,.0f}</td>"
        f"<td class='num {cls(r['moved'])}'>{r['moved']:+,.0f}</td>"
        f"<td class='num {cls(r['gain_pct'] or 0)}'>"
        f"{format(r['gain_pct'], '+.1f') + '%' if r['gain_pct'] is not None else '-'}</td></tr>"
        for r in sorted(port["rows"], key=lambda r: -abs(r["moved"])))
    total_gain = ("<div class='small'>Total gain since purchase: "
                  f"{port['total_gain']:+,.0f} {CURRENCY}</div>"
                  if port["total_gain"] is not None else "")
    note = f"<p class='small' style='font-size:14px'>{ai_note}</p>" if ai_note else ""

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
        footnotes.append("Foreign listings converted at " + ", ".join(
            f"1 {c} = {r:.4f} USD" for c, r in port["fx"].items()))
    if port.get("missing"):
        footnotes.append("No quote found for " + ", ".join(port["missing"]))
    footnotes.append(f"Positions read from {port.get('source', 'config')}")
    foot = "<p class='small'>" + ". ".join(footnotes) + ".</p>"
    return (f"<h2>Your portfolio</h2>"
            f"<div style='font-size:24px;font-weight:700'>"
            f"{CURRENCY} {port['value']:,.0f}</div>"
            f"<div class='{col}' style='font-size:16px;font-weight:600'>"
            f"{port['day_pl']:+,.0f} today ({port['day_pct']:+.2f}%)</div>"
            f"{total_gain}{note}<table>"
            f"<tr><th>Ticker</th><th class='num'>Shares</th><th class='num'>Price</th>"
            f"<th class='num'>Today</th><th class='num'>Value</th>"
            f"<th class='num'>Day P/L</th><th class='num'>Gain</th></tr>"
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
    rows = "".join(
        f"<tr><td><b>{e['sym']}</b></td>"
        f"<td>{e['date'].strftime('%a %b %d')}</td>"
        f"<td class='num'>{e['days']} day{'s' if e['days'] != 1 else ''}</td></tr>"
        for e in earnings)
    return ("<h2>Earnings coming up</h2><table>"
            "<tr><th>Ticker</th><th>Date</th><th class='num'>Away</th></tr>"
            + rows + "</table>")


def news_block(picks, news):
    if picks:
        rows = "".join(
            f"<tr><td><b>{p.get('title','')}</b>"
            f"<div class='small' style='margin-top:3px'>{p.get('why','')}</div></td></tr>"
            for p in picks)
        return ("<h2>What actually matters today</h2><table>" + rows + "</table>"
                "<details><summary class='small'>All headlines</summary><table>"
                + "".join(f"<tr><td><a href='{n['link']}'>{n['title']}</a></td></tr>"
                          for n in news) + "</table></details>")
    return ("<h2>Headlines</h2><table>" + "".join(
        f"<tr><td><a href='{n['link']}'>{n['title']}</a></td></tr>" for n in news)
        + "</table>")


def build_html(slot, quotes, news, cal_today, cal_ahead, fng, movers,
               near_ma, brief, ai_used, port, analysts, earnings):
    now = dt.datetime.now(LOCAL_TZ)

    lede = ("<div class='lede' style=\"background:#161b22;color:#e6edf3;"
            "border-left:3px solid #58a6ff;border-radius:6px;padding:14px 16px;"
            "margin:14px 0 6px;font-size:15px;line-height:1.55\">"
            f"{brief['summary']}</div>")
    if brief.get("chart_read"):
        chart_read = ("<p class='small' style=\"font-size:14px;margin:8px 0 0;"
                      f"color:#8b949e\">{brief['chart_read']}</p>")
    else:
        chart_read = ""
    if brief.get("considerations"):
        think = ("<h2>Things to think about</h2>"
                 "<div class='think' style=\"background:#161b22;color:#e6edf3;"
                 "border-left:3px solid #f0b429;border-radius:6px;padding:14px 16px;"
                 "margin:6px 0;font-size:14px;line-height:1.55\">"
                 f"{brief['considerations']}</div>"
                 "<p class='small'>Written by Claude as observations, not advice. "
                 "It has no knowledge of your plan, your tax position or your "
                 "timeline.</p>")
    else:
        think = ""

    header = (f"<div class='hdr'>{slot}</div>"
              f"<div class='small'>{now.strftime('%A %B %d, %Y at %I:%M %p')} MT</div>"
              f"{lede}"
              f"<div class='small' style='margin-bottom:4px'>"
              f"{'Written by Claude from the data below.' if ai_used else 'Auto generated summary.'}"
              f"</div>")

    idx = ("<h2>US indices and rates</h2><table>"
           "<tr><th>Market</th><th class='num'>Last</th>"
           "<th class='num'>vs prev close</th><th class='num'>vs open</th></tr>"
           + quote_rows(INDEXES, quotes) + "</table>")

    sec = "<h2>Sectors, best to worst</h2>" + simple_table(
        SECTORS, quotes, "Sector", sort=True)

    crypto = "<h2>Crypto</h2>" + simple_table(CRYPTO, quotes, "Coin")
    comm = "<h2>Metals, energy and the dollar</h2>" + simple_table(
        COMMODITIES, quotes, "Contract")
    glob = ("<h2>Global markets</h2>" + simple_table(GLOBAL, quotes, "Index")
            + "<p class='small'>Asia and Europe are closed during US hours, "
              "so these reflect their most recent completed session.</p>")

    heat = "<h2>Heat map</h2><img src='cid:heatmap'>"
    charts = ("<h2>S&amp;P 500 intraday</h2><img src='cid:chart'>"
              "<h2>S&amp;P 500 daily</h2><img src='cid:daily'>" + chart_read)

    econ = ("<h2>US economic data today</h2>" + cal_table(cal_today)
            + "<h2>Coming up this week</h2>" + cal_table(cal_ahead, show_day=True))

    return (f"<html><head><meta charset='utf-8'>"
            f"<meta name='color-scheme' content='dark'>"
            f"<meta name='supported-color-schemes' content='dark'>"
            f"<style>{CSS}</style></head>"
            f"<body style='margin:0;padding:0;background:#0d1117'>"
            f"<div class='wrap' style=\"background:#0d1117;color:#e6edf3;padding:18px;"
            f"font-family:-apple-system,Segoe UI,Arial,sans-serif\">"
            f"{header}"
            f"{portfolio_block(port, brief.get('portfolio_note'))}"
            f"{think}"
            f"{news_block(brief.get('news_picks'), news)}"
            f"{idx}{sec}{fng_block(fng)}{heat}{charts}"
            f"{movers_block(movers)}{ma_block(near_ma)}"
            f"{analyst_block(analysts)}{earnings_block(earnings)}"
            f"{crypto}{comm}{glob}{econ}"
            f"<p class='small'>Generated automatically. Prices and analyst data from "
            f"Yahoo Finance, sentiment from CNN, calendar from Forex Factory.</p>"
            f"</div></body></html>")


# ============================== SEND ==============================


def send_email(subject, html, images):
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
    watch = list(HOLDINGS) + [m["sym"] for m in movers]
    analysts = get_analysts(sorted(set(watch))[:20])
    earnings = get_earnings(sorted(set(watch))[:20])

    prev = read_state()
    today_key = dt.datetime.now(MARKET_TZ).date().isoformat()
    prev_today = prev if prev.get("date") == today_key else {}

    payload = summary_payload(quotes, fng, movers, near_ma, cal_today,
                              cal_ahead, news, port, analysts, earnings,
                              prev_today)
    brief, ai_used = ai_brief(payload, [chart, daily], quotes, fng, movers,
                              cal_today, port)

    slot = "Weekend review" if args.weekly else (slot_name() or "Market report")
    html = build_html(slot, quotes, news, cal_today, cal_ahead, fng, movers,
                      near_ma, brief, ai_used, port, analysts, earnings)

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
        print("wrote report.html, heatmap.png, chart.png, daily.png")
        print("ai used:", ai_used)
        print("subject:", subject)
        return

    send_email(subject, html, {"heatmap": heat, "chart": chart,
                               "daily": daily})
    write_state({"date": today_key, "slot": slot,
                 "summary": brief["summary"],
                 "spx": quotes.get("^GSPC", {}).get("last")})
    print("sent:", subject)


if __name__ == "__main__":
    main()
