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
import datetime as dt
import io
import os
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
MAIL_TO = "youraddress@gmail.com"            # where the report goes

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
    "QQQ": "Nasdaq 100 (QQQ)",
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

MEGACAPS = {
    "AAPL": "AAPL", "MSFT": "MSFT", "NVDA": "NVDA", "GOOGL": "GOOGL",
    "AMZN": "AMZN", "META": "META", "AVGO": "AVGO", "TSLA": "TSLA",
    "LLY": "LLY", "COST": "COST", "JPM": "JPM", "XOM": "XOM",
    "WMT": "WMT", "MU": "MU", "AMD": "AMD",
}

CHART_SYMBOL = "^GSPC"
INTRADAY_INTERVAL = "5m"   # "5m" or "15m"
INTRADAY_DAYS = 2          # 2 gives yesterday for context in the morning report
NEWS_FEED = "https://finance.yahoo.com/news/rssindex"
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


def get_calendar():
    """US economic events for today, medium and high impact."""
    try:
        r = requests.get(CALENDAR_URL, timeout=20,
                         headers={"User-Agent": "Mozilla/5.0"})
        data = r.json()
    except Exception as e:
        print(f"calendar failed: {e}", file=sys.stderr)
        return []

    today = dt.datetime.now(LOCAL_TZ).date()
    rows = []
    for ev in data:
        if ev.get("country") != "USD":
            continue
        if ev.get("impact") not in ("High", "Medium"):
            continue
        try:
            when = dt.datetime.fromisoformat(ev["date"]).astimezone(LOCAL_TZ)
        except Exception:
            continue
        if when.date() != today:
            continue
        rows.append({
            "time": when.strftime("%-I:%M %p") if os.name != "nt" else when.strftime("%#I:%M %p"),
            "title": ev.get("title", ""),
            "impact": ev.get("impact", ""),
            "actual": ev.get("actual") or "",
            "forecast": ev.get("forecast") or "",
            "previous": ev.get("previous") or "",
            "past": when <= dt.datetime.now(LOCAL_TZ),
        })
    rows.sort(key=lambda x: x["title"])
    return rows

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
body{background:#0d1117;color:#e6edf3;font-family:-apple-system,Segoe UI,Arial,sans-serif;
     margin:0;padding:18px;}
h2{font-size:16px;margin:26px 0 8px;color:#e6edf3;border-bottom:1px solid #30363d;padding-bottom:6px;}
table{border-collapse:collapse;width:100%;font-size:14px;}
td,th{padding:7px 8px;text-align:left;border-bottom:1px solid #21262d;}
th{color:#8b949e;font-weight:600;font-size:12px;text-transform:uppercase;}
.num{text-align:right;font-variant-numeric:tabular-nums;}
.up{color:#3fb950;font-weight:600;}
.dn{color:#f85149;font-weight:600;}
.flat{color:#8b949e;}
img{width:100%;border-radius:8px;margin-top:6px;}
a{color:#79c0ff;text-decoration:none;}
.small{color:#8b949e;font-size:12px;}
.hdr{font-size:20px;font-weight:700;}
.pill{display:inline-block;padding:2px 8px;border-radius:10px;font-size:11px;}
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


def build_html(slot, quotes, sector_q, news, cal):
    now = dt.datetime.now(LOCAL_TZ)
    header = f"<div class='hdr'>{slot}</div><div class='small'>{now.strftime('%A %B %d, %Y at %I:%M %p')} MT</div>"

    idx = ("<h2>Index and rates</h2><table>"
           "<tr><th>Market</th><th class='num'>Last</th>"
           "<th class='num'>vs prev close</th><th class='num'>vs open</th></tr>"
           + quote_rows(INDEXES, quotes) + "</table>")

    sec_sorted = sorted(SECTORS.items(),
                        key=lambda kv: quotes.get(kv[0], {}).get("pct", 0),
                        reverse=True)
    sec_rows = "".join(
        f"<tr><td>{lab}</td><td class='num'>{quotes[s]['last']:,.2f}</td>"
        f"<td class='num {cls(quotes[s]['pct'])}'>{quotes[s]['pct']:+.2f}%</td></tr>"
        for s, lab in sec_sorted if s in quotes)
    sec = ("<h2>Sectors, best to worst</h2><table>"
           "<tr><th>Sector</th><th class='num'>Last</th><th class='num'>Change</th></tr>"
           + sec_rows + "</table>")

    heat = "<h2>Heat map</h2><img src='cid:heatmap'>"
    chart = ("<h2>S&amp;P 500 intraday</h2><img src='cid:chart'>"
             "<h2>S&amp;P 500 daily</h2><img src='cid:daily'>")

    if cal:
        rows = "".join(
            f"<tr><td>{c['time']}</td><td>{c['title']}"
            f"{' <span class=small>(' + c['impact'] + ')</span>' if c['impact'] else ''}</td>"
            f"<td class='num'>{c['actual'] or '-'}</td>"
            f"<td class='num'>{c['forecast'] or '-'}</td>"
            f"<td class='num'>{c['previous'] or '-'}</td></tr>" for c in cal)
        econ = ("<h2>US economic data today</h2><table>"
                "<tr><th>Time MT</th><th>Event</th><th class='num'>Actual</th>"
                "<th class='num'>Forecast</th><th class='num'>Prior</th></tr>"
                + rows + "</table>")
    else:
        econ = "<h2>US economic data today</h2><p class='small'>Nothing scheduled at medium or high impact.</p>"

    news_html = "<h2>Yahoo Finance headlines</h2><table>" + "".join(
        f"<tr><td><a href='{n['link']}'>{n['title']}</a></td></tr>" for n in news
    ) + "</table>"

    return (f"<html><head><meta charset='utf-8'><style>{CSS}</style></head><body>"
            f"{header}{idx}{sec}{heat}{chart}{econ}{news_html}"
            f"<p class='small'>Generated automatically. Data from Yahoo Finance.</p>"
            f"</body></html>")

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
    args = ap.parse_args()

    if not (args.preview or args.force):
        if slot_name() is None:
            print("no report due right now, exiting")
            return
        if not market_traded_today():
            print("market closed today, exiting")
            return

    symbols = list(INDEXES) + list(SECTORS) + list(MEGACAPS)
    quotes = get_quotes(symbols)

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
    news = get_news()
    cal = get_calendar()

    slot = slot_name() or "Market report"
    html = build_html(slot, quotes, sector_items, news, cal)

    spx = quotes.get("^GSPC", {}).get("pct", 0)
    qqq = quotes.get("QQQ", {}).get("pct", 0)
    subject = f"{slot}: SPX {spx:+.2f}%, QQQ {qqq:+.2f}%"

    if args.preview:
        with open("report.html", "w", encoding="utf-8") as f:
            f.write(html.replace("cid:heatmap", "heatmap.png")
                        .replace("cid:chart", "chart.png")
                        .replace("cid:daily", "daily.png"))
        open("heatmap.png", "wb").write(heat)
        open("chart.png", "wb").write(chart)
        open("daily.png", "wb").write(daily)
        print("wrote report.html, heatmap.png, chart.png, daily.png")
        print("subject:", subject)
        return

    send_email(subject, html, {"heatmap": heat, "chart": chart,
                               "daily": daily})
    print("sent:", subject)


if __name__ == "__main__":
    main()
