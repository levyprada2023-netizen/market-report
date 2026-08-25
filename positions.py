"""
Reads a broker positions CSV into holdings the report can use.

Source priority, first one that works wins:
  1. HOLDINGS_CSV_URL environment variable, a link to a published CSV
  2. positions.csv sitting next to the script
  3. the HOLDINGS dictionary in holdings.py

Handles the quirks in a real broker export: dollar signs, thousands commas,
negatives in brackets, closed positions, option contracts, and Canadian
listings that price in CAD.
"""

import csv
import io
import os
import re
import sys

# Column names this understands. Add yours here if your broker differs.
COL_SYMBOL = ("symbol", "ticker", "instrument", "security")
COL_QTY = ("open qty", "quantity", "qty", "shares", "position")
COL_COST = ("avg price", "average price", "avg cost", "cost basis",
            "average cost", "book value per share")
COL_VALUE = ("mkt value", "market value", "value", "position value")

# Option contracts look like PLTR17Jun27P100.00 or SPY14Aug26C777.00
OPTION_RE = re.compile(r"^[A-Z.]{1,6}\d{1,2}[A-Za-z]{3}\d{2}[CP][\d.]+$")

# Suffixes that trade in a currency other than USD
FX_SUFFIX = {".TO": "CAD", ".V": "CAD", ".NE": "CAD", ".CN": "CAD",
             ".L": "GBP", ".AX": "AUD", ".HK": "HKD", ".DE": "EUR",
             ".PA": "EUR", ".AS": "EUR", ".SW": "CHF", ".T": "JPY"}


def _num(text):
    """'$(1,234.56)' becomes -1234.56, '--' becomes None."""
    if text is None:
        return None
    t = str(text).strip()
    if t in ("", "--", "-", "n/a", "N/A"):
        return None
    neg = t.startswith("(") or (t.startswith("$(") or t.endswith(")"))
    t = re.sub(r"[^\d.\-]", "", t)
    if t in ("", "-", "."):
        return None
    try:
        v = float(t)
    except ValueError:
        return None
    return -v if neg and v > 0 else v


def _pick(header, options):
    low = [h.strip().strip('"').lower() for h in header]
    for want in options:
        if want in low:
            return low.index(want)
    for i, h in enumerate(low):
        if any(h.startswith(w) for w in options):
            return i
    return None


def currency_of(symbol):
    for suf, cur in FX_SUFFIX.items():
        if symbol.upper().endswith(suf):
            return cur
    return "USD"


def parse_csv(text):
    """Returns (holdings, book_cost, options, skipped)."""
    rows = list(csv.reader(io.StringIO(text)))
    rows = [r for r in rows if any(c.strip() for c in r)]
    if not rows:
        return {}, {}, [], []

    header = rows[0]
    i_sym = _pick(header, COL_SYMBOL)
    i_qty = _pick(header, COL_QTY)
    i_cost = _pick(header, COL_COST)
    i_val = _pick(header, COL_VALUE)

    if i_sym is None or i_qty is None:
        raise ValueError(
            "Could not find a symbol column and a quantity column. "
            f"Header seen: {header}")

    holdings, book, options, skipped = {}, {}, [], []

    for r in rows[1:]:
        if len(r) <= max(i_sym, i_qty):
            continue
        sym = r[i_sym].strip().strip('"').upper()
        if not sym or sym.lower() in ("total", "totals", "cash"):
            continue

        qty = _num(r[i_qty])
        if not qty:
            skipped.append(sym)          # closed out, nothing open
            continue

        if OPTION_RE.match(sym):
            options.append({
                "symbol": sym,
                "qty": qty,
                "value": _num(r[i_val]) if i_val is not None else None,
            })
            continue

        holdings[sym] = holdings.get(sym, 0) + qty
        if i_cost is not None:
            c = _num(r[i_cost])
            if c:
                book[sym] = c

    return holdings, book, options, skipped


def normalize_url(url):
    """Turn a pasted share link into a direct CSV download link.

    Handles the three forms people actually paste:
      drive.google.com/file/d/<id>/view          a file in Drive
      docs.google.com/spreadsheets/d/<id>/edit   a live Sheet
      .../pub?output=csv                         already published, left alone
    """
    u = url.strip()

    m = re.search(r"drive\.google\.com/file/d/([\w-]+)", u)
    if m:
        return f"https://drive.google.com/uc?export=download&id={m.group(1)}"

    m = re.search(r"drive\.google\.com/open\?id=([\w-]+)", u)
    if m:
        return f"https://drive.google.com/uc?export=download&id={m.group(1)}"

    if "docs.google.com/spreadsheets" in u and "output=csv" not in u \
            and "format=csv" not in u:
        m = re.search(r"/spreadsheets/d/([\w-]+)", u)
        if m:
            gid = re.search(r"[#&]gid=(\d+)", u)
            tail = f"&gid={gid.group(1)}" if gid else ""
            return (f"https://docs.google.com/spreadsheets/d/{m.group(1)}"
                    f"/export?format=csv{tail}")

    if "dropbox.com" in u:
        return u.replace("?dl=0", "?dl=1").replace("&dl=0", "&dl=1")

    return u


def load_positions():
    """Try each source in turn. Returns a dict describing what was found."""
    url = os.environ.get("HOLDINGS_CSV_URL", "").strip()
    if url:
        try:
            import requests
            direct = normalize_url(url)
            r = requests.get(direct, timeout=30, allow_redirects=True,
                             headers={"User-Agent": "Mozilla/5.0"})
            r.raise_for_status()
            body = r.text
            if "<html" in body[:400].lower():
                raise ValueError(
                    "That link returned a web page rather than a CSV. Check "
                    "the file is shared as Anyone with the link, or in Google "
                    "Sheets use File, Share, Publish to web, comma separated "
                    "values.")
            h, b, o, s = parse_csv(body)
            if h:
                return {"holdings": h, "book": b, "options": o,
                        "skipped": s, "source": "shared CSV link"}
            print("CSV link parsed but held no open positions", file=sys.stderr)
        except Exception as e:
            print(f"CSV link failed, falling back: {e}", file=sys.stderr)

    if os.path.exists("positions.csv"):
        try:
            with open("positions.csv", encoding="utf-8-sig") as f:
                h, b, o, s = parse_csv(f.read())
            if h:
                return {"holdings": h, "book": b, "options": o,
                        "skipped": s, "source": "positions.csv"}
        except Exception as e:
            print(f"positions.csv failed: {e}", file=sys.stderr)

    try:
        from holdings import HOLDINGS, BOOK_COST
        if HOLDINGS:
            return {"holdings": dict(HOLDINGS), "book": dict(BOOK_COST),
                    "options": [], "skipped": [], "source": "holdings.py"}
    except Exception:
        pass

    return {"holdings": {}, "book": {}, "options": [], "skipped": [],
            "source": "none"}


if __name__ == "__main__":
    import json
    path = sys.argv[1] if len(sys.argv) > 1 else "positions.csv"
    with open(path, encoding="utf-8-sig") as f:
        h, b, o, s = parse_csv(f.read())
    print(json.dumps({"holdings": h, "book": b, "options": o,
                      "skipped": s}, indent=1))
