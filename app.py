#!/usr/bin/env python3
"""
Jakob's Money: a simple, private net worth and allocation tracker.

- Balances from Kiwibank, Sharesies and KiwiSaver (through Akahu) and Swyftx crypto.
- Anything that can't sync, such as IRD items (student loan, tax owed or refunds),
  property or money owed to you, is added by hand.
- Saves a daily snapshot so you can see net worth and allocation over time.
- Everything stays on this Mac in finance.db. It only connects out to Akahu and Swyftx.

Standard library only, works with the python3 that ships with macOS (3.9+).
Run:  python3 app.py            (real data, needs config.json)
      python3 app.py --demo     (fake data to try it out)
"""
import base64
import io
import json
import os
import statistics
import zipfile
import xml.etree.ElementTree as ET
import random
import re
import sqlite3
import subprocess
import sys
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import webbrowser
from datetime import date, datetime, timedelta, timezone
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer


HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)      # the Python bundled on Windows doesn't look in the script's folder by itself
CONFIG_PATH = os.path.join(HERE, "config.json")
STATIC_DIR = os.path.join(HERE, "static")
import cloud   # noqa: E402  seeing it away from home; does nothing until that has been set up

AKAHU = os.environ.get("JM_AKAHU_API", "https://api.akahu.io/v1")
SWYFTX = "https://api.swyftx.com.au"
HOST = "127.0.0.1"
APP_VERSION = "16"  # keep in step with UI_VERSION in static/index.html
UA = "jakobs-money-local/2.0"

DEMO = "--demo" in sys.argv
NO_BROWSER = "--no-browser" in sys.argv
DB_PATH = os.path.join(HERE, "demo.db" if DEMO else "finance.db")
DEFAULT_CONFIG = {"sync_every_minutes": 15, "port": 8765}

# Asset classes, in display order. Colours live in the UI and follow the class, never its rank.
CLASSES = [
    ("cash", "Cash"),
    ("shares", "Shares & funds"),
    ("crypto", "Crypto"),
    ("kiwisaver", "KiwiSaver"),
    ("property", "Property & other"),
    ("debt", "Debts"),
]
CLASS_KEYS = [c for c, _ in CLASSES]
CLASS_NAME = dict(CLASSES)
LIQUID = {"cash", "shares", "crypto"}

_lock = threading.RLock()
_sync = {"running": False, "last_error": None}
_cloud = {"error": None, "pushed": None, "timer": None, "state_at": 0.0, "pull_at": 0.0}


# ---------------------------------------------------------------- config / db
def load_config():
    cfg = dict(DEFAULT_CONFIG)
    if os.path.exists(CONFIG_PATH):
        with open(CONFIG_PATH) as f:
            cfg.update(json.load(f))
    cfg["app_token"] = os.environ.get("AKAHU_APP_TOKEN", cfg.get("app_token", ""))
    cfg["user_token"] = os.environ.get("AKAHU_USER_TOKEN", cfg.get("user_token", ""))
    cfg["swyftx_api_key"] = os.environ.get("SWYFTX_API_KEY", cfg.get("swyftx_api_key", ""))
    for k in ("app_token", "user_token", "swyftx_api_key"):
        if "PASTE" in (cfg[k] or ""):
            cfg[k] = ""
    return cfg


def db():
    con = sqlite3.connect(DB_PATH, check_same_thread=False)
    con.row_factory = sqlite3.Row
    return con


def init_db():
    con = db()
    con.executescript("""
    CREATE TABLE IF NOT EXISTS accounts (
        id TEXT PRIMARY KEY, name TEXT, bank TEXT, type TEXT,
        balance REAL, available REAL, in_forecast INTEGER DEFAULT 0, updated TEXT);
    CREATE TABLE IF NOT EXISTS holdings (
        account_id TEXT, code TEXT, name TEXT, amount REAL, price REAL, value REAL,
        change24h REAL, updated TEXT, PRIMARY KEY (account_id, code));
    CREATE TABLE IF NOT EXISTS snapshots (
        date TEXT, account_id TEXT, value REAL, PRIMARY KEY (date, account_id));
    CREATE TABLE IF NOT EXISTS manual (
        id INTEGER PRIMARY KEY AUTOINCREMENT, name TEXT, cls TEXT, value REAL,
        note TEXT, updated TEXT);
    CREATE TABLE IF NOT EXISTS meta (key TEXT PRIMARY KEY, value TEXT);
    CREATE TABLE IF NOT EXISTS holding_days (
        date TEXT, account_id TEXT, code TEXT, amount REAL, price REAL, est INTEGER DEFAULT 0,
        PRIMARY KEY (date, account_id, code));
    CREATE TABLE IF NOT EXISTS account_meta (account_id TEXT PRIMARY KEY, breakdown TEXT, portfolio TEXT, updated TEXT);
    """)
    cols = [r[1] for r in con.execute("PRAGMA table_info(accounts)")]
    for col, decl in (("cls_override", "TEXT"), ("hidden", "INTEGER DEFAULT 0"), ("status", "TEXT")):
        if col not in cols:
            con.execute("ALTER TABLE accounts ADD COLUMN %s %s" % (col, decl))
    mcols = [r[1] for r in con.execute("PRAGMA table_info(manual)")]
    for col, decl in (("sched_amount", "REAL"), ("sched_every", "TEXT"), ("sched_next", "TEXT")):
        if col not in mcols:
            con.execute("ALTER TABLE manual ADD COLUMN %s %s" % (col, decl))
    if "est" not in [r[1] for r in con.execute("PRAGMA table_info(snapshots)")]:
        con.execute("ALTER TABLE snapshots ADD COLUMN est INTEGER DEFAULT 0")
    con.commit()
    return con


def meta_get(con, key, default=None):
    r = con.execute("SELECT value FROM meta WHERE key=?", (key,)).fetchone()
    return r[0] if r else default


def meta_set(con, key, value):
    con.execute("INSERT OR REPLACE INTO meta(key, value) VALUES (?,?)", (key, value))


def now_iso():
    return datetime.now(timezone.utc).isoformat()


# ---------------------------------------------------------------- classes
def auto_class(type_, name="", balance=0.0):
    t = (type_ or "").upper()
    n = (name or "").lower()
    if t == "CRYPTO" or "crypto" in n:
        return "crypto"
    if t == "KIWISAVER" or "kiwisaver" in n:
        return "kiwisaver"
    if t in ("INVESTMENT",):
        return "shares"
    if t in ("CREDITCARD", "LOAN"):
        return "debt"
    if t == "TAX":
        return "debt" if (balance or 0) < 0 else "cash"
    return "cash"  # CHECKING, SAVINGS, TERMDEPOSIT, WALLET, FOREIGN, REWARDS


def account_cls(a):
    return a["cls_override"] if a["cls_override"] in CLASS_KEYS else auto_class(a["type"], a["name"], a["balance"])


EVERY = {"weekly": 7, "fortnightly": 14}


def step(d, every):
    if every in EVERY:
        return d + timedelta(days=EVERY[every])
    y, mth = d.year + (d.month == 12), d.month % 12 + 1  # monthly
    for day in (d.day, 30, 29, 28):
        try:
            return date(y, mth, day)
        except ValueError:
            continue


def sched_dates(m, after, until):
    """Dates a scheduled change happens, strictly after `after` and up to `until`."""
    if not m["sched_amount"] or m["sched_every"] not in ("weekly", "fortnightly", "monthly") or not m["sched_next"]:
        return []
    try:
        d = date.fromisoformat(m["sched_next"])
    except ValueError:
        return []
    out = []
    while d <= until and len(out) < 5000:
        if d > after:
            out.append(d)
        d = step(d, m["sched_every"])
    return out


def manual_amount(m, on=None):
    """The amount today (or on a given date): the value you entered, plus any scheduled
    changes since you entered it. Debts stop at zero."""
    base = abs(m["value"] or 0)
    try:
        since = date.fromisoformat((m["updated"] or "")[:10])
    except ValueError:
        since = date.today()
    n = len(sched_dates(m, since, on or date.today()))
    return max(0.0, base + (m["sched_amount"] or 0) * n)


def manual_value(m, on=None):
    """Debts are stored as positive amounts owed and count negative in net worth."""
    v = manual_amount(m, on)
    return -v if m["cls"] == "debt" else v


# ---------------------------------------------------------------- HTTP helpers
def http_json(url, method="GET", body=None, headers=None, timeout=30):
    h = {"Accept": "application/json", "User-Agent": UA}
    h.update(headers or {})
    data = None
    if body is not None:
        data = json.dumps(body).encode()
        h["Content-Type"] = "application/json"
    req = urllib.request.Request(url, data=data, method=method, headers=h)
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        return json.loads(resp.read().decode())


def num(x):
    try:
        return float(x)
    except (TypeError, ValueError):
        return 0.0


# ---------------------------------------------------------------- Akahu
def parse_portfolio(meta):
    """Akahu passes portfolio details through from each provider, so the shape varies.
    Pull out whatever holdings we can recognise; return [] if nothing fits."""
    p = (meta or {}).get("portfolio")
    if isinstance(p, dict):
        for key in ("holdings", "assets", "funds", "instruments", "items"):
            if isinstance(p.get(key), list):
                p = p[key]
                break
    if not isinstance(p, list):
        return []
    out = []
    for h in p[:200]:
        if not isinstance(h, dict):
            continue
        name = h.get("name") or h.get("fund_name") or h.get("description") or h.get("code") or h.get("symbol")
        code = h.get("code") or h.get("symbol") or h.get("ticker") or name
        val = h.get("value")
        if isinstance(val, dict):
            val = val.get("amount") or val.get("current")
        if val is None:
            val = h.get("market_value") or h.get("amount") or h.get("balance")
        if not name or num(val) == 0:
            continue
        amount = num(h.get("quantity") or h.get("units") or h.get("shares"))
        price = num(h.get("price") or h.get("unit_price") or h.get("share_price"))
        if not price and amount > 0:
            price = num(val) / amount
        out.append({"code": str(code)[:24], "name": str(name)[:80], "amount": amount, "price": price, "value": num(val)})
    return out


def sync_akahu(cfg):
    hdr = {"Authorization": "Bearer " + cfg["user_token"], "X-Akahu-Id": cfg["app_token"]}
    try:
        http_json(AKAHU + "/refresh", "POST", {}, hdr)  # rate-limited for personal apps; fine if refused
    except Exception:
        pass
    items = http_json(AKAHU + "/accounts", headers=hdr).get("items", [])
    con = db()
    try:
        ts = now_iso()
        for a in items:
            bal = a.get("balance") or {}
            refreshed = (a.get("refreshed") or {}).get("balance") or ts
            con.execute("""INSERT INTO accounts(id,name,bank,type,balance,available,updated,status)
                           VALUES (?,?,?,?,?,?,?,?)
                           ON CONFLICT(id) DO UPDATE SET name=excluded.name, bank=excluded.bank, type=excluded.type,
                             balance=excluded.balance, available=excluded.available, updated=excluded.updated,
                             status=excluded.status""",
                        (a["_id"], a.get("name"), (a.get("connection") or {}).get("name"), a.get("type"),
                         num(bal.get("current")), num(bal.get("available")), refreshed, a.get("status")))
            m = a.get("meta") or {}
            if m.get("breakdown") is not None or m.get("portfolio") is not None:   # kept as sent, so more can be made of it later
                con.execute("INSERT OR REPLACE INTO account_meta VALUES (?,?,?,?)",
                            (a["_id"], json.dumps(m.get("breakdown"))[:20000], json.dumps(m.get("portfolio"))[:60000], ts))
            hold = parse_portfolio(a.get("meta"))
            if hold:
                con.execute("DELETE FROM holdings WHERE account_id=?", (a["_id"],))
                con.executemany("INSERT OR REPLACE INTO holdings VALUES (?,?,?,?,?,?,?,?)",
                                [(a["_id"], h["code"], h["name"], h["amount"], h["price"], h["value"], None, ts) for h in hold])
        con.commit()
    finally:
        con.close()
    return {"accounts": len(items)}


# ---------------------------------------------------------------- Swyftx
def swyftx_prices(by_code, base_code):
    base = by_code.get(base_code)
    if not base:
        return None
    raw = http_json("%s/live-rates/%s/" % (SWYFTX, base["id"]))
    if isinstance(raw, list):
        raw = {str(r.get("assetId") or r.get("id")): r for r in raw}
    prices = {}
    for k, r in (raw or {}).items():
        if not isinstance(r, dict):
            continue
        mid = num(r.get("midPrice")) or (num(r.get("askPrice")) + num(r.get("bidPrice"))) / 2
        if mid > 0:
            prices[str(k)] = (mid, num(r.get("dailyPriceChange")))
    btc = by_code.get("BTC")
    if btc and str(btc["id"]) in prices and prices[str(btc["id"])][0] < 1:  # rates came back inverted
        prices = {k: (1 / v[0], v[1]) for k, v in prices.items()}
    return prices or None


def usd_to_nzd(cfg, by_code, usd_prices):
    nzd = by_code.get("NZD")
    if nzd and usd_prices and str(nzd["id"]) in usd_prices:
        return 1 / usd_prices[str(nzd["id"])][0]
    for url in ("https://api.frankfurter.dev/v1/latest?base=USD&symbols=NZD",
                "https://api.frankfurter.app/latest?from=USD&to=NZD"):
        try:
            return num(http_json(url)["rates"]["NZD"])
        except Exception:
            continue
    return num(cfg.get("usd_nzd_fallback", 1.7))


def sync_swyftx(cfg):
    token = http_json(SWYFTX + "/auth/refresh/", "POST", {"apiKey": cfg["swyftx_api_key"]}).get("accessToken")
    if not token:
        raise RuntimeError("Swyftx didn't accept the API key")
    balances = http_json(SWYFTX + "/user/balance/", headers={"Authorization": "Bearer " + token})
    assets = http_json(SWYFTX + "/markets/assets/")
    by_id = {str(a.get("id")): a for a in assets}
    by_code = {(a.get("code") or "").upper(): a for a in assets}
    try:
        prices, fx = swyftx_prices(by_code, "NZD"), 1.0
    except Exception:
        prices = None
    if not prices:
        prices = swyftx_prices(by_code, "USD") or {}
        fx = usd_to_nzd(cfg, by_code, prices)
    rows, total = [], 0.0
    for b in balances or []:
        aid = str(b.get("assetId"))
        amount = num(b.get("availableBalance")) + num(b.get("stakingBalance"))
        if amount <= 0:
            continue
        a = by_id.get(aid, {})
        code = (a.get("code") or aid).upper()
        if code == "NZD":
            price, ch = 1.0, 0.0
        elif code == "USD":
            price, ch = fx, 0.0
        else:
            p = prices.get(aid)
            price, ch = ((p[0] * fx), p[1]) if p else (0.0, 0.0)
        value = amount * price
        if value < 0.01 and code != "NZD":
            continue
        total += value
        rows.append((code, a.get("name") or code, amount, price, value, ch))
    con = db()
    try:
        ts = now_iso()
        con.execute("""INSERT INTO accounts(id,name,bank,type,balance,available,updated,status)
                       VALUES ('swyftx','Swyftx','Swyftx','CRYPTO',?,?,?,'ACTIVE')
                       ON CONFLICT(id) DO UPDATE SET balance=excluded.balance, available=excluded.available,
                         updated=excluded.updated""", (round(total, 2), round(total, 2), ts))
        con.execute("DELETE FROM holdings WHERE account_id='swyftx'")
        con.executemany("INSERT INTO holdings VALUES ('swyftx',?,?,?,?,?,?,?)", [r + (ts,) for r in rows])
        con.commit()
    finally:
        con.close()
    return {"holdings": len(rows), "value_nzd": round(total, 2)}


# ---------------------------------------------------------------- snapshots / sync
def record_snapshot(con):
    today = date.today().isoformat()
    for a in con.execute("SELECT id, balance FROM accounts WHERE ifnull(hidden,0)=0"):
        con.execute("INSERT OR REPLACE INTO snapshots(date, account_id, value, est) VALUES (?,?,?,0)", (today, a["id"], a["balance"] or 0))
    for m in con.execute("SELECT * FROM manual"):
        con.execute("INSERT OR REPLACE INTO snapshots(date, account_id, value, est) VALUES (?,?,?,0)", (today, "manual:%d" % m["id"], manual_value(m)))
    record_prices(con, today)
    con.commit()


def record_prices(con, today):
    """One line per holding per day: how many units and what one was worth. This is what lets the
    app tell a gain from prices apart from money you added."""
    yesterday = (date.fromisoformat(today) - timedelta(days=1)).isoformat()
    for h in con.execute("SELECT h.* FROM holdings h JOIN accounts a ON a.id=h.account_id WHERE ifnull(a.hidden,0)=0").fetchall():
        amount = h["amount"] or 0
        price = h["price"] or ((h["value"] or 0) / amount if amount > 0 else 0)
        if amount <= 0 or price <= 0:
            continue
        key = (h["account_id"], h["code"])
        seen = con.execute("SELECT 1 FROM holding_days WHERE account_id=? AND code=? AND date<? LIMIT 1", key + (today,)).fetchone()
        ch = h["change24h"]
        if not seen and ch is not None and ch > -99:      # first sight: the provider's own 24-hour change gives yesterday's price
            con.execute("INSERT OR IGNORE INTO holding_days(date, account_id, code, amount, price, est) VALUES (?,?,?,?,?,1)",
                        (yesterday,) + key + (amount, price / (1 + ch / 100.0)))
        con.execute("INSERT OR REPLACE INTO holding_days(date, account_id, code, amount, price, est) VALUES (?,?,?,?,?,0)",
                    (today,) + key + (amount, price))


# ---------------------------------------------------------------- rebuilding past history
def fetch_akahu_transactions(cfg, days=365):
    """One-off download used only to rebuild history. Nothing is stored."""
    hdr = {"Authorization": "Bearer " + cfg["user_token"], "X-Akahu-Id": cfg["app_token"]}
    start = (datetime.now(timezone.utc) - timedelta(days=days)).strftime("%Y-%m-%dT00:00:00.000Z")
    params, out = {"start": start}, []
    for _ in range(300):
        page = http_json(AKAHU + "/transactions?" + urllib.parse.urlencode(params), headers=hdr)
        for t in page.get("items", []):
            out.append({"id": t.get("_id"), "account_id": t.get("_account"), "date": local_date(t.get("date")),
                        "amount": num(t.get("amount")), "description": " ".join(
                            x for x in (t.get("description"), (t.get("merchant") or {}).get("name")) if x)})
        nxt = (page.get("cursor") or {}).get("next")
        if not nxt or not page.get("items"):
            break
        params = {"start": start, "cursor": nxt}
    return out


def local_date(iso):
    try:
        dt = datetime.fromisoformat((iso or "").replace("Z", "+00:00"))
        return (dt.astimezone() if dt.tzinfo else dt).date().isoformat()
    except ValueError:
        return (iso or "")[:10]


def stored_transactions(con):
    """Transactions left in finance.db by the previous version of the app, if any."""
    if not con.execute("SELECT name FROM sqlite_master WHERE name='transactions'").fetchone():
        return []
    return [{"id": r["id"], "account_id": r["account_id"], "date": r["date"], "amount": r["amount"] or 0,
             "description": " ".join(x for x in (r["description"], r["merchant"]) if x)}
            for r in con.execute("SELECT * FROM transactions WHERE ifnull(pending,0)=0")]


# Words that identify money going to each investment platform in your bank transactions.
PLATFORM_WORDS = {"swyftx": ["swyftx", "easy crypto", "easycrypto"], "sharesies": ["sharesies"],
                  "hatch": ["hatch"], "kernel": ["kernel"], "simplicity": ["simplicity"], "stake": ["stake"]}


def rebuild_history(days=365):
    """Fill in daily net worth before the app's first real snapshot.

    Bank accounts: exact, today's balance minus every transaction since.
    Investment platforms: estimated, today's value minus money you've sent there since
      (plus money you took out). Market ups and downs before today aren't known.
    KiwiSaver and items you added by hand: held at today's value (estimate)."""
    txns = {}
    cfg = load_config()
    fetched = 0
    if not DEMO and cfg["app_token"] and cfg["user_token"]:
        try:
            for t in fetch_akahu_transactions(cfg, days):
                txns[t["id"] or (t["account_id"], t["date"], t["amount"], t["description"])] = t
            fetched = len(txns)
        except Exception as e:
            fetched = "failed (%s)" % e
    con = db()
    try:
        for t in stored_transactions(con):
            txns.setdefault(t["id"], t)
        accts = [dict(a) for a in con.execute("SELECT * FROM accounts")]
        first_real = con.execute("SELECT MIN(date) FROM snapshots WHERE ifnull(est,0)=0").fetchone()[0] or date.today().isoformat()
        end = date.fromisoformat(first_real) - timedelta(days=1)
        start = date.today() - timedelta(days=days)
        if end < start:
            return {"ok": True, "days_added": 0, "note": "History already goes back a year."}
        by_acct = {}
        for t in txns.values():
            by_acct.setdefault(t["account_id"], []).append(t)

        # Value of each account at the end of the first real snapshot day (our anchor).
        anchor = {r["account_id"]: r["value"] for r in con.execute(
            "SELECT account_id, value FROM snapshots WHERE date=?", (first_real,))}
        cash_ids = [a["id"] for a in accts if account_cls(a) in ("cash", "debt") and a["id"] != "swyftx"
                    and (a["bank"] or "").lower() not in PLATFORM_WORDS]
        groups = {}  # platform -> its accounts
        for a in accts:
            key = (a["bank"] or a["name"] or "").lower()
            if key in PLATFORM_WORDS or account_cls(a) in ("shares", "crypto"):
                groups.setdefault(key, []).append(a)

        # Money into / out of each platform, seen from your bank accounts.
        flows = {g: [] for g in groups}
        for aid in cash_ids:
            for t in by_acct.get(aid, []):
                d = t["description"].lower()
                for g in groups:
                    if any(w in d for w in PLATFORM_WORDS.get(g, [g])):
                        flows[g].append((t["date"], -t["amount"]))  # bank outflow = money into platform
                        break

        rows = []
        day = start
        while day <= end:
            ds = day.isoformat()
            for aid in cash_ids:
                if aid not in anchor:
                    continue
                later = sum(t["amount"] for t in by_acct.get(aid, []) if ds < t["date"] <= first_real)
                rows.append((ds, aid, round(anchor[aid] - later, 2)))
            for g, members in groups.items():
                now_total = sum(anchor.get(a["id"], a["balance"] or 0) for a in members)
                net_in_since = sum(v for d, v in flows[g] if ds < d <= first_real)
                est_total = max(0.0, now_total - net_in_since)
                for a in members:
                    share = (anchor.get(a["id"], a["balance"] or 0) / now_total) if now_total else 0
                    rows.append((ds, a["id"], round(est_total * share, 2)))
            for a in accts:  # KiwiSaver and anything else without flows: hold flat
                if a["id"] in cash_ids or any(a in m for m in groups.values()) or a["id"] not in anchor:
                    continue
                rows.append((ds, a["id"], anchor[a["id"]]))
            for k, v in anchor.items():
                if k.startswith("manual:"):
                    rows.append((ds, k, v))
            day += timedelta(days=1)
        con.execute("DELETE FROM snapshots WHERE est=1")
        con.executemany("INSERT OR IGNORE INTO snapshots(date, account_id, value, est) VALUES (?,?,?,1)", rows)
        meta_set(con, "history_rebuilt", now_iso())
        con.commit()
        return {"ok": True, "days_added": (end - start).days + 1, "transactions_used": len(txns),
                "fetched_from_akahu": fetched, "from": start.isoformat(), "to": end.isoformat()}
    finally:
        con.close()


def describe_error(source, e):
    if isinstance(e, urllib.error.HTTPError):
        msg = "%s said %s %s" % (source, e.code, e.reason)
        if e.code in (401, 403):
            msg += " (check the key/tokens in config.json)"
        return msg
    return "%s: %s" % (source, e)


def run_sync():
    with _lock:
        if _sync["running"]:
            return {"ok": False, "error": "Sync already running"}
        _sync["running"] = True
    try:
        result, errors = {}, []
        if not DEMO:
            cfg = load_config()
            has_akahu = bool(cfg["app_token"] and cfg["user_token"])
            has_swyftx = bool(cfg.get("swyftx_api_key"))
            if not has_akahu and not has_swyftx:
                errors.append("No Akahu tokens or Swyftx key yet. Add them to config.json (see README).")
            if has_akahu:
                try:
                    result["akahu"] = sync_akahu(cfg)
                except Exception as e:
                    errors.append(describe_error("Akahu", e))
            if has_swyftx:
                try:
                    result["swyftx"] = sync_swyftx(cfg)
                except Exception as e:
                    errors.append(describe_error("Swyftx", e))
        con = db()
        try:
            record_snapshot(con)
            meta_set(con, "last_sync", now_iso())
            con.commit()
        finally:
            con.close()
        if not DEMO and not errors:
            c2 = db()
            done = meta_get(c2, "history_rebuilt")
            c2.close()
            if not done:
                try:
                    result["history"] = rebuild_history()
                except Exception as e:
                    errors.append("Rebuilding history: %s" % e)
        _sync["last_error"] = "; ".join(errors) or None
        threading.Thread(target=cloud_exchange, daemon=True).start()
        return {"ok": not errors, "result": result, "error": _sync["last_error"]}
    finally:
        _sync["running"] = False


# ---------------------------------------------------------------- away from home (see cloud.py)
def cloud_ready():
    if DEMO and not os.environ.get("JM_GITHUB_API"):
        return None
    cfg = load_config()
    return cfg if cloud.configured(cfg) else None


def cloud_exchange(edited=False):
    """Send the phone exactly what this computer shows, straight away. Now and then (or after an edit) also
    hand the scheduled job a copy of the data, and fill in any days this computer missed from what it recorded."""
    cfg = cloud_ready()
    if not cfg:
        return
    try:
        now = time.time()
        if now - _cloud["pull_at"] > 3600:
            cloud.pull(cfg, DB_PATH)
            _cloud["pull_at"] = now
        if edited or now - _cloud["state_at"] > 3600:
            cloud.push(cfg, DB_PATH)
            _cloud["state_at"] = now
        con = db()
        try:
            bundle = cloud.make_bundle(sys.modules[__name__], con, _sync["last_error"], cfg.get("owner"), "computer")
        finally:
            con.close()
        cloud.publish_live(cfg, bundle)
        _cloud["error"], _cloud["pushed"] = None, now_iso()
    except Exception as e:
        _cloud["error"] = str(e)


def cloud_push_soon():
    """After an edit: wait a moment in case more follow, then send it and refresh the phone page."""
    if not cloud_ready():
        return
    with _lock:
        if _cloud["timer"]:
            _cloud["timer"].cancel()
        t = threading.Timer(3, cloud_exchange, kwargs={"edited": True})
        t.daemon = True
        _cloud["timer"] = t
        t.start()


def sync_loop():
    """Every 15 minutes. Banks only change as often as Akahu checks them, but prices move all day."""
    while True:
        run_sync()
        time.sleep(max(5.0, float(load_config().get("sync_every_minutes", 15))) * 60)


# ---------------------------------------------------------------- analysis
def positions(con):
    """Every account and manual item with its class and value."""
    out = []
    for a in con.execute("SELECT * FROM accounts WHERE ifnull(hidden,0)=0"):
        out.append({"key": a["id"], "source": "sync", "name": a["name"], "institution": a["bank"],
                    "type": (a["type"] or "").lower(), "cls": account_cls(a), "auto_cls": auto_class(a["type"], a["name"], a["balance"]),
                    "value": round(a["balance"] or 0, 2), "updated": a["updated"], "status": a["status"]})
    for m in con.execute("SELECT * FROM manual"):
        out.append({"key": "manual:%d" % m["id"], "id": m["id"], "source": "manual", "name": m["name"],
                    "institution": m["note"] or "", "type": "manual", "cls": m["cls"], "value": round(manual_value(m), 2),
                    "amount": round(manual_amount(m), 2), "updated": m["updated"],
                    "sched": {"amount": m["sched_amount"], "every": m["sched_every"], "next": next_change(m)}
                    if m["sched_amount"] else None})
    return out


def explore(con):
    """Everything the interface needs in one go: each account and item with its
    day-by-day history, so any number can be opened up or wound back in time."""
    today = date.today().isoformat()
    pts, dates = {}, {today}
    for r in con.execute("SELECT * FROM snapshots WHERE date<=? ORDER BY date", (today,)):
        pts.setdefault(r["account_id"], {})[r["date"]] = (r["value"] or 0, 1 if r["est"] == 1 else 0)
        dates.add(r["date"])
    days = {}
    for r in con.execute("SELECT * FROM holding_days WHERE date<=? ORDER BY date", (today,)):
        days.setdefault((r["account_id"], r["code"]), {})[r["date"]] = (r["price"], r["amount"])
        dates.add(r["date"])
    dates = sorted(dates)
    hold = {}
    for h in holdings(con):
        mine, lastp, ps, qs = days.get((h["account_id"], h["code"]), {}), None, [], []
        for d in dates:                       # null until the first day a price was recorded, then carried forward
            lastp = mine.get(d, lastp)
            ps.append(round(lastp[0], 6) if lastp else None)
            qs.append(lastp[1] if lastp else None)
        hold.setdefault(h["account_id"], []).append({
            "code": h["code"], "name": h["name"], "amount": h["amount"], "price": h["price"],
            "value": round(h["value"] or 0, 2), "change24h": h["change24h"], "p": ps if mine else None, "q": qs if mine else None})
    payoffs = {}
    for m in con.execute("SELECT * FROM manual WHERE cls='debt' AND sched_amount < 0"):
        d = payoff(m)
        if d:
            payoffs[m["id"]] = d.isoformat()
    leaves = []
    for p in positions(con):
        mine = pts.get(p["key"], {})
        first = min(mine) if mine else None
        last, vals, est = None, [], []
        for d in dates:
            if d in mine:
                last = mine[d]
                v, e = last
            elif first and d < first:
                v, e = mine[first][0], 1      # before we knew about it: hold flat, mark as estimated
            elif last:
                v, e = last                   # gap between snapshots: carry forward
            else:
                v, e = p["value"], 1
            vals.append(round(v, 2))
            est.append(e)
        vals[-1], est[-1] = p["value"], 0     # today is always the live value
        leaf = dict(p, series=vals, est=est, holdings=hold.get(p["key"], []))
        if p["source"] == "manual":
            leaf["payoff"] = payoffs.get(p["id"])
        leaves.append(leaf)
    hidden = [{"key": a["id"], "name": a["name"]} for a in con.execute("SELECT * FROM accounts WHERE ifnull(hidden,0)=1")]
    return {"today": today, "dates": dates, "leaves": leaves, "hidden": hidden,
            "classes": [{"key": k, "name": n} for k, n in CLASSES]}


def next_change(m):
    ds = sched_dates(m, date.today(), date.today() + timedelta(days=70))
    return ds[0].isoformat() if ds else None


def payoff(m):
    """When a scheduled debt reaches zero at its current rate."""
    owed, per = manual_amount(m), m["sched_amount"] or 0
    if m["cls"] != "debt" or per >= 0 or owed <= 0:
        return None
    n = int(-(-owed // -per))  # ceil(owed / |per|)
    d = date.fromisoformat(next_change(m) or date.today().isoformat())
    for _ in range(max(0, n - 1)):
        d = step(d, m["sched_every"])
    return d


def holdings(con):
    return [dict(h) for h in con.execute(
        "SELECT h.*, a.name AS account FROM holdings h JOIN accounts a ON a.id=h.account_id "
        "WHERE ifnull(a.hidden,0)=0 ORDER BY h.value DESC")]


def history(con, days=None):
    """Net worth per snapshot date, split by class. Accounts use today's class so the past lines up."""
    cls_of = {}
    for a in con.execute("SELECT * FROM accounts"):
        cls_of[a["id"]] = account_cls(a)
    for m in con.execute("SELECT id, cls FROM manual"):
        cls_of["manual:%d" % m["id"]] = m["cls"]
    hidden = {r[0] for r in con.execute("SELECT id FROM accounts WHERE ifnull(hidden,0)=1")}
    q, args = "SELECT * FROM snapshots", ()
    if days:
        q += " WHERE date>=?"
        args = ((date.today() - timedelta(days=days)).isoformat(),)
    # Each account's own timeline. Gaps between snapshots carry the last value forward;
    # days before an account's first snapshot hold its first value and count as estimated.
    series, dates, est = {}, set(), set()
    for r in con.execute(q + " ORDER BY date", args):
        if r["account_id"] in hidden or r["account_id"] not in cls_of:
            continue  # deleted manual items and hidden accounts drop out of history too
        series.setdefault(r["account_id"], {})[r["date"]] = (r["value"] or 0, r["est"] == 1)
        dates.add(r["date"])
    dates = sorted(dates)
    by_date = {d: {k: 0.0 for k in CLASS_KEYS} for d in dates}
    for aid, pts in series.items():
        first = min(pts)
        last = pts[first]
        for d in dates:
            if d in pts:
                last = pts[d]
                v, e = last
            elif d < first:
                v, e = pts[first][0], True
            else:
                v, e = last
            by_date[d][cls_of[aid]] += v
            if e:
                est.add(d)
    out = []
    for d in dates:
        v = by_date[d]
        out.append(dict(date=d, net_worth=round(sum(v.values()), 2), estimated=d in est,
                        **{k: round(x, 2) for k, x in v.items()}))
    return out


def summary(con):
    pos = positions(con)
    by_cls = {k: 0.0 for k in CLASS_KEYS}
    for p in pos:
        by_cls[p["cls"]] += p["value"]
    assets = sum(p["value"] for p in pos if p["value"] > 0)
    debts = -sum(p["value"] for p in pos if p["value"] < 0)
    nw = assets - debts
    gross = sum(v for k, v in by_cls.items() if k != "debt" and v > 0) or 1
    alloc = [{"cls": k, "name": CLASS_NAME[k], "value": round(by_cls[k], 2),
              "pct_of_assets": round(by_cls[k] / gross * 100, 1) if k != "debt" else None}
             for k in CLASS_KEYS if abs(by_cls[k]) >= 0.005]
    hist = history(con)
    hidden = [{"key": a["id"], "name": a["name"], "institution": a["bank"]}
              for a in con.execute("SELECT * FROM accounts WHERE ifnull(hidden,0)=1")]
    return {"net_worth": round(nw, 2), "assets": round(assets, 2), "debts": round(debts, 2), "hidden": hidden,
            "allocation": alloc, "positions": pos, "holdings": holdings(con),
            "changes": changes(hist, nw), "insights": insights(con, pos, by_cls, assets, nw, hist)}


def value_at(hist, days_ago):
    target = (date.today() - timedelta(days=days_ago)).isoformat()
    older = [h for h in hist if h["date"] <= target]
    if older:
        return older[-1]
    # Allow a little slack so a history that started ~a year ago still counts as "1 year".
    if hist and hist[0]["date"] <= (date.today() - timedelta(days=days_ago - 14)).isoformat():
        return hist[0]
    return None


def changes(hist, nw):
    out = {}
    for label, days in (("30d", 30), ("1y", 365)):
        h = value_at(hist, days)
        if h:
            out[label] = {"from": h["net_worth"], "change": round(nw - h["net_worth"], 2), "since": h["date"]}
    if hist:
        out["start"] = {"from": hist[0]["net_worth"], "change": round(nw - hist[0]["net_worth"], 2), "since": hist[0]["date"]}
    return out


def fmt(v):
    return ("-" if v < 0 else "") + "$" + format(abs(v), ",.0f")


def insights(con, pos, by_cls, assets, nw, hist):
    """Plain, factual observations. No advice, just what the numbers show."""
    out = []
    gross = sum(v for k, v in by_cls.items() if k != "debt" and v > 0)

    # 1. What moved net worth over the last 30 days.
    base = value_at(hist, 30)
    if base:
        diffs = {k: by_cls[k] - base[k] for k in CLASS_KEYS}
        ch = nw - base["net_worth"]
        top = max(diffs.items(), key=lambda kv: abs(kv[1]))
        if abs(ch) >= 1:
            out.append({"tone": "up" if ch >= 0 else "down",
                        "title": "Net worth %s %s in 30 days" % ("up" if ch >= 0 else "down", fmt(abs(ch))),
                        "detail": ("Paying down debts added %s." % fmt(top[1]) if top[0] == "debt" and top[1] > 0 else
                                   "Debts grew by %s." % fmt(-top[1]) if top[0] == "debt" else
                                   "%s moved the most, %s%s." % (CLASS_NAME[top[0]], "up " if top[1] >= 0 else "down ", fmt(abs(top[1]))))})

    if gross > 0:
        # 2. Largest class.
        big = max((k for k in CLASS_KEYS if k != "debt"), key=lambda k: by_cls[k])
        out.append({"tone": "neutral", "title": "%s is your biggest allocation" % CLASS_NAME[big],
                    "detail": "%s, %d%% of everything you own." % (fmt(by_cls[big]), round(by_cls[big] / gross * 100))})

        # 3. Crypto share and volatility.
        if by_cls["crypto"] > 0:
            pct = by_cls["crypto"] / gross * 100
            ch24 = sum((h["value"] or 0) - (h["value"] or 0) / (1 + (h["change24h"] or 0) / 100)
                       for h in holdings(con) if h["change24h"])
            d = "%d%% of your assets." % round(pct)
            if abs(ch24) >= 1:
                d += " Prices moved it %s%s in the last 24 hours." % ("+" if ch24 >= 0 else "-", fmt(abs(ch24)))
            out.append({"tone": "neutral", "title": "Crypto: %s" % fmt(by_cls["crypto"]), "detail": d})

        # 4. Biggest single position.
        cands = [(h["name"], h["value"]) for h in holdings(con) if (h["value"] or 0) > 0 and h["code"] != "NZD"]
        cands += [(p["name"], p["value"]) for p in pos if p["value"] > 0 and not any(
            h["account_id"] == p["key"] for h in holdings(con))]
        if cands:
            name, v = max(cands, key=lambda x: x[1])
            if v / gross >= 0.2 and abs(v - by_cls[big]) > 0.5:
                out.append({"tone": "neutral", "title": "%s is %d%% of your assets" % (name, round(v / gross * 100)),
                            "detail": "Your largest single holding, worth %s." % fmt(v)})

        # 5. Liquidity.
        liquid = sum(by_cls[k] for k in LIQUID)
        if by_cls["kiwisaver"] > 0:
            out.append({"tone": "neutral", "title": "%d%% is accessible now" % round(liquid / gross * 100),
                        "detail": "%s is in KiwiSaver, which is locked until 65 (except first-home withdrawals)." % fmt(by_cls["kiwisaver"])})
        # 6. Cash share.
        out.append({"tone": "neutral", "title": "Cash: %s (%d%% of assets)" % (fmt(by_cls["cash"]), round(by_cls["cash"] / gross * 100)),
                    "detail": "Spread across %d account%s." % (
                        sum(1 for p in pos if p["cls"] == "cash" and p["value"] > 0),
                        "" if sum(1 for p in pos if p["cls"] == "cash" and p["value"] > 0) == 1 else "s")})

    # 7. Debts.
    if by_cls["debt"] < 0:
        out.append({"tone": "neutral", "title": "Debts: %s" % fmt(-by_cls["debt"]),
                    "detail": "%s." % ", ".join("%s %s" % (p["name"], fmt(-p["value"])) for p in pos if p["cls"] == "debt" and p["value"] < 0)})

    # 7b. When scheduled debts are paid off.
    for m in con.execute("SELECT * FROM manual WHERE cls='debt' AND sched_amount < 0"):
        d = payoff(m)
        if d:
            yrs = (d - date.today()).days / 365.25
            out.append({"tone": "neutral", "title": "%s paid off around %s" % (m["name"], d.strftime("%b %Y")),
                        "detail": "About %.1f years at %s a %s." % (yrs, fmt(-m["sched_amount"]),
                                                                  {"weekly": "week", "fortnightly": "fortnight", "monthly": "month"}[m["sched_every"]])})

    # 8. Stale data.
    stale = []
    cutoff_manual = date.today() - timedelta(days=90)
    for p in pos:
        try:
            d = datetime.fromisoformat((p["updated"] or "").replace("Z", "+00:00")).date()
        except ValueError:
            continue
        if p["source"] == "manual" and d < cutoff_manual and not p.get("sched"):
            stale.append("%s (updated %s)" % (p["name"], d.isoformat()))
        if p["source"] == "sync" and (p.get("status") == "INACTIVE" or d < date.today() - timedelta(days=7)):
            stale.append("%s (synced %s)" % (p["name"], d.isoformat()))
    if stale:
        out.append({"tone": "warn", "title": "Some values may be out of date", "detail": "; ".join(stale[:4]) + "."})
    return out


# ---------------------------------------------------------------- demo data
def build_demo(con):
    if con.execute("SELECT COUNT(*) FROM accounts").fetchone()[0]:
        return
    rnd = random.Random(11)
    ts = now_iso()
    accts = [("acc_every", "EVERYDAY", "Kiwibank", "CHECKING", 412.30), ("acc_bills", "BILLS POOL", "Kiwibank", "CHECKING", 180.00),
             ("acc_emerg", "EMERGENCY", "Kiwibank", "SAVINGS", 2600.00),
             ("acc_shr", "My Investments", "Sharesies", "INVESTMENT", 4487.20),
             ("acc_wal", "My NZD Wallet", "Sharesies", "WALLET", 200.21),
             ("acc_ks", "Simplicity Growth Fund", "Simplicity", "KIWISAVER", 14250.00)]
    for i, n, b, t, v in accts:
        con.execute("INSERT INTO accounts(id,name,bank,type,balance,available,updated,status) VALUES (?,?,?,?,?,?,?,'ACTIVE')",
                    (i, n, b, t, v, v, ts))
    hold = [("BTC", "Bitcoin", 0.0124, 162400.0, -1.8), ("ETH", "Ethereum", 0.21, 6150.0, -2.6),
            ("SOL", "Solana", 1.9, 310.0, 1.2), ("NZD", "New Zealand Dollar", 12.40, 1.0, 0.0)]
    crypto = 0.0
    for code, name, amt, price, ch in hold:
        crypto += amt * price
        con.execute("INSERT INTO holdings VALUES ('swyftx',?,?,?,?,?,?,?)", (code, name, amt, price, amt * price, ch, ts))
    con.execute("INSERT INTO accounts(id,name,bank,type,balance,available,updated,status) VALUES ('swyftx','Swyftx','Swyftx','CRYPTO',?,?,?,'ACTIVE')",
                (round(crypto, 2), round(crypto, 2), ts))
    shares = [("FNZ", "Smartshares NZ Top 50", 1850.0, 3.70), ("USF", "Smartshares US 500", 1620.0, 16.20),
              ("AIR", "Air New Zealand", 410.0, 0.82), ("TSLA", "Tesla", 607.2, 607.2)]
    for code, name, v, price in shares:
        con.execute("INSERT INTO holdings VALUES ('acc_shr',?,?,?,?,?,?,?)", (code, name, v / price, price, v, None, ts))
    # Four months of daily prices, walked backwards from today, with one top-up along the way.
    for acct, rows, swing in (("swyftx", [(c, a, pr) for c, _, a, pr, _ in hold if c != "NZD"], 0.035),
                              ("acc_shr", [(c, v / pr, pr) for c, _, v, pr in shares], 0.012)):
        for code, amount, price in rows:
            for back in range(0, 121):
                d = (date.today() - timedelta(days=back)).isoformat()
                con.execute("INSERT OR REPLACE INTO holding_days(date, account_id, code, amount, price, est) VALUES (?,?,?,?,?,0)",
                            (d, acct, code, amount * (0.8 if back > 45 else 1), price))
                price /= 1 + rnd.uniform(-swing, swing * 1.12)
    con.execute("INSERT INTO manual(name, cls, value, note, updated) VALUES (?,?,?,?,?)",
                ("Student loan", "debt", 18420.0, "IRD", (date.today() - timedelta(days=20)).isoformat()))
    # A year of weekly snapshots.
    ends = {"acc_every": 412.3, "acc_bills": 180.0, "acc_emerg": 2600.0, "acc_shr": 4487.2, "acc_wal": 200.21,
            "acc_ks": 14250.0, "swyftx": crypto, "manual:1": -18420.0}
    starts = {"acc_every": 900.0, "acc_bills": 150.0, "acc_emerg": 1200.0, "acc_shr": 1900.0, "acc_wal": 50.0,
              "acc_ks": 11600.0, "swyftx": crypto * 0.55, "manual:1": -19300.0}
    walk = 0.0
    for w in range(53):
        d = (date.today() - timedelta(days=7 * (52 - w))).isoformat()
        f = w / 52
        walk += rnd.uniform(-0.09, 0.1)
        for k in ends:
            v = starts[k] + (ends[k] - starts[k]) * f
            if k == "acc_every":
                v += rnd.uniform(-300, 300) * (1 - f)
            if k in ("acc_shr", "acc_ks"):
                v *= 1 + rnd.uniform(-0.025, 0.025) * (1 - f)
            if k == "swyftx":
                v *= max(0.5, 1 + walk * (1 - f))
            con.execute("INSERT OR REPLACE INTO snapshots(date, account_id, value, est) VALUES (?,?,?,?)",
                        (d, k, round(v, 2), 1 if w < 44 else 0))
    meta_set(con, "last_sync", ts)
    con.commit()


# ---------------------------------------------------------------- myIR import
def read_xlsx_rows(raw):
    """Minimal .xlsx reader (first sheet) using only the standard library."""
    ns = {"m": "http://schemas.openxmlformats.org/spreadsheetml/2006/main"}
    with zipfile.ZipFile(io.BytesIO(raw)) as z:
        shared = []
        if "xl/sharedStrings.xml" in z.namelist():
            for si in ET.fromstring(z.read("xl/sharedStrings.xml")).findall("m:si", ns):
                shared.append("".join(t.text or "" for t in si.iter("{%s}t" % ns["m"])))
        sheets = sorted(n for n in z.namelist() if re.match(r"xl/worksheets/sheet\d+\.xml$", n))
        if not sheets:
            raise ValueError("That file doesn't look like a spreadsheet.")
        root = ET.fromstring(z.read(sheets[0]))
    rows = []
    for row in root.iter("{%s}row" % ns["m"]):
        cells = {}
        for c in row.findall("m:c", ns):
            ref = re.match(r"([A-Z]+)", c.get("r") or "A").group(1)
            col = 0
            for ch in ref:
                col = col * 26 + ord(ch) - 64
            v = c.find("m:v", ns)
            t = c.get("t")
            if t == "s" and v is not None:
                val = shared[int(v.text)]
            elif t == "inlineStr":
                val = "".join(x.text or "" for x in c.iter("{%s}t" % ns["m"]))
            elif v is not None:
                try:
                    val = float(v.text)
                except (TypeError, ValueError):
                    val = v.text
            else:
                val = None
            cells[col - 1] = val
        if cells:
            rows.append([cells.get(i) for i in range(max(cells) + 1)])
    return rows


def excel_date(v):
    if isinstance(v, (int, float)):
        return date(1899, 12, 30) + timedelta(days=int(v))
    for f in ("%d/%m/%Y", "%Y-%m-%d", "%d-%b-%Y", "%d %b %Y"):
        try:
            return datetime.strptime(str(v).strip(), f).date()
        except ValueError:
            pass
    return None


def import_student_loan(con, data):
    """Import a myIR student loan transactions export (.xlsx).
    Fills in exact past balances, and sets the loan to keep going down at your usual repayment."""
    balance = abs(num(data.get("balance")))
    if not balance:
        raise ValueError("Enter your current student loan balance from myIR.")
    try:
        rows = read_xlsx_rows(base64.b64decode(data.get("file") or ""))
    except zipfile.BadZipFile:
        raise ValueError("Couldn't open that file. Use the .xlsx download from myIR.")
    head = next((i for i, r in enumerate(rows) if r and "Date" in [str(x).strip() for x in r if x]
                 and "Amount" in [str(x).strip() for x in r if x]), None)
    if head is None:
        raise ValueError("Couldn't find the Date / Transaction / Amount columns in that file.")
    hdr = [str(x).strip() if x else "" for x in rows[head]]
    ci = {k: hdr.index(k) for k in ("Date", "Transaction", "Amount") if k in hdr}
    ti = hdr.index("Account type") if "Account type" in hdr else None
    txns = []
    for r in rows[head + 1:]:
        if len(r) <= max(ci.values()) or r[ci["Date"]] is None:
            continue
        if ti is not None and r[ti] and "student" not in str(r[ti]).lower():
            continue
        d, amt = excel_date(r[ci["Date"]]), num(r[ci["Amount"]])
        if d and amt:
            txns.append((d, str(r[ci.get("Transaction", ci["Date"])] or ""), amt))
    if not txns:
        raise ValueError("No student loan transactions found in that file.")
    txns.sort()
    today = date.today()

    # Usual repayment: the typical recent deduction, less yearly fees spread over 26 fortnights.
    deds = [-a for d, t, a in txns if a < 0]
    recent = deds[-6:]
    usual = round(statistics.median(recent), 2)
    fees_year = sum(a for d, t, a in txns if a > 0 and (today - d).days <= 365)
    per = round(usual - fees_year / 26.0, 2)
    last_ded = max(d for d, t, a in txns if a < 0)
    nxt = last_ded + timedelta(days=14)
    while nxt <= today:
        nxt += timedelta(days=14)

    row = con.execute("SELECT id FROM manual WHERE lower(name) LIKE '%student loan%' ORDER BY id LIMIT 1").fetchone()
    vals = ("Student loan", "debt", balance, "IRD", today.isoformat(), -per, "fortnightly", nxt.isoformat())
    if row:
        mid = row["id"]
        con.execute("""UPDATE manual SET name=?, cls=?, value=?, note=?, updated=?, sched_amount=?, sched_every=?,
                       sched_next=? WHERE id=?""", vals + (mid,))
    else:
        mid = con.execute("""INSERT INTO manual(name, cls, value, note, updated, sched_amount, sched_every, sched_next)
                             VALUES (?,?,?,?,?,?,?,?)""", vals).lastrowid

    # Exact past balances: today's balance, undoing every transaction since each day.
    key = "manual:%d" % mid
    # The file is the source of truth for the loan's past, so replace anything stored before today.
    con.execute("DELETE FROM snapshots WHERE account_id=? AND date<?", (key, today.isoformat()))
    # Same one-year window as the rest of the rebuilt history, so the chart lines up.
    d, rows_out = max(txns[0][0], today - timedelta(days=365)), []
    while d < today:
        owed = balance - sum(a for td, t, a in txns if td > d)
        rows_out.append((d.isoformat(), key, -round(owed, 2)))
        d += timedelta(days=1)
    con.executemany("INSERT OR IGNORE INTO snapshots(date, account_id, value, est) VALUES (?,?,?,2)", rows_out)
    con.execute("INSERT OR REPLACE INTO snapshots(date, account_id, value, est) VALUES (?,?,?,0)",
                (today.isoformat(), key, -balance))
    con.commit()
    return {"ok": True, "transactions": len(txns), "from": txns[0][0].isoformat(), "usual_repayment": usual,
            "yearly_fees": fees_year, "net_per_fortnight": per, "next_deduction": nxt.isoformat(),
            "paid_off": (payoff(con.execute("SELECT * FROM manual WHERE id=?", (mid,)).fetchone()) or today).isoformat()}


# ---------------------------------------------------------------- phone access (off until you turn it on)
# The app normally answers only this Mac. Turning phone access on opens a second
# door for devices on the same Wi-Fi, and only for requests carrying a private key.


# ---------------------------------------------------------------- QR code
# Draws the phone link as a square code the phone's camera can read, so the link never has to be typed.
# Byte mode, error level L, versions 1 to 5 (up to 106 characters). No libraries.
def qr_matrix(text):
    data = text.encode("utf-8")
    caps = {1: (19, 7), 2: (34, 10), 3: (55, 15), 4: (80, 20), 5: (108, 26)}   # version: (data bytes, check bytes)
    ver = next((v for v in sorted(caps) if len(data) + 2 <= caps[v][0]), None)
    if ver is None:
        return None
    nd, ne = caps[ver]
    bits = "0100" + format(len(data), "08b") + "".join(format(b, "08b") for b in data)
    bits += "0" * min(4, nd * 8 - len(bits))
    bits += "0" * (-len(bits) % 8)
    cw = [int(bits[i:i + 8], 2) for i in range(0, len(bits), 8)]
    while len(cw) < nd:
        cw.append(0xEC if (nd - len(cw)) % 2 == (nd - len(bits) // 8) % 2 else 0x11)
    exp, log, x = [0] * 512, [0] * 256, 1
    for i in range(255):
        exp[i], log[x] = x, i
        x <<= 1
        if x & 0x100:
            x ^= 0x11D
    for i in range(255, 512):
        exp[i] = exp[i - 255]
    mul = lambda a, b: 0 if a == 0 or b == 0 else exp[log[a] + log[b]]
    gen = [1]
    for i in range(ne):
        nxt = [0] * (len(gen) + 1)
        for j, g in enumerate(gen):
            nxt[j] ^= g
            nxt[j + 1] ^= mul(g, exp[i])
        gen = nxt
    rem = cw + [0] * ne
    for i in range(nd):
        f = rem[i]
        if f:
            for j, g in enumerate(gen):
                rem[i + j] ^= mul(g, f)
    stream = "".join(format(b, "08b") for b in cw + rem[nd:])

    n = 17 + 4 * ver
    M = [[0] * n for _ in range(n)]
    fn = [[False] * n for _ in range(n)]

    def put(x, y, v):
        if 0 <= x < n and 0 <= y < n:
            M[y][x], fn[y][x] = 1 if v else 0, True

    for cx, cy in ((3, 3), (n - 4, 3), (3, n - 4)):          # the three corner squares
        for dy in range(-4, 5):
            for dx in range(-4, 5):
                d = max(abs(dx), abs(dy))
                put(cx + dx, cy + dy, d != 2 and d != 4)
    for i in range(8, n - 8):                                 # timing lines
        put(i, 6, i % 2 == 0)
        put(6, i, i % 2 == 0)
    if ver >= 2:                                              # the small square near the fourth corner
        c = n - 7
        for dy in range(-2, 3):
            for dx in range(-2, 3):
                put(c + dx, c + dy, max(abs(dx), abs(dy)) != 1)
    for i in range(9):                                        # keep room for the format bits
        for x, y in ((8, i), (i, 8)):
            if not fn[y][x]:
                put(x, y, 0)
    for i in range(8):
        put(n - 1 - i, 8, 0)
        put(8, n - 1 - i, 0)
    put(8, n - 8, 1)

    k = 0
    for right in range(n - 1, 0, -2):                         # the data snakes up and down in pairs of columns
        if right <= 6:
            right -= 1
        up = ((right + 1) & 2) == 0
        for v in range(n):
            y = n - 1 - v if up else v
            for x in (right, right - 1):
                if not fn[y][x]:
                    M[y][x] = int(stream[k]) if k < len(stream) else 0
                    k += 1

    masks = [lambda x, y: (x + y) % 2 == 0, lambda x, y: y % 2 == 0, lambda x, y: x % 3 == 0, lambda x, y: (x + y) % 3 == 0,
             lambda x, y: (x // 3 + y // 2) % 2 == 0, lambda x, y: x * y % 2 + x * y % 3 == 0,
             lambda x, y: (x * y % 2 + x * y % 3) % 2 == 0, lambda x, y: ((x + y) % 2 + x * y % 3) % 2 == 0]

    def finished(m):
        G = [[M[y][x] ^ (1 if not fn[y][x] and masks[m](x, y) else 0) for x in range(n)] for y in range(n)]
        d = (1 << 3) | m                                      # level L + which mask
        r = d << 10
        for i in range(14, 9, -1):
            if (r >> i) & 1:
                r ^= 0x537 << (i - 10)
        f = ((d << 10) | r) ^ 0x5412
        bit = lambda i: (f >> i) & 1
        for i in range(6):
            G[i][8] = bit(i)
        G[7][8], G[8][8], G[8][7] = bit(6), bit(7), bit(8)
        for i in range(9, 15):
            G[8][14 - i] = bit(i)
        for i in range(8):
            G[8][n - 1 - i] = bit(i)
        for i in range(8, 15):
            G[n - 15 + i][8] = bit(i)
        G[n - 8][8] = 1
        return G

    def penalty(G):                                           # prefer the pattern that's easiest for a camera
        p = 0
        for lines in (G, list(zip(*G))):
            for line in lines:
                run = 1
                for i in range(1, n):
                    if line[i] == line[i - 1]:
                        run += 1
                    else:
                        p += run - 2 if run >= 5 else 0
                        run = 1
                p += run - 2 if run >= 5 else 0
                s = "".join(map(str, line))
                p += 40 * (s.count("10111010000") + s.count("00001011101"))
        for y in range(n - 1):
            for x in range(n - 1):
                if G[y][x] == G[y][x + 1] == G[y + 1][x] == G[y + 1][x + 1]:
                    p += 3
        dark = sum(map(sum, G)) * 100 // (n * n)
        return p + 10 * (abs(dark - 50) // 5)

    best = min((finished(m) for m in range(8)), key=penalty)
    return ["".join(map(str, row)) for row in best]


def phone_state():
    """The private link for opening this on a phone, once cloud-setup.command has been run."""
    cfg = cloud_ready()
    if not cfg:
        return {"away": None}
    link = cloud.phone_link(cfg)
    return {"away": {"url": link, "qr": qr_matrix(link), "error": _cloud["error"], "sent": _cloud["pushed"]}}


def shape(v, depth=0):
    """The outline of some data with the values removed: names of fields and what kind of thing each holds."""
    if isinstance(v, dict):
        return {str(k)[:40]: shape(x, depth + 1) for k, x in list(v.items())[:40]} if depth < 6 else "..."
    if isinstance(v, list):
        return [shape(v[0], depth + 1), "x%d" % len(v)] if v else []
    if isinstance(v, bool):
        return "yes/no"
    if isinstance(v, (int, float)):
        return "number"
    return "nothing" if v is None else "text"


def shapes(con):
    out = []
    for a in con.execute("SELECT a.type, a.bank, m.breakdown, m.portfolio FROM accounts a LEFT JOIN account_meta m ON m.account_id=a.id"):
        n = con.execute("SELECT COUNT(*), SUM(amount>0), SUM(price>0) FROM holdings WHERE account_id IN (SELECT id FROM accounts WHERE type=? AND bank=?)",
                        (a["type"], a["bank"])).fetchone()
        out.append({"type": a["type"], "from": a["bank"], "breakdown": shape(json.loads(a["breakdown"])) if a["breakdown"] else None,
                    "portfolio": shape(json.loads(a["portfolio"])) if a["portfolio"] else None,
                    "holdings_read": n[0], "with_units": n[1] or 0, "with_price": n[2] or 0})
    return out


# ---------------------------------------------------------------- HTTP server
class Handler(BaseHTTPRequestHandler):
    def log_message(self, *a):
        pass

    def send_json(self, obj, code=200):
        body = json.dumps(obj).encode()
        self.send_response(code)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(body)

    def body(self):
        n = int(self.headers.get("Content-Length") or 0)
        return json.loads(self.rfile.read(n) or b"{}")

    def is_local(self):
        return self.client_address[0] in ("127.0.0.1", "::1", "::ffff:127.0.0.1")

    def refuse(self, text="forbidden"):
        body = text.encode()
        self.send_response(403)
        self.send_header("Content-Type", "text/plain; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)
        return False

    def guard(self):
        full_host = self.headers.get("Host") or ""
        origin = self.headers.get("Origin")
        if self.is_local():
            # This Mac's own browser (also blocks DNS-rebinding and cross-site requests).
            if full_host.split(":")[0] not in ("127.0.0.1", "localhost"):
                return self.refuse()
            if self.command != "GET" and origin and not re.match(r"^http://(127\.0\.0\.1|localhost)(:\d+)?$", origin):
                return self.refuse()
            return True
        return self.refuse()    # nothing else on the network gets an answer

    def do_GET(self):
        u = urllib.parse.urlparse(self.path)
        if u.path == "/icon.png":   # just the icon, so a phone can show it on its home screen
            with open(os.path.join(STATIC_DIR, "icon.png"), "rb") as f:
                data = f.read()
            self.send_response(200)
            self.send_header("Content-Type", "image/png")
            self.send_header("Content-Length", str(len(data)))
            self.end_headers()
            self.wfile.write(data)
            return
        if not self.guard():
            return
        qs = dict(urllib.parse.parse_qsl(u.query))
        if u.path in ("/", "/index.html"):
            with open(os.path.join(STATIC_DIR, "index.html"), "rb") as f:
                data = f.read().replace(b"__APP_NAME__", cloud.app_name(load_config()).encode("utf-8"))
            self.send_response(200)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.send_header("Content-Length", str(len(data)))
            self.send_header("Cache-Control", "no-store")
            self.send_header("Referrer-Policy", "no-referrer")
            self.end_headers()
            self.wfile.write(data)
            return
        con = db()
        try:
            if u.path == "/api/state":
                cfg = load_config()
                self.send_json({"version": APP_VERSION, "demo": DEMO, "local": self.is_local(),
                                "configured": bool((cfg["app_token"] and cfg["user_token"]) or cfg["swyftx_api_key"]),
                                "last_sync": meta_get(con, "last_sync"), "syncing": _sync["running"],
                                "last_error": _sync["last_error"], "classes": [{"key": k, "name": n} for k, n in CLASSES]})
            elif u.path == "/api/summary":
                self.send_json(summary(con))
            elif u.path == "/api/phone":
                self.send_json(phone_state())
            elif u.path == "/api/shapes":
                self.send_json(shapes(con))
            elif u.path == "/api/explore":
                self.send_json(explore(con))
            elif u.path == "/api/history":
                d = qs.get("days")
                self.send_json(history(con, int(d) if d and d.isdigit() else None))
            else:
                self.send_json({"error": "not found"}, 404)
        finally:
            con.close()

    def do_POST(self):
        if not self.guard():
            return
        path = urllib.parse.urlparse(self.path).path
        if path == "/api/restart":       # after an update: hand over to a fresh copy running the new files
            self.send_json({"ok": True})
            threading.Timer(0.3, restart).start()
            return
        if path == "/api/sync":
            return self.send_json(run_sync())
        if path == "/api/rebuild-history":
            try:
                out = rebuild_history()
                cloud_push_soon()
                return self.send_json(out)
            except Exception as e:
                return self.send_json({"ok": False, "error": str(e)})
        data = self.body()
        con = db()
        try:
            if path == "/api/manual":
                cls = data.get("cls")
                name = (data.get("name") or "").strip()
                if cls not in CLASS_KEYS or not name:
                    return self.send_json({"error": "Need a name and a type"}, 400)
                val = abs(num(data.get("value")))
                today = date.today().isoformat()
                sa = num(data.get("sched_amount")) or None
                se = data.get("sched_every") if data.get("sched_every") in ("weekly", "fortnightly", "monthly") else None
                sn = data.get("sched_next") or None
                if not (sa and se and sn):
                    sa = se = sn = None
                if data.get("id"):
                    con.execute("""UPDATE manual SET name=?, cls=?, value=?, note=?, updated=?, sched_amount=?,
                                   sched_every=?, sched_next=? WHERE id=?""",
                                (name, cls, val, data.get("note") or "", today, sa, se, sn, int(data["id"])))
                else:
                    con.execute("""INSERT INTO manual(name, cls, value, note, updated, sched_amount, sched_every, sched_next)
                                   VALUES (?,?,?,?,?,?,?,?)""", (name, cls, val, data.get("note") or "", today, sa, se, sn))
                con.commit()
                record_snapshot(con)
                cloud_push_soon()
                return self.send_json({"ok": True})
            if path == "/api/import/student-loan":
                try:
                    out = import_student_loan(con, data)
                    cloud_push_soon()
                    return self.send_json(out)
                except ValueError as e:
                    return self.send_json({"ok": False, "error": str(e)}, 400)
            m = re.match(r"^/api/manual/(\d+)/delete$", path)
            if m:
                con.execute("DELETE FROM manual WHERE id=?", (int(m.group(1)),))
                con.execute("DELETE FROM snapshots WHERE account_id=?", ("manual:%s" % m.group(1),))
                con.commit()
                cloud_push_soon()
                return self.send_json({"ok": True})
            m = re.match(r"^/api/accounts/(.+)$", path)
            if m:
                aid = urllib.parse.unquote(m.group(1))
                if "cls" in data:
                    cls = data["cls"] if data["cls"] in CLASS_KEYS else None
                    con.execute("UPDATE accounts SET cls_override=? WHERE id=?", (cls, aid))
                if "hidden" in data:
                    con.execute("UPDATE accounts SET hidden=? WHERE id=?", (1 if data["hidden"] else 0, aid))
                con.commit()
                cloud_push_soon()
                return self.send_json({"ok": True})
            self.send_json({"error": "not found"}, 404)
        finally:
            con.close()


def restart():
    kw = {"creationflags": 0x00000008 | 0x00000200} if sys.platform == "win32" else {"start_new_session": True}   # detached
    try:
        args = [a for a in sys.argv[1:] if a != "--no-browser"] + ["--no-browser"]
        subprocess.Popen([sys.executable, os.path.join(HERE, "app.py")] + args, cwd=HERE, close_fds=True,
                         stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, **kw)
    finally:
        os._exit(0)


def main():
    if sys.stdout is None or sys.stderr is None:      # started without a window (Windows): keep a log instead
        sys.stdout = sys.stderr = open(os.path.join(HERE, "money.log"), "a", buffering=1, encoding="utf-8")
    cfg = load_config()
    con = init_db()
    if DEMO:
        build_demo(con)
    meta_set(con, "phone_on", "0")   # the home wi-fi link from an earlier version is gone
    con.commit()
    con.close()
    if os.path.exists(CONFIG_PATH):
        try:
            os.chmod(CONFIG_PATH, 0o600)
        except OSError:
            pass
    port = int(cfg.get("port", 8765)) + (1 if DEMO else 0)
    threading.Thread(target=sync_loop, daemon=True).start()
    for attempt in range(24):                         # a copy that's just been told to restart may still hold the port
        try:
            server = ThreadingHTTPServer((HOST, port), Handler)
            break
        except OSError:
            if attempt == 23:
                raise
            time.sleep(0.25)
    url = "http://127.0.0.1:%d" % port
    print("%s%s running at %s  (Ctrl+C to stop)" % (cloud.app_name(cfg), " [DEMO]" if DEMO else "", url))
    if not NO_BROWSER:
        threading.Timer(0.8, lambda: webbrowser.open(url)).start()
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass


if __name__ == "__main__":
    main()
