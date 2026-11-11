#!/usr/bin/env python3
"""Seeing your money when you're out, with the computer on or off.

Your computer can't answer when it's off, so this hands the regular syncing to GitHub:

  - Every few hours a small job on GitHub fetches your balances (the same way the Mac does)
    and publishes a page your phone can open from anywhere.
  - Everything it stores or publishes is encrypted first. The page is scrambled data until
    your phone unscrambles it with the key in your private link. The key is never sent anywhere.
  - Your Akahu tokens and Swyftx key are kept in GitHub's secret store, which the job can use
    but nobody can read back, not even you.
  - The page is view only. You add and edit things on the Mac, and it passes them on.

Commands (the .command files run these for you):
  python3 cloud.py setup     set it up, or update it after changing files or keys
  python3 cloud.py push      send the Mac's current data up now
  python3 cloud.py link      print your private phone link
  python3 cloud.py off       stop the scheduled sync
  python3 cloud.py run DIR   what the job on GitHub runs

No libraries: Python's standard library. It uses openssl for speed where there is one (macOS, Linux)
and its own copy of the same cipher where there isn't (Windows).
"""
import base64
import contextlib
import getpass
import hashlib
import hmac
import io
import json
import os
import secrets
import sqlite3
import subprocess
import sys
import tempfile
import time
import traceback
import urllib.error
import urllib.parse
import urllib.request
import webbrowser
import zlib

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)      # so "import app" works from any Python, including the one bundled on Windows
CONFIG_PATH = os.path.join(HERE, "config.json")
API = os.environ.get("JM_GITHUB_API", "https://api.github.com")
WORKFLOW = "sync.yml"
SECRET_NAME = "JM_SECRETS"
MAGIC = b"JM2"
# What gets published as the code of the scheduled job. Never config.json, never the database.
CODE_FILES = {
    "app.py": "app.py",
    "cloud.py": "cloud.py",
    "static/index.html": "static/index.html",
    "static/icon.png": "static/icon.png",
    "cloud-job/sync.yml": ".github/workflows/" + WORKFLOW,
}
PUBLIC_README = ("This repository runs a scheduled job for one person.\n\n"
                 "The data it stores and publishes is encrypted and can't be read without a key that isn't kept here.\n")


# ---------------------------------------------------------------- encryption
# AES-256 in counter mode, with a SHA-256 HMAC over everything, so a changed or wrong-key file is
# refused rather than half-read. The same format is opened in the phone's browser with its built-in crypto.
def _keys(key):
    return hmac.new(key, b"enc", "sha256").digest(), hmac.new(key, b"mac", "sha256").digest()


def _tables():
    """The AES lookup tables, built once from first principles."""
    sbox, p, q = [0] * 256, 1, 1
    while True:                                   # multiplicative inverses in GF(2^8), then the affine step
        p = p ^ ((p << 1) & 0xFF) ^ (0x1B if p & 0x80 else 0)
        q ^= q << 1
        q ^= q << 2
        q ^= q << 4
        q &= 0xFF
        if q & 0x80:
            q ^= 0x09
        x = q ^ (q << 1 | q >> 7) ^ (q << 2 | q >> 6) ^ (q << 3 | q >> 5) ^ (q << 4 | q >> 4)
        sbox[p] = (x ^ 0x63) & 0xFF
        if p == 1:
            break
    sbox[0] = 0x63
    t0 = []
    for x in sbox:
        x2 = ((x << 1) ^ 0x1B) & 0xFF if x & 0x80 else x << 1
        t0.append((x2 << 24) | (x << 16) | (x << 8) | (x2 ^ x))
    rot = lambda w, n: ((w >> n) | (w << (32 - n))) & 0xFFFFFFFF
    return sbox, t0, [rot(w, 8) for w in t0], [rot(w, 16) for w in t0], [rot(w, 24) for w in t0]


_T = None


def _aes_ctr_python(data, key, iv):
    """AES-256-CTR without openssl. Encrypting and decrypting are the same operation."""
    global _T
    if _T is None:
        _T = _tables()
    S, T0, T1, T2, T3 = _T
    w = [int.from_bytes(key[i:i + 4], "big") for i in range(0, 32, 4)]          # key schedule: 15 round keys
    rcon = 1
    for i in range(8, 60):
        t = w[i - 1]
        if i % 8 == 0:
            t = ((t << 8) | (t >> 24)) & 0xFFFFFFFF
            t = (S[t >> 24] << 24) | (S[(t >> 16) & 255] << 16) | (S[(t >> 8) & 255] << 8) | S[t & 255]
            t ^= rcon << 24
            rcon = ((rcon << 1) ^ 0x11B) & 0xFF if rcon & 0x80 else rcon << 1
        elif i % 8 == 4:
            t = (S[t >> 24] << 24) | (S[(t >> 16) & 255] << 16) | (S[(t >> 8) & 255] << 8) | S[t & 255]
        w.append(w[i - 8] ^ t)
    n0, n1, n2 = (int.from_bytes(iv[i:i + 4], "big") for i in (0, 4, 8))
    ctr = int.from_bytes(iv[12:16], "big")
    out = bytearray()
    for _ in range((len(data) + 15) // 16):
        s0, s1, s2, s3 = n0 ^ w[0], n1 ^ w[1], n2 ^ w[2], ctr ^ w[3]
        for r in range(4, 56, 4):
            s0, s1, s2, s3 = (T0[s0 >> 24] ^ T1[(s1 >> 16) & 255] ^ T2[(s2 >> 8) & 255] ^ T3[s3 & 255] ^ w[r],
                              T0[s1 >> 24] ^ T1[(s2 >> 16) & 255] ^ T2[(s3 >> 8) & 255] ^ T3[s0 & 255] ^ w[r + 1],
                              T0[s2 >> 24] ^ T1[(s3 >> 16) & 255] ^ T2[(s0 >> 8) & 255] ^ T3[s1 & 255] ^ w[r + 2],
                              T0[s3 >> 24] ^ T1[(s0 >> 16) & 255] ^ T2[(s1 >> 8) & 255] ^ T3[s2 & 255] ^ w[r + 3])
        for a, b, c, d, k in ((s0, s1, s2, s3, w[56]), (s1, s2, s3, s0, w[57]), (s2, s3, s0, s1, w[58]), (s3, s0, s1, s2, w[59])):
            out += (((S[a >> 24] << 24) | (S[(b >> 16) & 255] << 16) | (S[(c >> 8) & 255] << 8) | S[d & 255]) ^ k).to_bytes(4, "big")
        ctr = (ctr + 1) & 0xFFFFFFFF
    return bytes(x ^ y for x, y in zip(data, out))


def _openssl(mode, data, key, iv, decrypt=False):
    try:
        p = subprocess.run(["openssl", "enc", "-aes-256-" + mode, "-d" if decrypt else "-e", "-K", key.hex(), "-iv", iv.hex()],
                           input=data, capture_output=True)
    except OSError:
        return None
    return p.stdout if p.returncode == 0 else None


def _aes_ctr(data, key, iv):
    out = _openssl("ctr", data, key, iv)
    return out if out is not None and len(out) == len(data) else _aes_ctr_python(data, key, iv)


def seal(data, key, compress=True):
    ek, mk = _keys(key)
    iv = secrets.token_bytes(12) + b"\x00\x00\x00\x00"       # 12 random bytes, then a block counter starting at zero
    body = MAGIC + (b"\x01" if compress else b"\x00") + iv + _aes_ctr(zlib.compress(data, 9) if compress else data, ek, iv)
    return body + hmac.new(mk, body, "sha256").digest()


def unseal(blob, key):
    ek, mk = _keys(key)
    if len(blob) < 52 or blob[:3] not in (b"JM1", b"JM2"):
        raise ValueError("not one of this app's files")
    body, tag = blob[:-32], blob[-32:]
    if not hmac.compare_digest(hmac.new(mk, body, "sha256").digest(), tag):
        raise ValueError("wrong key, or the file was changed")
    if blob[:3] == b"JM1":                       # files written before 11 Nov 2026 (needs openssl)
        data = _openssl("cbc", body[20:], ek, body[4:20], True)
        if data is None:
            raise ValueError("an older file that this computer can't open")
    else:
        data = _aes_ctr(body[20:], ek, body[4:20])
    return zlib.decompress(data) if body[3] == 1 else data


def view_key_bytes(text):
    return base64.urlsafe_b64decode(text + "=" * (-len(text) % 4))


# ---------------------------------------------------------------- config
def read_config():
    if not os.path.exists(CONFIG_PATH):
        return {}
    with open(CONFIG_PATH) as f:
        return json.load(f)


def write_config(cfg):
    tmp = CONFIG_PATH + ".tmp"
    with open(tmp, "w") as f:
        json.dump(cfg, f, indent=2)
        f.write("\n")
    os.chmod(tmp, 0o600)
    os.replace(tmp, CONFIG_PATH)


def configured(cfg):
    return bool(cfg.get("github_token") and cfg.get("github_repo") and cfg.get("cloud_master_key") and cfg.get("cloud_view_key"))


def page_url(cfg):
    if cfg.get("cloud_url"):
        return cfg["cloud_url"]
    owner, name = cfg["github_repo"].split("/", 1)
    return "https://%s.github.io/%s/" % (owner.lower(), name)


def phone_link(cfg):
    return "%s#k=%s" % (page_url(cfg), cfg["cloud_view_key"])


WINDOWS_ZONES = {"New Zealand Standard Time": "Pacific/Auckland", "Chatham Islands Standard Time": "Pacific/Chatham",
                 "AUS Eastern Standard Time": "Australia/Sydney", "E. Australia Standard Time": "Australia/Brisbane",
                 "Cen. Australia Standard Time": "Australia/Adelaide", "AUS Central Standard Time": "Australia/Darwin",
                 "W. Australia Standard Time": "Australia/Perth", "Tasmania Standard Time": "Australia/Hobart",
                 "GMT Standard Time": "Europe/London", "UTC": "UTC"}


def local_timezone():
    try:
        if sys.platform == "win32":
            p = subprocess.run(["powershell", "-NoProfile", "-Command", "[System.TimeZoneInfo]::Local.Id"], capture_output=True, text=True, timeout=20)
            return WINDOWS_ZONES.get(p.stdout.strip(), "Pacific/Auckland")
        real = os.path.realpath("/etc/localtime")
        if "zoneinfo/" in real:
            return real.split("zoneinfo/", 1)[1]
    except Exception:
        pass
    return os.environ.get("TZ") or "Pacific/Auckland"


def owner(cfg=None):
    name = ((cfg if cfg is not None else read_config()).get("owner") or "Jakob").strip()
    return name or "Jakob"


def app_name(cfg=None):
    return owner(cfg) + "'s Money"


# ---------------------------------------------------------------- GitHub
class GitHubError(Exception):
    def __init__(self, code, message):
        Exception.__init__(self, "GitHub said %s: %s" % (code, message))
        self.code = code


def gh(token, method, path, body=None, raw=False, ok=()):
    """One call to GitHub. Returns parsed JSON (or bytes with raw=True); None for a status listed in ok."""
    req = urllib.request.Request(
        API + path, method=method, data=json.dumps(body).encode() if body is not None else None,
        headers={"Authorization": "Bearer " + token, "User-Agent": "jakobs-money", "X-GitHub-Api-Version": "2022-11-28",
                 "Accept": "application/vnd.github.raw" if raw else "application/vnd.github+json",
                 "Content-Type": "application/json"})
    try:
        with urllib.request.urlopen(req, timeout=60) as r:
            data = r.read()
            return data if raw else (json.loads(data) if data else {})
    except urllib.error.HTTPError as e:
        if e.code in ok:
            return None
        try:
            message = json.loads(e.read()).get("message") or e.reason
        except Exception:
            message = e.reason
        raise GitHubError(e.code, message)


def push_branch(token, repo, branch, files, message):
    """Replace a branch with a single commit holding these files. No history builds up."""
    entries = []
    for path, data in files.items():
        blob = gh(token, "POST", "/repos/%s/git/blobs" % repo, {"content": base64.b64encode(data).decode(), "encoding": "base64"})
        entries.append({"path": path, "mode": "100644", "type": "blob", "sha": blob["sha"]})
    tree = gh(token, "POST", "/repos/%s/git/trees" % repo, {"tree": entries})
    commit = gh(token, "POST", "/repos/%s/git/commits" % repo, {"message": message, "tree": tree["sha"], "parents": []})
    moved = gh(token, "PATCH", "/repos/%s/git/refs/heads/%s" % (repo, branch), {"sha": commit["sha"], "force": True}, ok=(404, 422))
    if moved is None:
        gh(token, "POST", "/repos/%s/git/refs" % repo, {"ref": "refs/heads/" + branch, "sha": commit["sha"]})


def dispatch(cfg, patience=1):
    """Ask GitHub to run the job now. Just after the job is first uploaded GitHub can take a moment to notice it."""
    for attempt in range(patience):
        try:
            return gh(cfg["github_token"], "POST", "/repos/%s/actions/workflows/%s/dispatches" % (cfg["github_repo"], WORKFLOW), {"ref": "main"})
        except GitHubError as e:
            if e.code not in (404, 422) or attempt == patience - 1:
                raise
            time.sleep(5)


# ---------------------------------------------------------------- what travels between the Mac and GitHub
def slim_copy(db_path, from_mac=True):
    """A copy of the database without anything the scheduled job doesn't need."""
    fd, tmp = tempfile.mkstemp(suffix=".db")
    os.close(fd)
    try:
        src, dst = sqlite3.connect(db_path), sqlite3.connect(tmp)
        with dst:
            src.backup(dst)
        src.close()
        dst.execute("DROP TABLE IF EXISTS transactions")
        dst.execute("DELETE FROM meta WHERE key IN ('phone_key', 'phone_on')")
        if from_mac:
            dst.execute("DELETE FROM meta WHERE key='mac_sha'")
        dst.commit()
        dst.execute("VACUUM")
        dst.close()
        with open(tmp, "rb") as f:
            return f.read()
    finally:
        os.unlink(tmp)


def merge_snapshots(con, both):
    """Add days this copy is missing. A real figure replaces an estimate; nothing real is overwritten."""
    rows, prices = both
    if prices and con.execute("SELECT 1 FROM sqlite_master WHERE name='holding_days'").fetchone():
        ids = {r[0] for r in con.execute("SELECT id FROM accounts")}
        con.executemany("INSERT OR IGNORE INTO holding_days(date, account_id, code, amount, price, est) VALUES (?,?,?,?,?,?)",
                        [p for p in prices if p[1] in ids])
    known = {r[0] for r in con.execute("SELECT id FROM accounts")} | {"manual:%d" % r[0] for r in con.execute("SELECT id FROM manual")}
    added = 0
    for d, aid, value, est in rows:
        if aid not in known:
            continue
        cur = con.execute("SELECT est FROM snapshots WHERE date=? AND account_id=?", (d, aid)).fetchone()
        if cur is None:
            con.execute("INSERT INTO snapshots(date, account_id, value, est) VALUES (?,?,?,?)", (d, aid, value, est or 0))
            added += 1
        elif cur[0] == 1 and not est:
            con.execute("UPDATE snapshots SET value=?, est=0 WHERE date=? AND account_id=?", (value, d, aid))
            added += 1
    con.commit()
    return added


def snapshot_rows(db_bytes):
    """The daily values, and the daily prices, held in a copy of the database."""
    fd, tmp = tempfile.mkstemp(suffix=".db")
    os.close(fd)
    try:
        with open(tmp, "wb") as f:
            f.write(db_bytes)
        con = sqlite3.connect(tmp)
        try:
            rows = con.execute("SELECT date, account_id, value, est FROM snapshots").fetchall()
            prices = []
            if con.execute("SELECT 1 FROM sqlite_master WHERE name='holding_days'").fetchone():
                prices = con.execute("SELECT date, account_id, code, amount, price, est FROM holding_days").fetchall()
            return rows, prices
        finally:
            con.close()
    finally:
        os.unlink(tmp)


def push(cfg, db_path, run_now=False):
    """Computer -> GitHub: send the current data (encrypted) so the scheduled job has your latest items and settings."""
    blob = seal(slim_copy(db_path), bytes.fromhex(cfg["cloud_master_key"]))
    push_branch(cfg["github_token"], cfg["github_repo"], "mac-state", {"mac.enc": blob}, "state")
    if run_now:
        dispatch(cfg)


def pull(cfg, db_path):
    """GitHub -> Mac: fill in the days the Mac was off, from what the scheduled job recorded."""
    blob = gh(cfg["github_token"], "GET", "/repos/%s/contents/cloud.enc?ref=cloud-state" % cfg["github_repo"], raw=True, ok=(404,))
    if not blob:
        return 0
    rows = snapshot_rows(unseal(blob, bytes.fromhex(cfg["cloud_master_key"])))
    con = sqlite3.connect(db_path)
    try:
        return merge_snapshots(con, rows)
    finally:
        con.close()


# ---------------------------------------------------------------- the job on GitHub
def make_bundle(app, con, error, owner_name, source):
    """Everything the phone shows, in one piece. "source" says who made it: "computer" or "github"."""
    return {"built": app.now_iso(), "name": (owner_name or "Jakob") + "'s Money", "source": source,
            "/api/state": {"version": app.APP_VERSION, "demo": False, "local": False, "cloud": True, "configured": True,
                           "last_sync": app.meta_get(con, "last_sync"), "syncing": False, "last_error": error,
                           "classes": [{"key": k, "name": n} for k, n in app.CLASSES]},
            "/api/explore": app.explore(con)}


def live_blob(bundle, view_key):
    return seal(json.dumps(bundle, separators=(",", ":")).encode(), view_key, compress=True)


def publish_live(cfg, bundle):
    """Computer -> phone, straight away: the phone reads this branch every minute while it's open."""
    push_branch(cfg["github_token"], cfg["github_repo"], "live", {"data.enc": live_blob(bundle, view_key_bytes(cfg["cloud_view_key"]))}, "live")


def build_site(out_dir, bundle, view_key):
    os.makedirs(out_dir, exist_ok=True)
    with open(os.path.join(HERE, "static", "index.html"), encoding="utf-8") as f:
        html = f.read()
    marker = '<meta name="jm-mode" content="local">'
    if marker not in html:
        raise RuntimeError("index.html is missing its mode marker")
    repo = os.environ.get("GITHUB_REPOSITORY", "")
    html = html.replace(marker, '<meta name="jm-mode" content="cloud">\n<meta name="jm-repo" content="%s">\n<meta name="robots" content="noindex, nofollow">' % repo)
    html = html.replace('href="/icon.png"', 'href="icon.png"').replace("__APP_NAME__", bundle.get("name") or "Money")
    with open(os.path.join(out_dir, "index.html"), "w", encoding="utf-8") as f:
        f.write(html)
    with open(os.path.join(HERE, "static", "icon.png"), "rb") as f, open(os.path.join(out_dir, "icon.png"), "wb") as g:
        g.write(f.read())
    with open(os.path.join(out_dir, "data.enc"), "wb") as f:
        f.write(seal(json.dumps(bundle, separators=(",", ":")).encode(), view_key, compress=False))


def stop(reason):
    """End the job with a reason that shows on the run's summary page (and in cloud-setup's window)."""
    print("::error::" + reason)
    sys.exit(1)


def run(work):
    """Runs on GitHub. Its log is public, so it prints nothing about your money: no names, no figures."""
    try:
        run_job(work)
    except SystemExit:
        raise
    except Exception as e:      # say where, never what: the message of an error can carry figures
        frames = traceback.extract_tb(e.__traceback__)
        ours = [f for f in frames if os.path.basename(f.filename) in ("cloud.py", "app.py")] or frames
        where = "; ".join("%s line %d in %s" % (os.path.basename(f.filename), f.lineno, f.name) for f in ours[-3:])
        stop("Something unexpected went wrong (%s). Where: %s. Tell Claude this line." % (type(e).__name__, where))


def run_job(work):
    again = "On your computer, run the phone setup again (cloud-setup.command on a Mac, Phone setup.bat on Windows)."
    text = (os.environ.get("JM_SECRETS") or "").strip()
    if not text:
        stop("There is no secret called JM_SECRETS in this repository yet. " + again)
    try:
        sec = json.loads(text)
        master, view = bytes.fromhex(sec["master_key"]), view_key_bytes(sec["view_key"])
    except Exception:
        stop("The JM_SECRETS secret isn't what cloud-setup put on the clipboard (something else was pasted). " + again)
    for v in sec.values():
        if isinstance(v, str) and len(v) > 5 and "/" not in v:
            print("::add-mask::" + v)
    os.environ["TZ"] = sec.get("tz") or "Pacific/Auckland"   # so "today" means your today, not the server's
    if hasattr(time, "tzset"):
        time.tzset()
    os.environ["AKAHU_APP_TOKEN"] = sec.get("app_token", "")
    os.environ["AKAHU_USER_TOKEN"] = sec.get("user_token", "")
    os.environ["SWYFTX_API_KEY"] = sec.get("swyftx_api_key", "")

    def load(name):
        p = os.path.join(work, name)
        if not os.path.exists(p) or os.path.getsize(p) == 0:
            return None, None
        with open(p, "rb") as f:
            blob = f.read()
        try:
            return unseal(blob, master), hashlib.sha256(blob).hexdigest()
        except ValueError:
            stop("The saved data (%s) couldn't be unlocked with the key in JM_SECRETS, so the two don't match. %s" % (name, again))

    mac, mac_sha = load("mac.enc")
    cloud, _ = load("cloud.enc")
    db_path = os.path.join(work, "run.db")
    merged = None
    if cloud is not None:
        with open(db_path, "wb") as f:
            f.write(cloud)
        con = sqlite3.connect(db_path)
        seen = con.execute("SELECT value FROM meta WHERE key='mac_sha'").fetchone()
        con.close()
        if mac is not None and (not seen or seen[0] != mac_sha):
            merged = snapshot_rows(cloud)       # the Mac sent something new: start from it, keep the days only we recorded
    if cloud is None or merged is not None:
        if mac is None:
            stop("There's no data to start from yet. " + again)
        with open(db_path, "wb") as f:
            f.write(mac)

    import app
    app.DB_PATH = db_path
    app.CONFIG_PATH = os.path.join(work, "no-config.json")     # tokens come from the secret store only
    app.rebuild_history = lambda *a, **k: {}                   # past history is the Mac's job
    con = app.init_db()
    if merged is not None:
        merge_snapshots(con, merged)
    if mac_sha:
        app.meta_set(con, "mac_sha", mac_sha)
    con.commit()
    con.close()

    quiet = io.StringIO()
    with contextlib.redirect_stdout(quiet), contextlib.redirect_stderr(quiet):
        result = app.run_sync()
    print("sync: ok" if result.get("ok") else "sync: there was a problem. the page says what it was")

    con = app.db()
    try:
        bundle = make_bundle(app, con, result.get("error"), sec.get("owner"), "github")
    finally:
        con.close()
    build_site(os.path.join(work, "site"), bundle, view)
    live_dir = os.path.join(work, "live")
    os.makedirs(live_dir, exist_ok=True)
    with open(os.path.join(live_dir, "data.enc"), "wb") as f:
        f.write(live_blob(bundle, view))
    state_dir = os.path.join(work, "state")
    os.makedirs(state_dir, exist_ok=True)
    with open(os.path.join(state_dir, "cloud.enc"), "wb") as f:
        f.write(seal(slim_copy(db_path, from_mac=False), master))
    os.unlink(db_path)
    print("page: built")


# ---------------------------------------------------------------- setting it up from the Mac
def say(text=""):
    print(text, flush=True)


def ask(prompt, default=""):
    try:
        return input(prompt).strip() or default
    except EOFError:
        return default


def open_in_browser(url):
    try:
        if os.environ.get("JM_NO_BROWSER") or not webbrowser.open(url):
            say("  Open this in your browser: " + url)
    except Exception:
        say("  Open this in your browser: " + url)


def clipboard(text):
    try:
        if sys.platform == "darwin":
            return subprocess.run(["pbcopy"], input=text.encode(), check=False).returncode == 0
        if sys.platform == "win32":
            if not text:
                return subprocess.run("echo off | clip", shell=True, check=False).returncode == 0
            return subprocess.run(["clip"], input=text.encode(), check=False).returncode == 0
    except OSError:
        pass
    return False


def secret_exists(cfg):
    """True / False, or None if GitHub won't say."""
    try:
        return gh(cfg["github_token"], "GET", "/repos/%s/actions/secrets/%s" % (cfg["github_repo"], SECRET_NAME), ok=(404,)) is not None
    except GitHubError:
        return None


def last_run(cfg):
    runs = (gh(cfg["github_token"], "GET", "/repos/%s/actions/workflows/%s/runs?per_page=1" % (cfg["github_repo"], WORKFLOW), ok=(404,)) or {}).get("workflow_runs") or []
    return runs[0] if runs else None


def why_failed(cfg, run):
    """The reasons a run gave for stopping, in plain words where it left any."""
    token, repo, out = cfg["github_token"], cfg["github_repo"], []
    try:
        for job in gh(token, "GET", "/repos/%s/actions/runs/%s/jobs" % (repo, run["id"])).get("jobs", []):
            for st in job.get("steps") or []:
                if st.get("conclusion") == "failure":
                    out.append("It stopped at the step called \"%s\"." % st.get("name"))
            url = job.get("check_run_url") or ""
            if url.startswith(API):
                for a in gh(token, "GET", url[len(API):] + "/annotations") or []:
                    msg = (a.get("message") or "").strip()
                    if a.get("annotation_level") == "failure" and msg and not msg.startswith("Process completed"):
                        out.append(msg)
    except Exception:
        pass
    return out


def wait_for_run(cfg, after, minutes=5):
    token, repo = cfg["github_token"], cfg["github_repo"]
    deadline = time.time() + minutes * 60
    while time.time() < deadline:
        time.sleep(6)
        runs = (gh(token, "GET", "/repos/%s/actions/workflows/%s/runs?per_page=1" % (repo, WORKFLOW)) or {}).get("workflow_runs") or []
        if runs and runs[0].get("created_at", "") >= after and runs[0].get("status") == "completed":
            return runs[0]
        sys.stdout.write(".")
        sys.stdout.flush()
    return None


def setup():
    say("%s on your phone" % app_name())
    say("=" * 46)
    cfg = read_config()
    if not ((cfg.get("app_token") and cfg.get("user_token")) or cfg.get("swyftx_api_key")):
        sys.exit("There are no Akahu tokens or Swyftx key yet. Get the app working on this computer first.")
    db_path = os.path.join(HERE, "finance.db")
    if not os.path.exists(db_path):
        sys.exit("There's no data yet. Open the app on this computer and let it sync once first.")
    first_time = not configured(cfg)

    # 1. the GitHub token
    if not cfg.get("github_token"):
        say("\nStep 1. This needs a free GitHub account and a token so it can set things up for you.")
        say("  A page is opening. Sign in (or sign up), set Expiration to \"No expiration\",")
        say("  leave the ticked boxes as they are, scroll down, click Generate token, and copy it.")
        open_in_browser("https://github.com/settings/tokens/new?scopes=repo,workflow&description=Money%20app")
        say("  When you paste, NOTHING SHOWS ON SCREEN. That's on purpose. Paste once, press Return.")
        try:
            token = getpass.getpass("  Paste the token here and press Return: ").strip()
        except (EOFError, KeyboardInterrupt):
            token = ""
        if not token:
            sys.exit("No token entered. Nothing was changed.")
        cfg["github_token"] = token
    token = cfg["github_token"]
    try:
        login = gh(token, "GET", "/user")["login"]
    except GitHubError as e:
        if e.code == 401:
            cfg.pop("github_token", None)
            write_config(cfg)
            sys.exit("GitHub didn't accept that token. Run this again and paste a new one.")
        raise
    say("\nSigned in to GitHub as %s." % login)

    # 2. the repository
    repo = cfg.get("github_repo") or "%s/money" % login
    name = repo.split("/", 1)[1]
    if gh(token, "GET", "/repos/" + repo, ok=(404,)) is None:
        say("Creating %s ..." % repo)
        gh(token, "POST", "/user/repos", {"name": name, "private": False, "auto_init": True, "has_issues": False,
                                          "has_wiki": False, "has_projects": False,
                                          "description": "Scheduled job. Its data is encrypted."})
        time.sleep(3)
    cfg["github_repo"] = repo
    new_secret = first_time
    if not cfg.get("cloud_master_key"):
        cfg["cloud_master_key"] = secrets.token_bytes(32).hex()
    if not cfg.get("cloud_view_key"):
        cfg["cloud_view_key"] = base64.urlsafe_b64encode(secrets.token_bytes(16)).decode().rstrip("=")
    if not first_time:
        before = None
        try:
            before = last_run(cfg)
        except GitHubError:
            pass
        if secret_exists(cfg) is False:
            say("\nThe keys haven't been saved on GitHub yet, so that's next.")
            new_secret = True
        elif before and before.get("conclusion") == "failure":
            say("\nThe last run on GitHub failed:")
            for line in why_failed(cfg, before) or ["(it didn't say why)"]:
                say("  " + line)
            say("So the keys go in again, to rule them out.")
            new_secret = True
        elif ask("\nMake a new phone link? The old one stops working. [y/N] ").lower().startswith("y"):
            cfg["cloud_view_key"] = base64.urlsafe_b64encode(secrets.token_bytes(16)).decode().rstrip("=")
            new_secret = True
        elif ask("Have your Akahu tokens or Swyftx key changed since you set this up? [y/N] ").lower().startswith("y"):
            new_secret = True
    write_config(cfg)

    # 3. the code of the scheduled job, and your data (encrypted)
    say("Sending the scheduled job ...")
    files = {"README.md": PUBLIC_README.encode()}
    for src, dst in CODE_FILES.items():
        with open(os.path.join(HERE, src), "rb") as f:
            files[dst] = f.read()
    try:
        push_branch(token, repo, "main", files, "Scheduled job")
    except GitHubError as e:
        if e.code != 409:
            raise
        # a completely empty repository needs one ordinary file before anything else
        gh(token, "PUT", "/repos/%s/contents/README.md" % repo, {"message": "Start", "content": base64.b64encode(PUBLIC_README.encode()).decode()})
        time.sleep(2)
        push_branch(token, repo, "main", files, "Scheduled job")
    say("Sending your data, encrypted ...")
    push(cfg, db_path)

    # 4. the page
    pages = None
    try:
        pages = gh(token, "POST", "/repos/%s/pages" % repo, {"build_type": "workflow"}, ok=(409,))
        if pages is None:
            gh(token, "PUT", "/repos/%s/pages" % repo, {"build_type": "workflow"})
            pages = gh(token, "GET", "/repos/%s/pages" % repo)
    except GitHubError:
        say("\nGitHub wouldn't switch the page on automatically. A settings page is opening:")
        say("  under \"Build and deployment\", set Source to \"GitHub Actions\".")
        open_in_browser("https://github.com/%s/settings/pages" % repo)
        ask("  Press Return when that's done. ")
    if pages and pages.get("html_url"):
        cfg["cloud_url"] = pages["html_url"] if pages["html_url"].endswith("/") else pages["html_url"] + "/"
    write_config(cfg)

    # 5. the secret: your keys, handed to GitHub's secret store by you, so they never pass through anything else
    if new_secret:
        blob = json.dumps({"app_token": cfg.get("app_token", ""), "user_token": cfg.get("user_token", ""),
                           "swyftx_api_key": cfg.get("swyftx_api_key", ""), "master_key": cfg["cloud_master_key"],
                           "view_key": cfg["cloud_view_key"], "tz": local_timezone(), "owner": owner(cfg)})
        url = "https://github.com/%s/settings/secrets/actions/new" % repo
        exists = secret_exists(cfg)
        if exists:
            url = "https://github.com/%s/settings/secrets/actions/%s" % (repo, SECRET_NAME)
        say("\nStep 2. One paste. Your keys are now on the clipboard, and a GitHub page is opening.")
        paste = "Ctrl+V" if sys.platform == "win32" else "Cmd+V"
        if exists:
            say("  Click in the big box, paste (%s), and click \"Update secret\"." % paste)
        else:
            say("  In Name, type exactly:  %s" % SECRET_NAME)
            say("  Click in the big Secret box, paste (%s), and click \"Add secret\"." % paste)
        if not clipboard(blob):
            tmp = os.path.join(HERE, "paste-this-then-delete-me.txt")
            with open(tmp, "w") as f:
                f.write(blob)
            os.chmod(tmp, 0o600)
            say("  (Couldn't use the clipboard. Copy the contents of %s instead, then delete that file.)" % tmp)
        open_in_browser(url)
        say("  THEN COME BACK TO THIS WINDOW and press Return. Nothing starts until you do.")
        for attempt in range(4):
            ask("  Press Return here once it's saved. ")
            if secret_exists(cfg) is not False:
                break
            say("  GitHub doesn't have a secret called %s yet. Check the name is exactly that, paste again" % SECRET_NAME)
            say("  (it's still on the clipboard), and click the green button.")
        else:
            clipboard("")
            say("\nStopping here, because the phone version can't work without that step. Run this again when you're ready.")
            return
        clipboard("")

    # 6. first run
    say("\nStarting a sync on GitHub (about a minute) ")
    started = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(time.time() - 5))
    try:
        dispatch(cfg, patience=8)
        done = wait_for_run(cfg, started)
    except GitHubError as e:
        done = None
        say("Couldn't start it automatically (%s)." % e)
        say("Open https://github.com/%s/actions, choose \"sync\", and click \"Run workflow\"." % repo)
    say()
    if done and done.get("conclusion") == "success":
        say("It worked. While this computer is on, your phone matches it within a minute or so.")
        say("While it's off, GitHub keeps your phone up to date every 15 to 30 minutes.")
    elif done:
        say("The run on GitHub didn't finish cleanly.")
        for line in why_failed(cfg, done):
            say("  " + line)
        say("The page for it: %s" % done.get("html_url"))
        say("If it isn't obvious what to do, copy the lines above to Claude.")
    else:
        say("It's still going. Check on it at https://github.com/%s/actions" % repo)
    if done and done.get("conclusion") == "success":
        say("\nIn the app on this computer, type  phone  and point your phone's camera at the square.")
        say("Then on the phone: Share (iPhone) or the menu (Android), Add to Home Screen.")


def off():
    cfg = read_config()
    if not cfg.get("github_token") or not cfg.get("github_repo"):
        sys.exit("It isn't set up.")
    try:
        gh(cfg["github_token"], "PUT", "/repos/%s/actions/workflows/%s/disable" % (cfg["github_repo"], WORKFLOW))
        say("The scheduled sync is switched off.")
    except GitHubError as e:
        say("Couldn't switch it off automatically (%s)." % e)
    say("To remove everything, delete the repository: https://github.com/%s/settings (bottom of the page)," % cfg["github_repo"])
    say("and delete the token at https://github.com/settings/tokens")
    for k in ("cloud_view_key", "cloud_master_key", "cloud_url"):
        cfg.pop(k, None)
    write_config(cfg)
    say("This computer has stopped sending data. Run the phone setup again to turn it back on.")


def main():
    for stream in (sys.stdout, sys.stderr):          # never let an unusual character stop the setup on an old Windows console
        try:
            stream.reconfigure(errors="replace")
        except Exception:
            pass
    cmd = sys.argv[1] if len(sys.argv) > 1 else ""
    if cmd == "run" and len(sys.argv) > 2:
        return run(sys.argv[2])
    try:
        if cmd == "setup":
            return setup()
        if cmd == "off":
            return off()
        cfg = read_config()
        if not configured(cfg):
            sys.exit("It isn't set up yet. Double-click cloud-setup.command.")
        if cmd == "push":
            push(cfg, os.path.join(HERE, "finance.db"), run_now=True)
            return say("Sent. The page updates in about a minute.")
        if cmd == "link":
            return say(phone_link(cfg))
    except GitHubError as e:
        sys.exit(str(e))
    except urllib.error.URLError as e:
        sys.exit("Couldn't reach GitHub: %s" % e.reason)
    sys.exit(__doc__)


if __name__ == "__main__":
    main()
