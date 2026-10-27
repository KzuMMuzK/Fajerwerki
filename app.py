"""
Prywatna strona z cenami fajerwerków (Flask, Render): wejście tylko na zaproszenie, logowanie przez Discorda,
panel administratora (użytkownicy, zaproszenia, ręczna edycja produktów i cen, kolejność).

Dane o cenach: plik fajerwerki.db z prywatnego repo z danymi (GitHub API). Dane aplikacji (użytkownicy, zaproszenia,
ręczne zmiany): plik JSON na osobnej gałęzi tego samego repo (domyślnie app-data) - Render na darmowym planie nie
ma trwałego dysku, a w ten sposób nie potrzeba żadnej dodatkowej bazy. Gałąź tworzy się sama.

Zmienne środowiskowe (Render > Environment):
  DATA_REPO, DATA_TOKEN      repo z danymi i token GitHub (fine-grained: tylko to repo, Contents = Read and write)
  SECRET_KEY                 długi losowy ciąg (min. 24 znaki) do podpisywania sesji
  BASE_URL                   adres strony, np. https://fajerwerki.onrender.com (dokładnie taki, jak w Discordzie)
  DISCORD_CLIENT_ID, DISCORD_CLIENT_SECRET   z discord.com/developers/applications > OAuth2
  ADMIN_DISCORD_IDS          Twoje ID użytkownika Discord (kilka po przecinku) - te osoby zawsze są administratorami
  opcjonalnie: REFRESH_MINUTES (30), DATA_PATH, DATA_REF, APP_STATE_PATH, APP_STATE_BRANCH
  testy lokalne: DATA_FILE (plik .db zamiast GitHuba), STATE_FILE (plik JSON zamiast GitHuba)
"""
import base64
import copy
import csv
import hmac
import io
import json
import os
import re
import secrets
import shutil
import sqlite3
import threading
import time
import unicodedata
from datetime import datetime, timedelta, timezone
from functools import wraps
from urllib.parse import quote, urlencode, urlparse

import requests
from flask import (Flask, Response, abort, flash, g, get_flashed_messages, redirect, render_template, request,
                   session, url_for)
from jinja2 import DictLoader

try:
    from zoneinfo import ZoneInfo
    TZ = ZoneInfo("Europe/Warsaw")
except Exception:  # brak bazy stref czasowych
    TZ = timezone.utc


def _env(name, default=""):
    return os.environ.get(name, default).strip()


REPO, TOKEN = _env("DATA_REPO"), _env("DATA_TOKEN")
DATA_PATH, DATA_REF = _env("DATA_PATH", "fajerwerki.db"), _env("DATA_REF")
GITHUB_API = _env("GITHUB_API", "https://api.github.com").rstrip("/")
DATA_FILE = _env("DATA_FILE")
REFRESH_MIN = int(_env("REFRESH_MINUTES", "30") or 30)
WORK = _env("WORK_DIR", "/tmp/fajerwerki-site")
STATE_FILE = _env("STATE_FILE")
STATE_PATH, STATE_BRANCH = _env("APP_STATE_PATH", "app-state.json"), _env("APP_STATE_BRANCH", "app-data")
SECRET_KEY, BASE_URL = _env("SECRET_KEY"), _env("BASE_URL").rstrip("/")
DISCORD_CLIENT_ID, DISCORD_CLIENT_SECRET = _env("DISCORD_CLIENT_ID"), _env("DISCORD_CLIENT_SECRET")
DISCORD_API = _env("DISCORD_API", "https://discord.com/api").rstrip("/")
DISCORD_AUTH = _env("DISCORD_AUTH_URL", "https://discord.com/oauth2/authorize")
ADMIN_IDS = {x.strip() for x in _env("ADMIN_DISCORD_IDS").split(",") if x.strip()}
PER_PAGE = 40

app = Flask(__name__)
app.secret_key = SECRET_KEY or None
app.config.update(
    SESSION_COOKIE_NAME="fj_session", SESSION_COOKIE_HTTPONLY=True, SESSION_COOKIE_SAMESITE="Lax",
    SESSION_COOKIE_SECURE=BASE_URL.startswith("https://") and not _env("INSECURE_COOKIES"),
    PERMANENT_SESSION_LIFETIME=timedelta(days=30), MAX_CONTENT_LENGTH=64 * 1024,
)


# ----------------------------------------------------------------------------- formatowanie / czas
def parse_ts(ts):
    try:
        d = datetime.fromisoformat(ts)
    except (TypeError, ValueError):
        return None
    return d if d.tzinfo else d.replace(tzinfo=timezone.utc)


def now_iso():
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def fold(text):
    """Małe litery bez polskich znaków - do wyszukiwania."""
    text = (text or "").lower().replace("ł", "l")
    text = unicodedata.normalize("NFKD", text)
    return "".join(c for c in text if not unicodedata.combining(c))


def keyify(code):
    return "".join(c for c in (code or "").upper() if c.isalnum())


# ----------------------------------------------------------------------------- magazyn danych aplikacji
class StoreError(Exception):
    pass


class Conflict(Exception):
    pass


class Denied(Exception):
    """Odmowa z komunikatem dla użytkownika (np. zaproszenie wygasło)."""


DEFAULT_STATE = {"users": {}, "invites": {}, "overrides": {}, "audit": [],
                 "settings": {"member_invites": True, "default_quota": 3, "invite_days": 7}}


def _clean(msg):
    msg = str(msg)
    for secret in (TOKEN, SECRET_KEY, DISCORD_CLIENT_SECRET):
        if secret:
            msg = msg.replace(secret, "***")
    return msg[:200]


class Store:
    """Stan aplikacji w pamięci + trwały zapis do pliku JSON (GitHub albo plik lokalny). Zmiany zawsze przez update()."""

    def __init__(self):
        self.lock = threading.RLock()
        self.data, self.sha, self.loaded = None, None, False

    # --- GitHub
    def _gh(self, method, path, **kw):
        headers = {"Authorization": f"Bearer {TOKEN}", "Accept": "application/vnd.github+json",
                   "X-GitHub-Api-Version": "2022-11-28", "User-Agent": "fajerwerki-site"}
        try:
            return requests.request(method, f"{GITHUB_API}{path}", headers=headers, timeout=30, **kw)
        except requests.RequestException as e:
            raise StoreError(_clean(f"GitHub niedostępny: {e.__class__.__name__}"))

    def _ensure_branch(self):
        r = self._gh("GET", f"/repos/{REPO}/branches/{quote(STATE_BRANCH, safe='')}")
        if r.status_code == 200:
            return
        if r.status_code != 404:
            raise StoreError(f"GitHub: HTTP {r.status_code} przy sprawdzaniu gałęzi {STATE_BRANCH}")
        info = self._gh("GET", f"/repos/{REPO}")
        if info.status_code != 200:
            raise StoreError(f"GitHub: HTTP {info.status_code} (sprawdź DATA_REPO i uprawnienia DATA_TOKEN)")
        default = info.json().get("default_branch", "main")
        ref = self._gh("GET", f"/repos/{REPO}/git/ref/heads/{quote(default, safe='')}")
        if ref.status_code != 200:
            raise StoreError(f"GitHub: nie można odczytać gałęzi {default} (HTTP {ref.status_code})")
        cr = self._gh("POST", f"/repos/{REPO}/git/refs",
                      json={"ref": f"refs/heads/{STATE_BRANCH}", "sha": ref.json()["object"]["sha"]})
        if cr.status_code not in (201, 422):  # 422 = już istnieje
            raise StoreError(f"GitHub: nie udało się utworzyć gałęzi {STATE_BRANCH} (HTTP {cr.status_code}) - "
                             "token potrzebuje uprawnienia Contents: Read and write")

    def _read(self):
        if STATE_FILE:
            if not os.path.exists(STATE_FILE):
                return None, None
            with open(STATE_FILE, encoding="utf-8") as f:
                return json.load(f), None
        r = self._gh("GET", f"/repos/{REPO}/contents/{quote(STATE_PATH)}", params={"ref": STATE_BRANCH})
        if r.status_code == 404:
            return None, None
        if r.status_code != 200:
            raise StoreError(f"GitHub: HTTP {r.status_code} przy odczycie stanu aplikacji")
        j = r.json()
        return json.loads(base64.b64decode(j["content"]).decode("utf-8")), j["sha"]

    def _write(self, message):
        body = json.dumps(self.data, ensure_ascii=False, indent=1, sort_keys=True).encode("utf-8")
        if STATE_FILE:
            tmp = STATE_FILE + ".part"
            with open(tmp, "wb") as f:
                f.write(body)
            os.replace(tmp, STATE_FILE)
            return
        payload = {"message": message, "content": base64.b64encode(body).decode(), "branch": STATE_BRANCH}
        if self.sha:
            payload["sha"] = self.sha
        r = self._gh("PUT", f"/repos/{REPO}/contents/{quote(STATE_PATH)}", json=payload)
        if r.status_code in (409, 422):
            raise Conflict()
        if r.status_code not in (200, 201):
            raise StoreError(f"GitHub: HTTP {r.status_code} przy zapisie stanu aplikacji")
        self.sha = r.json()["content"]["sha"]

    def _merge_defaults(self, data):
        for k, v in DEFAULT_STATE.items():
            data.setdefault(k, copy.deepcopy(v))
        for k, v in DEFAULT_STATE["settings"].items():
            data["settings"].setdefault(k, v)
        return data

    def _load(self):
        if not STATE_FILE:
            self._ensure_branch()
        data, sha = self._read()
        self.data, self.sha = self._merge_defaults(data or {}), sha
        self.loaded = True

    def ensure(self):
        with self.lock:
            if not self.loaded:
                self._load()

    def read(self, fn):
        with self.lock:
            self.ensure()
            return fn(self.data)

    def update(self, fn, message="app-state"):
        """fn(data) zmienia stan i może zwrócić wynik; przy błędzie zapisu stan wraca do poprzedniego."""
        with self.lock:
            self.ensure()
            for _ in range(3):
                snapshot = copy.deepcopy(self.data)
                try:
                    result = fn(self.data)
                    self._write(message)
                    return result
                except Conflict:      # ktoś zmienił plik w międzyczasie: wczytaj świeży stan i zastosuj zmianę jeszcze raz
                    self.data = snapshot
                    self._load()
                except BaseException:
                    self.data = snapshot
                    raise
            raise StoreError("Konflikt zapisu stanu aplikacji - spróbuj ponownie")

    def user(self, uid):
        u = self.read(lambda d: d["users"].get(uid))
        return dict(u) if u else None


store = Store()


def audit(data, who, action, target=""):
    data["audit"].append({"ts": now_iso(), "who": who, "action": action, "target": target[:120]})
    del data["audit"][:-500]


def is_admin(u):
    return bool(u) and (u.get("role") == "admin" or u.get("id") in ADMIN_IDS)


def invite_state(inv, now=None):
    if not inv:
        return "missing"
    if inv.get("revoked"):
        return "revoked"
    exp = parse_ts(inv.get("expires"))
    if exp and exp < (now or datetime.now(timezone.utc)):
        return "expired"
    if len(inv.get("uses", [])) >= int(inv.get("max_uses", 1)):
        return "used"
    return "ok"


INVITE_MSG = {"missing": "To zaproszenie nie istnieje.", "revoked": "To zaproszenie zostało wycofane.",
              "expired": "To zaproszenie wygasło.", "used": "To zaproszenie zostało już wykorzystane."}


def active_invites(data, uid):
    return sum(1 for i in data["invites"].values() if i.get("by") == uid and invite_state(i) == "ok")


def make_invite(data, uid, admin, max_uses=1, days=None, note=""):
    st = data["settings"]
    if not admin:
        if not st.get("member_invites"):
            raise Denied("Zapraszanie przez członków jest wyłączone.")
        quota = int(data["users"].get(uid, {}).get("quota", st.get("default_quota", 3)))
        if active_invites(data, uid) >= quota:
            raise Denied(f"Masz już {quota} aktywnych zaproszeń - poczekaj, aż ktoś je wykorzysta, albo wycofaj stare.")
        max_uses = 1
    days = max(1, min(int(days or st.get("invite_days", 7)), 90))
    code = secrets.token_urlsafe(16)
    data["invites"][code] = {"by": uid, "created": now_iso(), "revoked": False, "uses": [], "note": note[:60],
                             "max_uses": max(1, min(int(max_uses), 50)),
                             "expires": (datetime.now(timezone.utc) + timedelta(days=days)).isoformat(timespec="seconds")}
    audit(data, uid, "invite_create", note[:60])
    return code


def descendants(data, uid):
    out, queue_ = [], [uid]
    while queue_:
        cur = queue_.pop()
        for u in data["users"].values():
            if u.get("invited_by") == cur and u["id"] not in out and u["id"] != uid:
                out.append(u["id"])
                queue_.append(u["id"])
    return out


def new_user(profile, role, invited_by):
    return {"id": profile["id"], "name": profile["name"], "username": profile["username"], "avatar": profile["avatar"],
            "role": role, "invited_by": invited_by, "joined": now_iso(), "last_login": now_iso(), "banned": False}


def login_or_join(data, profile, invite_code):
    """Istniejący użytkownik loguje się; nowy musi mieć ważne zaproszenie (albo być administratorem z ADMIN_DISCORD_IDS)."""
    uid, users = profile["id"], data["users"]
    u = users.get(uid)
    if u:
        if u.get("banned") and uid not in ADMIN_IDS:
            raise Denied("Twoje konto zostało zablokowane.")
        u.update(name=profile["name"], username=profile["username"], avatar=profile["avatar"], last_login=now_iso())
        if uid in ADMIN_IDS:
            u["role"] = "admin"
        return u
    if invite_code:
        inv = data["invites"].get(invite_code)
        st = invite_state(inv)
        if st != "ok":
            raise Denied(INVITE_MSG[st])
        inviter = users.get(inv["by"])
        if not inviter or inviter.get("banned"):
            raise Denied(INVITE_MSG["revoked"])
        users[uid] = new_user(profile, "member", inv["by"])
        inv["uses"].append({"user": uid, "ts": now_iso()})
        audit(data, uid, "join", f"zaproszenie od {inv['by']}")
        return users[uid]
    if uid in ADMIN_IDS:
        users[uid] = new_user(profile, "admin", None)
        audit(data, uid, "join", "administrator z konfiguracji")
        return users[uid]
    raise Denied("Ta strona jest prywatna. Wejść można tylko z zaproszenia od kogoś, kto już ma dostęp.")


def user_action(data, actor, uid, act, extra=""):
    u = data["users"].get(uid)
    if not u:
        raise Denied("Nie ma takiego użytkownika.")
    if act in ("ban", "ban_tree", "demote", "remove") and (uid in ADMIN_IDS or uid == actor):
        raise Denied("Tego konta nie można zablokować, zdegradować ani usunąć (administrator z konfiguracji albo Ty sam).")

    def revoke_invites(x):
        for inv in data["invites"].values():
            if inv.get("by") == x:
                inv["revoked"] = True

    if act == "promote":
        u["role"] = "admin"
    elif act == "demote":
        u["role"] = "member"
    elif act in ("ban", "ban_tree"):
        targets = [uid] + (descendants(data, uid) if act == "ban_tree" else [])
        for t in targets:
            if t in ADMIN_IDS:
                continue
            data["users"][t]["banned"] = True
            revoke_invites(t)
        act = f"{act}({len(targets)})"
    elif act == "unban":
        u["banned"] = False
    elif act == "quota":
        u["quota"] = max(0, min(int(extra), 50))
    elif act == "remove":
        revoke_invites(uid)
        del data["users"][uid]
    else:
        raise Denied("Nieznana akcja.")
    audit(data, actor, "user_" + act, uid)


# ----------------------------------------------------------------------------- dane o cenach
_lock = threading.Lock()
_state = {"checked": 0.0, "etag": None, "mtime": None, "derived": None, "loaded_at": None, "error": None}


def _clean_err(e):
    return _clean(f"{e.__class__.__name__}: {e}")


def _fetch_github(src):
    """Pobiera bazę cen z GitHuba. True = nowa wersja, False = bez zmian (304)."""
    if not REPO or not TOKEN:
        raise RuntimeError("Ustaw DATA_REPO i DATA_TOKEN w zmiennych środowiskowych")
    headers = {"Authorization": f"Bearer {TOKEN}", "Accept": "application/vnd.github.raw+json",
               "X-GitHub-Api-Version": "2022-11-28", "User-Agent": "fajerwerki-site"}
    if _state["etag"] and os.path.exists(src):
        headers["If-None-Match"] = _state["etag"]
    params = {"ref": DATA_REF} if DATA_REF else None
    r = requests.get(f"{GITHUB_API}/repos/{REPO}/contents/{quote(DATA_PATH)}", headers=headers,
                     params=params, timeout=90, stream=True)
    if r.status_code == 304:
        return False
    if r.status_code == 404:
        raise RuntimeError(f"Nie znaleziono {DATA_PATH} w {REPO} (albo token nie ma dostępu do repo)")
    if r.status_code in (401, 403):
        raise RuntimeError(f"GitHub odmówił dostępu (HTTP {r.status_code}) - sprawdź DATA_TOKEN")
    r.raise_for_status()
    tmp = src + ".part"
    with open(tmp, "wb") as f:
        for chunk in r.iter_content(1 << 20):
            f.write(chunk)
    os.replace(tmp, src)
    _state["etag"] = r.headers.get("ETag")
    return True


def _recompute_keys(c, keys=None):
    """Liczba sklepów i najniższa dostępna cena dla każdego kodu (dla wszystkich albo wskazanych)."""
    sql = """UPDATE items SET key_shops = (SELECT COUNT(DISTINCT i2.site) FROM items i2 WHERE i2.code_key = items.code_key AND i2.hidden = 0),
                 key_min = (SELECT MIN(i2.price) FROM items i2 WHERE i2.code_key = items.code_key AND i2.hidden = 0
                            AND i2.avail = 'in_stock' AND i2.price IS NOT NULL)
             WHERE code_key IS NOT NULL"""
    if keys is None:
        c.execute(sql)
    else:
        for k in [k for k in keys if k]:
            c.execute(sql + " AND code_key = ?", (k,))


def _apply_override(c, url, ov):
    """Nakłada ręczne zmiany (ov) na wiersz produktu; ov=None przywraca dane ze scrapera."""
    row = c.execute("SELECT o_name, o_price, o_avail, o_code, o_key, o_prev, o_drop FROM items WHERE url = ?", (url,)).fetchone()
    if not row:
        return None
    o_name, o_price, o_avail, o_code, o_key, o_prev, o_drop = row
    ov = ov or {}
    name = ov.get("name") or o_name
    price = ov["price"] if ov.get("price") is not None else o_price
    avail = ov.get("avail") or o_avail
    code, key = (ov["code"], keyify(ov["code"])) if ov.get("code") else (o_code, o_key)
    prev, drop = (None, None) if ov.get("price") is not None else (o_prev, o_drop)
    c.execute("""UPDATE items SET name = ?, name_norm = ?, price = ?, avail = ?, code = ?, code_key = ?, prev_price = ?,
                 drop_pct = ?, hidden = ?, rank = ?, note = ?, edited = ? WHERE url = ?""",
              (name, fold(name), price, avail, code, key, prev, drop, 1 if ov.get("hidden") else 0,
               ov.get("rank"), ov.get("note"), 1 if ov else 0, url))
    return o_key


def _build_derived(src, dst):
    """Z bazy scrapera robi płaską tabelę 'items' (ostatnia cena, poprzednia cena, min/max...) i nakłada ręczne zmiany."""
    con = sqlite3.connect(src)
    cols = {r[1] for r in con.execute("PRAGMA table_info(products)")}
    code_sel = "p.code, p.code_key" if "code_key" in cols else "NULL, NULL"
    rows = con.execute(f"""
        SELECT p.url, p.site, p.name, {code_sel}, p.first_seen, p.last_seen,
               cur.price, cur.availability, cur.ts, cur.currency,
               (SELECT price FROM prices WHERE url = p.url AND price IS NOT NULL AND price IS NOT cur.price
                ORDER BY id DESC LIMIT 1),
               (SELECT availability FROM prices WHERE url = p.url AND id < cur.id ORDER BY id DESC LIMIT 1),
               (SELECT MIN(price) FROM prices WHERE url = p.url AND price IS NOT NULL),
               (SELECT MAX(price) FROM prices WHERE url = p.url AND price IS NOT NULL),
               (SELECT COUNT(*) FROM prices WHERE url = p.url)
        FROM products p JOIN prices cur ON cur.id = (SELECT MAX(id) FROM prices WHERE url = p.url)
    """).fetchall()
    con.close()
    if os.path.exists(dst):
        os.remove(dst)
    out = sqlite3.connect(dst)
    out.executescript("""
        CREATE TABLE items(url TEXT PRIMARY KEY, site TEXT, name TEXT, name_norm TEXT, code TEXT, code_key TEXT,
            first_seen TEXT, last_seen TEXT, price REAL, avail TEXT, changed_at TEXT, currency TEXT,
            prev_price REAL, prev_avail TEXT, min_price REAL, max_price REAL, n_changes INTEGER,
            drop_pct REAL, key_shops INTEGER, key_min REAL,
            o_name TEXT, o_price REAL, o_avail TEXT, o_code TEXT, o_key TEXT, o_prev REAL, o_drop REAL,
            hidden INTEGER DEFAULT 0, rank INTEGER, note TEXT, edited INTEGER DEFAULT 0);
        CREATE INDEX ix_site ON items(site); CREATE INDEX ix_key ON items(code_key);
        CREATE INDEX ix_changed ON items(changed_at);
        CREATE TABLE meta(k TEXT PRIMARY KEY, v TEXT);
    """)
    batch = []
    for (url, site, name, code, key, first, last, price, av, ts, cur, prev, prev_av, mn, mx, n) in rows:
        pct = (prev - price) * 100.0 / prev if (prev and price is not None and prev > 0) else None
        batch.append((url, site, name, fold(name), code, key, first, last, price, av, ts, cur or "PLN", prev, prev_av,
                      mn, mx, n, pct, None, None, name, price, av, code, key, prev, pct, 0, None, None, 0))
    out.executemany("INSERT INTO items VALUES(" + ",".join("?" * 31) + ")", batch)
    try:  # ręczne zmiany z magazynu aplikacji; brak magazynu nie blokuje pokazania cen
        overrides = store.read(lambda d: copy.deepcopy(d["overrides"]))
    except Exception:
        overrides = {}
    for url, ov in overrides.items():
        _apply_override(out, url, ov)
    _recompute_keys(out)
    out.execute("INSERT INTO meta VALUES('last_seen', (SELECT MAX(last_seen) FROM items))")
    out.execute("INSERT INTO meta VALUES('has_codes', ?)", ("1" if "code_key" in cols else "0",))
    out.commit()
    out.close()


def ensure_data(force=False):
    """Odświeża dane, jeśli minęło REFRESH_MINUTES. Zwraca ścieżkę do tabeli pomocniczej albo None."""
    with _lock:
        now = time.time()
        have = bool(_state["derived"]) and os.path.exists(_state["derived"])
        if have and not force and now - _state["checked"] < REFRESH_MIN * 60:
            return _state["derived"]
        try:
            os.makedirs(WORK, exist_ok=True)
            src = os.path.join(WORK, "src.db")
            if DATA_FILE:
                m = os.path.getmtime(DATA_FILE)
                changed = m != _state["mtime"]
                if changed:
                    shutil.copyfile(DATA_FILE, src)
                    _state["mtime"] = m
            else:
                changed = _fetch_github(src)
            if changed or not have or force:
                dst = os.path.join(WORK, f"derived-{int(now * 1000)}.db")
                _build_derived(src, dst)
                old, _state["derived"] = _state["derived"], dst
                _state["loaded_at"] = now
                if old and old != dst and os.path.exists(old):
                    os.remove(old)
            _state["error"] = None
        except Exception as e:
            _state["error"] = _clean_err(e)
        finally:
            _state["checked"] = now
        return _state["derived"] if _state["derived"] and os.path.exists(_state["derived"]) else None


def conn():
    path = ensure_data()
    if not path:
        abort(Response(render_template("error.html", msg=_state["error"] or "Brak danych"), 503))
    c = sqlite3.connect(f"file:{path}?mode=ro", uri=True)
    c.row_factory = sqlite3.Row
    return c


def apply_live(url):
    """Po zmianie ręcznej od razu nakłada ją na bieżącą tabelę (bez ponownego pobierania bazy)."""
    path = _state.get("derived")
    if not path or not os.path.exists(path):
        return
    ov = store.read(lambda d: copy.deepcopy(d["overrides"].get(url)))
    c = sqlite3.connect(path, timeout=10)
    try:
        before = c.execute("SELECT code_key FROM items WHERE url = ?", (url,)).fetchone()
        o_key = _apply_override(c, url, ov)
        after = c.execute("SELECT code_key FROM items WHERE url = ?", (url,)).fetchone()
        _recompute_keys(c, {before[0] if before else None, after[0] if after else None, o_key})
        c.commit()
    finally:
        c.close()


def history(url):
    src = os.path.join(WORK, "src.db")
    c = sqlite3.connect(f"file:{src}?mode=ro", uri=True)
    try:
        return c.execute("SELECT ts, price, availability FROM prices WHERE url = ? ORDER BY id", (url,)).fetchall()
    finally:
        c.close()


# ----------------------------------------------------------------------------- dostęp: sesja, CSRF, Discord
PUBLIC = {"health", "robots", "login", "invite_page", "auth_discord", "auth_callback", "logout"}


def csrf_token():
    if "csrf" not in session:
        session["csrf"] = secrets.token_urlsafe(24)
    return session["csrf"]


def safe_next(n):
    n = n or ""
    return n if n.startswith("/") and not n.startswith("//") and "\\" not in n and len(n) < 300 else "/"


def config_missing():
    miss = []
    for name, val in (("SECRET_KEY (min. 24 znaki)", len(SECRET_KEY) >= 24), ("BASE_URL", BASE_URL),
                      ("DISCORD_CLIENT_ID", DISCORD_CLIENT_ID), ("DISCORD_CLIENT_SECRET", DISCORD_CLIENT_SECRET),
                      ("ADMIN_DISCORD_IDS", ADMIN_IDS), ("DATA_REPO i DATA_TOKEN", STATE_FILE or (REPO and TOKEN))):
        if not val:
            miss.append(name)
    return miss


@app.errorhandler(StoreError)
def store_error(e):
    return Response(render_template("error.html", msg=_clean(e)), 503)


@app.before_request
def guard():
    g.user = None
    if request.path in ("/health", "/robots.txt"):
        return None
    miss = config_missing()
    if miss:
        return Response(render_template("setup.html", miss=miss), 503)
    if request.method == "POST":
        sent = request.form.get("csrf", "")
        if not session.get("csrf") or not hmac.compare_digest(session["csrf"], sent):
            abort(403)
    uid = session.get("uid")
    if uid:
        u = store.user(uid)
        if u and (not u.get("banned") or uid in ADMIN_IDS):
            g.user = u
        else:
            session.clear()
    if request.endpoint in PUBLIC or g.user:
        return None
    if request.method == "GET":
        return redirect(url_for("login", next=request.full_path.rstrip("?")))
    abort(403)


def admin_required(fn):
    @wraps(fn)
    def wrapper(*a, **kw):
        if not is_admin(g.user):
            abort(403)
        return fn(*a, **kw)
    return wrapper


@app.after_request
def headers(resp):
    resp.headers["Cache-Control"] = "no-store"
    resp.headers["X-Robots-Tag"] = "noindex, nofollow"
    resp.headers["X-Content-Type-Options"] = "nosniff"
    resp.headers["X-Frame-Options"] = "DENY"
    resp.headers["Referrer-Policy"] = "no-referrer"
    resp.headers["Content-Security-Policy"] = ("default-src 'none'; style-src 'unsafe-inline'; img-src 'self' data: "
                                               "https://cdn.discordapp.com; form-action 'self'; base-uri 'none'; frame-ancestors 'none'")
    return resp


@app.route("/health")
def health():
    return "ok"


@app.route("/robots.txt")
def robots():
    return Response("User-agent: *\nDisallow: /\n", mimetype="text/plain")


@app.route("/login")
def login():
    if g.user:
        return redirect(safe_next(request.args.get("next")))
    session["next"] = safe_next(request.args.get("next"))
    return render_template("login.html")


@app.route("/invite/<code>")
def invite_page(code):
    def info(d):
        inv = d["invites"].get(code)
        by = d["users"].get(inv["by"], {}) if inv else {}
        return invite_state(inv), by.get("name") or by.get("username") or "członka grupy"
    st, inviter = store.read(info)
    if g.user:
        return redirect(url_for("index"))
    if st != "ok":
        return render_template("denied.html", msg=INVITE_MSG[st]), 410
    session["invite"] = code
    return render_template("invite.html", inviter=inviter)


@app.route("/auth/discord")
def auth_discord():
    state = secrets.token_urlsafe(24)
    session["oauth_state"] = state
    params = {"client_id": DISCORD_CLIENT_ID, "redirect_uri": BASE_URL + "/auth/discord/callback", "response_type": "code",
              "scope": "identify", "state": state, "prompt": "none"}
    return redirect(DISCORD_AUTH + "?" + urlencode(params))


def discord_profile(code):
    try:
        t = requests.post(f"{DISCORD_API}/oauth2/token", timeout=20, headers={"User-Agent": "fajerwerki-site"},
                          data={"client_id": DISCORD_CLIENT_ID, "client_secret": DISCORD_CLIENT_SECRET,
                                "grant_type": "authorization_code", "code": code,
                                "redirect_uri": BASE_URL + "/auth/discord/callback"})
        if t.status_code != 200:
            raise Denied("Discord odrzucił logowanie (kod wygasł albo konfiguracja aplikacji jest niepoprawna).")
        me = requests.get(f"{DISCORD_API}/users/@me", timeout=20, headers={
            "Authorization": "Bearer " + t.json()["access_token"], "User-Agent": "fajerwerki-site"})
        if me.status_code != 200:
            raise Denied("Nie udało się pobrać profilu z Discorda.")
        j = me.json()
    except requests.RequestException:
        raise Denied("Discord jest chwilowo niedostępny - spróbuj za chwilę.")
    uid = str(j["id"])
    name = (j.get("global_name") or j.get("username") or uid)[:40]
    avatar = (f"https://cdn.discordapp.com/avatars/{uid}/{j['avatar']}.png?size=64" if j.get("avatar")
              else f"https://cdn.discordapp.com/embed/avatars/{(int(uid) >> 22) % 6}.png")
    return {"id": uid, "name": name, "username": str(j.get("username", ""))[:40], "avatar": avatar}


@app.route("/auth/discord/callback")
def auth_callback():
    if request.args.get("error"):
        return render_template("denied.html", msg="Logowanie przez Discord zostało anulowane."), 400
    state = session.pop("oauth_state", None)
    if not state or not hmac.compare_digest(state, request.args.get("state", "")) or not request.args.get("code"):
        return render_template("denied.html", msg="Sesja logowania wygasła - spróbuj jeszcze raz."), 400
    invite_code, nxt = session.get("invite"), safe_next(session.get("next"))
    try:
        profile = discord_profile(request.args["code"])
        user = store.update(lambda d: dict(login_or_join(d, profile, invite_code)), "app-state: logowanie")
    except Denied as e:
        session.pop("invite", None)
        return render_template("denied.html", msg=str(e)), 403
    session.clear()
    session.permanent = True
    session["uid"] = user["id"]
    csrf_token()
    return redirect(nxt)


@app.route("/logout", methods=["POST"])
def logout():
    session.clear()
    return redirect(url_for("login"))


# ----------------------------------------------------------------------------- formatowanie w szablonach
@app.template_filter("dt")
def f_dt(ts, fmt="%d.%m %H:%M"):
    d = parse_ts(ts)
    return d.astimezone(TZ).strftime(fmt) if d else ""


@app.template_filter("pln")
def f_pln(x):
    if x is None:
        return "–"
    return f"{x:,.2f}".replace(",", "\u00a0").replace(".", ",") + "\u00a0zł"


@app.template_filter("shops")
def f_shops(n):
    n = int(n or 0)
    if n == 1:
        return "1 sklep"
    return f"{n} sklepy" if 2 <= n % 10 <= 4 and not 12 <= n % 100 <= 14 else f"{n} sklepów"


@app.template_filter("pct")
def f_pct(x):
    return "" if x is None else f"{abs(x):.0f}%"


@app.context_processor
def helpers():
    def url_with(**kw):
        args = request.args.to_dict(flat=False)
        for k, v in kw.items():
            if v is None:
                args.pop(k, None)
            else:
                args[k] = v if isinstance(v, list) else [v]
        return request.path + ("?" + urlencode(args, doseq=True) if args else "")

    def export_url():
        args = request.args.to_dict(flat=False)
        for k in ("page", "s"):
            args.pop(k, None)
        return url_for("export_csv") + ("?" + urlencode(args, doseq=True) if args else "")
    user = g.get("user")
    return {"url_with": url_with, "export_url": export_url, "user": user, "is_admin": is_admin(user),
            "csrf": csrf_token(), "base_url": BASE_URL, "messages": get_flashed_messages(with_categories=True)}


def chart_svg(hist, last_seen, w=340, h=150):
    """Wykres schodkowy ceny (SVG) z zaznaczonymi okresami braku towaru."""
    pts = [(parse_ts(ts), p, av) for ts, p, av in hist if p is not None and parse_ts(ts)]
    if not pts:
        return ""
    t0 = pts[0][0]
    t1 = max(pts[-1][0], parse_ts(last_seen) or pts[-1][0])
    span = max((t1 - t0).total_seconds(), 1.0)
    lo, hi = min(p for _, p, _ in pts), max(p for _, p, _ in pts)
    if hi - lo < 0.01:
        lo, hi = lo - 1, hi + 1
    L, R, T, B = 44, 8, 8, 20
    X = lambda t: L + (w - L - R) * ((t - t0).total_seconds() / span)
    Y = lambda p: T + (h - T - B) * (1 - (p - lo) / (hi - lo))
    d, shade = [], []
    for i, (t, p, av) in enumerate(pts):
        x, y = X(t), Y(p)
        d.append(f"M{x:.1f},{y:.1f}" if i == 0 else f"H{x:.1f}V{y:.1f}")
        nxt = X(pts[i + 1][0]) if i + 1 < len(pts) else X(t1)
        if av == "out_of_stock":
            shade.append(f'<rect x="{x:.1f}" y="{T}" width="{max(nxt - x, 1):.1f}" height="{h - T - B}" class="oos"/>')
    d.append(f"H{X(t1):.1f}")
    dots = f'<circle cx="{X(t1):.1f}" cy="{Y(pts[-1][1]):.1f}" r="3.5" class="dot"/>'
    fmt = lambda t: t.astimezone(TZ).strftime("%d.%m")
    return (f'<svg viewBox="0 0 {w} {h}" class="chart" role="img" aria-label="Historia ceny">'
            f'{"".join(shade)}<path d="{"".join(d)}" class="line"/>{dots}'
            f'<text x="2" y="{T + 9}" class="ax">{hi:.0f} zł</text><text x="2" y="{h - B}" class="ax">{lo:.0f} zł</text>'
            f'<text x="{L}" y="{h - 4}" class="ax">{fmt(t0)}</text>'
            f'<text x="{w - R}" y="{h - 4}" class="ax" text-anchor="end">{fmt(t1)}</text></svg>')


# ----------------------------------------------------------------------------- produkty (dla członków)
SORTS = {
    "manual": ("kolejność strony (przypięte na górze)", "rank IS NULL, rank ASC, changed_at DESC"),
    "new": ("najnowsze zmiany", "changed_at DESC"),
    "price_asc": ("cena rosnąco", "price IS NULL, price ASC"),
    "price_desc": ("cena malejąco", "price DESC"),
    "drop": ("największa obniżka", "drop_pct IS NULL, drop_pct DESC"),
    "name": ("nazwa A-Z", "name_norm ASC"),
    "site": ("sklep", "site, name_norm"),
}


def vis(prefix=" AND "):
    """Ukryte produkty widzi tylko administrator."""
    return "" if is_admin(g.user) else prefix + "hidden = 0"


def build_filters():
    q = request.args.get("q", "").strip()
    where, args = [], []
    for w in fold(q).split():
        key = keyify(w)
        where.append("(name_norm LIKE ? OR code_key LIKE ?)")
        args += [f"%{w}%", f"%{key}%" if key else "%\u0000%"]
    sites = [s for s in request.args.getlist("site") if s]
    if sites:
        where.append(f"site IN ({','.join('?' * len(sites))})")
        args += sites
    if request.args.get("a") == "1":
        where.append("avail = 'in_stock'")
    if request.args.get("d") == "1":
        cutoff = (datetime.now(timezone.utc) - timedelta(days=14)).isoformat(timespec="seconds")
        where.append("prev_price IS NOT NULL AND price < prev_price AND changed_at >= ?")
        args.append(cutoff)
    for param, op in (("min", ">="), ("max", "<=")):
        try:
            v = float(request.args.get(param, "").replace(",", "."))
            where.append(f"price {op} ?")
            args.append(v)
        except ValueError:
            pass
    if not is_admin(g.user):
        where.append("hidden = 0")
    return q, (" WHERE " + " AND ".join(where)) if where else "", args


def common_ctx(c):
    adm = is_admin(g.user)
    shops = c.execute("SELECT site, COUNT(*) n FROM items" + ("" if adm else " WHERE hidden = 0") + " GROUP BY site ORDER BY site").fetchall()
    meta = dict(c.execute("SELECT k, v FROM meta").fetchall())
    return {"shops": shops, "last_seen": meta.get("last_seen"), "has_codes": meta.get("has_codes") == "1",
            "refresh_error": _state["error"]}


@app.route("/")
def index():
    c = conn()
    q, where, args = build_filters()
    s = request.args.get("s") or ("price_asc" if q else "manual")
    order = SORTS.get(s, SORTS["manual"])[1]
    try:
        page = max(int(request.args.get("page", "1")), 1)
    except ValueError:
        page = 1
    total = c.execute("SELECT COUNT(*) FROM items" + where, args).fetchone()[0]
    items = c.execute(f"SELECT * FROM items{where} ORDER BY {order} LIMIT ? OFFSET ?",
                      args + [PER_PAGE, (page - 1) * PER_PAGE]).fetchall()
    return render_template("index.html", items=items, total=total, page=page, pages=max((total + PER_PAGE - 1) // PER_PAGE, 1),
                           q=q, s=s, sorts=SORTS, sel_sites=request.args.getlist("site"), tab="list", **common_ctx(c))


@app.route("/export.csv")
def export_csv():
    c = conn()
    q, where, args = build_filters()
    rows = c.execute(f"SELECT site, name, code, price, avail, changed_at, url FROM items{where} "
                     f"ORDER BY site, name_norm LIMIT 50000", args).fetchall()
    buf = io.StringIO()
    w = csv.writer(buf, delimiter=";")
    w.writerow(["sklep", "produkt", "kod", "cena", "dostepnosc", "zmiana", "link"])
    w.writerows([tuple(r) for r in rows])
    return Response("\ufeff" + buf.getvalue(), mimetype="text/csv",
                    headers={"Content-Disposition": "attachment; filename=fajerwerki.csv"})


@app.route("/p")
def product():
    c = conn()
    url = request.args.get("u", "")
    it = c.execute("SELECT * FROM items WHERE url = ?" + vis(), (url,)).fetchone()
    if not it:
        abort(404)
    hist = history(url)
    others = []
    if it["code_key"]:
        others = c.execute("SELECT * FROM items WHERE code_key = ? AND url != ?" + vis() +
                           " ORDER BY (avail = 'in_stock') DESC, price ASC", (it["code_key"], url)).fetchall()
    return render_template("product.html", it=it, hist=list(reversed(hist))[:40], chart=chart_svg(hist, it["last_seen"]),
                           others=others, tab="list", **common_ctx(c))


@app.route("/compare")
def compare():
    c = conn()
    key = request.args.get("k", "")
    rows = c.execute("SELECT * FROM items WHERE code_key = ?" + vis() + " ORDER BY (avail = 'in_stock') DESC, price ASC", (key,)).fetchall()
    if not rows:
        abort(404)
    return render_template("compare.html", rows=rows, key=key, tab="deals", **common_ctx(c))


@app.route("/deals")
def deals():
    c = conn()
    try:
        ms = float(request.args.get("ms", "5").replace(",", "."))
    except ValueError:
        ms = 5.0
    rows = c.execute(f"""
        SELECT code_key, MIN(code) AS code, MIN(name) AS name, COUNT(DISTINCT site) AS shops,
               COUNT(DISTINCT CASE WHEN avail = 'in_stock' AND price IS NOT NULL THEN site END) AS n_avail,
               MIN(CASE WHEN avail = 'in_stock' THEN price END) AS pmin,
               MAX(CASE WHEN avail = 'in_stock' THEN price END) AS pmax
        FROM items WHERE code_key IS NOT NULL{vis()}
        GROUP BY code_key
        HAVING n_avail >= 2 AND pmax > pmin * (1 + ? / 100.0)
        ORDER BY (pmax - pmin) / pmin DESC LIMIT 100""", (ms,)).fetchall()
    return render_template("deals.html", rows=rows, ms=ms, tab="deals", **common_ctx(c))


@app.route("/changes")
def changes():
    c = conn()
    t = request.args.get("t", "drops")
    try:
        days = min(max(int(request.args.get("days", "7")), 1), 90)
    except ValueError:
        days = 7
    cutoff = (datetime.now(timezone.utc) - timedelta(days=days)).isoformat(timespec="seconds")
    conds = {
        "drops": ("prev_price IS NOT NULL AND price < prev_price", "drop_pct DESC"),
        "rises": ("prev_price IS NOT NULL AND price > prev_price", "drop_pct ASC"),
        "back": ("prev_avail = 'out_of_stock' AND avail = 'in_stock'", "changed_at DESC"),
        "gone": ("prev_avail = 'in_stock' AND avail = 'out_of_stock'", "changed_at DESC"),
    }
    if t not in conds:
        t = "drops"
    counts = {k: c.execute(f"SELECT COUNT(*) FROM items WHERE changed_at >= ? AND {cond}{vis()}", (cutoff,)).fetchone()[0]
              for k, (cond, _) in conds.items()}
    rows = c.execute(f"SELECT * FROM items WHERE changed_at >= ? AND {conds[t][0]}{vis()} ORDER BY {conds[t][1]} LIMIT 200",
                     (cutoff,)).fetchall()
    return render_template("changes.html", rows=rows, t=t, days=days, counts=counts, tab="changes", **common_ctx(c))


# ----------------------------------------------------------------------------- zaproszenia (członkowie)
def _invite_rows(data, who=None):
    rows = []
    for code, inv in data["invites"].items():
        if who and inv.get("by") != who:
            continue
        by = data["users"].get(inv["by"], {})
        rows.append({"code": code, "state": invite_state(inv), "by": by.get("name", inv["by"]), "created": inv["created"],
                     "expires": inv["expires"], "max_uses": inv["max_uses"], "used": len(inv["uses"]), "note": inv.get("note", ""),
                     "users": [data["users"].get(u["user"], {}).get("name", u["user"]) for u in inv["uses"]]})
    rows.sort(key=lambda r: r["created"], reverse=True)
    return rows


@app.route("/invites", methods=["GET", "POST"])
def invites():
    if request.method == "POST":
        try:
            def go(d):
                return make_invite(d, g.user["id"], is_admin(g.user), request.form.get("max_uses", "1") or 1,
                                   request.form.get("days") or None, request.form.get("note", ""))
            store.update(go, "app-state: zaproszenie")
            flash("Zaproszenie utworzone - skopiuj link poniżej i wyślij osobie, którą zapraszasz.", "ok")
        except (Denied, ValueError) as e:
            flash(str(e) or "Niepoprawne dane.", "err")
        return redirect(url_for("invites"))
    me = g.user["id"]
    rows, left = store.read(lambda d: (_invite_rows(d, me), max(0, int(d["users"][me].get("quota", d["settings"]["default_quota"])) - active_invites(d, me))
                                      if d["settings"]["member_invites"] else 0))
    allowed = is_admin(g.user) or store.read(lambda d: d["settings"]["member_invites"])
    return render_template("invites.html", rows=rows, left=left, allowed=allowed, tab="", **_basic())


def _basic():
    return {"last_seen": None, "refresh_error": None}


@app.route("/invites/revoke", methods=["POST"])
def invite_revoke():
    code = request.form.get("code", "")

    def go(d):
        inv = d["invites"].get(code)
        if not inv or (inv["by"] != g.user["id"] and not is_admin(g.user)):
            raise Denied("Nie ma takiego zaproszenia.")
        inv["revoked"] = True
        audit(d, g.user["id"], "invite_revoke", inv.get("note", ""))
    try:
        store.update(go, "app-state: wycofanie zaproszenia")
        flash("Zaproszenie wycofane.", "ok")
    except Denied as e:
        flash(str(e), "err")
    return redirect(safe_next(request.form.get("back")) if request.form.get("back") else url_for("invites"))


# ----------------------------------------------------------------------------- panel administratora
@app.route("/admin")
@admin_required
def admin_home():
    stats = store.read(lambda d: {"users": len(d["users"]), "banned": sum(1 for u in d["users"].values() if u.get("banned")),
                                  "admins": sum(1 for u in d["users"].values() if is_admin(u)),
                                  "invites": sum(1 for i in d["invites"].values() if invite_state(i) == "ok"),
                                  "overrides": len(d["overrides"])})
    return render_template("admin_home.html", stats=stats, tab="admin", sub="home", **_basic())


@app.route("/admin/users", methods=["GET", "POST"])
@admin_required
def admin_users():
    if request.method == "POST":
        try:
            store.update(lambda d: user_action(d, g.user["id"], request.form.get("uid", ""), request.form.get("act", ""),
                                               request.form.get("extra", "")), "app-state: użytkownik")
            flash("Zapisano.", "ok")
        except (Denied, ValueError) as e:
            flash(str(e) or "Niepoprawne dane.", "err")
        return redirect(url_for("admin_users"))

    def rows(d):
        out = []
        for u in d["users"].values():
            by = d["users"].get(u.get("invited_by") or "", {})
            out.append({**u, "admin": is_admin(u), "locked": u["id"] in ADMIN_IDS or u["id"] == g.user["id"],
                        "by_name": by.get("name") if u.get("invited_by") else "—",
                        "quota_eff": u.get("quota", d["settings"]["default_quota"]), "children": len(descendants(d, u["id"])),
                        "active": active_invites(d, u["id"])})
        return sorted(out, key=lambda x: x["joined"])
    return render_template("admin_users.html", rows=store.read(rows), tab="admin", sub="users", **_basic())


@app.route("/admin/invites", methods=["GET", "POST"])
@admin_required
def admin_invites():
    if request.method == "POST":
        try:
            store.update(lambda d: make_invite(d, g.user["id"], True, request.form.get("max_uses", "1") or 1,
                                               request.form.get("days") or None, request.form.get("note", "")), "app-state: zaproszenie")
            flash("Zaproszenie utworzone.", "ok")
        except (Denied, ValueError) as e:
            flash(str(e) or "Niepoprawne dane.", "err")
        return redirect(url_for("admin_invites"))
    return render_template("admin_invites.html", rows=store.read(_invite_rows), tab="admin", sub="invites", **_basic())


@app.route("/admin/settings", methods=["GET", "POST"])
@admin_required
def admin_settings():
    if request.method == "POST":
        try:
            def go(d):
                d["settings"]["member_invites"] = request.form.get("member_invites") == "1"
                d["settings"]["default_quota"] = max(0, min(int(request.form.get("default_quota", "3")), 50))
                d["settings"]["invite_days"] = max(1, min(int(request.form.get("invite_days", "7")), 90))
                audit(d, g.user["id"], "settings", json.dumps(d["settings"]))
            store.update(go, "app-state: ustawienia")
            flash("Ustawienia zapisane.", "ok")
        except ValueError:
            flash("Niepoprawne liczby.", "err")
        return redirect(url_for("admin_settings"))
    return render_template("admin_settings.html", st=store.read(lambda d: dict(d["settings"])), tab="admin", sub="settings", **_basic())


@app.route("/admin/audit")
@admin_required
def admin_audit():
    def rows(d):
        names = {u["id"]: u.get("name", u["id"]) for u in d["users"].values()}
        return [{**a, "who_name": names.get(a["who"], a["who"])} for a in reversed(d["audit"][-150:])]
    return render_template("admin_audit.html", rows=store.read(rows), tab="admin", sub="audit", **_basic())


@app.route("/admin/refresh", methods=["POST"])
@admin_required
def admin_refresh():
    ensure_data(force=True)
    flash("Dane odświeżone." if not _state["error"] else "Błąd odświeżania: " + _state["error"], "ok" if not _state["error"] else "err")
    return redirect(url_for("admin_home"))


def _parse_override(form):
    ov = {}
    name = form.get("name", "").strip()
    if name:
        ov["name"] = name[:200]
    price = form.get("price", "").strip().replace(",", ".").replace(" ", "")
    if price:
        v = float(price)
        if not 0 < v < 1_000_000:
            raise ValueError("Cena musi być większa od 0.")
        ov["price"] = round(v, 2)
    avail = form.get("avail", "")
    if avail in ("in_stock", "out_of_stock"):
        ov["avail"] = avail
    code = form.get("code", "").strip()
    if code:
        if not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9./\- ]{1,38}", code) or len(keyify(code)) < 3:
            raise ValueError("Kod: 3-40 znaków (litery, cyfry, - / .).")
        ov["code"] = code.upper()
    rank = form.get("rank", "").strip()
    if rank:
        ov["rank"] = max(-1_000_000, min(int(rank), 1_000_000))
    if form.get("hidden") == "1":
        ov["hidden"] = True
    note = form.get("note", "").strip()
    if note:
        ov["note"] = note[:80]
    return ov


@app.route("/admin/product", methods=["GET", "POST"])
@admin_required
def admin_product():
    url = request.values.get("u", "")
    c = conn()
    it = c.execute("SELECT * FROM items WHERE url = ?", (url,)).fetchone()
    if not it:
        abort(404)
    if request.method == "POST":
        try:
            ov = {} if request.form.get("act") == "clear" else _parse_override(request.form)

            def go(d):
                if ov:
                    d["overrides"][url] = {**ov, "by": g.user["id"], "ts": now_iso()}
                else:
                    d["overrides"].pop(url, None)
                audit(d, g.user["id"], "product_edit" if ov else "product_clear", it["name"][:80])
            store.update(go, "app-state: produkt")
            apply_live(url)
            flash("Zapisano." if ov else "Przywrócono dane ze scrapera.", "ok")
        except (ValueError, Denied) as e:
            flash(str(e) or "Niepoprawne dane.", "err")
            return redirect(url_for("admin_product", u=url))
        return redirect(url_for("product", u=url))
    ov = store.read(lambda d: dict(d["overrides"].get(url, {})))
    return render_template("admin_product.html", it=it, ov=ov, tab="list", **common_ctx(c))


@app.route("/admin/quick", methods=["POST"])
@admin_required
def admin_quick():
    url, act = request.form.get("u", ""), request.form.get("act", "")
    c = conn()
    it = c.execute("SELECT name FROM items WHERE url = ?", (url,)).fetchone()
    if not it or act not in ("pin", "unpin", "hide", "unhide"):
        abort(400)
    min_rank = c.execute("SELECT MIN(rank) FROM items").fetchone()[0]

    def go(d):
        ov = d["overrides"].setdefault(url, {})
        if act == "pin":
            ov["rank"] = (min_rank - 1) if min_rank is not None else 1
        elif act == "unpin":
            ov.pop("rank", None)
        elif act == "hide":
            ov["hidden"] = True
        else:
            ov.pop("hidden", None)
        if not ov:
            d["overrides"].pop(url, None)
        else:
            ov["by"], ov["ts"] = g.user["id"], now_iso()
        audit(d, g.user["id"], "product_" + act, it["name"][:80])
    store.update(go, "app-state: produkt")
    apply_live(url)
    return redirect(safe_next(request.form.get("back")))


# ----------------------------------------------------------------------------- wygląd
CSS = """
:root{--bg:#f6f7f9;--card:#fff;--fg:#14171c;--mut:#667085;--line:#e4e7ec;--accent:#d92d20;--ok:#12b76a;--no:#98a2b3;--chip:#eef1f5}
@media(prefers-color-scheme:dark){:root{--bg:#0e1116;--card:#171b22;--fg:#eceff4;--mut:#98a2b3;--line:#2a303a;--accent:#ff6b5e;--chip:#222833}}
*{box-sizing:border-box}body{margin:0;background:var(--bg);color:var(--fg);font:16px/1.4 system-ui,-apple-system,Segoe UI,Roboto,sans-serif}
a{color:inherit;text-decoration:none}.wrap{max-width:760px;margin:0 auto;padding:0 12px 40px}
header{position:sticky;top:0;background:var(--bg);padding:8px 0;z-index:5;border-bottom:1px solid var(--line)}
.userbar{display:flex;gap:12px;align-items:center;font-size:14px;padding:8px 0 0;flex-wrap:wrap}.userbar a{color:var(--mut);text-decoration:underline}
.av{border-radius:50%;background:var(--chip)}.un{font-weight:600}.inl{display:inline;margin:0}.lnk{background:none;border:0;color:var(--mut);text-decoration:underline;padding:0;font:inherit;cursor:pointer;font-weight:400}
.tabs{display:flex;gap:6px;margin-bottom:8px}.tabs a{flex:1;text-align:center;padding:7px 4px;border-radius:10px;background:var(--chip);font-weight:600;font-size:14px}
.tabs.sub{flex-wrap:wrap}.tabs.sub a{font-size:13px;padding:6px 8px;flex:1 1 auto}.tabs a.on{background:var(--accent);color:#fff}
form.s{display:flex;gap:6px}input,select,textarea{font:inherit;color:inherit;background:var(--card);border:1px solid var(--line);border-radius:10px;padding:9px 10px;min-width:0;width:100%}
form.s input[type=search]{flex:1}input[type=checkbox]{width:auto}
button,.btn{font:inherit;background:var(--accent);color:#fff;border:0;border-radius:10px;padding:9px 14px;font-weight:600;cursor:pointer;display:inline-block;text-align:center}
.sec{background:var(--chip);color:var(--fg)}.dng{background:#b42318}.sm{padding:5px 10px;font-size:13px}
details{margin-top:8px}summary{color:var(--mut);cursor:pointer;font-size:14px}.f{display:grid;grid-template-columns:1fr 1fr;gap:8px;margin-top:8px}
.f label{font-size:13px;color:var(--mut);display:flex;flex-direction:column;gap:3px}.f .chk{flex-direction:row;align-items:center;gap:8px;font-size:15px;color:var(--fg)}
.meta{color:var(--mut);font-size:13px;margin:10px 2px}.card{background:var(--card);border:1px solid var(--line);border-radius:14px;padding:11px 12px;margin:8px 0}.card.dim{opacity:.55}
.top{display:flex;gap:6px;align-items:center;flex-wrap:wrap;font-size:12px;margin-bottom:4px}.shop{background:var(--chip);border-radius:6px;padding:1px 7px;font-weight:600}
.code{border:1px solid var(--line);border-radius:6px;padding:0 6px;color:var(--mut)}.dot{width:9px;height:9px;border-radius:50%;background:var(--no);margin-left:auto}.dot.ok{background:var(--ok)}
.name{font-weight:600;display:block;margin-bottom:6px}.row{display:flex;align-items:baseline;gap:8px;flex-wrap:wrap}.price{font-size:20px;font-weight:700}
.old{color:var(--mut);text-decoration:line-through;font-size:14px}.up,.down{font-size:13px;font-weight:700;border-radius:6px;padding:0 6px}.down{background:#d1fadf;color:#05603a}.up{background:#fee4e2;color:#b42318}
@media(prefers-color-scheme:dark){.down{background:#0b3d2a;color:#75e0a7}.up{background:#4a1a15;color:#fda29b}}
.best{background:#fef0c7;color:#93370d;font-size:12px;font-weight:700;border-radius:6px;padding:1px 7px}.mini{font-size:13px;color:var(--mut);margin-left:auto;text-decoration:underline}
.qa{display:flex;gap:6px;flex-wrap:wrap;margin-top:8px;align-items:center}.qa form{margin:0}.pager{display:flex;justify-content:space-between;align-items:center;margin:14px 0}.pager a{background:var(--chip);padding:9px 14px;border-radius:10px;font-weight:600}.pager .off{opacity:.35}
.chart{width:100%;height:auto;margin:6px 0}.chart .line{fill:none;stroke:var(--accent);stroke-width:2}.chart .dot{fill:var(--accent)}.chart .ax{font-size:10px;fill:var(--mut)}.chart .oos{fill:var(--no);opacity:.18}
table{width:100%;border-collapse:collapse;font-size:14px}td,th{padding:6px 4px;border-bottom:1px solid var(--line);text-align:left}h1{font-size:19px;margin:14px 0 4px}h2{font-size:16px;margin:18px 0 6px}
.err{background:#fee4e2;color:#7a271a;border-radius:10px;padding:8px 10px;margin:8px 0;font-size:14px}.okm{background:#d1fadf;color:#05603a;border-radius:10px;padding:8px 10px;margin:8px 0;font-size:14px}
.note{color:var(--mut);font-size:13px}.stats{display:flex;gap:8px;flex-wrap:wrap;margin:8px 0}.stat{background:var(--card);border:1px solid var(--line);border-radius:12px;padding:8px 12px}.stat b{display:block;font-size:18px}
.center{text-align:center;padding:40px 8px}.center h1{font-size:24px}.big{padding:13px 22px;font-size:17px;margin-top:14px;background:#5865f2}
.badge{font-size:11px;font-weight:700;border-radius:6px;padding:1px 7px;background:var(--chip)}.badge.a{background:#d1fadf;color:#05603a}.badge.r{background:#fee4e2;color:#b42318}
@media(prefers-color-scheme:dark){.badge.a{background:#0b3d2a;color:#75e0a7}.badge.r{background:#4a1a15;color:#fda29b}}
ul.clean{padding-left:18px;margin:6px 0}.who{display:flex;gap:8px;align-items:center}
"""

TEMPLATES = {
    "base.html": """<!doctype html><html lang="pl"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover">
<meta name="robots" content="noindex,nofollow"><title>{% block title %}Ceny fajerwerków{% endblock %}</title><style>{{ css|safe }}</style></head><body><div class="wrap">
{% if user %}<div class="userbar"><span class="who"><img class="av" src="{{ user.avatar }}" alt="" width="24" height="24"><span class="un">{{ user.name }}</span></span>
<a href="{{ url_for('invites') }}">Zaproszenia</a>{% if is_admin %}<a href="{{ url_for('admin_home') }}">Admin</a>{% endif %}
<form method="post" action="{{ url_for('logout') }}" class="inl"><input type="hidden" name="csrf" value="{{ csrf }}"><button class="lnk">Wyloguj</button></form></div>{% endif %}
<header>{% if user %}<nav class="tabs"><a href="{{ url_for('index') }}" class="{{ 'on' if tab=='list' }}">Produkty</a><a href="{{ url_for('deals') }}" class="{{ 'on' if tab=='deals' }}">Porównanie</a><a href="{{ url_for('changes') }}" class="{{ 'on' if tab=='changes' }}">Zmiany</a></nav>{% endif %}{% block head %}{% endblock %}</header>
{% for cat, msg in messages %}<div class="{{ 'err' if cat == 'err' else 'okm' }}">{{ msg }}</div>{% endfor %}
{% if refresh_error %}<div class="err">Nie udało się odświeżyć danych ({{ refresh_error }}). Pokazuję poprzednią wersję.</div>{% endif %}
{% block body %}{% endblock %}
{% if last_seen %}<p class="note">Dane z: {{ last_seen|dt('%d.%m.%Y %H:%M') }}. Kody produktów są wyciągane z nazw i mogą się mylić - przed zakupem sprawdź, czy to ten sam model.</p>{% endif %}
</div></body></html>""",

    "card.html": """{% macro card(it) %}<div class="card{{ ' dim' if it.hidden }}"><div class="top"><span class="shop">{{ it.site }}</span>{% if it.code %}<span class="code">{{ it.code }}</span>{% endif %}
{% if it.rank is not none %}<span class="code">przypięty</span>{% endif %}{% if it.hidden %}<span class="code">ukryty</span>{% endif %}{% if it.note %}<span class="best">{{ it.note }}</span>{% endif %}
{% if is_admin and it.edited %}<span class="code">edytowany</span>{% endif %}<span class="dot {{ 'ok' if it.avail=='in_stock' }}" title="{{ 'dostępny' if it.avail=='in_stock' else 'niedostępny' }}"></span></div>
<a class="name" href="{{ url_for('product', u=it.url) }}">{{ it.name }}</a><div class="row"><span class="price">{{ it.price|pln }}</span>
{% if it.prev_price and it.price is not none and it.price != it.prev_price %}<span class="old">{{ it.prev_price|pln }}</span><span class="{{ 'down' if it.price < it.prev_price else 'up' }}">{{ '−' if it.price < it.prev_price else '+' }}{{ it.drop_pct|pct }}</span>{% endif %}
{% if it.key_shops and it.key_shops > 1 %}{% if it.avail=='in_stock' and it.price is not none and it.price == it.key_min %}<span class="best">najtaniej</span>{% endif %}<a class="mini" href="{{ url_for('compare', k=it.code_key) }}">{{ it.key_shops|shops }}</a>{% endif %}
</div><div class="note">zmiana: {{ it.changed_at|dt }}</div>
{% if is_admin %}<form method="post" action="{{ url_for('admin_quick') }}" class="qa"><input type="hidden" name="csrf" value="{{ csrf }}"><input type="hidden" name="u" value="{{ it.url }}"><input type="hidden" name="back" value="{{ request.full_path.rstrip('?') }}">
<button class="sec sm" name="act" value="{{ 'unpin' if it.rank is not none else 'pin' }}">{{ 'Odepnij' if it.rank is not none else 'Przypnij na górze' }}</button>
<button class="sec sm" name="act" value="{{ 'unhide' if it.hidden else 'hide' }}">{{ 'Pokaż' if it.hidden else 'Ukryj' }}</button><a class="btn sm sec" href="{{ url_for('admin_product', u=it.url) }}">Edytuj</a></form>{% endif %}</div>{% endmacro %}""",

    "error.html": """<!doctype html><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><style>{{ css|safe }}</style>
<body><div class="wrap center"><h1>Coś poszło nie tak</h1><p>{{ msg }}</p><p class="note">Sprawdź zmienne DATA_REPO i DATA_TOKEN oraz czy plik fajerwerki.db jest w repo z danymi.</p></div></body>""",

    "setup.html": """<!doctype html><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><style>{{ css|safe }}</style>
<body><div class="wrap"><h1>Strona wymaga konfiguracji</h1><p>Brakuje zmiennych środowiskowych (Render, zakładka Environment):</p><ul class="clean">{% for m in miss %}<li><b>{{ m }}</b></li>{% endfor %}</ul>
<p class="note">Do czasu uzupełnienia strona jest zamknięta dla wszystkich.</p></div></body>""",

    "login.html": """{% extends 'base.html' %}{% block body %}<div class="center"><h1>Strona prywatna</h1><p>Wejście tylko dla osób, które dostały zaproszenie od kogoś z grupy.</p>
<a class="btn big" href="{{ url_for('auth_discord') }}">Zaloguj przez Discord</a><p class="note" style="margin-top:18px">Nie masz zaproszenia? Poproś o link kogoś, kto już ma dostęp.</p></div>{% endblock %}""",

    "invite.html": """{% extends 'base.html' %}{% block body %}<div class="center"><h1>Masz zaproszenie</h1><p>Zaprasza Cię: <b>{{ inviter }}</b>.</p>
<a class="btn big" href="{{ url_for('auth_discord') }}">Dołącz przez Discord</a><p class="note" style="margin-top:18px">Logujesz się kontem Discord. Strona widzi tylko Twoją nazwę i ID.</p></div>{% endblock %}""",

    "denied.html": """{% extends 'base.html' %}{% block body %}<div class="center"><h1>Brak dostępu</h1><p>{{ msg }}</p><p><a class="btn" href="{{ url_for('login') }}">Wróć do logowania</a></p></div>{% endblock %}""",

    "index.html": """{% extends 'base.html' %}{% from 'card.html' import card with context %}
{% block head %}<form class="s" method="get" action="{{ url_for('index') }}"><input type="search" name="q" value="{{ q }}" placeholder="nazwa lub kod, np. PXO310" autocomplete="off"><button style="width:auto">Szukaj</button></form>
<details {{ 'open' if request.args.get('site') or request.args.get('a') or request.args.get('d') or request.args.get('min') or request.args.get('max') or request.args.get('s') }}><summary>Filtry i sortowanie</summary>
<form method="get" class="f"><input type="hidden" name="q" value="{{ q }}">
<label>Sortuj<select name="s">{% for k,(label,_) in sorts.items() %}<option value="{{ k }}" {{ 'selected' if k==s }}>{{ label }}</option>{% endfor %}</select></label>
<label>Sklep<select name="site" multiple size="3">{% for sh in shops %}<option value="{{ sh.site }}" {{ 'selected' if sh.site in sel_sites }}>{{ sh.site }} ({{ sh.n }})</option>{% endfor %}</select></label>
<label>Cena od<input name="min" inputmode="decimal" value="{{ request.args.get('min','') }}"></label><label>Cena do<input name="max" inputmode="decimal" value="{{ request.args.get('max','') }}"></label>
<label class="chk"><input type="checkbox" name="a" value="1" {{ 'checked' if request.args.get('a')=='1' }}> tylko dostępne</label><label class="chk"><input type="checkbox" name="d" value="1" {{ 'checked' if request.args.get('d')=='1' }}> tylko obniżki (14 dni)</label>
<button style="grid-column:1/3">Zastosuj</button></form></details>{% endblock %}
{% block body %}<div class="meta">{{ total }} produktów · <a href="{{ export_url() }}" style="text-decoration:underline">pobierz CSV</a></div>
{% for it in items %}{{ card(it) }}{% else %}<div class="card">Brak wyników.</div>{% endfor %}
<div class="pager"><a class="{{ '' if page>1 else 'off' }}" href="{{ url_with(page=page-1) if page>1 else '#' }}">← wstecz</a><span class="note">{{ page }} / {{ pages }}</span><a class="{{ '' if page<pages else 'off' }}" href="{{ url_with(page=page+1) if page<pages else '#' }}">dalej →</a></div>{% endblock %}""",

    "product.html": """{% extends 'base.html' %}{% from 'card.html' import card with context %}
{% block body %}<h1>{{ it.name }}</h1><div class="top"><span class="shop">{{ it.site }}</span>{% if it.code %}<span class="code">{{ it.code }}</span>{% endif %}<span class="note">{{ 'dostępny' if it.avail=='in_stock' else 'niedostępny' }}</span>{% if it.note %}<span class="best">{{ it.note }}</span>{% endif %}</div>
<div class="stats"><div class="stat"><span class="note">teraz</span><b>{{ it.price|pln }}</b></div><div class="stat"><span class="note">najniżej</span><b>{{ it.min_price|pln }}</b></div><div class="stat"><span class="note">najwyżej</span><b>{{ it.max_price|pln }}</b></div></div>
{{ chart|safe }}{% if not chart %}<p class="note">Brak historii cen.</p>{% endif %}<p><a class="btn" href="{{ it.url }}" target="_blank" rel="noopener noreferrer">Otwórz w sklepie</a>
{% if is_admin %} <a class="btn sec" href="{{ url_for('admin_product', u=it.url) }}">Edytuj</a>{% endif %}</p>
{% if is_admin and it.edited %}<div class="note">Ten produkt ma ręczne zmiany (cena ze scrapera: {{ it.o_price|pln }}).</div>{% endif %}
{% if others %}<h2>Ten sam kod w innych sklepach</h2>{% for o in others %}{{ card(o) }}{% endfor %}{% endif %}
<h2>Historia zmian</h2><table><tr><th>kiedy</th><th>cena</th><th>stan</th></tr>{% for ts,p,av in hist %}<tr><td>{{ ts|dt('%d.%m.%Y %H:%M') }}</td><td>{{ p|pln }}</td><td>{{ 'dostępny' if av=='in_stock' else 'brak' }}</td></tr>{% endfor %}</table>{% endblock %}""",

    "compare.html": """{% extends 'base.html' %}{% from 'card.html' import card with context %}
{% block body %}<h1>Kod {{ rows[0].code or key }}</h1><p class="note">{{ rows|length }} ofert · najtańsza dostępna oznaczona jako „najtaniej". Sprawdź, czy nazwy to na pewno ten sam produkt.</p>
{% for r in rows %}{{ card(r) }}{% endfor %}{% endblock %}""",

    "deals.html": """{% extends 'base.html' %}
{% block head %}<form method="get" class="s"><input name="ms" inputmode="decimal" value="{{ ms|int if ms==ms|int else ms }}" style="width:90px"><span class="note" style="align-self:center">min. różnica % między sklepami</span><button style="width:auto">OK</button></form>{% endblock %}
{% block body %}{% if not has_codes %}<div class="err">Baza nie ma jeszcze kodów produktów - uruchom scraper, żeby je wyliczył.</div>{% endif %}
<div class="meta">Produkty z tym samym kodem dostępne w co najmniej 2 sklepach, od największej różnicy cen.</div>
{% for r in rows %}<div class="card"><div class="top"><span class="code">{{ r.code }}</span><span class="note">{{ r.n_avail|shops }} z towarem</span></div><a class="name" href="{{ url_for('compare', k=r.code_key) }}">{{ r.name }}</a>
<div class="row"><span class="price">{{ r.pmin|pln }}</span><span class="old">{{ r.pmax|pln }}</span><span class="down">−{{ ((r.pmax-r.pmin)*100/r.pmax)|round|int }}%</span></div></div>{% else %}<div class="card">Brak takich produktów.</div>{% endfor %}{% endblock %}""",

    "changes.html": """{% extends 'base.html' %}{% from 'card.html' import card with context %}
{% block head %}<nav class="tabs">{% for k,l in [('drops','Obniżki'),('rises','Podwyżki'),('back','Wróciły'),('gone','Zniknęły')] %}<a class="{{ 'on' if t==k }}" href="{{ url_for('changes', t=k, days=days) }}">{{ l }} {{ counts[k] }}</a>{% endfor %}</nav>
<form class="s" method="get"><input type="hidden" name="t" value="{{ t }}"><select name="days">{% for d in (1,3,7,14,30) %}<option value="{{ d }}" {{ 'selected' if d==days }}>ostatnie {{ d }} dni</option>{% endfor %}</select><button style="width:auto">OK</button></form>{% endblock %}
{% block body %}{% for r in rows %}{{ card(r) }}{% else %}<div class="card">Brak zmian w tym okresie.</div>{% endfor %}{% endblock %}""",

    "invites.html": """{% extends 'base.html' %}{% block body %}<h1>Zaproszenia</h1>
{% if allowed %}<form method="post" class="f"><input type="hidden" name="csrf" value="{{ csrf }}">
{% if is_admin %}<label>Ile osób może użyć<input name="max_uses" value="1" inputmode="numeric"></label><label>Ważne dni<input name="days" placeholder="domyślnie" inputmode="numeric"></label>{% endif %}
<label style="grid-column:1/3">Notatka (np. dla kogo)<input name="note" maxlength="60"></label><button style="grid-column:1/3">Utwórz zaproszenie</button></form>
{% if not is_admin %}<p class="note">Możesz utworzyć jeszcze {{ left }} {{ 'zaproszenie' if left == 1 else 'zaproszeń' }}.</p>{% endif %}
{% else %}<div class="card">Zapraszanie przez członków jest wyłączone przez administratora.</div>{% endif %}
{% for r in rows %}<div class="card"><div class="top"><span class="badge {{ 'a' if r.state=='ok' else 'r' }}">{{ {'ok':'aktywne','used':'wykorzystane','expired':'wygasło','revoked':'wycofane'}[r.state] }}</span>{% if r.note %}<span class="code">{{ r.note }}</span>{% endif %}<span class="note" style="margin-left:auto">{{ r.used }}/{{ r.max_uses }}</span></div>
{% if r.state=='ok' %}<input readonly value="{{ base_url }}/invite/{{ r.code }}" aria-label="Link zaproszenia"><div class="note">ważne do {{ r.expires|dt('%d.%m.%Y') }}</div>{% endif %}
{% if r.users %}<div class="note">dołączyli: {{ r.users|join(', ') }}</div>{% endif %}
{% if r.state=='ok' %}<form method="post" action="{{ url_for('invite_revoke') }}" class="qa"><input type="hidden" name="csrf" value="{{ csrf }}"><input type="hidden" name="code" value="{{ r.code }}"><button class="sec sm">Wycofaj</button></form>{% endif %}</div>
{% else %}<div class="card">Nie masz jeszcze zaproszeń.</div>{% endfor %}{% endblock %}""",

    "admin_base.html": """{% extends 'base.html' %}{% block head %}<nav class="tabs sub">{% for k,l,u in [('home','Przegląd','admin_home'),('users','Użytkownicy','admin_users'),('invites','Zaproszenia','admin_invites'),('settings','Ustawienia','admin_settings'),('audit','Dziennik','admin_audit')] %}<a class="{{ 'on' if sub==k }}" href="{{ url_for(u) }}">{{ l }}</a>{% endfor %}</nav>{% endblock %}""",

    "admin_home.html": """{% extends 'admin_base.html' %}{% block body %}<h1>Panel administratora</h1>
<div class="stats"><div class="stat"><span class="note">użytkownicy</span><b>{{ stats.users }}</b></div><div class="stat"><span class="note">administratorzy</span><b>{{ stats.admins }}</b></div><div class="stat"><span class="note">zablokowani</span><b>{{ stats.banned }}</b></div><div class="stat"><span class="note">aktywne zaproszenia</span><b>{{ stats.invites }}</b></div><div class="stat"><span class="note">ręcznie zmienione produkty</span><b>{{ stats.overrides }}</b></div></div>
<p class="note">Produkty edytujesz z poziomu listy: przy każdym produkcie (jako administrator) masz przyciski „Przypnij na górze", „Ukryj" i „Edytuj".</p>
<form method="post" action="{{ url_for('admin_refresh') }}"><input type="hidden" name="csrf" value="{{ csrf }}"><button class="sec">Odśwież dane cen teraz</button></form>{% endblock %}""",

    "admin_users.html": """{% extends 'admin_base.html' %}{% block body %}<h1>Użytkownicy</h1>
{% for u in rows %}<div class="card{{ ' dim' if u.banned }}"><div class="who"><img class="av" src="{{ u.avatar }}" alt="" width="32" height="32"><div><b>{{ u.name }}</b> <span class="note">@{{ u.username }}</span><br>
<span class="badge {{ 'a' if u.admin else '' }}">{{ 'admin' if u.admin else 'członek' }}</span>{% if u.banned %} <span class="badge r">zablokowany</span>{% endif %}</div></div>
<div class="note">dołączył(a): {{ u.joined|dt('%d.%m.%Y') }} · zaprosił(a): {{ u.by_name }} · zaprosiła(a) dalej: {{ u.children }} · aktywne zaproszenia: {{ u.active }}/{{ u.quota_eff }}</div>
{% if u.locked %}<div class="note">To konto jest chronione (Ty albo administrator z konfiguracji).</div>{% else %}
<div class="qa">
<form method="post"><input type="hidden" name="csrf" value="{{ csrf }}"><input type="hidden" name="uid" value="{{ u.id }}"><button class="sec sm" name="act" value="{{ 'demote' if u.admin else 'promote' }}">{{ 'Odbierz admina' if u.admin else 'Nadaj admina' }}</button></form>
{% if u.banned %}<form method="post"><input type="hidden" name="csrf" value="{{ csrf }}"><input type="hidden" name="uid" value="{{ u.id }}"><button class="sec sm" name="act" value="unban">Odblokuj</button></form>
{% else %}<form method="post"><input type="hidden" name="csrf" value="{{ csrf }}"><input type="hidden" name="uid" value="{{ u.id }}"><button class="dng sm" name="act" value="ban">Zablokuj</button></form>{% endif %}</div>
<details><summary>Więcej</summary><div class="qa">
<form method="post" class="qa"><input type="hidden" name="csrf" value="{{ csrf }}"><input type="hidden" name="uid" value="{{ u.id }}"><input type="hidden" name="act" value="quota"><input name="extra" value="{{ u.quota_eff }}" inputmode="numeric" style="width:70px" aria-label="Limit zaproszeń"><button class="sec sm">Ustaw limit zaproszeń</button></form>
<form method="post" class="qa"><input type="hidden" name="csrf" value="{{ csrf }}"><input type="hidden" name="uid" value="{{ u.id }}"><input type="hidden" name="act" value="ban_tree"><label class="note"><input type="checkbox" required> potwierdzam</label><button class="dng sm">Zablokuj z całym drzewem zaproszonych</button></form>
<form method="post" class="qa"><input type="hidden" name="csrf" value="{{ csrf }}"><input type="hidden" name="uid" value="{{ u.id }}"><input type="hidden" name="act" value="remove"><label class="note"><input type="checkbox" required> potwierdzam</label><button class="dng sm">Usuń konto</button></form></div></details>{% endif %}</div>
{% else %}<div class="card">Brak użytkowników.</div>{% endfor %}{% endblock %}""",

    "admin_invites.html": """{% extends 'admin_base.html' %}{% block body %}<h1>Zaproszenia</h1>
<form method="post" class="f"><input type="hidden" name="csrf" value="{{ csrf }}"><label>Ile osób może użyć<input name="max_uses" value="1" inputmode="numeric"></label><label>Ważne dni<input name="days" placeholder="domyślnie" inputmode="numeric"></label>
<label style="grid-column:1/3">Notatka<input name="note" maxlength="60"></label><button style="grid-column:1/3">Utwórz zaproszenie</button></form>
{% for r in rows %}<div class="card"><div class="top"><span class="badge {{ 'a' if r.state=='ok' else 'r' }}">{{ {'ok':'aktywne','used':'wykorzystane','expired':'wygasło','revoked':'wycofane'}[r.state] }}</span><span class="code">od: {{ r.by }}</span>{% if r.note %}<span class="code">{{ r.note }}</span>{% endif %}<span class="note" style="margin-left:auto">{{ r.used }}/{{ r.max_uses }}</span></div>
{% if r.state=='ok' %}<input readonly value="{{ base_url }}/invite/{{ r.code }}" aria-label="Link zaproszenia"><div class="note">ważne do {{ r.expires|dt('%d.%m.%Y') }}</div>{% endif %}
{% if r.users %}<div class="note">dołączyli: {{ r.users|join(', ') }}</div>{% endif %}
{% if r.state=='ok' %}<form method="post" action="{{ url_for('invite_revoke') }}" class="qa"><input type="hidden" name="csrf" value="{{ csrf }}"><input type="hidden" name="code" value="{{ r.code }}"><input type="hidden" name="back" value="/admin/invites"><button class="sec sm">Wycofaj</button></form>{% endif %}</div>
{% else %}<div class="card">Brak zaproszeń.</div>{% endfor %}{% endblock %}""",

    "admin_settings.html": """{% extends 'admin_base.html' %}{% block body %}<h1>Ustawienia</h1>
<form method="post" class="f"><input type="hidden" name="csrf" value="{{ csrf }}">
<label class="chk" style="grid-column:1/3"><input type="checkbox" name="member_invites" value="1" {{ 'checked' if st.member_invites }}> członkowie mogą zapraszać innych</label>
<label>Limit aktywnych zaproszeń na osobę<input name="default_quota" value="{{ st.default_quota }}" inputmode="numeric"></label><label>Ważność zaproszenia (dni)<input name="invite_days" value="{{ st.invite_days }}" inputmode="numeric"></label>
<button style="grid-column:1/3">Zapisz</button></form>{% endblock %}""",

    "admin_audit.html": """{% extends 'admin_base.html' %}{% block body %}<h1>Dziennik zmian</h1>
{% for a in rows %}<div class="card"><div class="top"><b>{{ a.action }}</b><span class="note" style="margin-left:auto">{{ a.ts|dt('%d.%m %H:%M') }}</span></div><div class="note">{{ a.who_name }}{% if a.target %} · {{ a.target }}{% endif %}</div></div>{% else %}<div class="card">Pusto.</div>{% endfor %}{% endblock %}""",

    "admin_product.html": """{% extends 'base.html' %}{% block body %}<h1>Edycja produktu</h1><p class="note">{{ it.o_name }} · {{ it.site }}<br>Zostaw pole puste, żeby użyć danych ze scrapera. Zmiany widzą wszyscy od razu.</p>
<form method="post" class="f"><input type="hidden" name="csrf" value="{{ csrf }}"><input type="hidden" name="u" value="{{ it.url }}">
<label style="grid-column:1/3">Nazwa<input name="name" value="{{ ov.name or '' }}" placeholder="{{ it.o_name }}" maxlength="200"></label>
<label>Cena (zł)<input name="price" value="{{ ov.price if ov.price is not none else '' }}" placeholder="{{ it.o_price|pln }}" inputmode="decimal"></label>
<label>Dostępność<select name="avail"><option value="">ze scrapera</option><option value="in_stock" {{ 'selected' if ov.avail=='in_stock' }}>dostępny</option><option value="out_of_stock" {{ 'selected' if ov.avail=='out_of_stock' }}>niedostępny</option></select></label>
<label>Kod produktu<input name="code" value="{{ ov.code or '' }}" placeholder="{{ it.o_code or 'brak' }}" maxlength="40"></label>
<label>Pozycja (mniejsza = wyżej)<input name="rank" value="{{ ov.rank if ov.rank is not none else '' }}" inputmode="numeric" placeholder="brak"></label>
<label style="grid-column:1/3">Etykieta (np. polecamy, promocja)<input name="note" value="{{ ov.note or '' }}" maxlength="80"></label>
<label class="chk" style="grid-column:1/3"><input type="checkbox" name="hidden" value="1" {{ 'checked' if ov.hidden }}> ukryj produkt (widzą go tylko administratorzy)</label>
<button style="grid-column:1/3" name="act" value="save">Zapisz</button><button class="sec" style="grid-column:1/3" name="act" value="clear">Przywróć dane ze scrapera</button></form>
<p><a href="{{ url_for('product', u=it.url) }}" style="text-decoration:underline">← wróć do produktu</a></p>{% endblock %}""",
}

app.jinja_env.loader = DictLoader(TEMPLATES)
app.jinja_env.globals["css"] = CSS


if __name__ == "__main__":
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", "8000")))
