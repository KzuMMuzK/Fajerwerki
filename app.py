"""
Prywatna strona z cenami fajerwerków (Flask, Render): wejście tylko na zaproszenie, logowanie przez Discorda,
panel administratora (użytkownicy, zaproszenia, kupony, ręczna edycja produktów i cen, kolejność).

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
import html as htmllib
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

from PIL import Image, ImageOps, UnidentifiedImageError
import pytesseract
import requests
from flask import (Flask, Response, abort, flash, g, get_flashed_messages, jsonify, redirect, render_template,
                   request, session, url_for)
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
    PERMANENT_SESSION_LIFETIME=timedelta(days=30), MAX_CONTENT_LENGTH=6 * 1024 * 1024,
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


DEFAULT_STATE = {"users": {}, "invites": {}, "overrides": {}, "coupons": {}, "audit": [],
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


def _coupon_image(upload):
    if not upload or not upload.filename:
        return None
    raw = upload.stream.read(5 * 1024 * 1024 + 1)
    if len(raw) > 5 * 1024 * 1024:
        raise ValueError("Zdjęcie może mieć maksymalnie 5 MB.")
    try:
        image = Image.open(io.BytesIO(raw))
        if image.format not in ("JPEG", "PNG", "WEBP"):
            raise ValueError("Dozwolone są zdjęcia JPG, PNG i WebP.")
        if image.width * image.height > 30_000_000:
            raise ValueError("Zdjęcie ma zbyt dużą rozdzielczość.")
        image = ImageOps.exif_transpose(image).convert("RGB")
        image.thumbnail((1600, 1600))
        out = io.BytesIO()
        for quality in (85, 75, 65, 55):
            out.seek(0)
            out.truncate()
            image.save(out, format="JPEG", quality=quality, optimize=True)
            if out.tell() <= 1_500_000:
                return out.getvalue()
        raise ValueError("Nie udało się zmniejszyć zdjęcia do bezpiecznego rozmiaru.")
    except (UnidentifiedImageError, OSError, Image.DecompressionBombError) as e:
        raise ValueError("Nie udało się odczytać zdjęcia. Wybierz poprawny plik JPG, PNG lub WebP.") from e


def _coupon_code_candidates(text):
    candidates = []
    seen = set()
    for match in re.finditer(r"(?<![A-Z0-9])([A-Z0-9][A-Z0-9_-]{3,19})(?![A-Z0-9])", text.upper()):
        code = match.group(1).strip("-_")
        if (len(code) >= 4 and (any(char.isdigit() for char in code) or len(code) >= 6)
                and code not in seen):
            seen.add(code)
            candidates.append(code)
    return candidates[:20]


def _coupon_percent(discount):
    matches = re.findall(r"(?<![\d.,])(\d{1,2}(?:[.,]\d+)?)\s*%", str(discount or ""))
    if len(matches) != 1:
        return None
    try:
        percent = float(matches[0].replace(",", "."))
    except ValueError:
        return None
    return percent if 0 < percent < 100 else None


def _coupon_amount(discount):
    text = str(discount or "")
    if "%" in text:
        return None
    matches = re.findall(r"(?<![\d.,])(\d+(?:[.,]\d{1,2})?)\s*(?:zł|pln)\b", text, re.I)
    if len(matches) != 1:
        return None
    try:
        amount = float(matches[0].replace(",", "."))
    except ValueError:
        return None
    return amount if amount > 0 else None


def _coupon_shop_key(shop):
    parts = re.findall(r"[a-z0-9]+", fold(str(shop or "")))
    ignored = {"fajerwerki", "fajerwerk", "sklep", "hurtownia", "pl"}
    return "".join(part for part in parts if part not in ignored)


_CATEGORY_RULES = (
    ("Zestawy", r"zestaw|komplet|pakiet|bundle"),
    ("Wyrzutnie", r"wyrzutni|bateri|compound|salw"),
    ("Petardy", r"petard|hukow|emiter.?dzwieku"),
    ("Rakiety", r"rakiet"),
    ("Fontanny i wulkany", r"fontann|wulkan"),
    ("Rzymskie ognie", r"rzymsk"),
    ("Dymy", r"dym|smoke"),
    ("Race i flary", r"rac[aei]|flar"),
    ("Stroboskopy", r"strob|bengalsk"),
    ("Zimne ognie", r"zimne.?ognie"),
    ("Pirotechnika sceniczna", r"sceniczn|teatraln|wroclawsk"),
    ("Akcesoria", r"lont|zapalnik|zapalniczk|odpal|akcesori|okular|ochronn"),
)
PRODUCT_CATEGORIES = tuple(category for category, _ in _CATEGORY_RULES) + ("Pozostałe",)


def _product_categories(name, category=None):
    if category in PRODUCT_CATEGORIES:
        return [category]
    text = fold(name or "")
    matches = [category for category, pattern in _CATEGORY_RULES if re.search(pattern, text)]
    return matches or ["Pozostałe"]


def _best_coupon_for_offer(offer, coupons):
    categories = offer["categories"]
    candidates = []
    for coupon in coupons:
        if coupon["category"] and coupon["category"] not in categories:
            continue
        if coupon["excludes_promos"] and offer["promo"]:
            continue
        if coupon["discount_value"] is None:
            continue
        if coupon["discount_kind"] == "percent":
            price = offer["base_price"] * (1 - coupon["discount_value"] / 100)
        else:
            price = offer["base_price"] - coupon["discount_value"]
        candidates.append((max(0, round(price, 2)), coupon))
    if not candidates:
        return None
    price, coupon = min(candidates, key=lambda match: (match[0], match[1]["code"]))
    return {"code": coupon["code"], "price": price, "category": coupon["category"]}


def _coupon_rows(data, active_only=False):
    today = datetime.now(timezone.utc).date().isoformat()
    rows = []
    for coupon_id, coupon in data["coupons"].items():
        expired = bool(coupon.get("valid_until") and coupon["valid_until"] < today)
        if active_only and (not coupon.get("active", True) or expired):
            continue
        percent = _coupon_percent(coupon.get("discount"))
        amount = _coupon_amount(coupon.get("discount")) if percent is None else None
        rows.append({
            **coupon,
            "id": coupon_id,
            "expired": expired,
            "percent": percent,
            "amount": amount,
            "discount_kind": "percent" if percent is not None else "amount" if amount is not None else None,
            "discount_value": percent if percent is not None else amount,
            "shop_key": _coupon_shop_key(coupon.get("shop")),
            "category": coupon.get("category") or "",
        })
    return sorted(rows, key=lambda row: (row["expired"], row.get("valid_until") or "9999-12-31",
                                         row.get("created", "")), reverse=False)


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
    category = ov.get("category") if ov.get("category") in PRODUCT_CATEGORIES else _product_categories(name)[0]
    c.execute("""UPDATE items SET name = ?, name_norm = ?, price = ?, avail = ?, code = ?, code_key = ?, prev_price = ?,
                                 drop_pct = ?, hidden = ?, rank = ?, note = ?, edited = ?, category = ? WHERE url = ?""",
              (name, fold(name), price, avail, code, key, prev, drop, 1 if ov.get("hidden") else 0,
                             ov.get("rank"), ov.get("note"), 1 if ov else 0, category, url))
    return o_key


def _deduplicate_product_rows(rows):
    unique = {}
    for row in rows:
        url, site, name, _, code_key, _, last_seen, price, avail, changed_at, currency = row[:11]
        if name and str(name).strip():
            identity = (site, " ".join(fold(name).split()), code_key or "", price,
                        currency or "PLN", avail)
        else:
            identity = ("url", url)
        rank = (last_seen or "", changed_at or "", -len(url or ""), url or "")
        previous = unique.get(identity)
        if previous is None:
            unique[identity] = (rank, row)
            continue
        selected = row if rank > previous[0] else previous[1]
        merged = list(selected)
        historical_mins = [value for value in (previous[1][13], row[13]) if value is not None]
        historical_maxes = [value for value in (previous[1][14], row[14]) if value is not None]
        merged[13] = min(historical_mins) if historical_mins else None
        merged[14] = max(historical_maxes) if historical_maxes else None
        if len(merged) > 16:
            merged[16] = 1 if previous[1][16] or row[16] else None
        unique[identity] = (max(rank, previous[0]), tuple(merged))
    return [entry[1] for entry in unique.values()]


def _build_derived(src, dst):
    """Z bazy scrapera robi płaską tabelę 'items' (ostatnia cena, poprzednia cena, min/max...) i nakłada ręczne zmiany."""
    con = sqlite3.connect(src)
    cols = {r[1] for r in con.execute("PRAGMA table_info(products)")}
    code_sel = "p.code, p.code_key" if "code_key" in cols else "NULL, NULL"
    promo_sel = "p.promo" if "promo" in cols else "NULL"
    rows = con.execute(f"""
        SELECT p.url, p.site, p.name, {code_sel}, p.first_seen, p.last_seen,
               cur.price, cur.availability, cur.ts, cur.currency,
               (SELECT price FROM prices WHERE url = p.url AND price IS NOT NULL AND price IS NOT cur.price
                ORDER BY id DESC LIMIT 1),
               (SELECT availability FROM prices WHERE url = p.url AND id < cur.id ORDER BY id DESC LIMIT 1),
               (SELECT MIN(price) FROM prices WHERE url = p.url AND price IS NOT NULL),
               (SELECT MAX(price) FROM prices WHERE url = p.url AND price IS NOT NULL),
               (SELECT COUNT(*) FROM prices WHERE url = p.url), {promo_sel}
        FROM products p JOIN prices cur ON cur.id = (SELECT MAX(id) FROM prices WHERE url = p.url)
    """).fetchall()
    con.close()
    rows = _deduplicate_product_rows(rows)
    if os.path.exists(dst):
        os.remove(dst)
    out = sqlite3.connect(dst)
    out.executescript("""
        CREATE TABLE items(url TEXT PRIMARY KEY, site TEXT, name TEXT, name_norm TEXT, code TEXT, code_key TEXT,
            first_seen TEXT, last_seen TEXT, price REAL, avail TEXT, changed_at TEXT, currency TEXT,
            prev_price REAL, prev_avail TEXT, min_price REAL, max_price REAL, n_changes INTEGER,
            drop_pct REAL, key_shops INTEGER, key_min REAL,
            o_name TEXT, o_price REAL, o_avail TEXT, o_code TEXT, o_key TEXT, o_prev REAL, o_drop REAL,
            hidden INTEGER DEFAULT 0, rank INTEGER, note TEXT, edited INTEGER DEFAULT 0, promo INTEGER,
            category TEXT);
        CREATE INDEX ix_site ON items(site); CREATE INDEX ix_key ON items(code_key);
        CREATE INDEX ix_changed ON items(changed_at);
        CREATE TABLE meta(k TEXT PRIMARY KEY, v TEXT);
        CREATE TABLE change_events(
            url TEXT, site TEXT, name TEXT, name_norm TEXT, code TEXT, code_key TEXT,
            ts TEXT, price REAL, availability TEXT, currency TEXT,
            prev_price REAL, prev_availability TEXT, scan_id INTEGER, event_type TEXT
        );
        CREATE INDEX ix_change_events_ts ON change_events(ts);
        CREATE INDEX ix_change_events_site_ts ON change_events(site, ts);
        CREATE INDEX ix_change_events_date ON change_events(substr(ts, 1, 10));
        CREATE INDEX ix_change_events_scan ON change_events(scan_id);
        CREATE TABLE scan_options(
            scan_id INTEGER PRIMARY KEY, site TEXT, started_at TEXT,
            completed_at TEXT, status TEXT
        );
    """)
    batch = []
    for (url, site, name, code, key, first, last, price, av, ts, cur, prev, prev_av, mn, mx, n,
         promo) in rows:
        pct = (prev - price) * 100.0 / prev if (prev and price is not None and prev > 0) else None
        batch.append((url, site, name, fold(name), code, key, first, last, price, av, ts, cur or "PLN", prev, prev_av,
                      mn, mx, n, pct, None, None, name, price, av, code, key, prev, pct, 0, None, None, 0, promo,
                      _product_categories(name)[0]))
    out.executemany("INSERT INTO items VALUES(" + ",".join("?" * 33) + ")", batch)
    out.execute("ATTACH DATABASE ? AS source_db", (src,))
    source_tables = {row[0] for row in out.execute(
        "SELECT name FROM source_db.sqlite_master WHERE type = 'table'"
    )}
    price_columns = {row[1] for row in out.execute("PRAGMA source_db.table_info(prices)")}
    source_scan_expr = "p.scan_id" if "scan_id" in price_columns else "NULL"
    if "scrape_runs" in source_tables:
        out.execute("""
            INSERT OR IGNORE INTO scan_options(scan_id,site,started_at,completed_at,status)
            SELECT id,site,started_at,completed_at,status FROM source_db.scrape_runs
        """)
    out.execute(f"""
        WITH legacy_days AS (
            SELECT DISTINCT i.site, substr(p.ts, 1, 10) AS scan_day
            FROM source_db.prices p JOIN items i ON i.url = p.url
            WHERE p.ts IS NOT NULL AND COALESCE({source_scan_expr}, 0) = 0
        ), numbered_days AS (
            SELECT -ROW_NUMBER() OVER (ORDER BY site, scan_day) AS scan_id,
                   site, scan_day
            FROM legacy_days
        )
        INSERT OR IGNORE INTO scan_options(scan_id,site,started_at,completed_at,status)
        SELECT scan_id,site,scan_day || 'T00:00:00+00:00',
               scan_day || 'T23:59:59+00:00','legacy'
        FROM numbered_days
    """)
    out.execute(f"""
        INSERT INTO change_events(
            url, site, name, name_norm, code, code_key, ts, price, availability, currency,
            prev_price, prev_availability, scan_id, event_type
        )
        WITH ordered_prices AS (
            SELECT url, ts, price, availability, currency, {source_scan_expr} AS scan_id,
                   LAG(price) OVER (PARTITION BY url ORDER BY id) AS prev_price,
                   LAG(availability) OVER (PARTITION BY url ORDER BY id) AS prev_availability,
                   ROW_NUMBER() OVER (PARTITION BY url ORDER BY id) AS event_number
            FROM source_db.prices p
        )
        SELECT i.url, i.site, i.name, i.name_norm, i.code, i.code_key,
               p.ts, p.price, p.availability, p.currency, p.prev_price, p.prev_availability,
               COALESCE(p.scan_id, (
                   SELECT s.scan_id FROM scan_options s
                   WHERE s.site = i.site AND s.status = 'legacy'
                     AND substr(s.started_at, 1, 10) = substr(p.ts, 1, 10)
                   LIMIT 1
               )), 'change'
        FROM ordered_prices p JOIN items i ON i.url = p.url
        WHERE p.event_number > 1
    """)
    out.execute(f"""
        INSERT INTO change_events(
            url, site, name, name_norm, code, code_key, ts, price, availability, currency,
            prev_price, prev_availability, scan_id, event_type
        )
        WITH first_prices AS (
            SELECT url, ts, price, availability, currency, {source_scan_expr} AS scan_id,
                   ROW_NUMBER() OVER (PARTITION BY url ORDER BY id) AS event_number
            FROM source_db.prices p
        )
        SELECT i.url, i.site, i.name, i.name_norm, i.code, i.code_key,
               p.ts, p.price, p.availability, p.currency, NULL, NULL,
               COALESCE(p.scan_id, (
                   SELECT s.scan_id FROM scan_options s
                   WHERE s.site = i.site AND s.status = 'legacy'
                     AND substr(s.started_at, 1, 10) = substr(p.ts, 1, 10)
                   LIMIT 1
               )), 'new'
        FROM first_prices p JOIN items i ON i.url = p.url
        WHERE p.event_number = 1
    """)
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


def lowest_price_history(urls):
    if not urls:
        return []
    src = os.path.join(WORK, "src.db")
    c = sqlite3.connect(f"file:{src}?mode=ro", uri=True)
    try:
        rows = c.execute(
            "SELECT pr.url, p.site, pr.ts, pr.price, pr.availability "
            "FROM prices pr JOIN products p ON p.url = pr.url "
            "WHERE pr.url IN (" + ",".join("?" for _ in urls) + ") "
            "ORDER BY pr.ts, pr.id",
            urls,
        ).fetchall()
    finally:
        c.close()

    states, points = {}, []
    position = 0
    while position < len(rows):
        ts = rows[position][2]
        while position < len(rows) and rows[position][2] == ts:
            url, site, _, price, availability = rows[position]
            states[url] = (site, price, availability)
            position += 1
        priced = [(site, price, availability) for site, price, availability in states.values()
                  if price is not None]
        if not priced:
            continue
        site, price, availability = min(
            priced, key=lambda item: (item[1], item[2] != "in_stock", item[0])
        )
        point = {"ts": ts, "site": site, "price": price, "availability": availability}
        if not points or any(points[-1][key] != point[key] for key in ("site", "price", "availability")):
            points.append(point)
    return points


def lowest_price_chart(points, w=680, h=250):
    timed = [(parse_ts(point["ts"]), point) for point in points]
    timed = [(ts, point) for ts, point in timed if ts]
    if not timed:
        return ""
    t0, t1 = timed[0][0], timed[-1][0]
    span = max((t1 - t0).total_seconds(), 1.0)
    prices = [point["price"] for _, point in timed]
    lo, hi = min(prices), max(prices)
    if hi - lo < 0.01:
        lo, hi = max(0, lo - 1), hi + 1
    left, right, top, bottom = 52, 12, 12, 30
    x = lambda ts: left + (w - left - right) * (ts - t0).total_seconds() / span
    y = lambda price: top + (h - top - bottom) * (1 - (price - lo) / (hi - lo))
    path, markers = [], []
    for index, (ts, point) in enumerate(timed):
        px, py = x(ts), y(point["price"])
        path.append(f"M{px:.1f},{py:.1f}" if index == 0 else f"H{px:.1f}V{py:.1f}")
        date = ts.astimezone(TZ).strftime("%d.%m.%Y %H:%M")
        status = "dostępny" if point["availability"] == "in_stock" else "niedostępny"
        label = htmllib.escape(
            f"{date} | {point['site']} | {point['price']:.2f} zł | {status}", quote=True
        )
        markers.append(f'<circle cx="{px:.1f}" cy="{py:.1f}" r="4" class="price-point" '
                   f'data-x="{px:.1f}" data-tooltip="{label}"><title>{label}</title></circle>')
    fmt = lambda ts: ts.astimezone(TZ).strftime("%d.%m.%Y")
    return (f'<svg viewBox="0 0 {w} {h}" class="chart price-history" role="img" '
            f'aria-label="Najniższa cena w czasie, najedź na punkt po szczegóły">'
            f'<path d="{"".join(path)}H{x(t1):.1f}" class="line"/>{"".join(markers)}'
            f'<text x="2" y="{top + 9}" class="ax">{hi:.2f} zł</text>'
            f'<text x="2" y="{h - bottom}" class="ax">{lo:.2f} zł</text>'
            f'<text x="{left}" y="{h - 6}" class="ax">{fmt(t0)}</text>'
            f'<text x="{w - right}" y="{h - 6}" class="ax" text-anchor="end">{fmt(t1)}</text></svg>')


# ----------------------------------------------------------------------------- dostęp: sesja, CSRF, Discord
PUBLIC = {"health", "robots", "login", "invite_page", "auth_discord", "auth_callback", "logout", "favicon"}


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
    resp.headers["Content-Security-Policy"] = (
        "default-src 'none'; style-src 'unsafe-inline'; script-src 'unsafe-inline'; connect-src 'self'; "
        "img-src 'self' data: https://cdn.discordapp.com; form-action 'self'; base-uri 'none'; frame-ancestors 'none'"
    )
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
        args.pop("_partial", None)
        for k, v in kw.items():
            if v is None:
                args.pop(k, None)
            else:
                args[k] = v if isinstance(v, list) else [v]
        return request.path + ("?" + urlencode(args, doseq=True) if args else "")

    def export_url():
        args = request.args.to_dict(flat=False)
        for k in ("page", "s", "_partial"):
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
    if request.args.get("cheapest") == "1":
        where.append("key_shops > 1 AND avail = 'in_stock' AND price IS NOT NULL AND price = key_min")
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
    coupons = store.read(lambda data: _coupon_rows(data, active_only=True))
    coupons_by_shop = {}
    for coupon in coupons:
        if coupon["discount_value"] is not None and coupon["shop_key"]:
            coupons_by_shop.setdefault(coupon["shop_key"], []).append(coupon)
    return {"shops": shops, "last_seen": meta.get("last_seen"), "has_codes": meta.get("has_codes") == "1",
            "refresh_error": _state["error"], "coupons_by_shop": coupons_by_shop,
            "coupon_shop_key": _coupon_shop_key}


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
    offer_visibility = "" if is_admin(g.user) else " AND best.hidden = 0"
    items = c.execute(f"""
        SELECT i.*,
               CASE WHEN i.code_key IS NOT NULL THEN (
                   SELECT best.url FROM items best
                   WHERE best.code_key = i.code_key AND best.avail = 'in_stock'
                     AND best.price IS NOT NULL{offer_visibility}
                   ORDER BY best.price, best.site LIMIT 1
               ) WHEN i.avail = 'in_stock' AND i.price IS NOT NULL THEN i.url END AS cheapest_url
        FROM items i{where}
        ORDER BY {order} LIMIT ? OFFSET ?
    """, args + [PER_PAGE, (page - 1) * PER_PAGE]).fetchall()
    context = dict(items=items, total=total, page=page,
                   pages=max((total + PER_PAGE - 1) // PER_PAGE, 1),
                   q=q, s=s, sorts=SORTS, sel_sites=request.args.getlist("site"),
                   tab="list", **common_ctx(c))
    template = "product_results.html" if request.args.get("_partial") == "1" else "index.html"
    return render_template(template, **context)


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
    if it["code_key"]:
        rows = c.execute("SELECT * FROM items WHERE code_key = ?" + vis(), (it["code_key"],)).fetchall()
    else:
        rows = c.execute("SELECT * FROM items WHERE name_norm = ?" + vis(), (it["name_norm"],)).fetchall()
    rows = _best_shop_offers(rows)
    chart = lowest_price_chart(lowest_price_history([row["url"] for row in rows]))
    return render_template("compare.html", rows=rows, key=it["code"] or "", chart=chart,
                           tab="deals", **common_ctx(c))


@app.route("/compare")
def compare():
    c = conn()
    key = keyify(request.args.get("k", ""))
    rows = c.execute("SELECT * FROM items WHERE code_key = ?" + vis() +
                     " ORDER BY (avail = 'in_stock') DESC, price IS NULL, price ASC, changed_at DESC",
                     (key,)).fetchall()
    rows = _best_shop_offers(rows)
    if not rows:
        abort(404)
    chart = lowest_price_chart(lowest_price_history([row["url"] for row in rows]))
    return render_template("compare.html", rows=rows, key=key, chart=chart,
                           tab="deals", **common_ctx(c))


@app.route("/deals")
def deals():
    c = conn()
    try:
        ms = min(max(float(request.args.get("ms", "0").replace(",", ".")), 0), 95)
    except ValueError:
        ms = 0.0
    try:
        min_shops = min(max(int(request.args.get("shops", "2")), 2), 20)
    except ValueError:
        min_shops = 2
    try:
        min_saving = min(max(float(request.args.get("saving", "0").replace(",", ".")), 0), 100000)
    except ValueError:
        min_saving = 0.0
    query = " ".join(request.args.get("q", "").split())[:100]
    sort = request.args.get("sort", "percent")
    sort_orders = {
        "percent": "saving_pct DESC, saving DESC",
        "amount": "saving DESC, saving_pct DESC",
        "shops": "n_avail DESC, saving_pct DESC",
        "name": "name COLLATE NOCASE ASC",
    }
    if sort not in sort_orders:
        sort = "percent"
    try:
        page = max(int(request.args.get("page", "1")), 1)
    except ValueError:
        page = 1
    visible = vis()
    cte = f"""
        WITH ranked AS (
            SELECT *, ROW_NUMBER() OVER (
                PARTITION BY code_key, site
                ORDER BY CASE WHEN avail = 'in_stock' AND price IS NOT NULL THEN 0 ELSE 1 END,
                         price IS NULL, price ASC, changed_at DESC
            ) AS offer_rank
            FROM items WHERE code_key IS NOT NULL{visible}
        ), offers AS (
            SELECT * FROM ranked WHERE offer_rank = 1
        ), grouped AS (
            SELECT code_key, MIN(code) AS code, MIN(name) AS name,
                   MIN(name_norm) AS name_norm,
                   COUNT(DISTINCT site) AS shops,
                   COUNT(DISTINCT CASE WHEN avail = 'in_stock' AND price IS NOT NULL THEN site END) AS n_avail,
                   MIN(CASE WHEN avail = 'in_stock' AND price IS NOT NULL THEN price END) AS pmin,
                   MAX(CASE WHEN avail = 'in_stock' AND price IS NOT NULL THEN price END) AS pmax
            FROM offers GROUP BY code_key
        ), opportunities AS (
            SELECT *, pmax - pmin AS saving,
                   (pmax - pmin) * 100.0 / pmax AS saving_pct
            FROM grouped WHERE n_avail >= ? AND pmax > pmin AND pmax > 0
        )
    """
    filters = ["saving_pct >= ?", "saving >= ?"]
    params = [min_shops, ms, min_saving]
    if query:
        folded_query = fold(query)
        code_query = keyify(query)
        filters.append("(name_norm LIKE ? OR code_key LIKE ?)")
        params.extend([f"%{folded_query}%", f"%{code_query or query.upper()}%"])
    where = " WHERE " + " AND ".join(filters)
    total = c.execute(cte + " SELECT COUNT(*) FROM opportunities" + where, params).fetchone()[0]
    per_page = 100
    pages = max((total + per_page - 1) // per_page, 1)
    page = min(page, pages)
    rows = c.execute(
        cte + " SELECT * FROM opportunities" + where
        + f" ORDER BY {sort_orders[sort]}, code_key LIMIT ? OFFSET ?",
        params + [per_page, (page - 1) * per_page],
    ).fetchall()
    return render_template(
        "deals.html", rows=rows, ms=ms, min_shops=min_shops, min_saving=min_saving,
        query=query, sort=sort, page=page, pages=pages, total=total, tab="deals",
        **common_ctx(c),
    )


def _best_shop_offers(rows):
    best = {}
    for row in rows:
        available = row["avail"] == "in_stock" and row["price"] is not None
        price = row["price"] if row["price"] is not None else float("inf")
        rank = (available, row["price"] is not None, -price, row["changed_at"] or "")
        current = best.get(row["site"])
        if current is None or rank > current[0]:
            best[row["site"]] = (rank, row)
    return sorted(
        (entry[1] for entry in best.values()),
        key=lambda row: (row["avail"] != "in_stock", row["price"] is None,
                         row["price"] if row["price"] is not None else float("inf"), row["site"]),
    )


def _basket_product_by_url(c, url, price_mode="current", include_unavailable=False,
                           coupons_by_shop=None):
    selected = c.execute("SELECT * FROM items WHERE url = ? AND hidden = 0", (url,)).fetchone()
    if not selected:
        return {"url": url, "name": "Produkt nie jest już dostępny w bazie", "offers": [],
                "category": "Pozostałe", "categories": ["Pozostałe"],
                "cheapest": None, "error": "Odśwież koszyk, aby usunąć tę pozycję."}
    if selected["code_key"]:
        matches = c.execute("SELECT * FROM items WHERE code_key = ? AND hidden = 0",
                            (selected["code_key"],)).fetchall()
    else:
        matches = c.execute("SELECT * FROM items WHERE name_norm = ? AND hidden = 0",
                            (selected["name_norm"],)).fetchall()
    categories = _product_categories(selected["name"], selected["category"])
    offers = _basket_shop_offers(matches, price_mode, include_unavailable, coupons_by_shop)
    cheapest = min(offers, key=lambda offer: (offer["basket_price"], offer["site"])) if offers else None
    return {"url": url, "code": selected["code"], "name": selected["name"],
            "category": categories[0], "categories": categories,
            "offers": offers, "cheapest": cheapest,
            "error": None if cheapest else "Brak dostępnej oferty z ceną w wybranym trybie."}


def _basket_shop_offers(rows, price_mode, include_unavailable, coupons_by_shop=None):
    best = {}
    price_field = "min_price" if price_mode == "historical" else "price"
    for row in rows:
        if not include_unavailable and row["avail"] != "in_stock":
            continue
        price = row[price_field]
        if price is None:
            continue
        offer = dict(row)
        offer["base_price"] = price
        offer["basket_price"] = price
        offer["historical_price"] = price_mode == "historical"
        offer["categories"] = _product_categories(offer["name"], offer.get("category"))
        offer["promo"] = bool(offer.get("promo"))
        offer["coupon"] = None
        if price_mode == "current":
            coupon = _best_coupon_for_offer(
                offer, (coupons_by_shop or {}).get(_coupon_shop_key(offer["site"]), ())
            )
            if coupon:
                offer["coupon"] = coupon
                offer["basket_price"] = coupon["price"]
        current = best.get(row["site"])
        if current is None or offer["basket_price"] < current["basket_price"]:
            best[row["site"]] = offer
    return sorted(best.values(), key=lambda offer: (
        offer["avail"] != "in_stock", offer["basket_price"], offer["site"]
    ))


def _plan_basket(c, product_urls, selected_site, price_mode="current", include_unavailable=False,
                 coupons_by_shop=None):
    shops = [row["site"] for row in c.execute("SELECT DISTINCT site FROM items WHERE hidden = 0 ORDER BY site")]
    lines = [_basket_product_by_url(c, url, price_mode, include_unavailable, coupons_by_shop)
             for url in product_urls]

    mix_total = sum(line["cheapest"]["basket_price"] for line in lines if line["cheapest"])
    mix_missing = sum(line["cheapest"] is None for line in lines)
    shop_totals = []
    for shop in shops:
        products = []
        for line in lines:
            offer = next((offer for offer in line["offers"] if offer["site"] == shop), None)
            if offer:
                products.append({"name": line["name"], "url": offer["url"],
                                 "price": offer["basket_price"], "base_price": offer["base_price"],
                                 "coupon": offer["coupon"], "promo": offer["promo"],
                                 "availability": offer["avail"]})
        shop_totals.append({"site": shop, "total": sum(product["price"] for product in products),
                            "count": len(products), "products": products,
                            "missing": len(lines) - len(products)})
    complete = [total for total in shop_totals if total["missing"] == 0]
    best_store = min(complete, key=lambda total: total["total"]) if complete else None
    most_products_store = max(
        shop_totals, key=lambda total: (total["count"], -total["total"], total["site"]), default=None
    )
    if most_products_store and not most_products_store["count"]:
        most_products_store = None
    selected_total = next((total for total in shop_totals if total["site"] == selected_site), None)
    category_groups = [
        {"category": category, "lines": [line for line in lines if line["category"] == category]}
        for category in PRODUCT_CATEGORIES
        if any(line["category"] == category for line in lines)
    ]
    return {"lines": lines, "mix_total": mix_total, "mix_missing": mix_missing,
            "shop_totals": sorted(shop_totals, key=lambda total: (total["missing"], total["total"])),
            "best_store": best_store, "most_products_store": most_products_store,
            "selected_total": selected_total,
            "category_groups": category_groups,
            "price_mode": price_mode, "include_unavailable": include_unavailable}


@app.route("/basket")
def basket():
    c = conn()
    product_urls = list(dict.fromkeys(url[:1000] for url in request.args.getlist("u") if url))[:30]
    shops = c.execute("SELECT site FROM items WHERE hidden = 0 GROUP BY site ORDER BY site").fetchall()
    selected_site = request.args.get("site", "").strip()
    if selected_site not in {shop["site"] for shop in shops}:
        selected_site = ""
    price_mode = request.args.get("price_mode", "current")
    if price_mode not in ("current", "historical"):
        price_mode = "current"
    include_unavailable = request.args.get("unavailable") == "1"
    coupons = store.read(lambda data: _coupon_rows(data, active_only=True))
    coupons_by_shop = {}
    for coupon in coupons:
        coupons_by_shop.setdefault(coupon["shop_key"], []).append(coupon)
    plan = _plan_basket(c, product_urls, selected_site, price_mode,
                        include_unavailable, coupons_by_shop) if product_urls else None
    template = "basket_results.html" if request.args.get("_partial") == "1" else "basket.html"
    return render_template(template, product_urls=product_urls,
                           selected_site=selected_site, price_mode=price_mode,
                           include_unavailable=include_unavailable, plan=plan, tab="basket", shops=shops,
                           coupons=coupons, categories=PRODUCT_CATEGORIES)


@app.route("/changes")
def changes():
    c = conn()
    context = common_ctx(c)
    site = request.args.get("site", "").strip()
    if site not in {shop["site"] for shop in context["shops"]}:
        site = ""
    site_filter = " AND e.site = ?" if site else ""
    site_args = [site] if site else []
    t = request.args.get("t", "drops")
    conds = {
        "new": ("e.event_type = 'new'", "e.ts DESC"),
        "drops": ("e.event_type = 'change' AND e.prev_price IS NOT NULL AND e.price < e.prev_price",
                  "e.prev_price - e.price DESC, e.ts DESC"),
        "rises": ("e.event_type = 'change' AND e.prev_price IS NOT NULL AND e.price > e.prev_price",
                  "e.price - e.prev_price DESC, e.ts DESC"),
        "back": ("e.event_type = 'change' AND e.prev_availability = 'out_of_stock' AND e.availability = 'in_stock'", "e.ts DESC"),
        "gone": ("e.event_type = 'change' AND e.prev_availability = 'in_stock' AND e.availability = 'out_of_stock'", "e.ts DESC"),
    }
    if t not in conds:
        t = "drops"
    scan_options = [dict(row) for row in c.execute(
        "SELECT scan_id, site, started_at FROM scan_options "
        "ORDER BY started_at DESC, site LIMIT 365"
    )]
    scan_mode = request.args.get("scan_mode", "last")
    if scan_mode not in ("last", "range"):
        scan_mode = "last"
    date_from = request.args.get("date_from", "")
    date_to = request.args.get("date_to", "")
    valid_dates = []
    for value in (date_from, date_to):
        try:
            value = datetime.strptime(value, "%Y-%m-%d").date().isoformat()
        except ValueError:
            value = ""
        valid_dates.append(value)
    date_from, date_to = valid_dates
    if date_from and date_to and date_from > date_to:
        date_from, date_to = date_to, date_from
    scan_filter = ""
    scan_args = []
    if scan_mode == "last":
        relevant_scans = [
            scan for scan in scan_options
            if not site or scan["site"] == site
        ]
        latest_start = relevant_scans[0]["started_at"] if relevant_scans else None
        latest_scans = [
            scan["scan_id"] for scan in scan_options
            if latest_start and scan["started_at"] == latest_start
            and (not site or scan["site"] == site)
        ]
        if latest_scans:
            scan_filter = " AND e.scan_id IN (" + ",".join("?" * len(latest_scans)) + ")"
            scan_args = latest_scans
        else:
            scan_filter = " AND 0"
    else:
        if date_from:
            scan_filter += " AND substr(e.ts, 1, 10) >= ?"
            scan_args.append(date_from)
        if date_to:
            scan_filter += " AND substr(e.ts, 1, 10) <= ?"
            scan_args.append(date_to)
    visibility = "" if is_admin(g.user) else " AND i.hidden = 0"
    counts = {
        key: c.execute(
            "SELECT COUNT(*) FROM change_events e JOIN items i ON i.url = e.url "
            f"WHERE {condition}{scan_filter}{site_filter}{visibility}",
            scan_args + site_args,
        ).fetchone()[0]
        for key, (condition, _) in conds.items()
    }
    per_page = 50
    total = counts[t]
    pages = max((total + per_page - 1) // per_page, 1)
    try:
        page = max(int(request.args.get("page", "1")), 1)
    except ValueError:
        page = 1
    page = min(page, pages)
    rows = c.execute(
        "SELECT i.*, e.ts AS event_ts, e.price AS event_price, "
        "e.availability AS event_availability, e.prev_price AS event_prev_price, "
        "e.prev_availability AS event_prev_availability "
        "FROM change_events e JOIN items i ON i.url = e.url "
        f"WHERE {conds[t][0]}{scan_filter}{site_filter}{visibility} "
        f"ORDER BY {conds[t][1]}, e.url, e.ts DESC LIMIT ? OFFSET ?",
        scan_args + site_args + [per_page, (page - 1) * per_page],
    ).fetchall()
    display_rows = []
    for row in rows:
        item = dict(row)
        item["changed_at"] = item["event_ts"]
        item["price"] = item["event_price"]
        item["avail"] = item["event_availability"]
        item["prev_price"] = item["event_prev_price"]
        item["prev_avail"] = item["event_prev_availability"]
        item["is_new"] = t == "new"
        previous, current = item["prev_price"], item["price"]
        item["drop_pct"] = (
            (previous - current) * 100 / previous
            if previous and current is not None and previous > 0 else None
        )
        display_rows.append(item)
    return render_template(
        "changes.html", rows=display_rows, t=t, counts=counts, site=site,
        scan_mode=scan_mode, date_from=date_from, date_to=date_to,
        page=page, pages=pages,
        total=total, per_page=per_page, tab="changes", **context,
    )


@app.route("/coupons")
def coupons():
    rows = store.read(lambda data: _coupon_rows(data, active_only=True))
    return render_template("coupons.html", rows=rows, tab="coupons", **_basic())


@app.route("/coupon-image/<coupon_id>")
def coupon_image(coupon_id):
    image = store.read(lambda data: data["coupons"].get(coupon_id, {}).get("image"))
    if not image:
        abort(404)
    return Response(base64.b64decode(image, validate=True), mimetype="image/jpeg")


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


@app.route("/admin/coupons", methods=["GET", "POST"])
@admin_required
def admin_coupons():
    if request.method == "POST":
        try:
            shop = request.form.get("shop", "").strip()
            code = request.form.get("code", "").strip().upper()
            discount = request.form.get("discount", "").strip()
            terms = request.form.get("terms", "").strip()
            category = request.form.get("category", "").strip()
            valid_until = request.form.get("valid_until", "").strip()
            source = request.form.get("source", "").strip()
            image = _coupon_image(request.files.get("image"))
            if not shop or not discount:
                raise ValueError("Podaj sklep i opis rabatu.")
            if len(shop) > 80 or len(discount) > 120 or len(terms) > 500:
                raise ValueError("Przekroczono limit długości opisu, sklepu lub warunków.")
            if category and category not in PRODUCT_CATEGORIES:
                raise ValueError("Wybierz prawidłową kategorię produktów.")
            if not re.fullmatch(r"[A-Z0-9][A-Z0-9._-]{1,39}", code):
                raise ValueError("Kod musi mieć 2-40 znaków: litery, cyfry, kropka, _ lub -.")
            if valid_until:
                try:
                    valid_until = datetime.strptime(valid_until, "%Y-%m-%d").date().isoformat()
                except ValueError as e:
                    raise ValueError("Podaj poprawną datę ważności.") from e
            if source:
                parsed = urlparse(source)
                if parsed.scheme not in ("http", "https") or not parsed.netloc or len(source) > 500:
                    raise ValueError("Źródło musi być poprawnym adresem HTTP lub HTTPS (maks. 500 znaków).")
            if not image and not source:
                raise ValueError("Dodaj zdjęcie albo link do źródła kodu.")

            coupon_id = secrets.token_urlsafe(12)
            coupon = {
                "shop": shop, "code": code, "discount": discount, "terms": terms,
                "category": category,
                "valid_until": valid_until, "source": source,
                "excludes_promos": request.form.get("excludes_promos") == "1",
                "image": base64.b64encode(image).decode()
                if image else "", "created": now_iso(), "added_by": g.user["id"], "active": True,
            }

            def save(data):
                data["coupons"][coupon_id] = coupon
                audit(data, g.user["id"], "coupon_add", f"{shop}: {code}")

            store.update(save, "app-state: kupon")
            flash("Kupon dodany.", "ok")
        except ValueError as e:
            flash(str(e), "err")
        return redirect(url_for("admin_coupons"))
    rows = store.read(lambda data: _coupon_rows(data))
    return render_template("admin_coupons.html", rows=rows, categories=PRODUCT_CATEGORIES,
                           tab="admin", sub="coupons", **_basic())


@app.route("/admin/coupons/ocr", methods=["POST"])
@admin_required
def admin_coupon_ocr():
    try:
        image = _coupon_image(request.files.get("image"))
        if not image:
            return jsonify(error="Wybierz zdjęcie do odczytu."), 400
        text = pytesseract.image_to_string(Image.open(io.BytesIO(image)), lang="pol+eng",
                                           config="--psm 11")
        return jsonify(text=text[:4000], codes=_coupon_code_candidates(text))
    except ValueError as e:
        return jsonify(error=str(e)), 400
    except (pytesseract.TesseractNotFoundError, pytesseract.TesseractError) as e:
        app.logger.error("OCR kuponu niedostępny: %s", e.__class__.__name__)
        return jsonify(error="Odczyt OCR jest chwilowo niedostępny. Możesz wpisać kod ręcznie."), 503


@app.route("/admin/coupons/<coupon_id>/deactivate", methods=["POST"])
@admin_required
def admin_coupon_deactivate(coupon_id):
    def deactivate(data):
        coupon = data["coupons"].get(coupon_id)
        if not coupon:
            return False
        coupon["active"] = False
        audit(data, g.user["id"], "coupon_deactivate", f'{coupon["shop"]}: {coupon["code"]}')
        return True

    if not store.update(deactivate, "app-state: wycofanie kuponu"):
        abort(404)
    flash("Kupon wycofany.", "ok")
    return redirect(url_for("admin_coupons"))


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
    category = form.get("category", "").strip()
    if category:
        if category not in PRODUCT_CATEGORIES:
            raise ValueError("Wybierz prawidłową kategorię produktu.")
        ov["category"] = category
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
    return render_template("admin_product.html", it=it, ov=ov, categories=PRODUCT_CATEGORIES,
                           tab="list", **common_ctx(c))


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


@app.route("/favicon.ico")
def favicon():
    return "", 204


# ----------------------------------------------------------------------------- wygląd
CSS = """
:root{--bg:#080d18;--card:rgba(13,21,37,.9);--fg:#f1f5fb;--mut:#a6b1c3;--line:rgba(184,202,229,.18);--accent:#ff765f;--ok:#48d6a0;--no:#7e899b;--chip:rgba(143,164,193,.13)}
@media(prefers-color-scheme:dark){:root{--bg:#080d18;--card:rgba(13,21,37,.9);--fg:#f1f5fb;--mut:#a6b1c3;--line:rgba(184,202,229,.18);--accent:#ff765f;--ok:#48d6a0;--no:#7e899b;--chip:rgba(143,164,193,.13)}}
*{box-sizing:border-box}body{margin:0;background:var(--bg);color:var(--fg);font:16px/1.4 system-ui,-apple-system,Segoe UI,Roboto,sans-serif}
a{color:inherit;text-decoration:none}.wrap{max-width:760px;margin:0 auto;padding:0 12px 40px}
header{position:sticky;top:0;background:rgba(8,13,24,.84);backdrop-filter:blur(12px);padding:8px 0;z-index:5;border-bottom:1px solid var(--line)}
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
.meta{color:var(--mut);font-size:13px;margin:10px 2px}.card{background:var(--card);backdrop-filter:blur(8px);border:1px solid var(--line);border-radius:10px;padding:11px 12px;margin:8px 0}.card.dim{opacity:.55}
.top{display:flex;gap:6px;align-items:center;flex-wrap:wrap;font-size:12px;margin-bottom:4px}.shop{background:var(--chip);border-radius:6px;padding:1px 7px;font-weight:600}
.code{border:1px solid var(--line);border-radius:6px;padding:0 6px;color:var(--mut)}.dot{width:9px;height:9px;border-radius:50%;background:var(--no);margin-left:auto}.dot.ok{background:var(--ok)}
.name{font-weight:600;display:block;margin-bottom:6px}.row{display:flex;align-items:baseline;gap:8px;flex-wrap:wrap}.price{font-size:20px;font-weight:700}
.old{color:var(--mut);text-decoration:line-through;font-size:14px}.up,.down{font-size:13px;font-weight:700;border-radius:6px;padding:0 6px}.down{background:#d1fadf;color:#05603a}.up{background:#fee4e2;color:#b42318}
@media(prefers-color-scheme:dark){.down{background:#0b3d2a;color:#75e0a7}.up{background:#4a1a15;color:#fda29b}}
.best{background:#fef0c7;color:#93370d;font-size:12px;font-weight:700;border-radius:6px;padding:1px 7px}.mini{font-size:13px;color:var(--mut);margin-left:auto;text-decoration:underline}
.qa{display:flex;gap:6px;flex-wrap:wrap;margin-top:8px;align-items:center}.qa form{margin:0}.pager{display:flex;justify-content:space-between;align-items:center;margin:14px 0}.pager a{background:var(--chip);padding:9px 14px;border-radius:10px;font-weight:600}.pager .off{opacity:.35}
.coupon-options{display:flex;align-items:center;gap:6px 10px;flex-wrap:wrap;margin-top:8px;padding-top:7px;border-top:1px solid var(--line)}.coupon-choice{display:flex;align-items:center;gap:5px;font-size:13px}.coupon-choice input{width:auto}.coupon-result{display:inline-flex;align-items:baseline;gap:7px}.coupon-result-note{flex-basis:100%}
.chart{width:100%;height:auto;margin:6px 0}.chart .line{fill:none;stroke:var(--accent);stroke-width:2}.chart .dot{fill:var(--accent)}.chart .ax{font-size:10px;fill:var(--mut)}.chart .oos{fill:var(--no);opacity:.18}.chart .price-point{fill:var(--accent);stroke:var(--card);stroke-width:2}.price-chart-wrap{position:relative}.price-chart-tooltip{position:absolute;z-index:3;max-width:min(320px,calc(100% - 8px));padding:6px 9px;border:1px solid var(--line);border-radius:6px;background:var(--fg);color:var(--bg);font-size:12px;line-height:1.35;box-shadow:0 2px 8px #0003;pointer-events:none}.price-chart-wrap svg{display:block;cursor:crosshair}
table{width:100%;border-collapse:collapse;font-size:14px}td,th{padding:6px 4px;border-bottom:1px solid var(--line);text-align:left}h1{font-size:19px;margin:14px 0 4px}h2{font-size:16px;margin:18px 0 6px}
.err{background:#fee4e2;color:#7a271a;border-radius:10px;padding:8px 10px;margin:8px 0;font-size:14px}.okm{background:#d1fadf;color:#05603a;border-radius:10px;padding:8px 10px;margin:8px 0;font-size:14px}
.note{color:var(--mut);font-size:13px}.stats{display:flex;gap:8px;flex-wrap:wrap;margin:8px 0}.stat{background:var(--card);border:1px solid var(--line);border-radius:12px;padding:8px 12px}.stat b{display:block;font-size:18px}
.center{text-align:center;padding:40px 8px}.center h1{font-size:24px}.big{padding:13px 22px;font-size:17px;margin-top:14px;background:#5865f2}
.badge{font-size:11px;font-weight:700;border-radius:6px;padding:1px 7px;background:var(--chip)}.badge.a{background:#d1fadf;color:#05603a}.badge.r{background:#fee4e2;color:#b42318}
@media(prefers-color-scheme:dark){.badge.a{background:#0b3d2a;color:#75e0a7}.badge.r{background:#4a1a15;color:#fda29b}}
ul.clean{padding-left:18px;margin:6px 0}.who{display:flex;gap:8px;align-items:center}
/* ---------- fajerwerki w tle ---------- */
body{position:relative;isolation:isolate}
body::before{content:"";position:fixed;inset:0;z-index:-2;pointer-events:none;
    background:
        radial-gradient(1px 1px at 8% 18%,rgba(228,239,255,.82) 99%,transparent 100%),
        radial-gradient(1px 1px at 17% 72%,rgba(190,216,255,.72) 99%,transparent 100%),
        radial-gradient(1px 1px at 31% 34%,rgba(255,255,255,.72) 99%,transparent 100%),
        radial-gradient(1px 1px at 44% 11%,rgba(217,232,255,.7) 99%,transparent 100%),
        radial-gradient(1px 1px at 58% 64%,rgba(255,255,255,.68) 99%,transparent 100%),
        radial-gradient(1px 1px at 72% 25%,rgba(190,216,255,.76) 99%,transparent 100%),
        radial-gradient(1px 1px at 86% 57%,rgba(255,255,255,.7) 99%,transparent 100%),
        radial-gradient(1px 1px at 94% 12%,rgba(221,232,255,.72) 99%,transparent 100%),
        radial-gradient(700px 420px at 12% 2%,rgba(42,112,151,.19),transparent 72%),
        radial-gradient(760px 480px at 88% 8%,rgba(180,69,66,.14),transparent 72%),
        linear-gradient(180deg,#07101f 0%,#090e1b 54%,#12111d 100%)}
"""


# ----------------------------------------------------------------------------- szablony
TEMPLATES = {
    "base.html": """<!doctype html><html lang="pl"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover">
<meta name="robots" content="noindex,nofollow"><title>{% block title %}Ceny fajerwerków{% endblock %}</title><style>{{ css|safe }}</style></head><body>
<div class="wrap">
{% if user %}<div class="userbar"><span class="who"><img class="av" src="{{ user.avatar }}" alt="" width="24" height="24"><span class="un">{{ user.name }}</span></span>
<a href="{{ url_for('invites') }}">Zaproszenia</a>{% if is_admin %}<a href="{{ url_for('admin_home') }}">Admin</a>{% endif %}
<form method="post" action="{{ url_for('logout') }}" class="inl"><input type="hidden" name="csrf" value="{{ csrf }}"><button class="lnk">Wyloguj</button></form></div>{% endif %}
<header>{% if user %}<nav class="tabs"><a href="{{ url_for('index') }}" class="{{ 'on' if tab=='list' }}">Produkty</a><a href="{{ url_for('deals') }}" class="{{ 'on' if tab=='deals' }}">Okazje</a><a href="{{ url_for('basket') }}" class="{{ 'on' if tab=='basket' }}">Koszyk <span data-cart-count>0</span></a><a href="{{ url_for('coupons') }}" class="{{ 'on' if tab=='coupons' }}">Kody rabatowe</a><a href="{{ url_for('changes') }}" class="{{ 'on' if tab=='changes' }}">Zmiany</a></nav>{% endif %}{% block head %}{% endblock %}</header>
{% for cat, msg in messages %}<div class="{{ 'err' if cat == 'err' else 'okm' }}">{{ msg }}</div>{% endfor %}
{% if refresh_error %}<div class="err">Nie udało się odświeżyć danych ({{ refresh_error }}). Pokazuję poprzednią wersję.</div>{% endif %}
{% block body %}{% endblock %}
{% if last_seen %}<p class="note">Dane z: {{ last_seen|dt('%d.%m.%Y %H:%M') }}. Kody produktów są wyciągane z nazw i mogą się mylić - przed zakupem sprawdź, czy to ten sam model.</p>{% endif %}
</div>
<script>
(function(){
  const storageKey = 'fajerwerki-coupons-v1';
  let selected = {};
  let storageError = false;
  try { selected = JSON.parse(localStorage.getItem(storageKey) || '{}'); }
  catch (_) { storageError = true; }
  if (!selected || typeof selected !== 'object' || Array.isArray(selected)){
    selected = {};
    storageError = true;
  }

  function formatPrice(value){
    return new Intl.NumberFormat('pl-PL', { style: 'currency', currency: 'PLN' }).format(value);
  }
  function update(){
    document.querySelectorAll('[data-coupon-shop-group]').forEach(card => {
      const shop = card.dataset.couponShopGroup;
      const choices = [...card.querySelectorAll('[data-store-coupon]')];
      choices.forEach(input => { input.checked = !input.disabled && selected[shop] === input.dataset.couponId; });
      const active = choices.find(input => input.checked);
      const base = Number(card.dataset.couponBasePrice);
      const basePrice = card.querySelector('[data-coupon-base]');
      const original = card.querySelector('[data-coupon-original]');
      const discounted = card.querySelector('[data-coupon-discounted]');
      const result = card.querySelector('[data-coupon-result]');
      if (active && Number.isFinite(base) && original && discounted && result){
        const discount = Number(active.dataset.discountValue);
        const price = active.dataset.discountKind === 'percent'
          ? Math.round(base * (1 - discount / 100) * 100) / 100
          : Math.max(0, Math.round((base - discount) * 100) / 100);
        if (basePrice) basePrice.hidden = true;
        original.textContent = formatPrice(base);
        discounted.textContent = formatPrice(price);
        result.hidden = false;
        result.dataset.activeCode = active.dataset.couponCode;
        result.setAttribute('aria-label', `Szacunkowa cena po kodzie ${active.dataset.couponCode}: ${formatPrice(price)}`);
      } else if (result) {
        if (basePrice) basePrice.hidden = false;
        result.hidden = true;
        result.dataset.activeCode = '';
      }
      const note = card.querySelector('[data-coupon-result-note]');
      if (note) note.hidden = !active;
      const storageWarning = card.querySelector('[data-coupon-storage-error]');
      if (storageWarning) storageWarning.hidden = !storageError;
    });
  }
    const cartKey = 'fajerwerki-cart-v2';
    function readCart(){
        try {
            const urls = JSON.parse(localStorage.getItem(cartKey) || '[]');
            return Array.isArray(urls) ? [...new Set(urls.filter(url => typeof url === 'string'))].slice(0, 30) : [];
        } catch (_) { return []; }
    }
    function updateCartControls(){
        const urls = readCart();
        document.querySelectorAll('[data-cart-count]').forEach(node => { node.textContent = urls.length; });
        document.querySelectorAll('[data-cart-add]').forEach(button => {
            const added = urls.includes(button.dataset.url);
            button.textContent = added ? 'Dodano' : urls.length >= 30 ? 'Koszyk pełny' : 'Dodaj do koszyka';
            button.disabled = added || urls.length >= 30;
        });
    }
    window.fajerwerkiCart = {
        read: readCart,
        write(urls){
            try {
                localStorage.setItem(cartKey, JSON.stringify([...new Set(urls)].slice(0, 30)));
                updateCartControls();
                window.dispatchEvent(new Event('fajerwerki:cart-updated'));
                return true;
            } catch (_) { return false; }
        },
    };
    document.addEventListener('click', event => {
        const button = event.target.closest('[data-cart-add]');
        if (!button) return;
        const urls = readCart();
        if (!urls.includes(button.dataset.url)) urls.push(button.dataset.url);
        window.fajerwerkiCart.write(urls);
    });
    document.addEventListener('fajerwerki:products-updated', updateCartControls);
    updateCartControls();
  document.addEventListener('change', event => {
    const input = event.target.closest('[data-store-coupon]');
    if (!input) return;
    const shop = input.dataset.shop;
    if (input.checked) selected[shop] = input.dataset.couponId;
    else if (selected[shop] === input.dataset.couponId) delete selected[shop];
    try { localStorage.setItem(storageKey, JSON.stringify(selected)); storageError = false; }
    catch (_) { storageError = true; }
    update();
  });
  document.addEventListener('click', async event => {
    const button = event.target.closest('[data-copy-coupon]');
    if (!button) return;
    try {
      await navigator.clipboard.writeText(button.dataset.couponCode);
      button.textContent = 'Skopiowano';
      setTimeout(() => { button.textContent = 'Kopiuj kod'; }, 1400);
    } catch (_) {
      button.textContent = button.dataset.couponCode;
    }
  });
  document.addEventListener('fajerwerki:products-updated', update);
  update();
})();
</script>
<script>
(function(){
  if (matchMedia('(prefers-reduced-motion: reduce)').matches) return;

  const canvas = document.createElement('canvas');
  canvas.setAttribute('aria-hidden', 'true');
  canvas.style.cssText = 'position:fixed;inset:0;width:100%;height:100%;pointer-events:none;z-index:-1';
  document.body.prepend(canvas);
  const ctx = canvas.getContext('2d', { alpha: true });
  const DPR = Math.min(window.devicePixelRatio || 1, 2);

  let W = 0, H = 0;
  function resize(){
    W = innerWidth; H = innerHeight;
    canvas.width  = Math.floor(W * DPR);
    canvas.height = Math.floor(H * DPR);
    canvas.style.width  = W + 'px';
    canvas.style.height = H + 'px';
    ctx.setTransform(DPR, 0, 0, DPR, 0, 0);
    ctx.lineCap = 'round';
    ctx.lineJoin = 'round';
  }
  resize();
  addEventListener('resize', resize);

  const isMobile = /Mobi|Android/i.test(navigator.userAgent) || innerWidth < 700;
    const MAX_PARTICLES = isMobile ? 800 : 1900;
    const MAX_ROCKETS   = isMobile ? 8 : 14;

  const PALETTES = {
    redGold: [0, 15, 40],
    gold:    [38, 45, 50],
    blue:    [200, 210, 225],
    purple:  [265, 275, 290, 320],
    green:   [110, 125, 140],
    white:   [null],
    pink:    [315, 330, 345],
    rainbow: [0, 25, 45, 120, 210, 270, 330],
    multi:   [0, 25, 45, 120, 210, 270, 330, null],
  };
  const PAL_KEYS = Object.keys(PALETTES);
  const palette = () => PALETTES[PAL_KEYS[Math.floor(Math.random()*PAL_KEYS.length)]];
  const pick = p => p[Math.floor(Math.random()*p.length)];
  const rnd  = (a,b) => a + Math.random()*(b-a);

  const particles = [];
  const rockets   = [];

  function addParticle(p){
    if (particles.length >= MAX_PARTICLES) return;
    particles.push(p);
  }

  function makeParticle(x, y, vx, vy, life, hue, o){
    o = o || {};
    return {
      x, y, vx, vy,
      life, maxLife: life,
      hue, sat: o.sat || 100,
      size: o.size || 2,
      gravity: o.gravity != null ? o.gravity : 0.045,
      drag: o.drag != null ? o.drag : 0.985,
      trail: !!o.trail, trailLen: o.trailLen || 8,
      flicker: !!o.flicker, strobe: !!o.strobe,
      swim: !!o.swim, swimPhase: o.swimPhase || 0, swimAmp: o.swimAmp || 2,
    flash: !!o.flash,
      hist: [],
      splitAt: o.splitAt || 0, splitType: o.splitType || null, splitDone: false,
      _colCache: null,
    };
  }

  // ---------- wysokości ----------
  function randomHeight(){
    const r = Math.random();
    if (r < 0.15) return H * rnd(0.05, 0.18);   // bardzo wysoko
    if (r < 0.45) return H * rnd(0.18, 0.32);   // wysoko
    if (r < 0.75) return H * rnd(0.32, 0.48);   // średnio
    if (r < 0.92) return H * rnd(0.48, 0.62);   // nisko
    return H * rnd(0.62, 0.75);                  // bardzo nisko
  }
  function heightPower(targetY){
    return 0.85 + (1 - targetY / H) * 0.5; // im wyżej, tym większy bukiet
  }

  // ---------- efekty (wszystkie przyjmują power) ----------
  function spawnSphere(x, y, pal, opts){
    opts = opts || {};
    const power = opts.power || 1;
    const n = Math.floor((opts.count || 100) * (0.85 + power * 0.15));
    const baseSpeed = (opts.speed || 5) * power;
    const multi = opts.multi;
    const color = pick(pal);
    for (let i = 0; i < n; i++){
      const ang = (Math.PI*2*i)/n + rnd(-0.08, 0.08);
      const speedVar = 0.75 + Math.pow(Math.random(), 1.4) * 0.5;
      const s = baseSpeed * speedVar;
      const hue = multi ? pick(pal) : color;
      const hueJitter = hue === null ? null : hue + rnd(-4, 4);
      addParticle(makeParticle(x, y, Math.cos(ang)*s, Math.sin(ang)*s,
        rnd(opts.lifeMin || 60, opts.lifeMax || 90), hueJitter,
        { size: rnd(1.3, 2.3), gravity: opts.gravity || 0.045, drag: opts.drag || 0.985,
          trail: opts.trail, trailLen: opts.trailLen,
          flicker: opts.flicker, strobe: opts.strobe }));
    }
    if (!opts.noFlash){
            addParticle(makeParticle(x, y, 0, 0, 14, color,
                { size: 38 * power, gravity: 0, drag: 1, flash: true }));
      for (let i = 0; i < 6; i++){
        const ang = Math.random()*Math.PI*2, s = rnd(0.2, 0.9) * power;
        addParticle(makeParticle(x, y, Math.cos(ang)*s, Math.sin(ang)*s,
          rnd(8, 18), null, { size: rnd(3, 5), gravity: 0, drag: 0.9 }));
      }
    }
  }

  const EFFECTS = {
    peony: (x,y,p,pw) => spawnSphere(x,y,p,{ count:110, speed:5, power:pw, lifeMin:60, lifeMax:90 }),
    peonyMulti: (x,y,p,pw) => spawnSphere(x,y,p,{ count:130, speed:5, power:pw, multi:true, lifeMin:60, lifeMax:90 }),
    chrysanthemum: (x,y,p,pw) => spawnSphere(x,y,p,{ count:95, speed:4.4, power:pw, trail:true, trailLen:12, lifeMin:80, lifeMax:110, drag:0.978, gravity:0.05 }),
    willow: (x,y,p,pw) => {
      const n = Math.floor(70 * (0.85 + pw*0.15)), color = pick(p);
      for (let i = 0; i < n; i++){
        const ang = (Math.PI*2*i)/n + rnd(-0.15, 0.15);
        const s = rnd(1.8, 3.2) * pw;
        addParticle(makeParticle(x, y, Math.cos(ang)*s, Math.sin(ang)*s - 0.7,
          rnd(110, 150), color === null ? null : color + rnd(-3, 3),
          { size: 1.8, gravity: 0.09, drag: 0.99, trail: true, trailLen: 16, flicker: true }));
      }
    },
    ring: (x,y,p,pw) => {
      const n = 70, color = pick(p);
      const rot = rnd(0, Math.PI), tilt = rnd(0.4, 0.9);
      for (let i = 0; i < n; i++){
        const ang = (Math.PI*2*i)/n, s = rnd(3.5, 4.3) * pw;
        const dx = Math.cos(ang)*s, dy = Math.sin(ang)*s;
        const rx =  dx*Math.cos(rot) - dy*Math.sin(rot);
        const ry = (dx*Math.sin(rot) + dy*Math.cos(rot)) * tilt;
        addParticle(makeParticle(x, y, rx, ry, rnd(65, 85), color,
          { size: 2, gravity: 0.055, drag: 0.982, trail: true, trailLen: 6 }));
      }
    },
    doubleRing: (x,y,p,pw) => {
      const c1 = pick(p), c2 = pick(p);
      const rot = rnd(0, Math.PI), tilt = rnd(0.4, 0.9);
      const ring = (color, baseSpeed, n) => {
        for (let i = 0; i < n; i++){
          const ang = (Math.PI*2*i)/n, s = baseSpeed * pw * rnd(0.95, 1.05);
          const dx = Math.cos(ang)*s, dy = Math.sin(ang)*s;
          const rx =  dx*Math.cos(rot) - dy*Math.sin(rot);
          const ry = (dx*Math.sin(rot) + dy*Math.cos(rot)) * tilt;
          addParticle(makeParticle(x, y, rx, ry, rnd(65, 85), color,
            { size: 2, gravity: 0.055, drag: 0.982, trail: true, trailLen: 6 }));
        }
      };
      ring(c1, 4.5, 70);
      ring(c2, 2.5, 40);
    },
    palm: (x,y,p,pw) => {
      const n = 10 + Math.floor(Math.random()*5), color = pick(p);
      for (let i = 0; i < n; i++){
        const ang = (Math.PI*2*i)/n + rnd(-0.15, 0.15);
        const s = rnd(4, 5.5) * pw;
        addParticle(makeParticle(x, y, Math.cos(ang)*s, Math.sin(ang)*s,
          rnd(90, 120), color,
          { size: 2.8, gravity: 0.06, drag: 0.985, trail: true, trailLen: 14 }));
      }
    },
    crossette: (x,y,p,pw) => {
      const n = 30, color = pick(p);
      for (let i = 0; i < n; i++){
        const ang = (Math.PI*2*i)/n + rnd(-0.1, 0.1), s = 3.8 * pw;
        addParticle(makeParticle(x, y, Math.cos(ang)*s, Math.sin(ang)*s, 50, color,
          { size: 2, gravity: 0.05, drag: 0.97, trail: true,
            splitAt: 0.55, splitType: 'crossette' }));
      }
    },
    crackle: (x,y,p,pw) => {
      const n = 130;
      for (let i = 0; i < n; i++){
        const ang = Math.random()*Math.PI*2, s = rnd(0.8, 4) * pw;
        addParticle(makeParticle(x, y, Math.cos(ang)*s, Math.sin(ang)*s,
          rnd(45, 80), null,
          { size: 1.2, gravity: 0.08, drag: 0.955, flicker: true }));
      }
    },
    strobe: (x,y,p,pw) => {
      const color = pick(p), n = 60;
      for (let i = 0; i < n; i++){
        const ang = (Math.PI*2*i)/n, s = rnd(2.6, 3.8) * pw;
        addParticle(makeParticle(x, y, Math.cos(ang)*s, Math.sin(ang)*s,
          rnd(80, 105), color,
          { size: 2, gravity: 0.03, drag: 0.99, strobe: true }));
      }
    },
    multi: (x,y,p,pw) => {
      EFFECTS.peony(x,y,p,pw);
      setTimeout(() => { if (!document.hidden) EFFECTS.ring(x,y,[pick(p)],pw); }, 180);
      setTimeout(() => { if (!document.hidden) EFFECTS.crackle(x,y,p,pw); }, 420);
    },
    pistil: (x,y,p,pw) => {
      const outer = pick(p), inner = pick(p);
      spawnSphere(x,y,[outer],{ count:90, speed:5, power:pw, lifeMin:60, lifeMax:90 });
      spawnSphere(x,y,[inner],{ count:45, speed:2.5, power:pw, lifeMin:55, lifeMax:80, noFlash:true });
    },
    glitter: (x,y,p,pw) => {
      const color = pick(p), n = Math.floor(180 * (0.8 + pw*0.2));
      for (let i = 0; i < n; i++){
        const ang = Math.random()*Math.PI*2, s = rnd(0.5, 4.5) * pw;
        addParticle(makeParticle(x, y, Math.cos(ang)*s, Math.sin(ang)*s,
          rnd(90, 140), color === null ? null : color + rnd(-5, 5),
          { size: rnd(0.8, 1.6), gravity: 0.06, drag: 0.96, flicker: true, trail: true, trailLen: 4 }));
      }
    },
    horsetail: (x,y,p,pw) => {
      const color = pick(p), n = 100;
      for (let i = 0; i < n; i++){
        const ang = (Math.PI*2*i)/n + rnd(-0.1, 0.1);
        const s = rnd(2.5, 4) * pw;
        addParticle(makeParticle(x, y, Math.cos(ang)*s, Math.sin(ang)*s,
          rnd(100, 130), color,
          { size: 2.2, gravity: 0.09, drag: 0.99, trail: true, trailLen: 12 }));
      }
    },
    fish: (x,y,p,pw) => {
      const color = pick(p), n = 60;
      for (let i = 0; i < n; i++){
        const ang = Math.random()*Math.PI*2, s = rnd(1.5, 3) * pw;
        addParticle(makeParticle(x, y, Math.cos(ang)*s, Math.sin(ang)*s,
          rnd(80, 120), color,
          { size: 1.8, gravity: 0.06, drag: 0.985, swim: true, swimAmp: rnd(1.5, 3) }));
      }
    },
    spiral: (x,y,p,pw) => {
      const color = pick(p);
      for (let arm = 0; arm < 3; arm++){
        for (let i = 0; i < 25; i++){
          const t = i / 25;
          const ang = arm * (Math.PI*2/3) + t * Math.PI*2;
          const s = (1 + t * 4) * pw;
          addParticle(makeParticle(x, y, Math.cos(ang)*s, Math.sin(ang)*s,
            rnd(70, 95), color,
            { size: 1.8, gravity: 0.05, drag: 0.985, trail: true, trailLen: 8 }));
        }
      }
    },
    star: (x,y,p,pw) => {
      const color = pick(p), points = 5;
      for (let i = 0; i < 100; i++){
        const ang = (Math.PI*2 * i) / 100;
        const r = 1 + 0.5 * Math.cos(points * ang);
        const s = 4 * r * pw;
        addParticle(makeParticle(x, y, Math.cos(ang)*s, Math.sin(ang)*s,
          rnd(60, 80), color,
          { size: 1.8, gravity: 0.05, drag: 0.985, trail: true, trailLen: 6 }));
      }
    },
    heart: (x,y,p,pw) => {
      const color = pick(p);
      for (let i = 0; i < 100; i++){
        const t = (Math.PI*2 * i) / 100;
        const hx = 16 * Math.pow(Math.sin(t), 3);
        const hy = -(13 * Math.cos(t) - 5 * Math.cos(2*t) - 2 * Math.cos(3*t) - Math.cos(4*t));
        const scale = 0.3 * pw;
        addParticle(makeParticle(x, y, hx * scale, hy * scale,
          rnd(70, 90), color,
          { size: 2, gravity: 0.04, drag: 0.99, trail: true, trailLen: 6 }));
      }
    },
    halfHalf: (x,y,p,pw) => {
      const c1 = pick(p), c2 = pick(p), n = 100;
      for (let i = 0; i < n; i++){
        const ang = (Math.PI*2*i)/n;
        const s = 5 * pw * rnd(0.85, 1.15);
        const color = Math.sin(ang) < 0 ? c1 : c2;
        addParticle(makeParticle(x, y, Math.cos(ang)*s, Math.sin(ang)*s,
          rnd(60, 85), color,
          { size: 2, gravity: 0.05, drag: 0.985 }));
      }
    },
    atomic: (x,y,p,pw) => {
      const color = pick(p);
      for (let i = 0; i < 30; i++){
        const ang = Math.random()*Math.PI*2, s = rnd(0.3, 1) * pw;
        addParticle(makeParticle(x, y, Math.cos(ang)*s, Math.sin(ang)*s,
          rnd(20, 40), null, { size: 2.5, gravity: 0.02, drag: 0.95, flicker: true }));
      }
      for (let i = 0; i < 70; i++){
        const ang = (Math.PI*2*i)/70, s = rnd(3.5, 4.5) * pw;
        addParticle(makeParticle(x, y, Math.cos(ang)*s, Math.sin(ang)*s,
          rnd(70, 95), color,
          { size: 1.8, gravity: 0.05, drag: 0.985, trail: true, trailLen: 8 }));
      }
    },
    brocade: (x,y,p,pw) => {
      const color = 40, n = 120;
      for (let i = 0; i < n; i++){
        const ang = (Math.PI*2*i)/n + rnd(-0.1, 0.1);
        const s = rnd(2.5, 4.5) * pw;
        addParticle(makeParticle(x, y, Math.cos(ang)*s, Math.sin(ang)*s,
          rnd(110, 150), color,
          { size: 1.8, gravity: 0.07, drag: 0.992, trail: true, trailLen: 16, flicker: true }));
      }
    },
    cracklingWillow: (x,y,p,pw) => {
      const color = pick(p), n = 60;
      for (let i = 0; i < n; i++){
        const ang = (Math.PI*2*i)/n + rnd(-0.15, 0.15);
        const s = rnd(2, 3.2) * pw;
        addParticle(makeParticle(x, y, Math.cos(ang)*s, Math.sin(ang)*s - 0.5,
          rnd(100, 130), color,
          { size: 1.8, gravity: 0.09, drag: 0.99, trail: true, trailLen: 14,
            splitAt: 0.7, splitType: 'crackle' }));
      }
    },
  };
  const EFFECT_KEYS = Object.keys(EFFECTS);

  // ---------- rakieta ----------
  function spawnRocket(x, baseY, targetY, effect, pal){
    if (rockets.length >= MAX_ROCKETS) return;
    rockets.push({
      x, y: baseY, vx: rnd(-0.3, 0.3), vy: -rnd(8.5, 11),
      targetY, hue: pick(pal), effect, pal,
      wobblePhase: rnd(0, Math.PI*2), wobbleAmp: rnd(0.15, 0.5),
    age: 0, hist: [],
      power: heightPower(targetY),
    });
  }

  // ---------- wyrzutnie ----------
  function launchSingle(){
    const effect = EFFECT_KEYS[Math.floor(Math.random()*EFFECT_KEYS.length)];
    const targetY = randomHeight();
    spawnRocket(rnd(80, W-80), H + 10, targetY, effect, palette());
  }
  function launchBarrage(){
    const n = 3 + Math.floor(Math.random()*4);
    const baseX = rnd(120, W-120), pal = palette();
    const effect = EFFECT_KEYS[Math.floor(Math.random()*EFFECT_KEYS.length)];
    const baseY = randomHeight();
    for (let i = 0; i < n; i++){
      setTimeout(() => {
        if (document.hidden) return;
        spawnRocket(baseX + rnd(-80, 80), H + 10, baseY + rnd(-30, 30), effect, pal);
      }, i*220);
    }
  }
  function launchRomanCandle(){
    const x = rnd(80, W-80), n = 8 + Math.floor(Math.random()*6);
    const pal = palette();
    for (let i = 0; i < n; i++){
      setTimeout(() => {
        if (document.hidden) return;
        const targetY = H * (0.55 - i * 0.04) + rnd(-20, 20);
        spawnRocket(x + rnd(-15, 15), H + 10, targetY, 'crackle', pal);
      }, i*110);
    }
  }
  function launchFinale(){
    const n = 5 + Math.floor(Math.random()*4);
    for (let i = 0; i < n; i++) setTimeout(() => {
      if (!document.hidden) launchSingle();
    }, i*140);
  }
  function launchFan(){
    const n = 4 + Math.floor(Math.random()*3);
    const baseX = rnd(150, W-150), pal = palette();
    const baseY = randomHeight();
    const effect = EFFECT_KEYS[Math.floor(Math.random()*EFFECT_KEYS.length)];
    for (let i = 0; i < n; i++){
      setTimeout(() => {
        if (document.hidden) return;
        const offset = (i - (n-1)/2) * 60;
        spawnRocket(baseX + offset, H + 10, baseY + rnd(-15, 15), effect, pal);
      }, i*100);
    }
  }
  function launchColumn(){
    const x = rnd(100, W-100), pal = palette();
    const n = 3 + Math.floor(Math.random()*3);
    const effect = EFFECT_KEYS[Math.floor(Math.random()*EFFECT_KEYS.length)];
    for (let i = 0; i < n; i++){
      setTimeout(() => {
        if (document.hidden) return;
        spawnRocket(x + rnd(-30, 30), H + 10, H * (0.15 + i * 0.15), effect, pal);
      }, i*280);
    }
  }
  function launchScatter(){
    const n = 3 + Math.floor(Math.random()*3);
    for (let i = 0; i < n; i++){
      setTimeout(() => {
        if (document.hidden) return;
        launchSingle();
      }, i*180);
    }
  }

  const LAUNCHERS = [
    { fn: launchSingle,       w: 38 },
    { fn: launchBarrage,      w: 14 },
    { fn: launchRomanCandle,  w: 12 },
    { fn: launchFinale,       w: 8 },
    { fn: launchFan,          w: 10 },
    { fn: launchColumn,       w: 8 },
    { fn: launchScatter,      w: 10 },
  ];
  const TW = LAUNCHERS.reduce((s,l)=>s+l.w,0);
  function launchRandom(){
    let r = Math.random()*TW;
    for (const l of LAUNCHERS){ if (r < l.w){ l.fn(); return; } r -= l.w; }
    launchSingle();
  }

  // ---------- update / draw ----------
  function updateParticle(p, dt){
    p.vx *= p.drag;
    p.vy *= p.drag;
    p.vy += p.gravity * dt;

    if (p.swim){
      p.swimPhase += 0.15 * dt;
      const speed = Math.hypot(p.vx, p.vy) || 1;
      const perpX = -p.vy / speed, perpY = p.vx / speed;
      const wob = Math.sin(p.swimPhase) * p.swimAmp * 0.05;
      p.vx += perpX * wob * dt;
      p.vy += perpY * wob * dt;
    }

    if (p.trail){
      p.hist.push(p.x, p.y);
      const max = (p.trailLen || 8) * 2;
      if (p.hist.length > max) p.hist.splice(0, p.hist.length - max);
    }
    p.x += p.vx * dt;
    p.y += p.vy * dt;
    p.life -= dt;

    if (p.splitAt > 0 && !p.splitDone && p.life <= p.maxLife * p.splitAt){
      p.splitDone = true;
      if (p.splitType === 'crossette'){
        for (let i = 0; i < 4; i++){
          const ang = (Math.PI/2)*i + rnd(-0.25, 0.25), s = 1.8;
          addParticle(makeParticle(p.x, p.y,
            p.vx*0.25 + Math.cos(ang)*s, p.vy*0.25 + Math.sin(ang)*s,
            30, p.hue, { size: 1.5, gravity: 0.06, drag: 0.97, trail: true, trailLen: 5 }));
        }
      } else if (p.splitType === 'crackle'){
        for (let i = 0; i < 3; i++){
          const ang = Math.random()*Math.PI*2, s = rnd(0.5, 1.5);
          addParticle(makeParticle(p.x, p.y, Math.cos(ang)*s, Math.sin(ang)*s,
            15, null, { size: 1, gravity: 0.05, drag: 0.95, flicker: true }));
        }
      }
    }
  }

  function particleColor(p, age){
    if (p.hue === null) return '#ffffff';
    const bucket = Math.min(19, Math.floor(age * 19));
    if (!p._colCache) p._colCache = [];
    if (p._colCache[bucket]) return p._colCache[bucket];
    const a = bucket / 19;
    let L;
    if (a < 0.12) L = 100 - (a / 0.12) * 38;
    else          L = Math.max(0, 62 - (a - 0.12) * 62);
    const c = `hsl(${p.hue}, ${p.sat}%, ${L}%)`;
    p._colCache[bucket] = c;
    return c;
  }

  function drawParticle(p){
    const age = 1 - p.life / p.maxLife;
    if (age < 0 || age > 1) return;

    let alpha = 1 - Math.pow(age, 2.4);
    if (p.strobe) alpha *= (Math.floor(p.life / 3) % 2 === 0) ? 1 : 0.08;
    else if (p.flicker) alpha *= 0.55 + Math.random() * 0.6;
    if (alpha <= 0.01) return;

    const color = particleColor(p, age);

        if (p.flash){
            const radius = p.size * (0.25 + age * 0.75);
            const hue = p.hue === null ? 42 : p.hue;
            const glow = ctx.createRadialGradient(p.x, p.y, 0, p.x, p.y, radius);
            glow.addColorStop(0, `hsla(${hue}, 100%, 96%, ${alpha})`);
            glow.addColorStop(0.14, `hsla(${hue}, 100%, 76%, ${alpha * 0.8})`);
            glow.addColorStop(1, `hsla(${hue}, 100%, 55%, 0)`);
            ctx.fillStyle = glow;
            ctx.globalAlpha = 1;
            ctx.beginPath();
            ctx.arc(p.x, p.y, radius, 0, Math.PI*2);
            ctx.fill();
            return;
        }

    if (p.trail && p.hist.length >= 4){
      const N = p.hist.length;
      const mid = (N >> 2) << 1;
      ctx.strokeStyle = color;
      ctx.globalAlpha = alpha * 0.22;
      ctx.lineWidth = p.size * 0.55;
      ctx.beginPath();
      ctx.moveTo(p.hist[0], p.hist[1]);
      for (let i = 2; i < mid; i += 2) ctx.lineTo(p.hist[i], p.hist[i+1]);
      ctx.stroke();
      ctx.globalAlpha = alpha * 0.7;
      ctx.lineWidth = p.size * 0.9;
      ctx.beginPath();
      ctx.moveTo(p.hist[mid], p.hist[mid+1]);
      for (let i = mid + 2; i < N; i += 2) ctx.lineTo(p.hist[i], p.hist[i+1]);
      ctx.lineTo(p.x, p.y);
      ctx.stroke();
    }

    ctx.fillStyle = color;
    ctx.globalAlpha = alpha * 0.18;
    ctx.beginPath();
    ctx.arc(p.x, p.y, p.size * 3.2, 0, Math.PI*2);
    ctx.fill();

    ctx.globalAlpha = alpha;
    ctx.beginPath();
    ctx.arc(p.x, p.y, p.size, 0, Math.PI*2);
    ctx.fill();
  }

  // ---------- pętla ----------
  let running = true, lastT = 0;
  function tick(t){
    if (!running) return;
    if (!lastT) lastT = t;
    let dt = (t - lastT) / 16.667;
    if (dt > 3) dt = 3;
    lastT = t;

    ctx.clearRect(0, 0, W, H);
    ctx.globalCompositeOperation = 'lighter';

    for (let i = rockets.length - 1; i >= 0; i--){
      const r = rockets[i];
    r.hist.push(r.x, r.y);
    if (r.hist.length > 22) r.hist.splice(0, 2);
      r.age += dt;
      const wob = Math.sin(r.age * 0.15 + r.wobblePhase) * r.wobbleAmp;
      r.x += (r.vx + wob * 0.1) * dt;
      r.y += r.vy * dt;
      r.vy += 0.09 * dt;

      if (Math.random() < 0.85){
        addParticle(makeParticle(
          r.x + rnd(-1, 1), r.y + rnd(0, 4),
          rnd(-0.5, 0.5), rnd(0.2, 1.2),
          rnd(8, 18), null,
          { size: rnd(0.7, 1.4), gravity: 0.05, drag: 0.93 }));
      }

      const rc = r.hue === null ? '#ffffff' : `hsl(${r.hue}, 100%, 78%)`;
            if (r.hist.length >= 4){
                const tail = ctx.createLinearGradient(r.hist[0], r.hist[1], r.x, r.y);
                tail.addColorStop(0, 'rgba(255,255,255,0)');
                tail.addColorStop(1, rc);
                ctx.strokeStyle = tail;
                ctx.globalAlpha = 0.85;
                ctx.lineWidth = 2.2;
                ctx.beginPath();
                ctx.moveTo(r.hist[0], r.hist[1]);
                for (let point = 2; point < r.hist.length; point += 2){
                    ctx.lineTo(r.hist[point], r.hist[point + 1]);
                }
                ctx.lineTo(r.x, r.y);
                ctx.stroke();
            }
      ctx.fillStyle = rc;
      ctx.globalAlpha = 0.35;
            ctx.shadowBlur = 18;
            ctx.shadowColor = rc;
      ctx.beginPath(); ctx.arc(r.x, r.y, 9, 0, Math.PI*2); ctx.fill();
            ctx.shadowBlur = 0;
      ctx.globalAlpha = 1;
      ctx.beginPath(); ctx.arc(r.x, r.y, 2.4, 0, Math.PI*2); ctx.fill();

      if (r.y <= r.targetY || r.vy >= -0.5){
        (EFFECTS[r.effect] || EFFECTS.peony)(r.x, r.y, r.pal, r.power);
        rockets.splice(i, 1);
      }
    }

    for (let i = particles.length - 1; i >= 0; i--){
      const p = particles[i];
      updateParticle(p, dt);
      drawParticle(p);
      if (p.life <= 0) particles.splice(i, 1);
    }

    ctx.globalAlpha = 1;
    ctx.globalCompositeOperation = 'source-over';
    requestAnimationFrame(tick);
  }
  requestAnimationFrame(tick);

  let nextLaunch;
  function autoLaunch(){
    if (document.hidden){ nextLaunch = setTimeout(autoLaunch, 1000); return; }
    launchRandom();
    nextLaunch = setTimeout(autoLaunch, rnd(950, 1750));
  }
  setTimeout(autoLaunch, 350);

  document.addEventListener('visibilitychange', () => {
    if (document.hidden){
      running = false;
      clearTimeout(nextLaunch);
    } else if (!running){
      running = true; lastT = 0;
      requestAnimationFrame(tick);
      nextLaunch = setTimeout(autoLaunch, 500);
    }
  });
})();
</script>
</body></html>""",

    "coupon_controls.html": """{% macro coupon_controls(it) %}{% set shop_key = coupon_shop_key(it.site) %}{% set coupon_options = coupons_by_shop.get(shop_key, []) if shop_key else [] %}{% set categories = product_categories(it.name, it.category) %}{% set eligible_coupons = [] %}{% for coupon in coupon_options %}{% if (not coupon.category or coupon.category in categories) and (not coupon.excludes_promos or not it.promo) %}{% set _ = eligible_coupons.append(coupon) %}{% endif %}{% endfor %}{% if eligible_coupons and it.price is not none %}<div class="coupon-options"><span class="note">Kod rabatowy dla {{ it.site }}:</span>{% for coupon in eligible_coupons %}<label class="coupon-choice"><input type="checkbox" data-store-coupon data-shop="{{ shop_key }}" data-coupon-id="{{ coupon.id }}" data-coupon-code="{{ coupon.code }}" data-discount-kind="{{ coupon.discount_kind }}" data-discount-value="{{ coupon.discount_value }}" title="{{ coupon.terms or '' }}"> Uwzględnij {{ coupon.code }} (−{{ coupon.percent ~ '%' if coupon.discount_kind=='percent' else coupon.amount ~ ' zł' }})</label><button type="button" class="sec sm" data-copy-coupon data-coupon-code="{{ coupon.code }}">Kopiuj kod</button>{% endfor %}<div class="coupon-result-note note" data-coupon-result-note hidden>Cena jest szacunkowa dla jednej sztuki; sprawdź warunki kodu i wklej go w sklepie.</div><div class="coupon-storage-error note" data-coupon-storage-error aria-live="polite" hidden>Nie udało się zapamiętać wyboru kuponu; pozostanie aktywny tylko do odświeżenia strony.</div></div>{% endif %}{% endmacro %}""",

    "card.html": """{% from 'coupon_controls.html' import coupon_controls with context %}{% macro card(it) %}{% set shop_key = coupon_shop_key(it.site) %}{% set coupon_options = coupons_by_shop.get(shop_key, []) if shop_key else [] %}<div class="card{{ ' dim' if it.hidden }}"{% if coupon_options and it.price is not none %} data-coupon-shop-group="{{ shop_key }}" data-coupon-base-price="{{ it.price }}"{% endif %}><div class="top"><span class="shop">{{ it.site }}</span>{% if it.code %}<span class="code">{{ it.code }}</span>{% endif %}{% if it.promo %}<span class="badge r">promocja wykryta</span>{% endif %}
{% if it.rank is not none %}<span class="code">przypięty</span>{% endif %}{% if it.hidden %}<span class="code">ukryty</span>{% endif %}{% if it.note %}<span class="best">{{ it.note }}</span>{% endif %}
{% if is_admin and it.edited %}<span class="code">edytowany</span>{% endif %}<span class="dot {{ 'ok' if it.avail=='in_stock' }}" title="{{ 'dostępny' if it.avail=='in_stock' else 'niedostępny' }}"></span></div>
<a class="name" href="{{ url_for('product', u=it.url) }}">{{ it.name }}</a><div class="row"><span class="price" data-coupon-base>{{ it.price|pln }}</span>{% if coupon_options and it.price is not none %}<span class="coupon-result" data-coupon-result hidden><span class="old" data-coupon-original></span><b class="price" data-coupon-discounted></b></span>{% endif %}
{% if it.prev_price and it.price is not none and it.price != it.prev_price %}<span class="old">{{ it.prev_price|pln }}</span><span class="{{ 'down' if it.price < it.prev_price else 'up' }}">{{ '−' if it.price < it.prev_price else '+' }}{{ it.drop_pct|pct }}</span>{% endif %}
{% if it.key_shops and it.key_shops > 1 %}{% if it.avail=='in_stock' and it.price is not none and it.price == it.key_min %}<span class="best">najtaniej</span>{% endif %}<a class="mini" href="{{ url_for('compare', k=it.code_key) }}">{{ it.key_shops|shops }}</a>{% endif %}
</div><div class="note">zmiana: {{ it.changed_at|dt }}</div>
{{ coupon_controls(it) }}
<div class="qa"><button type="button" class="sec sm" data-cart-add data-url="{{ it.url }}">Dodaj do koszyka</button>{% if it.cheapest_url %}<a class="btn sm" href="{{ it.cheapest_url }}" target="_blank" rel="noopener noreferrer">Najtaniej teraz</a>{% endif %}{% if is_admin %}<form method="post" action="{{ url_for('admin_quick') }}" class="qa"><input type="hidden" name="csrf" value="{{ csrf }}"><input type="hidden" name="u" value="{{ it.url }}"><input type="hidden" name="back" value="{{ request.full_path.rstrip('?') }}">
<button class="sec sm" name="act" value="{{ 'unpin' if it.rank is not none else 'pin' }}">{{ 'Odepnij' if it.rank is not none else 'Przypnij na górze' }}</button>
<button class="sec sm" name="act" value="{{ 'unhide' if it.hidden else 'hide' }}">{{ 'Pokaż' if it.hidden else 'Ukryj' }}</button><a class="btn sm sec" href="{{ url_for('admin_product', u=it.url) }}">Edytuj</a></form>{% endif %}</div></div>{% endmacro %}""",

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

    "index.html": """{% extends 'base.html' %}
{% block head %}<form class="s" method="get" action="{{ url_for('index') }}" data-product-search><input type="search" name="q" value="{{ q }}" placeholder="nazwa lub kod, np. PXO310" autocomplete="off"><button style="width:auto">Szukaj</button></form><p id="search-status" class="note" aria-live="polite">Wyniki aktualizują się podczas wpisywania.</p>
<details {{ 'open' if request.args.get('site') or request.args.get('a') or request.args.get('d') or request.args.get('min') or request.args.get('max') or request.args.get('s') or request.args.get('cheapest') }}><summary>Filtry i sortowanie</summary>
<form method="get" class="f"><input type="hidden" name="q" value="{{ q }}">
<label>Sortuj<select name="s">{% for k,(label,_) in sorts.items() %}<option value="{{ k }}" {{ 'selected' if k==s }}>{{ label }}</option>{% endfor %}</select></label>
<label>Sklep<select name="site" multiple size="3">{% for sh in shops %}<option value="{{ sh.site }}" {{ 'selected' if sh.site in sel_sites }}>{{ sh.site }} ({{ sh.n }})</option>{% endfor %}</select></label>
<label>Cena od<input name="min" inputmode="decimal" value="{{ request.args.get('min','') }}"></label><label>Cena do<input name="max" inputmode="decimal" value="{{ request.args.get('max','') }}"></label>
<label class="chk"><input type="checkbox" name="a" value="1" {{ 'checked' if request.args.get('a')=='1' }}> tylko dostępne</label><label class="chk"><input type="checkbox" name="d" value="1" {{ 'checked' if request.args.get('d')=='1' }}> tylko obniżki (14 dni)</label>
<label class="chk"><input type="checkbox" name="cheapest" value="1" {{ 'checked' if request.args.get('cheapest')=='1' }}> tylko najtańsze wśród sklepów</label>
<button style="grid-column:1/3">Zastosuj</button></form></details>{% endblock %}
{% block body %}{% include 'product_results.html' %}
<script>
(() => {
  const form = document.querySelector('[data-product-search]');
  const input = form.elements.q;
  const status = document.getElementById('search-status');
  let timer;
  let controller;
  async function updateResults() {
    if (controller) controller.abort();
    controller = new AbortController();
    const url = new URL(form.action, location.href);
    const current = new URL(location.href);
    current.searchParams.forEach((value, key) => {
      if (key !== 'q' && key !== 'page' && key !== '_partial') url.searchParams.append(key, value);
    });
    url.searchParams.set('q', input.value);
    url.searchParams.set('_partial', '1');
    status.textContent = 'Szukam…';
    try {
      const response = await fetch(url, { signal: controller.signal });
      if (!response.ok) throw new Error(`HTTP ${response.status}`);
      const parsed = new DOMParser().parseFromString(await response.text(), 'text/html');
      const next = parsed.getElementById('product-results');
      const currentResults = document.getElementById('product-results');
      if (!next || !currentResults) throw new Error('Nieprawidłowa odpowiedź serwera.');
      currentResults.replaceWith(next);
      document.dispatchEvent(new Event('fajerwerki:products-updated'));
      const filterQuery = document.querySelector('.f input[name="q"]');
      if (filterQuery) filterQuery.value = input.value;
      url.searchParams.delete('_partial');
      history.replaceState(null, '', url);
      status.textContent = 'Wyniki zaktualizowane.';
    } catch (error) {
      if (error.name !== 'AbortError') status.textContent = 'Nie udało się odświeżyć wyników. Użyj przycisku Szukaj.';
    }
  }
  form.addEventListener('submit', event => { event.preventDefault(); clearTimeout(timer); updateResults(); });
  input.addEventListener('input', () => { clearTimeout(timer); timer = setTimeout(updateResults, 250); });
})();
</script>{% endblock %}""",
    "product_results.html": """{% from 'card.html' import card with context %}<div id="product-results"><div class="meta">{{ total }} produktów · <a href="{{ export_url() }}" style="text-decoration:underline">pobierz CSV</a></div>
{% for it in items %}{{ card(it) }}{% else %}<div class="card">Brak wyników.</div>{% endfor %}
<div class="pager"><a class="{{ '' if page>1 else 'off' }}" href="{{ url_with(page=page-1) if page>1 else '#' }}">← wstecz</a><span class="note">{{ page }} / {{ pages }}</span><a class="{{ '' if page<pages else 'off' }}" href="{{ url_with(page=page+1) if page<pages else '#' }}">dalej →</a></div></div>""",

    "product.html": """{% extends 'base.html' %}{% from 'card.html' import card with context %}{% from 'coupon_controls.html' import coupon_controls with context %}
{% block body %}<h1>{{ it.name }}</h1><div class="top"><span class="shop">{{ it.site }}</span>{% if it.code %}<span class="code">{{ it.code }}</span>{% endif %}<span class="note">{{ 'dostępny' if it.avail=='in_stock' else 'niedostępny' }}</span>{% if it.note %}<span class="best">{{ it.note }}</span>{% endif %}</div>
{% set shop_key = coupon_shop_key(it.site) %}{% set coupon_options = coupons_by_shop.get(shop_key, []) if shop_key else [] %}
<div class="stats"><div class="stat"{% if coupon_options and it.price is not none %} data-coupon-shop-group="{{ shop_key }}" data-coupon-base-price="{{ it.price }}"{% endif %}><span class="note">teraz</span><b data-coupon-base>{{ it.price|pln }}</b>{% if coupon_options and it.price is not none %}<span class="coupon-result" data-coupon-result hidden><span class="old" data-coupon-original></span><b class="price" data-coupon-discounted></b></span>{{ coupon_controls(it) }}{% endif %}</div><div class="stat"><span class="note">najniżej</span><b>{{ it.min_price|pln }}</b></div><div class="stat"><span class="note">najwyżej</span><b>{{ it.max_price|pln }}</b></div></div>
{{ chart|safe }}{% if not chart %}<p class="note">Brak historii cen.</p>{% endif %}<p><a class="btn" href="{{ it.url }}" target="_blank" rel="noopener noreferrer">Otwórz w sklepie</a>
{% if is_admin %} <a class="btn sec" href="{{ url_for('admin_product', u=it.url) }}">Edytuj</a>{% endif %}</p>
{% if is_admin and it.edited %}<div class="note">Ten produkt ma ręczne zmiany (cena ze scrapera: {{ it.o_price|pln }}).</div>{% endif %}
{% if it.promo %}<p class="note">Scraper wykrył oznaczenie promocji. Kod rabatowy może nie obejmować tego produktu — sprawdź warunki sklepu.</p>{% endif %}
{% if others %}<h2>Ten sam kod w innych sklepach</h2>{% for o in others %}{{ card(o) }}{% endfor %}{% endif %}
<h2>Historia zmian</h2><table><tr><th>kiedy</th><th>cena</th><th>stan</th></tr>{% for ts,p,av in hist %}<tr><td>{{ ts|dt('%d.%m.%Y %H:%M') }}</td><td>{{ p|pln }}</td><td>{{ 'dostępny' if av=='in_stock' else 'brak' }}</td></tr>{% endfor %}</table>{% endblock %}""",

    "compare.html": """{% extends 'base.html' %}{% from 'card.html' import card with context %}
    {% block body %}<h1>{{ rows[0].name }}</h1><p class="note">{% if key %}Kod {{ key }} · {% endif %}{{ rows|length }} ofert, dostępne przed niedostępnymi, od najtańszej. Najedź na punkt wykresu po szczegóły.</p>
        {% if chart %}<div class="price-chart-wrap">{{ chart|safe }}<div class="price-chart-tooltip" role="status" hidden></div></div>
<script>
(() => {
    const wrap = document.querySelector('.price-chart-wrap');
    if (!wrap) return;
    const svg = wrap.querySelector('svg.price-history');
    const tooltip = wrap.querySelector('.price-chart-tooltip');
    const points = [...svg.querySelectorAll('.price-point')].map(point => ({
        x: Number(point.dataset.x),
        label: point.dataset.tooltip,
    }));
    if (!points.length) return;
    wrap.addEventListener('pointermove', event => {
        const rect = svg.getBoundingClientRect();
        const x = (event.clientX - rect.left) * svg.viewBox.baseVal.width / rect.width;
        let nearest = points[0];
        for (const point of points) {
            if (Math.abs(point.x - x) < Math.abs(nearest.x - x)) nearest = point;
        }
        tooltip.textContent = nearest.label;
        tooltip.hidden = false;
        const bounds = wrap.getBoundingClientRect();
        const left = event.clientX - bounds.left + 12;
        const top = event.clientY - bounds.top - tooltip.offsetHeight - 12;
        tooltip.style.left = `${Math.max(4, Math.min(left, bounds.width - tooltip.offsetWidth - 4))}px`;
        tooltip.style.top = `${Math.max(4, top)}px`;
    });
    wrap.addEventListener('pointerleave', () => { tooltip.hidden = true; });
})();
</script>
{% else %}<p class="note">Brak historii cen dla tych ofert.</p>{% endif %}
{% for r in rows %}{{ card(r) }}{% endfor %}{% endblock %}""",

        "basket.html": """{% extends 'base.html' %}
{% block body %}<h1>Koszyk</h1><p class="note">Dodaj produkty z listy, a tutaj porównasz aktualne oferty i pełne koszyki sklepów.</p>
<div id="basket-settings" data-endpoint="{{ url_for('basket') }}" class="f">
<label>Cena<select id="basket-price-mode"><option value="current">Aktualna</option><option value="historical">Najniższa historyczna</option></select></label>
<label>Sklep<select id="basket-site"><option value="">Porównaj wszystkie</option>{% for sh in shops %}<option value="{{ sh.site }}">{{ sh.site }}</option>{% endfor %}</select></label>
<label class="chk" style="grid-column:1/3"><input type="checkbox" id="basket-unavailable"> Uwzględnij także niedostępne oferty</label>
<button type="button" class="sec" data-cart-clear style="grid-column:1/3">Wyczyść koszyk</button></div>
<p id="basket-status" class="note" role="status" aria-live="polite">Wczytywanie koszyka...</p>
{% include 'basket_results.html' %}
<script>
document.addEventListener('DOMContentLoaded', () => {
    const settings = document.getElementById('basket-settings');
    const status = document.getElementById('basket-status');
    const cart = window.fajerwerkiCart;
    let controller;
    async function renderBasket(){
        if (controller) controller.abort();
        controller = new AbortController();
        const urls = cart.read();
        const params = new URLSearchParams({ _partial: '1', price_mode: document.getElementById('basket-price-mode').value,
            site: document.getElementById('basket-site').value });
        if (document.getElementById('basket-unavailable').checked) params.set('unavailable', '1');
        urls.forEach(url => params.append('u', url));
        status.textContent = 'Przeliczam oferty...';
        try {
            const response = await fetch(`${settings.dataset.endpoint}?${params}`, { signal: controller.signal });
            if (!response.ok) throw new Error(`HTTP ${response.status}`);
            const parsed = new DOMParser().parseFromString(await response.text(), 'text/html');
            const current = document.getElementById('basket-results');
            const next = parsed.getElementById('basket-results');
            if (!current || !next) throw new Error('Nieprawidłowa odpowiedź serwera.');
            current.replaceWith(next);
            status.textContent = `${urls.length} ${urls.length === 1 ? 'produkt' : 'produktów'} w koszyku`;
        } catch (error) {
            if (error.name !== 'AbortError') status.textContent = 'Nie udało się przeliczyć koszyka. Spróbuj ponownie.';
        }
    }
    document.addEventListener('click', event => {
        const remove = event.target.closest('[data-cart-remove]');
        if (remove) cart.write(cart.read().filter(url => url !== remove.dataset.url));
        if (event.target.closest('[data-cart-clear]')) cart.write([]);
    });
    settings.addEventListener('change', renderBasket);
    window.addEventListener('fajerwerki:cart-updated', renderBasket);
    window.addEventListener('storage', renderBasket);
    renderBasket();
});
</script>{% endblock %}""",
    "coupons.html": """{% extends 'base.html' %}{% block body %}<h1>Kody rabatowe</h1><p class="note">Sprawdź warunki i ważność kodu przed zakupem. Sklepy mogą wykluczać produkty w promocji; scraper wykrywa tylko część takich oznaczeń, więc brak etykiety nie potwierdza, że kod zadziała.</p>
{% for c in rows %}<div class="card"><div class="top"><span class="shop">{{ c.shop }}</span><span class="code">{{ c.code }}</span><span class="best">{{ c.discount }}</span></div>
{% if c.image %}<img src="{{ url_for('coupon_image', coupon_id=c.id) }}" alt="Zdjęcie źródła kodu {{ c.code }}" loading="lazy" style="display:block;max-width:100%;max-height:360px;object-fit:contain;margin:10px 0">{% endif %}
<div class="note">Zakres: {{ c.category or 'wszystkie produkty' }}</div>{% if c.terms %}<p>{{ c.terms }}</p>{% endif %}{% if c.excludes_promos %}<p class="note">Nie łączy się z innymi promocjami.</p>{% endif %}<div class="note">{% if c.valid_until %}ważny do {{ c.valid_until|dt('%d.%m.%Y') }}{% else %}brak podanej daty końca{% endif %}{% if c.source %} · <a href="{{ c.source }}" target="_blank" rel="noopener noreferrer" style="text-decoration:underline">źródło</a>{% endif %}</div></div>
{% else %}<div class="card">Nie ma teraz aktywnych kodów rabatowych.</div>{% endfor %}{% endblock %}""",

    "basket_results.html": """<div id="basket-results">{% if plan %}<div class="stats"><div class="stat"><span class="note">Najtańszy miks sklepów</span><b>{{ plan.mix_total|pln }}</b><span class="note">{% if plan.mix_missing %}brak ofert dla {{ plan.mix_missing }} pozycji{% else %}wszystkie pozycje dostępne{% endif %}</span></div>
<div class="stat"><span class="note">Najtaniej w jednym sklepie</span><b>{{ plan.best_store.total|pln if plan.best_store else 'brak pełnej oferty' }}</b><span class="note">{{ plan.best_store.site if plan.best_store else 'żaden sklep nie ma wszystkich dostępnych pozycji' }}</span></div></div>
{% if plan.most_products_store %}<div class="card"><div class="top"><strong>Najwięcej pozycji ma {{ plan.most_products_store.site }}</strong><span class="best">{{ plan.most_products_store.count }} z {{ plan.lines|length }} produktów</span><span class="price">{{ plan.most_products_store.total|pln }}</span></div>
{% for product in plan.most_products_store.products %}<div class="row"><a class="name" href="{{ product.url }}" target="_blank" rel="noopener noreferrer">{{ product.name }}</a>{% if product.coupon %}<span class="code">{{ product.coupon.code }}</span><span class="old">{{ product.base_price|pln }}</span>{% endif %}<span class="price">{{ product.price|pln }}</span><span class="note">{{ 'dostępny' if product.availability=='in_stock' else 'niedostępny' }}</span></div>{% endfor %}</div>{% endif %}
{% if plan.price_mode=='historical' %}<p class="note">Ceny historyczne nie oznaczają dostępności produktu w tej chwili. Kody rabatowe stosujemy tylko do cen aktualnych.</p>{% else %}<p class="note">Koszyk automatycznie wybiera najlepszy zapisany kod dla sklepu, kategorii i wykrytej promocji. Progi zamówienia oraz pozostałe warunki kuponu sprawdź przed zakupem.</p>{% endif %}
{% if selected_site %}<div class="card"><b>{{ selected_site }}:</b> {% if plan.selected_total and not plan.selected_total.missing %}{{ plan.selected_total.total|pln }} · pełny koszyk{% elif plan.selected_total %}brak ofert dla {{ plan.selected_total.missing }} pozycji{% else %}brak danych{% endif %}</div>{% endif %}
{% for group in plan.category_groups %}<h2>{{ group.category }} <span class="note">{{ group.lines|length }}</span></h2>{% for line in group.lines %}<div class="card"><div class="top"><strong>{{ line.name }}</strong>{% if line.code %}<span class="code">{{ line.code }}</span>{% endif %}<button type="button" class="sec sm" data-cart-remove data-url="{{ line.url }}">Usuń</button></div>
{% if line.error %}<p class="note">{{ line.error }}</p>{% endif %}
{% for offer in line.offers %}<div class="row"><span>{{ offer.site }} · {{ 'dostępny' if offer.avail=='in_stock' else 'niedostępny' }}{% if offer.promo %} · <span class="badge r">promocja</span>{% endif %}</span>{% if offer.coupon %}<span class="old">{{ offer.base_price|pln }}</span><span class="code">{{ offer.coupon.code }}</span>{% endif %}<span class="price">{{ offer.basket_price|pln }}</span>{% if offer.url==line.cheapest.url %}<span class="best">najkorzystniej</span>{% endif %}<a class="mini" href="{{ offer.url }}" target="_blank" rel="noopener noreferrer">Otwórz ofertę</a></div>{% else %}<p class="note">Brak pasujących ofert z ceną w wybranym trybie.</p>{% endfor %}</div>{% endfor %}{% endfor %}
<details><summary>Produkty i sumy według sklepu</summary>{% for total in plan.shop_totals %}<section><div class="row"><strong>{{ total.site }} · {{ total.count }}/{{ plan.lines|length }} produktów</strong><span>{% if total.missing %}brak {{ total.missing }} · suma częściowa {{ total.total|pln }}{% else %}pełny koszyk · {{ total.total|pln }}{% endif %}</span></div>{% for product in total.products %}<div class="row"><a class="mini" href="{{ product.url }}" target="_blank" rel="noopener noreferrer">{{ product.name }}</a>{% if product.promo %}<span class="badge r">promocja</span>{% endif %}{% if product.coupon %}<span class="code">{{ product.coupon.code }}</span><span class="old">{{ product.base_price|pln }}</span>{% endif %}<span>{{ product.price|pln }}</span></div>{% endfor %}</section>{% else %}<p class="note">Brak sklepów z ofertami.</p>{% endfor %}</details>{% else %}<div class="card">Koszyk jest pusty. Dodaj produkty z listy produktów.</div>{% endif %}</div>""",

    "deals.html": """{% extends 'base.html' %}
{% block body %}<h1>Okazje</h1><p class="note">Porównanie dostępnych ofert między sklepami. Procent pokazuje oszczędność względem najwyższej ceny.</p>
<form method="get" class="f"><label style="grid-column:1/3">Szukaj nazwy lub kodu<input type="search" name="q" value="{{ query }}" placeholder="np. PXO310 albo wyrzutnia"></label>
<label>Min. różnica ceny (%)<input name="ms" type="number" min="0" max="95" step="0.5" value="{{ ms }}"></label><label>Min. oszczędność (zł)<input name="saving" type="number" min="0" step="1" value="{{ min_saving }}"></label>
<label>Min. sklepów z ofertą<select name="shops">{% for n in (2,3,4,5) %}<option value="{{ n }}" {{ 'selected' if min_shops==n }}>{{ n }}+</option>{% endfor %}</select></label>
<label>Sortuj<select name="sort"><option value="percent" {{ 'selected' if sort=='percent' }}>Największy procent</option><option value="amount" {{ 'selected' if sort=='amount' }}>Największa oszczędność zł</option><option value="shops" {{ 'selected' if sort=='shops' }}>Najwięcej sklepów</option><option value="name" {{ 'selected' if sort=='name' }}>Nazwa A-Z</option></select></label><button style="grid-column:1/3">Szukaj okazji</button></form>
<div class="meta">{{ total }} okazji · strona {{ page }} / {{ pages }} ({{ rows|length }} na stronie)</div>
{% for r in rows %}<div class="card"><div class="top"><span class="code">{{ r.code }}</span><span class="best">{{ r.saving_pct|round(1) }}% taniej</span><span class="note">{{ r.n_avail }} z {{ r.shops }} sklepów</span></div><a class="name" href="{{ url_for('compare', k=r.code_key) }}">{{ r.name }}</a>
<div class="row"><span class="price">{{ r.pmin|pln }}</span><span class="old">{{ r.pmax|pln }}</span><span class="down">oszczędzasz {{ r.saving|pln }}</span></div></div>{% else %}<div class="card">Brak okazji dla tych filtrów.</div>{% endfor %}
<div class="pager"><a class="{{ '' if page>1 else 'off' }}" href="{{ url_with(page=page-1) if page>1 else '#' }}">← wstecz</a><span class="note">{{ page }} / {{ pages }}</span><a class="{{ '' if page<pages else 'off' }}" href="{{ url_with(page=page+1) if page<pages else '#' }}">dalej →</a></div>{% endblock %}""",

    "changes.html": """{% extends 'base.html' %}{% from 'card.html' import card with context %}
{% block head %}<nav class="tabs">{% for k,l in [('new','Nowości'),('drops','Obniżki'),('rises','Podwyżki'),('back','Wróciły'),('gone','Zniknęły')] %}<a class="{{ 'on' if t==k }}" href="{{ url_with(t=k, scan=None, page=None) }}">{{ l }} {{ counts[k] }}</a>{% endfor %}</nav>
<form class="f" method="get"><input type="hidden" name="t" value="{{ t }}">
<label>Zakres skanów<select name="scan_mode" id="scan-mode"><option value="last" {{ 'selected' if scan_mode=='last' }}>Ostatni skan</option><option value="range" {{ 'selected' if scan_mode=='range' }}>Od–do</option></select></label>
<label>Sklep<select name="site"><option value="">Wszystkie sklepy</option>{% for sh in shops %}<option value="{{ sh.site }}" {{ 'selected' if sh.site==site }}>{{ sh.site }}</option>{% endfor %}</select></label>
<label id="scan-from" style="{{ '' if scan_mode=='range' else 'display:none' }}">Od<input type="date" name="date_from" value="{{ date_from }}"></label><label id="scan-to" style="{{ '' if scan_mode=='range' else 'display:none' }}">Do<input type="date" name="date_to" value="{{ date_to }}"></label>
<button>Filtruj zmiany</button></form><p class="note">{% if scan_mode=='last' %}Wyświetlane są zmiany z ostatniego skanu.{% else %}Wyświetlane są zmiany z wybranego zakresu dat.{% endif %}</p>
<script>document.getElementById('scan-mode').addEventListener('change', event => { const range=event.target.value==='range'; document.getElementById('scan-from').style.display=range?'flex':'none'; document.getElementById('scan-to').style.display=range?'flex':'none'; });</script>{% endblock %}
{% block body %}<div class="meta">{{ total }} zmian · strona {{ page }} / {{ pages }} ({{ rows|length }} na stronie)</div>
{% for r in rows %}{{ card(r) }}{% else %}<div class="card">Brak zmian dla wybranych skanów.</div>{% endfor %}
<div class="pager"><a class="{{ '' if page>1 else 'off' }}" href="{{ url_with(page=page-1, scan=None) if page>1 else '#' }}">← wstecz</a><span class="note">{{ page }} / {{ pages }}</span><a class="{{ '' if page<pages else 'off' }}" href="{{ url_with(page=page+1, scan=None) if page<pages else '#' }}">dalej →</a></div>{% endblock %}""",

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

    "admin_base.html": """{% extends 'base.html' %}{% block head %}<nav class="tabs sub">{% for k,l,u in [('home','Przegląd','admin_home'),('users','Użytkownicy','admin_users'),('invites','Zaproszenia','admin_invites'),('coupons','Kody rabatowe','admin_coupons'),('settings','Ustawienia','admin_settings'),('audit','Dziennik','admin_audit')] %}<a class="{{ 'on' if sub==k }}" href="{{ url_for(u) }}">{{ l }}</a>{% endfor %}</nav>{% endblock %}""",

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

    "admin_coupons.html": """{% extends 'admin_base.html' %}{% block body %}<h1>Kody rabatowe</h1><p class="note">Dodaj kod ze zdjęcia lub linku. OCR tylko podpowiada tekst — sprawdź kod i warunki przed publikacją. Kategoria produktu jest rozpoznawana na podstawie nazwy.</p>
<form method="post" enctype="multipart/form-data" class="f"><input type="hidden" name="csrf" value="{{ csrf }}">
<label>Sklep<input name="shop" maxlength="80" required></label><label>Kod rabatowy<input name="code" maxlength="40" pattern="[A-Za-z0-9][A-Za-z0-9._-]{1,39}" required></label>
<label style="grid-column:1/3">Rabat / promocja<input name="discount" maxlength="120" placeholder="np. 10% na całe zamówienie" required></label>
<label style="grid-column:1/3">Obowiązuje na<select name="category"><option value="">Wszystkie produkty</option>{% for category in categories %}<option value="{{ category }}">{{ category }}</option>{% endfor %}</select></label>
<label style="grid-column:1/3">Warunki<input name="terms" maxlength="500" placeholder="np. od 200 zł, tylko produkty nieprzecenione"></label>
<label class="chk" style="grid-column:1/3"><input type="checkbox" name="excludes_promos" value="1"> nie łączy się z innymi promocjami</label>
<label>Ważny do<input type="date" name="valid_until"></label><label>Link do źródła<input type="url" name="source" maxlength="500" placeholder="https://..."></label>
<label style="grid-column:1/3">Zdjęcie kodu (JPG, PNG, WebP; maks. 5 MB)<input type="file" name="image" accept="image/jpeg,image/png,image/webp"></label>
<div style="grid-column:1/3"><button class="sec" type="button" data-coupon-ocr>Odczytaj tekst ze zdjęcia</button><span class="note" data-coupon-ocr-status aria-live="polite"></span><div data-coupon-code-suggestions class="qa"></div>
<label style="display:block;margin-top:8px">Tekst odczytany ze zdjęcia<textarea rows="4" readonly data-coupon-ocr-text></textarea></label></div>
<button style="grid-column:1/3">Dodaj kod</button></form>
{% for c in rows %}<div class="card{{ ' dim' if not c.active or c.expired }}"><div class="top"><span class="shop">{{ c.shop }}</span><span class="code">{{ c.code }}</span><span class="best">{{ c.discount }}</span><span class="badge {{ 'a' if c.active and not c.expired else 'r' }}">{{ 'aktywny' if c.active and not c.expired else 'wycofany' if not c.active else 'wygasł' }}</span></div>
<div class="note">{{ c.category or 'Wszystkie produkty' }}</div>
{% if c.image %}<img src="{{ url_for('coupon_image', coupon_id=c.id) }}" alt="Zdjęcie kodu {{ c.code }}" loading="lazy" style="display:block;max-width:100%;max-height:240px;object-fit:contain;margin:10px 0">{% endif %}
{% if c.terms %}<p>{{ c.terms }}</p>{% endif %}{% if c.excludes_promos %}<p class="note">Nie łączy się z innymi promocjami.</p>{% endif %}<div class="note">{% if c.valid_until %}ważny do {{ c.valid_until|dt('%d.%m.%Y') }}{% else %}bez daty końca{% endif %}{% if c.source %} · <a href="{{ c.source }}" target="_blank" rel="noopener noreferrer">źródło</a>{% endif %}</div>
{% if c.active %}<form method="post" action="{{ url_for('admin_coupon_deactivate', coupon_id=c.id) }}" class="qa"><input type="hidden" name="csrf" value="{{ csrf }}"><button class="sec sm">Wycofaj kupon</button></form>{% endif %}</div>
{% else %}<div class="card">Brak dodanych kuponów.</div>{% endfor %}
<script>
(() => {
  const button = document.querySelector('[data-coupon-ocr]');
  const form = button.closest('form');
  const status = document.querySelector('[data-coupon-ocr-status]');
  const text = document.querySelector('[data-coupon-ocr-text]');
  const suggestions = document.querySelector('[data-coupon-code-suggestions]');
  button.addEventListener('click', async () => {
    const image = form.elements.image.files[0];
    if (!image) { status.textContent = ' Wybierz zdjęcie.'; return; }
    button.disabled = true;
    status.textContent = ' Odczytuję…';
    suggestions.replaceChildren();
    try {
      const body = new FormData();
      body.append('csrf', form.elements.csrf.value);
      body.append('image', image);
      const response = await fetch('{{ url_for("admin_coupon_ocr") }}', { method: 'POST', body });
      const result = await response.json();
      if (!response.ok) throw new Error(result.error || `HTTP ${response.status}`);
      text.value = result.text;
      for (const code of result.codes) {
        const choice = document.createElement('button');
        choice.type = 'button';
        choice.className = 'sec sm';
        choice.textContent = code;
        choice.addEventListener('click', () => { form.elements.code.value = code; });
        suggestions.append(choice);
      }
      status.textContent = result.codes.length ? ' Wybierz podpowiedź lub sprawdź kod ręcznie:' : ' Sprawdź odczyt i wpisz kod ręcznie.';
    } catch (error) {
      status.textContent = ` ${error.message}`;
    } finally {
      button.disabled = false;
    }
  });
})();
</script>{% endblock %}""",

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
<label style="grid-column:1/3">Kategoria<select name="category"><option value="">Automatycznie: {{ it.category }}</option>{% for category in categories %}<option value="{{ category }}" {{ 'selected' if ov.category==category }}>{{ category }}</option>{% endfor %}</select></label>
<label>Kod produktu<input name="code" value="{{ ov.code or '' }}" placeholder="{{ it.o_code or 'brak' }}" maxlength="40"></label>
<label>Pozycja (mniejsza = wyżej)<input name="rank" value="{{ ov.rank if ov.rank is not none else '' }}" inputmode="numeric" placeholder="brak"></label>
<label style="grid-column:1/3">Etykieta (np. polecamy, promocja)<input name="note" value="{{ ov.note or '' }}" maxlength="80"></label>
<label class="chk" style="grid-column:1/3"><input type="checkbox" name="hidden" value="1" {{ 'checked' if ov.hidden }}> ukryj produkt (widzą go tylko administratorzy)</label>
<button style="grid-column:1/3" name="act" value="save">Zapisz</button><button class="sec" style="grid-column:1/3" name="act" value="clear">Przywróć dane ze scrapera</button></form>
<p><a href="{{ url_for('product', u=it.url) }}" style="text-decoration:underline">← wróć do produktu</a></p>{% endblock %}""",
}

app.jinja_env.loader = DictLoader(TEMPLATES)
app.jinja_env.globals["css"] = CSS
app.jinja_env.globals["product_categories"] = _product_categories


if __name__ == "__main__":
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", "8000")))
