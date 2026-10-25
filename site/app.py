"""
Strona z cenami fajerwerków (Flask) - do hostowania na Render (onrender.com).

Skąd bierze dane: pobiera plik bazy fajerwerki.db z PRYWATNEGO repo z danymi (GitHub API + token tylko do odczytu),
sprawdza zmiany co REFRESH_MINUTES (zapytanie warunkowe ETag - zwykle 304, bez pobierania) i buduje z niego
szybką tabelę pomocniczą. Cała strona jest za logowaniem (HTTP Basic), bo dane mają być prywatne.

Zmienne środowiskowe (Render > Environment):
  DATA_REPO       wymagane  np. twojlogin/fajerwerki-dane
  DATA_TOKEN      wymagane  token GitHub (fine-grained) z uprawnieniem Contents: Read-only do tego repo
  SITE_PASSWORD   wymagane  hasło do strony (min. 8 znaków); bez niego strona się nie uruchomi
  SITE_USER       opcjonalne, domyślnie admin
  DATA_PATH       opcjonalne, domyślnie fajerwerki.db     DATA_REF  opcjonalne (gałąź)
  REFRESH_MINUTES opcjonalne, domyślnie 30
  DATA_FILE       tylko do testów lokalnych: ścieżka do pliku .db zamiast GitHuba
"""
import csv
import hmac
import io
import os
import shutil
import sqlite3
import threading
import time
import unicodedata
from datetime import datetime, timedelta, timezone
from urllib.parse import quote, urlencode

import requests
from flask import Flask, Response, abort, render_template, request, url_for
from jinja2 import DictLoader

try:
    from zoneinfo import ZoneInfo
    TZ = ZoneInfo("Europe/Warsaw")
except Exception:  # brak bazy stref czasowych
    TZ = timezone.utc

REPO = os.environ.get("DATA_REPO", "").strip()
TOKEN = os.environ.get("DATA_TOKEN", "").strip()
DATA_PATH = os.environ.get("DATA_PATH", "fajerwerki.db").strip()
DATA_REF = os.environ.get("DATA_REF", "").strip()
GITHUB_API = os.environ.get("GITHUB_API", "https://api.github.com").rstrip("/")
DATA_FILE = os.environ.get("DATA_FILE", "").strip()
REFRESH_MIN = int(os.environ.get("REFRESH_MINUTES", "30") or 30)
SITE_USER = os.environ.get("SITE_USER", "admin") or "admin"
SITE_PASSWORD = os.environ.get("SITE_PASSWORD", "")
WORK = os.environ.get("WORK_DIR", "/tmp/fajerwerki-site")
PER_PAGE = 40

app = Flask(__name__)

# ----------------------------------------------------------------------------- dane
_lock = threading.Lock()
_state = {"checked": 0.0, "etag": None, "mtime": None, "derived": None, "loaded_at": None, "error": None}


def fold(text):
    """Małe litery bez polskich znaków - do wyszukiwania."""
    text = (text or "").lower().replace("ł", "l")
    text = unicodedata.normalize("NFKD", text)
    return "".join(c for c in text if not unicodedata.combining(c))


def _clean_err(e):
    msg = f"{e.__class__.__name__}: {str(e)[:200]}"
    return msg.replace(TOKEN, "***") if TOKEN else msg


def _fetch_github(src):
    """Pobiera bazę z GitHuba. True = nowa wersja, False = bez zmian (304)."""
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


def _build_derived(src, dst):
    """Z bazy scrapera robi płaską tabelę 'items' (ostatnia cena, poprzednia cena, min/max, liczba zmian...)."""
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
            drop_pct REAL, key_shops INTEGER, key_min REAL);
        CREATE INDEX ix_site ON items(site); CREATE INDEX ix_key ON items(code_key);
        CREATE INDEX ix_changed ON items(changed_at);
        CREATE TABLE meta(k TEXT PRIMARY KEY, v TEXT);
    """)
    batch = []
    for (url, site, name, code, key, first, last, price, av, ts, cur, prev, prev_av, mn, mx, n) in rows:
        pct = (prev - price) * 100.0 / prev if (prev and price is not None and prev > 0) else None
        batch.append((url, site, name, fold(name), code, key, first, last, price, av, ts, cur or "PLN",
                      prev, prev_av, mn, mx, n, pct, None, None))
    out.executemany("INSERT INTO items VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)", batch)
    out.execute("""UPDATE items SET key_shops = (SELECT COUNT(DISTINCT i2.site) FROM items i2 WHERE i2.code_key = items.code_key),
                   key_min = (SELECT MIN(i2.price) FROM items i2 WHERE i2.code_key = items.code_key
                              AND i2.avail = 'in_stock' AND i2.price IS NOT NULL)
                   WHERE code_key IS NOT NULL""")
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
            if changed or not have:
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


def history(url):
    """Pełna historia zmian z oryginalnej bazy."""
    src = os.path.join(WORK, "src.db")
    c = sqlite3.connect(f"file:{src}?mode=ro", uri=True)
    try:
        return c.execute("SELECT ts, price, availability FROM prices WHERE url = ? ORDER BY id", (url,)).fetchall()
    finally:
        c.close()


# ----------------------------------------------------------------------------- dostęp
@app.before_request
def guard():
    if request.path in ("/health", "/robots.txt"):
        return None
    if len(SITE_PASSWORD) < 8:
        return Response("Ustaw zmienną SITE_PASSWORD (min. 8 znaków) w Render > Environment.", 503)
    a = request.authorization
    ok = bool(a) and hmac.compare_digest((a.username or "").encode(), SITE_USER.encode()) \
        and hmac.compare_digest((a.password or "").encode(), SITE_PASSWORD.encode())
    if not ok:
        time.sleep(0.5)  # spowalnia zgadywanie hasła
        return Response("Wymagane logowanie", 401, {"WWW-Authenticate": 'Basic realm="Fajerwerki"'})
    return None


@app.after_request
def headers(resp):
    resp.headers["Cache-Control"] = "no-store"
    resp.headers["X-Robots-Tag"] = "noindex, nofollow"
    resp.headers["X-Content-Type-Options"] = "nosniff"
    resp.headers["Referrer-Policy"] = "no-referrer"
    return resp


@app.route("/health")
def health():
    return "ok"


@app.route("/robots.txt")
def robots():
    return Response("User-agent: *\nDisallow: /\n", mimetype="text/plain")


# ----------------------------------------------------------------------------- formatowanie
def parse_ts(ts):
    try:
        d = datetime.fromisoformat(ts)
    except (TypeError, ValueError):
        return None
    return d if d.tzinfo else d.replace(tzinfo=timezone.utc)


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
    return {"url_with": url_with, "export_url": export_url}


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


# ----------------------------------------------------------------------------- zapytania
SORTS = {
    "new": ("najnowsze zmiany", "changed_at DESC"),
    "price_asc": ("cena rosnąco", "price IS NULL, price ASC"),
    "price_desc": ("cena malejąco", "price DESC"),
    "drop": ("największa obniżka", "drop_pct IS NULL, drop_pct DESC"),
    "name": ("nazwa A-Z", "name_norm ASC"),
    "site": ("sklep", "site, name_norm"),
}


def build_filters():
    q = request.args.get("q", "").strip()
    where, args = [], []
    for w in fold(q).split():
        key = "".join(c for c in w.upper() if c.isalnum())
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
    return q, (" WHERE " + " AND ".join(where)) if where else "", args


def common_ctx(c):
    shops = c.execute("SELECT site, COUNT(*) n FROM items GROUP BY site ORDER BY site").fetchall()
    meta = dict(c.execute("SELECT k, v FROM meta").fetchall())
    return {"shops": shops, "last_seen": meta.get("last_seen"), "has_codes": meta.get("has_codes") == "1",
            "refresh_error": _state["error"]}


@app.route("/")
def index():
    c = conn()
    q, where, args = build_filters()
    s = request.args.get("s") or ("price_asc" if q else "new")
    order = SORTS.get(s, SORTS["new"])[1]
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
    it = c.execute("SELECT * FROM items WHERE url = ?", (url,)).fetchone()
    if not it:
        abort(404)
    hist = history(url)
    others = []
    if it["code_key"]:
        others = c.execute("SELECT * FROM items WHERE code_key = ? AND url != ? "
                           "ORDER BY (avail = 'in_stock') DESC, price ASC", (it["code_key"], url)).fetchall()
    return render_template("product.html", it=it, hist=list(reversed(hist))[:40], chart=chart_svg(hist, it["last_seen"]),
                           others=others, tab="list", **common_ctx(c))


@app.route("/compare")
def compare():
    c = conn()
    key = request.args.get("k", "")
    rows = c.execute("SELECT * FROM items WHERE code_key = ? ORDER BY (avail = 'in_stock') DESC, price ASC", (key,)).fetchall()
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
    rows = c.execute("""
        SELECT code_key, MIN(code) AS code, MIN(name) AS name, COUNT(DISTINCT site) AS shops,
               COUNT(DISTINCT CASE WHEN avail = 'in_stock' AND price IS NOT NULL THEN site END) AS n_avail,
               MIN(CASE WHEN avail = 'in_stock' THEN price END) AS pmin,
               MAX(CASE WHEN avail = 'in_stock' THEN price END) AS pmax
        FROM items WHERE code_key IS NOT NULL
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
    counts = {k: c.execute(f"SELECT COUNT(*) FROM items WHERE changed_at >= ? AND {cond}", (cutoff,)).fetchone()[0]
              for k, (cond, _) in conds.items()}
    rows = c.execute(f"SELECT * FROM items WHERE changed_at >= ? AND {conds[t][0]} ORDER BY {conds[t][1]} LIMIT 200",
                     (cutoff,)).fetchall()
    return render_template("changes.html", rows=rows, t=t, days=days, counts=counts, tab="changes", **common_ctx(c))


# ----------------------------------------------------------------------------- szablony
CSS = """
:root{--bg:#f6f7f9;--card:#fff;--fg:#14171c;--mut:#667085;--line:#e4e7ec;--accent:#d92d20;--ok:#12b76a;--no:#98a2b3;--chip:#eef1f5}
@media(prefers-color-scheme:dark){:root{--bg:#0e1116;--card:#171b22;--fg:#eceff4;--mut:#98a2b3;--line:#2a303a;--accent:#ff6b5e;--chip:#222833}}
*{box-sizing:border-box}body{margin:0;background:var(--bg);color:var(--fg);font:16px/1.4 system-ui,-apple-system,Segoe UI,Roboto,sans-serif}
a{color:inherit;text-decoration:none}.wrap{max-width:760px;margin:0 auto;padding:0 12px 40px}
header{position:sticky;top:0;background:var(--bg);padding:10px 0 8px;z-index:5;border-bottom:1px solid var(--line)}
.tabs{display:flex;gap:6px;margin-bottom:8px}.tabs a{flex:1;text-align:center;padding:7px 4px;border-radius:10px;background:var(--chip);font-weight:600;font-size:14px}
.tabs a.on{background:var(--accent);color:#fff}
form.s{display:flex;gap:6px}input,select{font:inherit;color:inherit;background:var(--card);border:1px solid var(--line);border-radius:10px;padding:9px 10px;min-width:0}
input[type=search]{flex:1}button,.btn{font:inherit;background:var(--accent);color:#fff;border:0;border-radius:10px;padding:9px 14px;font-weight:600;cursor:pointer;display:inline-block}
details{margin-top:8px}summary{color:var(--mut);cursor:pointer;font-size:14px}.f{display:grid;grid-template-columns:1fr 1fr;gap:8px;margin-top:8px}
.f label{font-size:13px;color:var(--mut);display:flex;flex-direction:column;gap:3px}.f .chk{flex-direction:row;align-items:center;gap:8px;font-size:15px;color:var(--fg)}
.meta{color:var(--mut);font-size:13px;margin:10px 2px}.card{background:var(--card);border:1px solid var(--line);border-radius:14px;padding:11px 12px;margin:8px 0}
.top{display:flex;gap:6px;align-items:center;flex-wrap:wrap;font-size:12px;margin-bottom:4px}.shop{background:var(--chip);border-radius:6px;padding:1px 7px;font-weight:600}
.code{border:1px solid var(--line);border-radius:6px;padding:0 6px;color:var(--mut)}.dot{width:9px;height:9px;border-radius:50%;background:var(--no);margin-left:auto}.dot.ok{background:var(--ok)}
.name{font-weight:600;display:block;margin-bottom:6px}.row{display:flex;align-items:baseline;gap:8px;flex-wrap:wrap}.price{font-size:20px;font-weight:700}
.old{color:var(--mut);text-decoration:line-through;font-size:14px}.up,.down{font-size:13px;font-weight:700;border-radius:6px;padding:0 6px}.down{background:#d1fadf;color:#05603a}.up{background:#fee4e2;color:#b42318}
@media(prefers-color-scheme:dark){.down{background:#0b3d2a;color:#75e0a7}.up{background:#4a1a15;color:#fda29b}}
.best{background:#fef0c7;color:#93370d;font-size:12px;font-weight:700;border-radius:6px;padding:1px 7px}.mini{font-size:13px;color:var(--mut);margin-left:auto;text-decoration:underline}
.pager{display:flex;justify-content:space-between;align-items:center;margin:14px 0}.pager a{background:var(--chip);padding:9px 14px;border-radius:10px;font-weight:600}.pager .off{opacity:.35}
.chart{width:100%;height:auto;margin:6px 0}.chart .line{fill:none;stroke:var(--accent);stroke-width:2}.chart .dot{fill:var(--accent)}.chart .ax{font-size:10px;fill:var(--mut)}.chart .oos{fill:var(--no);opacity:.18}
table{width:100%;border-collapse:collapse;font-size:14px}td,th{padding:6px 4px;border-bottom:1px solid var(--line);text-align:left}h1{font-size:19px;margin:14px 0 4px}h2{font-size:16px;margin:18px 0 6px}
.err{background:#fee4e2;color:#7a271a;border-radius:10px;padding:8px 10px;margin:8px 0;font-size:14px}.note{color:var(--mut);font-size:13px}
.stats{display:flex;gap:8px;flex-wrap:wrap;margin:8px 0}.stat{background:var(--card);border:1px solid var(--line);border-radius:12px;padding:8px 12px}.stat b{display:block;font-size:18px}
"""

BASE = """<!doctype html><html lang="pl"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover">
<meta name="robots" content="noindex,nofollow"><title>{% block title %}Ceny fajerwerków{% endblock %}</title><style>{{ css|safe }}</style></head><body><div class="wrap">
<header><nav class="tabs"><a href="{{ url_for('index') }}" class="{{ 'on' if tab=='list' }}">Produkty</a><a href="{{ url_for('deals') }}" class="{{ 'on' if tab=='deals' }}">Porównanie</a><a href="{{ url_for('changes') }}" class="{{ 'on' if tab=='changes' }}">Zmiany</a></nav>{% block head %}{% endblock %}</header>
{% if refresh_error %}<div class="err">Nie udało się odświeżyć danych ({{ refresh_error }}). Pokazuję poprzednią wersję.</div>{% endif %}
{% block body %}{% endblock %}
<p class="note">Dane z: {{ last_seen|dt('%d.%m.%Y %H:%M') }}. Kody produktów są wyciągane z nazw i mogą się mylić - przed zakupem sprawdź, czy to ten sam model.</p>
</div></body></html>"""

CARD = """{% macro card(it, show_shop=true) %}<div class="card"><div class="top"><span class="shop">{{ it.site }}</span>{% if it.code %}<span class="code">{{ it.code }}</span>{% endif %}<span class="dot {{ 'ok' if it.avail=='in_stock' }}" title="{{ 'dostępny' if it.avail=='in_stock' else 'niedostępny' }}"></span></div>
<a class="name" href="{{ url_for('product', u=it.url) }}">{{ it.name }}</a><div class="row"><span class="price">{{ it.price|pln }}</span>
{% if it.prev_price and it.price is not none and it.price != it.prev_price %}<span class="old">{{ it.prev_price|pln }}</span><span class="{{ 'down' if it.price < it.prev_price else 'up' }}">{{ '−' if it.price < it.prev_price else '+' }}{{ it.drop_pct|pct }}</span>{% endif %}
{% if it.key_shops and it.key_shops > 1 %}{% if it.avail=='in_stock' and it.price is not none and it.price == it.key_min %}<span class="best">najtaniej</span>{% endif %}<a class="mini" href="{{ url_for('compare', k=it.code_key) }}">{{ it.key_shops|shops }}</a>{% endif %}
</div><div class="note">zmiana: {{ it.changed_at|dt }}</div></div>{% endmacro %}"""

TEMPLATES = {
    "base.html": BASE,
    "card.html": CARD,
    "error.html": """<!doctype html><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<body style="font:16px system-ui;padding:20px"><h2>Dane niedostępne</h2><p>{{ msg }}</p><p>Sprawdź zmienne DATA_REPO, DATA_TOKEN i czy plik fajerwerki.db jest w prywatnym repo.</p></body>""",
    "index.html": """{% extends 'base.html' %}{% from 'card.html' import card %}
{% block head %}<form class="s" method="get" action="{{ url_for('index') }}"><input type="search" name="q" value="{{ q }}" placeholder="nazwa lub kod, np. PXO310" autocomplete="off"><button>Szukaj</button></form>
<details {{ 'open' if request.args.get('site') or request.args.get('a') or request.args.get('d') or request.args.get('min') or request.args.get('max') }}><summary>Filtry i sortowanie</summary>
<form method="get" class="f"><input type="hidden" name="q" value="{{ q }}">
<label>Sortuj<select name="s">{% for k,(label,_) in sorts.items() %}<option value="{{ k }}" {{ 'selected' if k==s }}>{{ label }}</option>{% endfor %}</select></label>
<label>Sklep<select name="site" multiple size="3">{% for sh in shops %}<option value="{{ sh.site }}" {{ 'selected' if sh.site in sel_sites }}>{{ sh.site }} ({{ sh.n }})</option>{% endfor %}</select></label>
<label>Cena od<input name="min" inputmode="decimal" value="{{ request.args.get('min','') }}"></label><label>Cena do<input name="max" inputmode="decimal" value="{{ request.args.get('max','') }}"></label>
<label class="chk"><input type="checkbox" name="a" value="1" {{ 'checked' if request.args.get('a')=='1' }}> tylko dostępne</label><label class="chk"><input type="checkbox" name="d" value="1" {{ 'checked' if request.args.get('d')=='1' }}> tylko obniżki (14 dni)</label>
<button style="grid-column:1/3">Zastosuj</button></form></details>{% endblock %}
{% block body %}<div class="meta">{{ total }} produktów · <a href="{{ export_url() }}" style="text-decoration:underline">pobierz CSV</a></div>
{% for it in items %}{{ card(it) }}{% else %}<div class="card">Brak wyników.</div>{% endfor %}
<div class="pager"><a class="{{ '' if page>1 else 'off' }}" href="{{ url_with(page=page-1) if page>1 else '#' }}">← wstecz</a><span class="note">{{ page }} / {{ pages }}</span><a class="{{ '' if page<pages else 'off' }}" href="{{ url_with(page=page+1) if page<pages else '#' }}">dalej →</a></div>{% endblock %}""",
    "product.html": """{% extends 'base.html' %}{% from 'card.html' import card %}
{% block body %}<h1>{{ it.name }}</h1><div class="top"><span class="shop">{{ it.site }}</span>{% if it.code %}<span class="code">{{ it.code }}</span>{% endif %}<span class="note">{{ 'dostępny' if it.avail=='in_stock' else 'niedostępny' }}</span></div>
<div class="stats"><div class="stat"><span class="note">teraz</span><b>{{ it.price|pln }}</b></div><div class="stat"><span class="note">najniżej</span><b>{{ it.min_price|pln }}</b></div><div class="stat"><span class="note">najwyżej</span><b>{{ it.max_price|pln }}</b></div></div>
{{ chart|safe }}{% if not chart %}<p class="note">Brak historii cen.</p>{% endif %}<p><a class="btn" href="{{ it.url }}" target="_blank" rel="noopener noreferrer">Otwórz w sklepie</a></p>
{% if others %}<h2>Ten sam kod w innych sklepach</h2>{% for o in others %}{{ card(o) }}{% endfor %}{% endif %}
<h2>Historia zmian</h2><table><tr><th>kiedy</th><th>cena</th><th>stan</th></tr>{% for ts,p,av in hist %}<tr><td>{{ ts|dt('%d.%m.%Y %H:%M') }}</td><td>{{ p|pln }}</td><td>{{ 'dostępny' if av=='in_stock' else 'brak' }}</td></tr>{% endfor %}</table>{% endblock %}""",
    "compare.html": """{% extends 'base.html' %}{% from 'card.html' import card %}
{% block body %}<h1>Kod {{ rows[0].code or key }}</h1><p class="note">{{ rows|length }} ofert · najtańsza dostępna oznaczona jako „najtaniej". Sprawdź, czy nazwy to na pewno ten sam produkt.</p>
{% for r in rows %}{{ card(r) }}{% endfor %}{% endblock %}""",
    "deals.html": """{% extends 'base.html' %}
{% block head %}<form method="get" class="s"><input name="ms" inputmode="decimal" value="{{ ms|int if ms==ms|int else ms }}" style="width:90px"><span class="note" style="align-self:center">min. różnica % między sklepami</span><button>OK</button></form>{% endblock %}
{% block body %}{% if not has_codes %}<div class="err">Baza nie ma jeszcze kodów produktów - uruchom scraper, żeby je wyliczył.</div>{% endif %}
<div class="meta">Produkty z tym samym kodem dostępne w co najmniej 2 sklepach, od największej różnicy cen.</div>
{% for r in rows %}<div class="card"><div class="top"><span class="code">{{ r.code }}</span><span class="note">{{ r.n_avail|shops }} z towarem</span></div><a class="name" href="{{ url_for('compare', k=r.code_key) }}">{{ r.name }}</a>
<div class="row"><span class="price">{{ r.pmin|pln }}</span><span class="old">{{ r.pmax|pln }}</span><span class="down">−{{ ((r.pmax-r.pmin)*100/r.pmax)|round|int }}%</span></div></div>{% else %}<div class="card">Brak takich produktów.</div>{% endfor %}{% endblock %}""",
    "changes.html": """{% extends 'base.html' %}{% from 'card.html' import card %}
{% block head %}<nav class="tabs">{% for k,l in [('drops','Obniżki'),('rises','Podwyżki'),('back','Wróciły'),('gone','Zniknęły')] %}<a class="{{ 'on' if t==k }}" href="{{ url_for('changes', t=k, days=days) }}">{{ l }} {{ counts[k] }}</a>{% endfor %}</nav>
<form class="s" method="get"><input type="hidden" name="t" value="{{ t }}"><select name="days">{% for d in (1,3,7,14,30) %}<option value="{{ d }}" {{ 'selected' if d==days }}>ostatnie {{ d }} dni</option>{% endfor %}</select><button>OK</button></form>{% endblock %}
{% block body %}{% for r in rows %}{{ card(r) }}{% else %}<div class="card">Brak zmian w tym okresie.</div>{% endfor %}{% endblock %}""",
}
app.jinja_env.loader = DictLoader(TEMPLATES)
app.jinja_env.globals["css"] = CSS


if __name__ == "__main__":
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", "8000")))
