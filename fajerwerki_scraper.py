#!/usr/bin/env python3
"""
Scraper cen fajerwerków – produkty, linki, dostępność, historia cen (SQLite).

Instalacja:  pip install requests beautifulsoup4 lxml
Użycie:
  python fajerwerki_scraper.py scrape                 # wszystkie sklepy z SITES
  python fajerwerki_scraper.py -v scrape --site pirohit --max 20   # z logiem każdego adresu
  python fajerwerki_scraper.py scrape --site sklep1 --max 200
  python fajerwerki_scraper.py scrape --proxy http://user:haslo@host:8080   # opcjonalnie przez proxy
  python fajerwerki_scraper.py export out.csv         # aktualny stan
  python fajerwerki_scraper.py history "https://..."  # historia cen produktu

Zmienne środowiskowe (GitHub Actions: Settings > Secrets and variables > Actions):
  SEKRETY (nigdy w kodzie ani w repo):
    SCRAPER_PROXIES     proxy po przecinku: http://user:haslo@ip:port,http://user:haslo@ip2:port
    SCRAPER_CONTACT     Twój e-mail/URL, wysyłany sklepom w nagłówku User-Agent
    DATA_REPO, DATA_REPO_TOKEN   (tylko workflow) prywatne repo na bazę i CSV oraz token do niego
  USTAWIENIA (opcjonalne):
    SCRAPER_ONLY=pirohit,lider   SCRAPER_MAX=2   SCRAPER_WORKERS=12   SCRAPER_DELAY=0.5
    SCRAPER_VERBOSE=1   SCRAPER_RECHECK=1   SCRAPER_PROXY_ALL=1   SCRAPER_DB=sciezka/do/bazy.db

Jak to działa (tryb sitemap; tryb listing czyta strony kategorii - patrz SITES):
  1. Adresy produktów bierze z sitemap.xml sklepu (robots.txt -> Sitemap:).
  2. Dane czyta z JSON-LD (schema.org Product/Offer), potem z meta tagów,
     a na końcu z selektorów CSS podanych w konfiguracji sklepu.
  3. Zapisuje do SQLite; nowy wpis w historii powstaje tylko gdy zmieni się
     cena lub dostępność.
  4. Szanuje robots.txt i robi odstępy między zapytaniami.
"""
import argparse
import csv
import gzip
import itertools
import json
import logging
import os
import queue
import random
import re
import sqlite3
import sys
import threading
import time
import xml.etree.ElementTree as ET
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timedelta, timezone
from urllib.parse import urljoin, urlparse
from urllib.robotparser import RobotFileParser

import requests
import soupsieve as sv  # instalowany razem z beautifulsoup4
from bs4 import BeautifulSoup

log = logging.getLogger("scraper")


def env(name, default=None):
    """Zmienna środowiskowa; pusta wartość = brak (tak działają puste pola w GitHub Actions)."""
    v = os.environ.get(name, "").strip()
    return v if v else default

DB_PATH = env("SCRAPER_DB", "fajerwerki.db")  # w Actions: data/fajerwerki.db (prywatne repo z danymi)
USER_AGENT = "FajerwerkiPriceBot/1.0" + (f" (+kontakt: {env('SCRAPER_CONTACT')})" if env("SCRAPER_CONTACT") else "")
# Kontakt (e-mail) idzie z sekretu SCRAPER_CONTACT - nie wpisuj go w kod.
DELAY = float(env('SCRAPER_DELAY', 0.5))   # min. odstęp (s) między ZAPYTANIAMI do jednego hosta (wspólny dla wszystkich wątków)
WORKERS = int(env('SCRAPER_WORKERS', 12))   # równoległe wątki -> max ok. 1/DELAY zapytań na sekundę do sklepu
BROWSER_UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) "
              "Chrome/124.0.0.0 Safari/537.36")
BROWSER_UA_SPEC = (env("SCRAPER_BROWSER_UA", "") or "").lower()  # "" = nikt, "1" = wszystkie, albo lista sklepów
NONPRODUCT_TTL_DAYS = 14  # tyle dni pamiętamy, że dany adres NIE jest produktem

# ---------------------------------------------------------------------------
# KONFIGURACJA SKLEPÓW – dodawaj kolejne wpisy.
#   url_regex  : filtr adresów z sitemapy (tylko strony produktów) – mocno
#                przyspiesza, ale opcjonalny
#   selectors  : (opcjonalnie) nadpisanie, gdy sklep nie ma JSON-LD
#   sitemaps   : (opcjonalnie) ręczne adresy sitemap
# ---------------------------------------------------------------------------
# Wspólne wzorce szablonów sklepów (IdoSell, WooCommerce, PrestaShop).
_IDO = {"next": "{url}?counter={page}", "start": 0, "item": "div.product",
        "name": "a.product__name", "link": "a.product__name@href"}
_IDO_OUT = "span.--disable, [data-product_disable='true']"
_WOO = {"next": "{url}page/{page}/", "start": 1, "item": "li.product"}
_WOO_PRICE = ["ins .woocommerce-Price-amount", ".woocommerce-Price-amount"]
_PRESTA = {"next": "{url}?page={page}", "start": 1}

_LIDER = "https://fajerwerkilider.pl/pl/"
_HAS = "https://fajerwerkigorzow.pl/produkty/hurtownia/"
_PZ = "https://pirozone.pl/"

SITES = {
    # --- TRYB "listing": czyta strony kategorii (kilkadziesiąt produktów na 1 zapytanie).
    # To jest ~20-40x szybsze niż wejście na każdy produkt osobno.
    # Pola: categories = adresy kategorii; item = kafelek produktu (lub lista selektorów: pierwszy,
    # który coś znajdzie); name/link/price = selektor CSS wewnątrz kafelka ("sel@atrybut" czyta
    # atrybut, lista = próbuj po kolei); in_stock = selektor, którego BRAK oznacza brak towaru;
    # out_of_stock = selektor, którego obecność oznacza brak; out_text = teksty oznaczające brak;
    # price_strip = regexy wycinane z tekstu ceny; first/next = wzorce adresów stron ({url}, {page});
    # start = numer pierwszej strony.
    # Opcje sklepu: cookies, headers, delay (min. odstęp w s dla tego sklepu), use_proxy.
    "odpalaj": {
        "base": "https://odpalaj.pl",
        "listing": {**_PRESTA, "categories": ["https://odpalaj.pl/pl/2-wszystko"],
            "item": "article.product-miniature",
            "name": "h2.product-title a", "link": "h2.product-title a@href", "price": "span.price",
            "out_of_stock": "ul.product-flags li.out_of_stock", "out_text": ["brak na stanie"]},
    },
    "pirohit": {
        "base": "https://pirohit.pl", "use_proxy": True,
        "listing": {**_IDO, "price": "strong.price.--main", "in_stock": "button.add_to_basket__button",
            "categories": [
                "https://pirohit.pl/Petardy-i-emitery-dzwieku-c15", "https://pirohit.pl/Wyrzutnie-c20",
                "https://pirohit.pl/Wulkany-Fontanny-c18", "https://pirohit.pl/Rakiety-c19",
                "https://pirohit.pl/Compoud-Wyrzutnie-laczone-c50", "https://pirohit.pl/Dymy-c22",
                "https://pirohit.pl/Race-i-Flary-c28", "https://pirohit.pl/Stroboskopy-c21",
                "https://pirohit.pl/Piro-Bajery-c16", "https://pirohit.pl/Rzymskie-ognie-c30",
                "https://pirohit.pl/Single-Shoty-Mozdzierze-c23", "https://pirohit.pl/Zimne-ognie-c31",
                "https://pirohit.pl/Zestawy-Fajerwerkow-c32", "https://pirohit.pl/Artykuly-pirotechniczne-rozne-c24",
                "https://pirohit.pl/Akcesoria-c25", "https://pirohit.pl/Zapalarki-i-zapalniczki-c29",
                "https://pirohit.pl/Rakietnice-pistoletowe-c41", "https://pirohit.pl/Pistolety-i-rewolwery-hukowe-c43",
                "https://pirohit.pl/pl/menu/granaty-reczne-asg-201.html"]},
    },
    "pyroking": {
        "base": "https://www.pyroking.pl", "cookies": {"currency": "PLN"},
        "listing": {
            "categories": [
                "https://www.pyroking.pl/WYRZUTNIE-c101", "https://www.pyroking.pl/RAKIETY-c95",
                "https://www.pyroking.pl/PETARDY-c98", "https://www.pyroking.pl/RACE-I-FLARY-c23",
                "https://www.pyroking.pl/GRANATY-DYMNE-c21", "https://www.pyroking.pl/STROBOSKOPY-c103",
                "https://www.pyroking.pl/RZYMSKIE-OGNIE-c96", "https://www.pyroking.pl/SINGLE-SHOTY-c93",
                "https://www.pyroking.pl/PIROBAJERY-c104", "https://www.pyroking.pl/ZIMNE-OGNIE-c102",
                "https://www.pyroking.pl/WULKANY-I-FONTANNY-c50", "https://www.pyroking.pl/RACE-PISTOLETOWE-c99",
                "https://www.pyroking.pl/PISTOLETY-SYGNALOWE-c105", "https://www.pyroking.pl/PALNIKI-I-ZAPALNICZKI-c94",
                "https://www.pyroking.pl/LONT-I-AKCESORIA-c60", "https://www.pyroking.pl/strzelajace-diabelki",
                "https://www.pyroking.pl/fajerwerki-na-wesele", "https://www.pyroking.pl/Granaty-ASG-c134",
                "https://www.pyroking.pl/DROP-BOX-c137", "https://www.pyroking.pl/DANGER-HOBBY-made-by-PYRO-CARTEL-c143",
                "https://www.pyroking.pl/GATLING-c145"],
            "first": "{url}", "next": "{url}/pa/{page}", "start": 1,
            "item": "figure.product-tile",
            "name": "div.product-name a", "link": "div.product-name a@href",
            "price": "span.core_priceFormat@data-price", "out_text": ["produkt niedostępny"]},
    },
    "arka": {
        "base": "https://www.arkafajerwerki.pl",
        "listing": {**_IDO, "price": "strong.price", "out_of_stock": _IDO_OUT,
            "categories": [
                "https://www.arkafajerwerki.pl/pol_m_Fajerwerki-100.html",
                "https://www.arkafajerwerki.pl/Promocja-spromo-pol.html",
                "https://www.arkafajerwerki.pl/Nowosc-snewproducts-pol.html",
                "https://www.arkafajerwerki.pl/pol_m_Pirotechnika-profesjonalna-i-sceniczna-304.html"]},
    },
    "lider": {
        "base": "https://fajerwerkilider.pl",
        "headers": {"Referer": "https://fajerwerkilider.pl/", "Accept-Language": "pl-PL,pl;q=0.9,en-US;q=0.8,en;q=0.7"},
        "listing": {**_IDO, "price": "strong.price", "price_strip": [r"najniższa.*?dni[^\d]*\d[\d\s]*(?:[.,]\d{1,2})?\s*(?:zł)?"], "out_of_stock": _IDO_OUT,
            "categories": [_LIDER + x for x in (
                "5-art-rozne-pirobajery", "15-bron-hukowa-naboje-race-pistoletowe", "61-ciche-fajerwerki",
                "4-flary-i-race", "9-fontanny-fajerwerki-wulkany", "8-fontanny-tortowe-i-swieczki", "10-katiusze",
                "471-miny-dymne", "12-mozdzierze", "452-odstraszacze-zwierzyny", "16-petardy",
                "13-pirotechnika-profesjonalna", "14-pirotechnika-sceniczna", "17-pochodnie-parafinowe",
                "menu/race-pistoletowe-229.html", "18-rakiety", "19-rzymskie-ognie", "436-single-shot-jednostrzaly",
                "20-stroboskopy", "3-swiece-dymne", "11-tuby-strzelajace-konfetti", "menu/wyrzutnie-dzienne-230.html",
                "21-wyrzutnie-fajerwerkow-baterie", "22-zestawy-fajerwerkow-do-samodzielnego-odpalenia",
                "menu/wyrzutnie-hukowe-231.html", "23-zestawy-fajerwerkow", "24-zimne-ognie",
                "menu/gatlingi-254.html", "51-fajerwerki-na-wesele")]},
    },
    "pyrostar": {
        "base": "https://pyrostar.pl",
        "listing": {**_IDO, "price": "strong.price.--main", "in_stock": "button.add_to_basket__button-listing",
            "out_of_stock": "span.--disable", "categories": ["https://pyrostar.pl/pl/menu/oferta-232.html"]},
    },
    "pirozaur": {
        "base": "https://www.pirozaur.pl", "delay": 1.0,
        "listing": {**_PRESTA, "categories": ["https://www.pirozaur.pl/2-strona-glowna"],
            "item": ["div.js-product", "article.product-miniature"],
            "name": ["h3.product-title a", "a.product-thumbnail"],
            "link": ["h3.product-title a@href", "a.product-thumbnail@href"],
            "price": ["span.price", "meta[itemprop=price]@content"],
            "out_of_stock": "li.out_of_stock, button[data-button-action='add-to-cart'][disabled]"},
    },
    "sklepzpetardami": {
        "base": "https://sklepzpetardami.pl",
        "listing": {**_PRESTA, "categories": ["https://sklepzpetardami.pl/kategoria-produktu/oferta/"],
            "item": "article.product-miniature",
            "name": "div.tvproduct-name a", "link": "div.tvproduct-name a@href", "price": "span.price",
            "out_of_stock": "button.add-to-cart.tvproduct-out-of-stock, button.add-to-cart.disable, button.add-to-cart[disabled]"},
    },
    "piroman": {
        "base": "https://piroman.pl",
        "listing": {**_PRESTA, "item": "article.product-miniature",
            "name": "h3.product-title a", "link": "h3.product-title a@href", "price": "span[itemprop=price]@content",
            "out_of_stock": "button.add-to-cart.disabled, li.available_date",
            "categories": ["https://piroman.pl/23-fajerwerki", "https://piroman.pl/10-strefa-kibica",
                           "https://piroman.pl/24-odstraszanie-zwierzyny"]},
    },
    "hurtowniaas": {
        "base": "https://fajerwerkigorzow.pl",
        "listing": {"first": "{url}", "next": "{url}?product-page={page}", "start": 1, "item": "li.product",
            "name": "h2.woocommerce-loop-product__title", "link": "a.woocommerce-LoopProduct-link@href",
            "price": _WOO_PRICE, "in_stock": ".instock",
            "categories": ["https://fajerwerkigorzow.pl/produkty/nowe/"] + [_HAS + x + "/" for x in (
                "hurtownia-petardy", "hurtownia-emitery-dzwieku", "hurtownia-wyrzutnie",
                "hurtownia-race-pistoletowe-amunicja", "hurtownia-dymy-flary-stroboskopy", "hurtownia-fontanny",
                "hurtownia-rzymskie-ognie", "hurtownia-rakiety-i-zestawy", "hurtownia-art-rozne",
                "hurtownia-ciche-fajerwerki", "hurtownia-pirotechnika-na-wesela", "hurtownia-strefa-kibica",
                "hurtownia-wybuchowa-niespodzianka")]},
    },
    "szopik": {
        "base": "https://fajerwerki.shop.pl", "use_proxy": True,
        "listing": {"next": "{url}?counter={page}&p=5", "start": 0, "item": "div.product",
            "name": "a[class*='product__name']", "link": "a[class*='product__name']@href",
            "price": ["strong[class*='price']", "span[class*='price']"],
            "out_of_stock": "span[class*='--disable'], [data-product_disable='true']",
            "categories": ["https://fajerwerki.shop.pl/pl/menu/" + x + ".html" for x in (
                "emiter-dzwieku-154", "petardy-155", "single-shoty-mozdzierze-157", "strefa-kibica-153",
                "palniki-zarowe-158", "rzymskie-ognie-159", "wulkany-fontanny-160", "swiece-dymne-161",
                "pirobajery-baczki-cyrkoblitze-162", "zimne-ognie-163", "rakiety-164",
                "race-sygnalowe-startowce-165", "artykuly-weselne-party-gender-party-166",
                "pirotechnika-sceniczna-167", "lonty-i-zapalniki-splonka-168", "gadzety-fun-gadzet-169",
                "ciche-fajerwerki-170", "produkty-bez-rabatu-175", "singleline-183", "wyrzutnie-50mm-182",
                "zestawy-zlozone-dso-compound-181", "katowe-wyrzutnie-189", "wyrzutnie-25-99-strzalow-190",
                "wyrzutnie-100-500-strzalow-191", "wyrzutnie-1-25-strzalow-192", "tpro-show-193")]},
    },
    "pyrotech": {
        "base": "https://hurtownia-fajerwerki.pl",
        "listing": {**_IDO, "price": "strong.price.--main", "out_of_stock": "span.--disable",
            "categories": ["https://hurtownia-fajerwerki.pl/pol_m_Fajerwerki-157.html"]},
    },
    "pirozone": {
        "base": "https://pirozone.pl", "delay": 0.7,
        "listing": {"next": "{url}page/{page}/?currency=PLN", "start": 1, "item": "li.product",
            "name": ["h3.woocommerce-loop-product__title a", "h3.woocommerce-loop-product__title"],
            "link": ["h3.woocommerce-loop-product__title a@href", "a.woocommerce-LoopProduct-link@href"],
            "price": ["span.price ins bdi", "p.price ins bdi", "span.price bdi", "p.price bdi", "span.price", "p.price"],
            "in_stock": ".instock", "out_of_stock": ".outofstock",
            "categories": [_PZ + x + "/" for x in (
                "petardy-i-emitery-dzwieku", "wyprzedaz", "nowosci", "piro-bajery", "single-shoty", "batterien",
                "wyrzutnie-baterie-kostki", "rakiety-fajerwerki-i-zestawy-rakiet", "pirotechnika-meczowa",
                "race-i-flary", "swiece-dymne", "stroboskopy", "wulkany-i-fontanny", "rzymskie-ognie",
                "mystery-boxy", "rarytasy", "race-pistoletowe", "pistolety-na-race",
                "systemy-i-zapalniki-elektryczne-pirotechniczne-do-fajerwerkow", "zimne-ognie",
                "konfetti-i-serpentyny", "cale-kartony-pirotechniki", "akcesoria",
                "rury-do-bomb-kulistych-sferycznych")]},
    },
    "firefactory": {
        "base": "https://www.firefactory.pl",
        "listing": {**_WOO, "name": "h2.woocommerce-loop-product__title", "link": "a.woocommerce-LoopProduct-link@href",
            "price": ["ins", "span.woocommerce-Price-amount"], "out_text": ["dowiedz się więcej"],
            "categories": ["https://www.firefactory.pl/sklep/"]},
    },
    "obornicka": {
        "base": "https://www.fajerwerki-obornicka.pl",
        "listing": {**_WOO, "name": "h2.woocommerce-loop-product__title", "link": "a.woocommerce-LoopProduct-link@href",
            "price": ["span.price ins bdi", "span.price bdi"], "out_text": ["brak w magazynie"],
            "categories": ["https://www.fajerwerki-obornicka.pl/home/sklep/"]},
    },
    "andrzej": {
        "base": "https://piroandrzej.pl",
        "listing": {**_WOO, "name": "h2.woocommerce-loop-product__title a",
            "link": "h2.woocommerce-loop-product__title a@href", "price": ["ins", "span.woocommerce-Price-amount"],
            "categories": ["https://piroandrzej.pl/sklep/"]},
    },
    "pironet": {
        "base": "https://pironet.pl",
        "listing": {**_WOO, "name": "h3.woocommerce-loop-product__title a",
            "link": "h3.woocommerce-loop-product__title a@href",
            "price": ["span.price ins bdi", "span.price bdi", "span.price"],
            "out_of_stock": ".outofstock", "out_text": ["dowiedz się więcej"],
            "categories": ["https://pironet.pl/sklep-z-fajerwerkami/"]},
    },
    "piroart": {
        "base": "https://piroart.pl",
        "listing": {**_WOO, "name": "div.product__title h3", "link": "a.woocommerce-loop-product__link@href",
            "price": "span.current span.woocommerce-Price-amount",
            "categories": ["https://piroart.pl/hurtownia/"]},
    },
    # --- TRYB "sitemap" (wolniejszy, uniwersalny): sklepy bez konfiguracji "listing"
    "petardyshop": {"base": "https://petardyshop.pl"},
    # Wzór wpisu z selektorami dla trybu sitemap, gdy sklep nie ma JSON-LD:
    # "nazwa": {"base": "https://example.pl", "url_regex": r"\.html$",
    #           "selectors": {"name": "h1", "price": ".price", "availability": ".stock"}},
}

_tls = threading.local()
_lock = threading.RLock()
_stats_lock = threading.Lock()
_robots, _crawl_delay, _next_slot = {}, {}, {}
_robots_note = {}
_proxies, _proxy_i, _proxy_fail, _proxy_dead = [], 0, Counter(), set()
_min_delay, _proxy_hosts = {}, set()   # netloc -> min. odstęp (crawl-delay / 'delay' sklepu); hosty z use_proxy
PROXY_ALL = env('SCRAPER_PROXY_ALL') == '1'  # 1 = proxy dla wszystkich sklepów, nie tylko z use_proxy
PROXY_MAX_FAILS = 3  # tyle błędów z rzędu i proxy wypada z rotacji


def session():
    """Osobna sesja HTTP na wątek."""
    sess = getattr(_tls, "s", None)
    if sess is None:
        sess = requests.Session()
        sess.headers.update({"User-Agent": USER_AGENT, "Accept-Language": "pl-PL,pl;q=0.9"})
        _tls.s = sess
    return sess


# ----------------------------- sieć -----------------------------------------
def mask(px):
    """Etykieta proxy do logów: bez hosta, portu i hasła (logi w publicznym repo są widoczne dla wszystkich)."""
    if not px:
        return "bezpośrednio"
    try:
        return f"proxy#{_proxies.index(px) + 1}"
    except ValueError:
        return "proxy"


def setup_proxies(args):
    """Proxy z --proxy, --proxy-file i zmiennej SCRAPER_PROXIES (rozdzielone przecinkami)."""
    global _proxies
    items = list(args.proxy or [])
    if args.proxy_file:
        with open(args.proxy_file, encoding="utf-8") as f:
            items += [l.strip() for l in f if l.strip() and not l.lstrip().startswith("#")]
    items += [x.strip() for x in os.environ.get("SCRAPER_PROXIES", "").split(",") if x.strip()]
    _proxies = list(dict.fromkeys(items))
    if _proxies:
        log.info("proxy: %d szt., rotacja round-robin", len(_proxies))
    return _proxies


def pick_proxy():
    """Następne działające proxy (round-robin). Bez listy proxy -> None (połączenie bezpośrednie)."""
    global _proxy_i
    if not _proxies:
        return None
    with _lock:
        for _ in range(len(_proxies)):
            px = _proxies[_proxy_i % len(_proxies)]
            _proxy_i += 1
            if px not in _proxy_dead:
                return px
    # celowo NIE wracamy do połączenia bezpośredniego - ujawniłoby Twoje IP
    raise RuntimeError("wszystkie proxy przestały działać - przerywam")


def report_proxy(px, ok):
    if not px:
        return
    with _lock:
        if ok:
            _proxy_fail[px] = 0
            return
        _proxy_fail[px] += 1
        if _proxy_fail[px] >= PROXY_MAX_FAILS and px not in _proxy_dead:
            _proxy_dead.add(px)
            log.warning("proxy %s wyłączone po %d błędach z rzędu (zostało %d)",
                        mask(px), PROXY_MAX_FAILS, len(_proxies) - len(_proxy_dead))


def proxy_for(netloc):
    """Proxy tylko dla sklepów z use_proxy (oszczędza transfer) albo dla wszystkich przy SCRAPER_PROXY_ALL=1."""
    return pick_proxy() if (PROXY_ALL or netloc in _proxy_hosts) else None


def proxy_kw(px):
    return {"proxies": {"http": px, "https": px}} if px else {}


def allowed(url):
    host = "{0.scheme}://{0.netloc}".format(urlparse(url))
    with _lock:
        if host not in _robots:
            rp, reason = None, "brak odpowiedzi"
            for _ in range(3):
                px = proxy_for(urlparse(url).netloc)
                try:
                    r = session().get(host + "/robots.txt", timeout=15, **proxy_kw(px))
                except requests.RequestException as e:
                    report_proxy(px, False)
                    reason = e.__class__.__name__
                    continue
                report_proxy(px, True)
                if r.status_code == 200:
                    rp = RobotFileParser()
                    rp.parse(r.text.splitlines())
                    reason = None
                elif r.status_code >= 500:
                    reason = f"HTTP {r.status_code}"
                    continue
                else:
                    reason = None  # 4xx = brak robots.txt -> wolno wszystko (RFC 9309)
                break
            if reason:  # robots.txt niedostępny z winy serwera -> ostrożnie wstrzymujemy
                log.warning("robots.txt dla %s niedostępny (%s) - pomijam ten host w tym przebiegu", host, reason)
                _robots_note[urlparse(url).netloc] = f"robots.txt niedostępny ({reason}) - sprawdź proxy/blokadę"
                rp = RobotFileParser()
                rp.disallow_all = True
            _robots[host] = rp
            cd = rp.crawl_delay(USER_AGENT) if rp else None
            nl = urlparse(url).netloc
            _min_delay[nl] = max(_min_delay.get(nl, 0.0), float(cd) if cd else 0.0)
            if cd:
                log.info("  robots.txt: Crawl-delay %s s dla %s", cd, host)
        rp = _robots[host]
    return True if rp is None else rp.can_fetch(USER_AGENT, url)


def throttle(host):
    """Rezerwuje następny wolny slot czasowy dla hosta (działa między wątkami)."""
    delay = max(DELAY, _min_delay.get(host, 0.0))
    with _lock:
        now = time.time()
        slot = max(now, _next_slot.get(host, 0.0))
        _next_slot[host] = slot + delay
    if slot > now:
        time.sleep(slot - now)


def get(url, stats=None, retries=3, cookies=None, headers=None):
    def bump(key):
        if stats is not None:
            with _stats_lock:
                stats[key] += 1

    if not allowed(url):
        bump("robots_zablokowane")
        log.debug("robots.txt zabrania: %s", url)
        _tls.last_fail = _robots_note.get(urlparse(url).netloc, "robots.txt zabrania tej ścieżki")
        return None
    host = urlparse(url).netloc
    last_err = "?"
    for attempt in range(retries):
        throttle(host)
        px = None
        try:
            px = proxy_for(host)
            r = session().get(url, timeout=25, cookies=cookies, headers=headers, **proxy_kw(px))
            report_proxy(px, True)
            code = r.status_code
            if code == 200:
                bump("pobrane_ok")
                return r
            if code in (403, 404, 410):
                bump(f"http_{code}")
                _tls.last_fail = f"HTTP {code}" + (f" (server: {r.headers.get('server', '?')})" if code == 403 else "")
                n = stats[f"http_{code}"] if stats is not None else 1
                if code == 403 and n <= 3:
                    log.warning("HTTP 403 (blokada / Cloudflare / bramka 18+?): %s", url)
                elif code != 403:
                    log.debug("HTTP %s: %s", code, url)
                return None
            log.warning("HTTP %s (próba %d/%d): %s", code, attempt + 1, retries, url)
            last_err = f"HTTP {code}"
            if code == 429 or code >= 500:
                pause = 10 * (attempt + 1)
                with _lock:  # spowalniamy WSZYSTKIE wątki dla tego hosta
                    _next_slot[host] = max(_next_slot.get(host, 0.0), time.time() + pause)
        except requests.RequestException as e:
            report_proxy(px, False)
            last_err = e.__class__.__name__
            log.warning("błąd sieci %s przez %s (próba %d/%d): %s", e.__class__.__name__,
                        mask(px), attempt + 1, retries, url)
        time.sleep(2 ** attempt)
    bump("nieudane")
    _tls.last_fail = f"nieudane po {retries} próbach ({last_err})"
    return None


# ----------------------------- sitemap --------------------------------------
def read_xml(url):
    r = get(url)
    if not r:
        return None
    data = r.content
    if url.endswith(".gz") or data[:2] == b"\x1f\x8b":
        try:
            data = gzip.decompress(data)
        except OSError:
            return None
    try:
        return ET.fromstring(data)
    except ET.ParseError:
        return None


def sitemap_urls(site):
    base = site["base"].rstrip("/")
    roots = list(site.get("sitemaps", []))
    if not roots:
        r = get(base + "/robots.txt")
        if r:
            roots = re.findall(r"(?im)^sitemap:\s*(\S+)", r.text)
        if not roots:
            roots = [base + "/sitemap.xml"]
            log.info("  brak wpisu Sitemap w robots.txt, próbuję %s", roots[0])
    seen, out, stack = set(), [], roots[:]
    while stack:
        sm = stack.pop()
        if sm in seen:
            continue
        seen.add(sm)
        tree = read_xml(sm)
        if tree is None:
            log.warning("  sitemapa niedostępna lub nieczytelna: %s", sm)
            continue
        found = child = 0
        for el in tree.iter():
            if el.tag.endswith("loc") and el.text:
                loc = el.text.strip()
                if re.search(r"\.xml(\.gz)?(\?|$)", loc):
                    stack.append(loc)
                    child += 1
                else:
                    out.append(loc)
                    found += 1
        log.info("  sitemapa %s: %d adresów, %d podsitemap", sm, found, child)
    before = len(out)
    pattern = site.get("url_regex")
    if pattern:
        out = [u for u in out if re.search(pattern, u)]
        log.info("  filtr url_regex: %d -> %d adresów", before, len(out))
    return list(dict.fromkeys(out))


# ----------------------------- parsowanie -----------------------------------
_PRICE_RE = re.compile(r"(\d{1,3}(?:[\s.]\d{3})+|\d+)(?:[.,](\d{1,2}))?(?!\d)")


def parse_price(text):
    if text is None:
        return None
    if isinstance(text, (int, float)):
        return float(text)
    cleaned = re.sub(r"[^\d,.\s]", "", str(text))
    m = _PRICE_RE.search(cleaned)
    if not m:
        return None
    whole = re.sub(r"[\s.]", "", m.group(1))
    return float(f"{whole}.{m.group(2) or '0'}")


def norm_availability(raw):
    if raw is None:
        return None
    s = str(raw).lower()
    if re.search(r"outofstock|soldout|brak|niedostęp|niedostep|wyprzedan|out of stock", s):
        return "out_of_stock"
    if re.search(r"preorder|presale|przedsprzeda|zapowiedź|zapowiedz", s):
        return "preorder"
    if re.search(r"instock|limitedavailability|dostępn|dostepn|w magazynie|na stanie|in stock", s):
        return "in_stock"
    return s[:40]


def walk_jsonld(node):
    if isinstance(node, list):
        for x in node:
            yield from walk_jsonld(x)
    elif isinstance(node, dict):
        t = node.get("@type")
        types = t if isinstance(t, list) else [t]
        if "Product" in types:
            yield node
        for v in node.values():
            if isinstance(v, (list, dict)):
                yield from walk_jsonld(v)


def from_jsonld(soup):
    for tag in soup.find_all("script", type="application/ld+json"):
        try:
            data = json.loads(tag.string or tag.get_text() or "")
        except json.JSONDecodeError:
            continue
        for prod in walk_jsonld(data):
            offers = prod.get("offers")
            if isinstance(offers, list):
                offers = offers[0] if offers else {}
            offers = offers or {}
            price = offers.get("price", offers.get("lowPrice"))
            if price is None and isinstance(offers.get("priceSpecification"), dict):
                price = offers["priceSpecification"].get("price")
            return {
                "_ld": True,
                "name": prod.get("name"),
                "sku": prod.get("sku") or prod.get("mpn"),
                "price": parse_price(price),
                "currency": offers.get("priceCurrency") or "PLN",
                "availability": norm_availability(offers.get("availability")),
            }
    return None


def meta(soup, *names):
    for n in names:
        el = soup.find("meta", attrs={"property": n}) or soup.find("meta", attrs={"name": n}) \
            or soup.find("meta", attrs={"itemprop": n})
        if el and el.get("content"):
            return el["content"]
    return None


def from_selectors(soup, sel):
    def txt(key):
        if key in sel:
            el = soup.select_one(sel[key])
            if el:
                return el.get("content") or el.get_text(" ", strip=True)
        return None
    return {
        "name": txt("name"),
        "price": parse_price(txt("price")),
        "availability": norm_availability(txt("availability")),
    }


def extract(html, site):
    soup = BeautifulSoup(html, "lxml")
    d = from_jsonld(soup) or {}
    if d.get("price") is None:
        d["price"] = parse_price(meta(soup, "product:price:amount", "og:price:amount", "price"))
        d.setdefault("currency", meta(soup, "product:price:currency", "og:price:currency") or "PLN")
    if not d.get("availability"):
        d["availability"] = norm_availability(meta(soup, "product:availability", "og:availability", "availability"))
    if not d.get("name"):
        d["name"] = meta(soup, "og:title") or (soup.h1.get_text(strip=True) if soup.h1 else None)
    if site.get("selectors"):
        s = from_selectors(soup, site["selectors"])
        for k, v in s.items():
            if v is not None and (d.get(k) is None or site.get("prefer_selectors")):
                d[k] = v
    if not d.get("name"):
        return None  # to nie jest strona produktu
    if d.get("price") is None and not d.get("_ld"):
        return None  # brak ceny i brak danych Product -> nie produkt
    return d


# ----------------------------- baza -----------------------------------------
def db():
    con = sqlite3.connect(DB_PATH)
    con.executescript("""
    CREATE TABLE IF NOT EXISTS products(
      url TEXT PRIMARY KEY, site TEXT, name TEXT, sku TEXT,
      first_seen TEXT, last_seen TEXT);
    CREATE TABLE IF NOT EXISTS prices(
      id INTEGER PRIMARY KEY AUTOINCREMENT, url TEXT, ts TEXT,
      price REAL, currency TEXT, availability TEXT);
    CREATE INDEX IF NOT EXISTS ix_prices_url ON prices(url, ts);
    CREATE TABLE IF NOT EXISTS nonproduct(url TEXT PRIMARY KEY, ts TEXT);
    """)
    return con


def save(con, site_name, url, d):
    now = datetime.now(timezone.utc).isoformat(timespec="seconds")
    con.execute("""INSERT INTO products(url,site,name,sku,first_seen,last_seen)
                   VALUES(?,?,?,?,?,?)
                   ON CONFLICT(url) DO UPDATE SET name=excluded.name,
                   sku=excluded.sku, last_seen=excluded.last_seen""",
                (url, site_name, d["name"], d.get("sku"), now, now))
    last = con.execute("SELECT price, availability FROM prices WHERE url=? "
                       "ORDER BY id DESC LIMIT 1", (url,)).fetchone()
    cur = (d["price"], d.get("availability"))
    if last != cur:
        con.execute("INSERT INTO prices(url,ts,price,currency,availability) VALUES(?,?,?,?,?)",
                    (url, now, d["price"], d.get("currency", "PLN"), d.get("availability")))
        return True
    return False


# ----------------------------- komendy --------------------------------------
def fmt_dur(sec):
    sec = int(sec)
    return f"{sec // 3600}h{sec % 3600 // 60:02d}m" if sec >= 3600 else f"{sec // 60}m{sec % 60:02d}s"


# ----------------------------- tryb LISTING ---------------------------------
def _pick(el, spec):
    """Wartość z kafelka wg 'selektor' lub 'selektor@atrybut'. Spec może być listą = próbuj po kolei."""
    if not spec:
        return None
    for one in ([spec] if isinstance(spec, str) else spec):
        css, attr = one, None
        m = re.match(r"^(.*)@([\w-]+)$", one)
        if m:
            css, attr = m.group(1), m.group(2)
        node = el.select_one(css) if css else el
        if node is None:
            continue
        val = node.get(attr) if attr else node.get_text(" ", strip=True)
        if val:
            return val
    return None


def has(tile, css):
    """Czy selektor pasuje do SAMEGO kafelka albo któregoś elementu w środku
    (np. klasa 'instock' na <li>, atrybut data-product_disable, przycisk w środku)."""
    return tile.select_one(css) is not None or sv.match(css, tile)


def parse_listing(html, page_url, cfg):
    """Zwraca (liczba_kafelków, [produkty]) ze strony kategorii.
    html: bajty (r.content) - kodowanie wykrywa BeautifulSoup, bo r.text myli polskie znaki
    gdy serwer nie poda charsetu w nagłówku."""
    soup = BeautifulSoup(html, "lxml")
    sel = cfg["item"]
    tiles = []
    for one in ([sel] if isinstance(sel, str) else sel):  # lista = pierwszy selektor, który coś znajdzie
        tiles = soup.select(one)
        if tiles:
            break
    products = []
    for tile in tiles:
        name, href = _pick(tile, cfg["name"]), _pick(tile, cfg["link"])
        if not name or not href:
            continue
        raw_price = _pick(tile, cfg.get("price"))
        if raw_price:
            for pat in cfg.get("price_strip", []):
                raw_price = re.sub(pat, " ", raw_price, flags=re.I | re.S)
        text = tile.get_text(" ", strip=True).lower()
        out = False
        if cfg.get("in_stock") and not has(tile, cfg["in_stock"]):
            out = True  # brak elementu "dostępny" (np. przycisku koszyka)
        if cfg.get("out_of_stock") and has(tile, cfg["out_of_stock"]):
            out = True
        if any(t.lower() in text for t in cfg.get("out_text", [])):
            out = True
        products.append({
            "name": name.strip(), "sku": None, "currency": "PLN",
            "availability": "out_of_stock" if out else "in_stock",
            "price": parse_price(raw_price),
            "url": urljoin(page_url, href.strip()),
        })
    return len(tiles), products


def site_headers(name, site):
    """Nagłówki sklepu. User-Agent przeglądarki tylko, gdy włączony: SCRAPER_BROWSER_UA=1 / lista sklepów,
    albo "browser_ua": True w konfiguracji sklepu."""
    h = dict(site.get("headers") or {})
    wanted = {x.strip() for x in BROWSER_UA_SPEC.split(",") if x.strip()}
    if site.get("browser_ua") or "1" in wanted or name.lower() in wanted:
        h.setdefault("User-Agent", BROWSER_UA)
        h.setdefault("Accept", "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8")
        h.setdefault("Accept-Language", "pl-PL,pl;q=0.9,en-US;q=0.8,en;q=0.7")
    return h or None


def diag(r):
    """Krótki opis odpowiedzi, gdy strona ma 0 kafelków: tytuł, serwer, czy to ochrona anty-botowa."""
    m = re.search(rb"<title[^>]*>(.*?)</title>", r.content[:20000], re.I | re.S)
    title = re.sub(r"\s+", " ", m.group(1).decode("utf-8", "replace")).strip()[:80] if m else "?"
    hdr = r.headers
    guard = "Cloudflare" if ("cf-ray" in hdr or "cloudflare" in hdr.get("server", "").lower()) else hdr.get("server", "?")
    return f"HTTP {r.status_code}, {len(r.content)} B, title={title!r}, serwer/ochrona={guard}"


def listing_category(name, site, cfg, cat_url, q, stats):
    """Wątek roboczy: przechodzi strony jednej kategorii i wrzuca produkty do kolejki."""
    start = cfg.get("start", 1)
    nxt = cfg.get("next", "{url}?page={page}")
    first = cfg.get("first")
    max_pages = cfg.get("max_pages", 400)
    hdrs = site_headers(name, site)
    seen, page, total, reason = set(), start, 0, None
    try:
        while page < start + max_pages:
            pattern = first if (first and page == start) else nxt
            url = pattern.format(url=cat_url, page=page)
            _tls.last_fail = "?"
            r = get(url, stats, cookies=site.get("cookies"), headers=hdrs)
            if not r:
                if page == start:
                    reason = _tls.last_fail
                    log.warning("[%s] kategoria niedostępna (%s): %s", name, reason, url)
                break
            n_tiles, items = parse_listing(r.content, url, cfg)
            new, on_page = [], set()
            for it in items:
                if it["url"] not in seen and it["url"] not in on_page:
                    new.append(it)
                    on_page.add(it["url"])
            if page == start and n_tiles == 0:
                reason = "0 kafelków: " + diag(r)
                log.warning("[%s] %s | %s", name, reason, url)
            elif page == start and n_tiles and not items:
                reason = f"{n_tiles} kafelków, ale selektory name/link nic nie wyciągają"
                log.warning("[%s] %s: %s", name, reason, url)
            if not new:
                break  # pusta strona albo ta sama co poprzednia (koniec paginacji)
            seen.update(it["url"] for it in new)
            total += len(new)
            q.put(("items", name, cat_url, page, new))
            page += 1
    except Exception as e:  # nigdy nie wieszamy głównego wątku
        reason = f"wyjątek: {e}"
        log.warning("[%s] błąd w kategorii %s: %s", name, cat_url, e)
    finally:
        q.put(("done", name, cat_url, page - start, total, reason))


def run_listing(con, names, args):
    """Wszystkie sklepy 'listing' naraz: kategorie jako zadania, zapis do bazy w jednym wątku."""
    t0 = time.time()
    per_shop = {n: list(SITES[n]["listing"]["categories"]) for n in names}
    tasks = []
    while any(per_shop.values()):  # na zmianę po sklepie, żeby wątki nie blokowały się na jednym hoście
        for n in names:
            if per_shop[n]:
                tasks.append((n, per_shop[n].pop(0)))
    stats = {n: Counter() for n in names}
    problems = {n: [] for n in names}
    cats_total = {n: len(SITES[n]["listing"]["categories"]) for n in names}
    q = queue.Queue()
    log.info("TRYB LISTING: %d sklepów, %d kategorii, wątki: %d, odstęp: %.2fs",
             len(names), len(tasks), args.workers, DELAY)
    ua_shops = [n for n in names if site_headers(n, SITES[n]) and "User-Agent" in site_headers(n, SITES[n])]
    if ua_shops:
        log.info("User-Agent przeglądarki włączony dla: %s", ", ".join(ua_shops))
    pool = ThreadPoolExecutor(max_workers=args.workers)
    for n, cat in tasks:
        cfg = dict(SITES[n]["listing"])
        if args.max:
            cfg["max_pages"] = args.max  # w trybie listing --max = limit stron na kategorię
        pool.submit(listing_category, n, SITES[n], cfg, cat, q, stats[n])
    pending, last_beat = len(tasks), time.time()
    try:
        while pending:
            try:
                msg = q.get(timeout=5)
            except queue.Empty:
                msg = None
            if msg and msg[0] == "items":
                _, n, cat, page, items = msg
                st = stats[n]
                st["strony"] += 1
                for d in items:
                    st["produkty"] += 1
                    if d["price"] is None:
                        st["bez_ceny"] += 1
                    if save(con, n, d["url"], d):
                        st["zmiany_w_historii"] += 1
                        log.debug("zapisano: %s | %s | %s", d["name"], d["price"], d["availability"])
            elif msg:
                _, n, cat, pages, total, reason = msg
                if reason:
                    problems[n].append((cat, reason))
                pending -= 1
                stats[n]["kategorie_gotowe"] += 1
                con.commit()
                log.info("[%s] kategoria gotowa: %s (%d str., %d prod.) | zostało kategorii: %d",
                         n, cat.rstrip("/").rsplit("/", 1)[-1], pages, total, pending)
            if time.time() - last_beat >= 20:
                last_beat = time.time()
                for n in names:
                    st = stats[n]
                    log.info("[%s] kategorie %d/%d | strony: %d | produkty: %d | zmiany: %d | błędy: %d | %s",
                             n, st["kategorie_gotowe"], cats_total[n], st["strony"], st["produkty"],
                             st["zmiany_w_historii"], st["nieudane"], fmt_dur(time.time() - t0))
    finally:
        pool.shutdown(wait=False, cancel_futures=True)
        con.commit()
    for n in names:
        st = stats[n]
        log.info("[%s] KONIEC | %s", n, ", ".join(f"{k}={v}" for k, v in sorted(st.items())) or "brak danych")
        if st["produkty"] == 0:
            log.error("[%s] 0 produktów - sprawdź selektory/blokadę (uruchom z SCRAPER_VERBOSE=1)", n)
    if any(problems.values()):
        log.warning("===== PROBLEMY: kategorie bez produktów (skopiuj ten blok, gdy chcesz poprawek) =====")
        for n in names:
            for cat, reason in problems[n]:
                log.warning("[%s] %s -> %s", n, cat, reason)
    log.info("TRYB LISTING zakończony w %s", fmt_dur(time.time() - t0))
    return [(n, stats[n]["strony"], stats[n]) for n in names]


def resolve_sites(args):
    if not args.site:
        return list(SITES)
    wanted = [x.lower() for x in re.split(r"[,\s]+", args.site) if x]
    lookup = {k.lower(): k for k in SITES}
    bad = [w for w in wanted if w not in lookup]
    if bad:
        raise SystemExit(f"Nieznane sklepy: {bad}. Dostępne: {', '.join(SITES)}")
    return [lookup[w] for w in wanted]


def fetch_one(url, site, stats, hdrs=None):
    """Praca wątku roboczego: pobierz + sparsuj. Zwraca (url, dane, status)."""
    r = get(url, stats, cookies=site.get("cookies"), headers=hdrs)
    if not r:
        return url, None, "fetch"
    try:
        d = extract(r.content, site)
    except Exception as e:
        return url, None, f"parse:{e}"
    return url, d, ("ok" if d else "nonproduct")


def cmd_scrape(args):
    global DELAY
    DELAY = args.delay
    setup_proxies(args)
    con = db()
    names = resolve_sites(args)
    for n in names:  # ustawienia per sklep: 'delay' (min. odstęp) i 'use_proxy'
        site = SITES[n]
        hosts = {urlparse(site["base"]).netloc}
        hosts |= {urlparse(c).netloc for c in site.get("listing", {}).get("categories", [])}
        for h in hosts:
            if site.get("delay"):
                _min_delay[h] = max(_min_delay.get(h, 0.0), float(site["delay"]))
            if site.get("use_proxy"):
                _proxy_hosts.add(h)
    if _proxies and not PROXY_ALL and not _proxy_hosts:
        log.warning("podano proxy, ale żaden wybrany sklep nie ma use_proxy (ustaw SCRAPER_PROXY_ALL=1, by użyć dla wszystkich)")
    in_actions = bool(os.environ.get("GITHUB_ACTIONS"))
    summary = []
    listing_names = [n for n in names if SITES[n].get("listing")]
    sitemap_names = [n for n in names if n not in listing_names]
    if listing_names:
        if in_actions:
            print("::group::tryb listing", flush=True)
        summary += run_listing(con, listing_names, args)
        if in_actions:
            print("::endgroup::", flush=True)
    for name in sitemap_names:
        if in_actions:
            print(f"::group::{name}", flush=True)
        site = SITES[name]
        t0 = time.time()
        log.info("[%s] START - pobieram sitemapę (wątki: %d, odstęp: %.2fs)", name, args.workers, DELAY)
        urls = sitemap_urls(site)
        if not urls:
            log.error("[%s] brak adresów do sprawdzenia - sitemapa pusta/niedostępna "
                      "albo url_regex nic nie łapie. Pomijam sklep.", name)
            summary.append((name, 0, Counter()))
            if in_actions:
                print("::endgroup::", flush=True)
            continue

        # pomijamy adresy, o których niedawno ustaliliśmy, że to nie produkty
        if not args.recheck:
            cutoff = (datetime.now(timezone.utc) - timedelta(days=NONPRODUCT_TTL_DAYS)).isoformat(timespec="seconds")
            known = {u for (u,) in con.execute("SELECT url FROM nonproduct WHERE ts > ?", (cutoff,))}
            before = len(urls)
            urls = [u for u in urls if u not in known]
            if before != len(urls):
                log.info("[%s] pomijam %d adresów znanych z poprzednich przebiegów jako nie-produkty", name, before - len(urls))
        if args.max:
            urls = urls[: args.max]
        n = len(urls)
        log.info("[%s] %d adresów do sprawdzenia", name, n)

        stats = Counter()
        samples_np, seen_np, samples_prod = [], 0, []
        last_beat = time.time()
        pool = ThreadPoolExecutor(max_workers=args.workers)
        try:
            for i, (url, d, status) in enumerate(pool.map(lambda u, h=site_headers(name, site): fetch_one(u, site, stats, h), urls), 1):
                if status == "ok":
                    stats["produkty"] += 1
                    if d.get("price") is None:
                        stats["bez_ceny"] += 1
                    if save(con, name, url, d):
                        stats["zmiany_w_historii"] += 1
                        log.debug("zapisano: %s | %s | %s", d["name"], d["price"], d.get("availability"))
                    con.execute("DELETE FROM nonproduct WHERE url=?", (url,))
                    if len(samples_prod) < 3:
                        samples_prod.append(url)
                elif status == "nonproduct":
                    stats["to_nie_produkt"] += 1
                    con.execute("INSERT OR REPLACE INTO nonproduct(url, ts) VALUES(?, ?)",
                                (url, datetime.now(timezone.utc).isoformat(timespec="seconds")))
                    seen_np += 1  # próbkowanie (reservoir) do podglądu w logu
                    if len(samples_np) < 8:
                        samples_np.append(url)
                    elif random.random() < 8 / seen_np:
                        samples_np[random.randrange(8)] = url
                elif status.startswith("parse:"):
                    stats["blad_parsowania"] += 1
                    log.warning("[%s] błąd parsowania %s: %s", name, url, status[6:])
                if i % 25 == 0:
                    con.commit()
                if time.time() - last_beat >= 20 or i == n:
                    last_beat = time.time()
                    el = time.time() - t0
                    rate = i / el if el else 0
                    eta = (n - i) / rate if rate else 0
                    log.info("[%s] %d/%d (%.0f%%) | produkty: %d | zmiany: %d | nie-produkty: %d | "
                             "błędy: %d | %.1f str/s | zostało ~%s",
                             name, i, n, 100 * i / n, stats["produkty"], stats["zmiany_w_historii"],
                             stats["to_nie_produkt"],
                             stats["nieudane"] + stats["blad_parsowania"], rate, fmt_dur(eta))
                if i == 20 and stats["produkty"] == 0:
                    log.warning("[%s] po 20 stronach 0 produktów - sprawdź url_regex, JSON-LD "
                                "lub selektory (uruchom z -v, żeby zobaczyć szczegóły)", name)
        finally:
            pool.shutdown(wait=False, cancel_futures=True)
            con.commit()

        log.info("[%s] KONIEC w %s | %s", name, fmt_dur(time.time() - t0),
                 ", ".join(f"{k}={v}" for k, v in sorted(stats.items())) or "brak danych")
        if samples_prod:
            log.info("[%s] przykładowe PRODUKTY:\n    %s", name, "\n    ".join(samples_prod))
        if samples_np:
            log.info("[%s] przykładowe NIE-produkty (na tej podstawie ustaw url_regex):\n    %s",
                     name, "\n    ".join(samples_np))
        summary.append((name, n, stats))
        if in_actions:
            print("::endgroup::", flush=True)

    log.info("===== PODSUMOWANIE =====")
    for name, n, st in summary:
        log.info("%-14s sprawdzone: %5d | produkty: %5d | zmiany: %5d | błędy: %d",
                 name, n, st["produkty"], st["zmiany_w_historii"], st["nieudane"] + st["blad_parsowania"])
    path = os.environ.get("GITHUB_STEP_SUMMARY")
    if path:
        with open(path, "a", encoding="utf-8") as f:
            f.write("| sklep | sprawdzone | produkty | zmiany | błędy |\n|---|---|---|---|---|\n")
            for name, n, st in summary:
                f.write(f"| {name} | {n} | {st['produkty']} | {st['zmiany_w_historii']} | "
                        f"{st['nieudane'] + st['blad_parsowania']} |\n")


def cmd_export(args):
    con = db()
    rows = con.execute("""
      SELECT p.site, p.name, p.sku, p.url, pr.price, pr.currency,
             pr.availability, pr.ts
      FROM products p JOIN prices pr ON pr.id =
        (SELECT MAX(id) FROM prices WHERE url = p.url)
      ORDER BY p.site, p.name""").fetchall()
    with open(args.path, "w", newline="", encoding="utf-8-sig") as f:
        w = csv.writer(f, delimiter=";")
        w.writerow(["sklep", "produkt", "sku", "link", "cena", "waluta", "dostepnosc", "zmiana_ts"])
        w.writerows(rows)
    print(f"Zapisano {len(rows)} wierszy do {args.path}")


def cmd_history(args):
    con = db()
    for ts, price, cur, av in con.execute(
            "SELECT ts, price, currency, availability FROM prices WHERE url=? ORDER BY id", (args.url,)):
        price_s = f"{price:>9.2f}" if price is not None else "     brak"
        print(f"{ts}  {price_s} {cur}  {av}")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    ap.add_argument("-v", "--verbose", action="store_true", help="loguj każdy adres (poziom DEBUG)")
    sub = ap.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("scrape")
    s.add_argument("--site", default=env("SCRAPER_ONLY"), help="sklepy po przecinku (domyślnie wszystkie; ENV: SCRAPER_ONLY)")
    s.add_argument("--max", type=int, default=int(env("SCRAPER_MAX", 0)) or None,
                   help="limit: adresów na sklep (sitemap) / stron na kategorię (listing); ENV: SCRAPER_MAX")
    s.add_argument("--workers", type=int, default=WORKERS, help="liczba równoległych wątków")
    s.add_argument("--delay", type=float, default=DELAY, help="min. odstęp między zapytaniami do hosta (s)")
    s.add_argument("--proxy", action="append", help="adres proxy (http://user:haslo@host:port lub socks5://...), można podać wiele razy")
    s.add_argument("--proxy-file", help="plik z proxy, jedno na linię")
    s.add_argument("--recheck", action="store_true", default=env("SCRAPER_RECHECK") == "1", help="sprawdź ponownie też adresy znane jako nie-produkty")
    s.set_defaults(fn=cmd_scrape)
    e = sub.add_parser("export")
    e.add_argument("path")
    e.set_defaults(fn=cmd_export)
    h = sub.add_parser("history")
    h.add_argument("url")
    h.set_defaults(fn=cmd_history)
    argv = sys.argv[1:]
    if not any(a in ("scrape", "export", "history") for a in argv):
        argv.append("scrape")  # bez argumentów = scrape (GitHub Actions: samo `python fajerwerki_scraper.py`)
    args = ap.parse_args(argv)
    try:
        sys.stdout.reconfigure(line_buffering=True)
    except AttributeError:
        pass
    logging.basicConfig(level=logging.DEBUG if (args.verbose or env("SCRAPER_VERBOSE") == "1") else logging.INFO,
                        format="%(asctime)s %(levelname)-7s %(message)s",
                        datefmt="%H:%M:%S", stream=sys.stdout)
    logging.getLogger("urllib3").setLevel(logging.WARNING)
    args.fn(args)


if __name__ == "__main__":
    main()
