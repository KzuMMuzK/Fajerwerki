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
    SCRAPER_PROXY_SOURCE=geonode   darmowe proxy z Geonode, tylko dla sklepów z use_proxy (opcje: SCRAPER_PROXY_COUNTRY=PL,DE  SCRAPER_FREE_PROXY_COUNT=12)
    SCRAPER_MODE=sitemap|listing|auto   SCRAPER_VERBOSE=1   SCRAPER_RECHECK=1   SCRAPER_PROXY_ALL=1   SCRAPER_DB=sciezka/do/bazy.db

Jak to działa (tryb sitemap; tryb listing czyta strony kategorii - patrz SITES):
  1. Adresy produktów bierze z sitemap.xml sklepu (robots.txt -> Sitemap:).
  2. Dane czyta z JSON-LD (schema.org Product/Offer), potem z meta tagów,
     a na końcu z selektorów CSS podanych w konfiguracji sklepu.
  3. Zapisuje do SQLite; nowy wpis w historii powstaje tylko gdy zmieni się
     cena lub dostępność.
  4. Szanuje robots.txt i robi odstępy między zapytaniami.
"""
import argparse
import contextlib
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
import unicodedata
import xml.etree.ElementTree as ET
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, as_completed
from concurrent.futures import TimeoutError as FuturesTimeout
from datetime import datetime, timedelta, timezone
from urllib.parse import unquote, urljoin, urlparse
from urllib.robotparser import RobotFileParser
from curl_cffi import requests as cffi_requests  # Dodaj na górze pliku

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
        "mode": "listing",   # przez proxy płacisz za transfer: strony kategorii (kilkadziesiąt produktów w 1 zapytaniu) zamiast tysięcy stron produktów; usuń tę linię, by użyć sitemapy
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
            "first": "{url}", "next": "{url}/page/{page}/", "start": 1,   # nowy szablon (Woodmart); paginacja do potwierdzenia
            "item": "div.wd-product",
            "name": ["h3 a", ".wd-entities-title a", "a"], "link": ["h3 a@href", ".wd-entities-title a@href", "a@href"],
            "price": ["span.price ins .woocommerce-Price-amount", "span.price .woocommerce-Price-amount",
                      ".woocommerce-Price-amount", "span.price"],
            "out_of_stock": ".outofstock", "out_text": ["produkt niedostępny", "brak w magazynie"]},
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
        "listing": {"next": "{url}?page={page}", "start": 1,   # nowy szablon (Tailwind); paginacja do potwierdzenia
            "item": "a.group.relative.flex", "name": ["img@alt", "h3", "h2"], "link": "@href",
            "price": "span[class*='font-semibold'][class*='text-[17px]']",
            "out_text": ["niedostępn", "brak towaru", "powiadom"],
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
        "mode": "listing",   # j.w. (strony ~0,9 MB); usuń tę linię, by użyć sitemapy
        "listing": {"next": "{url}?counter={page}&p=5", "start": 0, "item": "product-tile",
            "name": "a.link_no-underline", "link": "a.link_no-underline@href", "price": "span.price__value",
            "out_text": ["niedostępn", "powiadom o dostępności", "powiadom mnie", "brak towaru", "wyprzedan"],
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
        "base": "https://piroart.pl", "use_proxy": True,
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
_proxies, _proxy_i, _proxy_fail, _proxy_dead = [], 0, Counter(), {}   # _proxy_dead: proxy -> do kiedy w pauzie
_host_sem = {}  # netloc -> semafor: limit równoległych zapytań przez proxy
_proxy_strikes = Counter()  # ile razy proxy trafiło do pauzy
_min_delay, _proxy_hosts = {}, set()   # netloc -> min. odstęp (crawl-delay / 'delay' sklepu); hosty z use_proxy
PROXY_ALL = env('SCRAPER_PROXY_ALL') == '1'  # 1 = proxy dla wszystkich sklepów, nie tylko z use_proxy
PROXY_MAX_FAILS = 3   # tyle błędów z rzędu = pauza dla tego proxy
PROXY_PAUSE = 120     # sekundy pauzy (potem proxy dostaje kolejną szansę)

def session():
    """Osobna sesja HTTP na wątek (z imitacją Chrome, aby obejść blokady TLS)."""
    sess = getattr(_tls, "s", None)
    if sess is None:
        # impersonate="chrome" imituje TLS/HTTP2 nowoczesnej przeglądarki Chrome.
        # Możesz też użyć konkretnej wersji, np. "chrome124" lub "chrome120".
        sess = cffi_requests.Session(impersonate="chrome")
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


def short_err(e):
    """Sedno błędu sieci bez adresów IP i haseł, np. 'ProxyError: Tunnel connection failed: 407 Proxy
    Authentication Required' (logi w publicznym repo są widoczne dla wszystkich)."""
    msg = str(e)
    msg = re.sub(r"//[^/@\s]+@", "//***@", msg)
    msg = re.sub(r"\b\d{1,3}(?:\.\d{1,3}){3}(?::\d+)?\b", "<ip>", msg)
    m = re.search(r"(Tunnel connection failed: \d+ [^'\")]+|Connection refused|Connection reset[^'\")]*|"
                  r"timed out|Name or service not known|Temporary failure in name resolution|"
                  r"Remote end closed connection[^'\")]*|certificate verify failed[^'\")]*|Connection aborted[^'\")]*)", msg)
    detail = m.group(1) if m else re.sub(r"\s+", " ", msg)[-100:].strip(" ()'\"")
    return f"{e.__class__.__name__}: {detail}"[:160]


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


def _live_count():
    now = time.time()
    return sum(1 for px in _proxies if _proxy_dead.get(px, 0) <= now)


def pick_proxy():
    """Następne proxy (round-robin) pomijając te w pauzie. Bez listy proxy -> None (połączenie bezpośrednie).
    Gdy wszystkie są w pauzie, bierze to, którego pauza kończy się najwcześniej - NIGDY nie przechodzi na
    połączenie bezpośrednie (ujawniłoby Twoje IP)."""
    global _proxy_i
    if not _proxies:
        return None
    with _lock:
        now = time.time()
        for _ in range(len(_proxies)):
            px = _proxies[_proxy_i % len(_proxies)]
            _proxy_i += 1
            if _proxy_dead.get(px, 0) <= now:
                return px
        return min(_proxies, key=lambda x: _proxy_dead.get(x, 0))


def report_proxy(px, ok):
    if not px:
        return
    with _lock:
        if ok:
            _proxy_fail[px] = 0
            _proxy_dead.pop(px, None)
            return
        _proxy_fail[px] += 1
        if _proxy_fail[px] >= PROXY_MAX_FAILS:
            _proxy_fail[px] = 0
            _proxy_dead[px] = time.time() + PROXY_PAUSE
            _proxy_strikes[px] += 1
            if px in _free_proxies and _proxy_strikes[px] >= 2:  # darmowe proxy żyją krótko - nie męczymy ich w kółko
                label = mask(px)
                _proxies.remove(px)
                _free_proxies.discard(px)
                _proxy_dead.pop(px, None)
                log.warning("%s (darmowe) usunięte po powtarzających się błędach (zostało %d)", label, len(_proxies))
            else:
                log.warning("%s w pauzie %d s po %d błędach z rzędu (aktywnych: %d z %d)",
                            mask(px), PROXY_PAUSE, PROXY_MAX_FAILS, _live_count(), len(_proxies))


GEONODE_API = os.environ.get("GEONODE_API", "https://proxylist.geonode.com/api/proxy-list")
_free_proxies = set()   # proxy pochodzące z darmowej listy (nie dostają ruchu HTTP, tylko HTTPS)


def _socks_ok():
    try:
        import socks  # noqa: F401  (PySocks, instalowany przez requests[socks])
    except ImportError:
        return False
    return True


def geonode_candidates(countries=()):
    """Lista kandydatów z API Geonode: tylko 'anonymous'/'elite' (transparent zdradza Twoje IP), uptime >= 80%."""
    try:
        r = requests.get(GEONODE_API, params={"limit": 500, "page": 1, "sort_by": "lastChecked", "sort_type": "desc"},
                         timeout=30, headers={"User-Agent": USER_AGENT})
        r.raise_for_status()
        data = r.json().get("data", [])
    except Exception as e:
        log.warning("darmowe proxy: nie udało się pobrać listy z Geonode: %s", short_err(e))
        return []
    socks_ok, cands, skipped = _socks_ok(), [], Counter()
    for it in data:
        try:
            ip, port = str(it["ip"]), str(it["port"])
        except (KeyError, TypeError):
            continue
        if str(it.get("anonymityLevel", "")).lower() == "transparent":
            skipped["transparent"] += 1
            continue
        if countries and str(it.get("country", "")).upper() not in countries:
            continue
        up = float(it.get("upTime") or 0)
        if up < 80:
            skipped["niski uptime"] += 1
            continue
        protos = {str(x).lower() for x in (it.get("protocols") or [])}
        if protos & {"http", "https"}:
            scheme = "http"       # serwer proxy HTTP(S); do stron HTTPS używa tunelu CONNECT
        elif "socks5" in protos and socks_ok:
            scheme = "socks5h"    # DNS po stronie proxy
        elif "socks4" in protos and socks_ok:
            scheme = "socks4a"
        else:
            skipped["socks bez PySocks" if protos & {"socks4", "socks5"} else "inny protokół"] += 1
            continue
        prio = 0 if "https" in protos else (1 if scheme == "socks5h" else 2)
        cands.append((prio, round(-up / 10), round(float(it.get("responseTime") or 9999) / 200), f"{scheme}://{ip}:{port}"))
    random.shuffle(cands)                     # remisy losowo, żeby nie obciążać wciąż tych samych serwerów
    cands.sort(key=lambda c: c[:3])
    log.info("darmowe proxy (Geonode): %d na liście, %d kandydatów po filtrach%s", len(data), len(cands),
             (", odrzucone: " + ", ".join(f"{k} {v}" for k, v in skipped.items())) if skipped else "")
    return [c[3] for c in cands]


def _check_proxy(px, targets):
    """Czy proxy przepuszcza PRAWDZIWĄ stronę sklepu (HTTP 200 + HTML) z weryfikacją certyfikatu TLS?"""
    t0 = time.time()
    for url, hdrs in targets:
        try:
            r = requests.get(url, proxies={"http": px, "https": px}, timeout=(5, 9),
                             headers={"User-Agent": USER_AGENT, **(hdrs or {})})
        except requests.RequestException:
            return None
        if r.status_code != 200 or len(r.content) < 1500 or b"<html" not in r.content[:50000].lower():
            return None
    return time.time() - t0

def _fetch_from_proxyscrape(targets=None, countries=()):
    """Pobiera darmowe proxy z ProxyScrape (format tekstowy: protocol://ip:port)."""
    url = "https://api.proxyscrape.com/v4/free-proxy-list/get"
    params = {
        "request": "display_proxies",
        "proxy_format": "protocolipport",
        "format": "text",
    }
    if countries:
        params["country"] = ",".join(countries)
    try:
        r = requests.get(url, params=params, timeout=30, headers={"User-Agent": USER_AGENT})
        r.raise_for_status()
        lines = [line.strip() for line in r.text.splitlines() if line.strip()]
        proxies = [line for line in lines if line.startswith(("http://", "https://", "socks4://", "socks5://"))]
        log.info("ProxyScrape: otrzymano %d proxy", len(proxies))
        return proxies
    except requests.RequestException as e:
        log.warning("ProxyScrape: błąd pobierania: %s", short_err(e))
        return []


def acquire_free_proxies(targets, want=None, budget=None, countries=()):
    """Pobiera listę z Geonode i ProxyScrape, sprawdza kandydatów równolegle i dodaje działające do rotacji."""
    want = want or int(env("SCRAPER_FREE_PROXY_COUNT", 12))
    budget = budget or int(env("SCRAPER_FREE_PROXY_SECONDS", 90))
    t0 = time.time()

    # 1) Zbierz kandydatów z obu źródeł
    candidates = []
    try:
        candidates.extend(geonode_candidates(countries))
    except Exception as e:
        log.warning("Geonode: błąd pobierania: %s", short_err(e))
    try:
        candidates.extend(_fetch_from_proxyscrape(targets, countries))
    except Exception as e:
        log.warning("ProxyScrape: błąd pobierania: %s", short_err(e))

    # 2) Usuń duplikaty i już znane proxy
    seen = set()
    candidates = [p for p in candidates if not (p in seen or seen.add(p)) and p not in _proxies][:400]
    if not candidates:
        log.warning("darmowe proxy: żadne źródło nie zwróciło kandydatów")
        return []

    # 3) Sprawdź kandydatów równolegle na stronach docelowych sklepów
    found = []
    pool = ThreadPoolExecutor(max_workers=40)
    futs = {pool.submit(_check_proxy, px, targets): px for px in candidates}
    try:
        for fut in as_completed(futs, timeout=budget):
            ms = fut.result()
            if ms is not None:
                found.append((ms, futs[fut]))
                if len(found) >= want:
                    break
    except FuturesTimeout:
        pass
    finally:
        pool.shutdown(wait=False, cancel_futures=True)

    found.sort()
    with _lock:
        for _, px in found:
            if px not in _proxies:
                _proxies.append(px)
                _free_proxies.add(px)

    log.info("Darmowe proxy (Geonode + ProxyScrape): sprawdzono %d kandydatów w %.0f s, działa %d (cel: %d) – łącznie w rotacji: %d",
             len(futs), time.time() - t0, len(found), want, len(_proxies))
    if not found:
        log.warning("Darmowe proxy: żaden kandydat nie przepuścił stron sklepów – sklepy z use_proxy mogą nie działać w tym przebiegu")
    return [px for _, px in found]

def free_proxy_targets(names):
    """Strony główne sklepów używających proxy - na nich sprawdzamy kandydatów."""
    out, seen = [], set()
    for n in names:
        site = SITES[n]
        if not (PROXY_ALL or site.get("use_proxy")):
            continue
        host = urlparse(site["base"]).netloc
        if host not in seen:
            seen.add(host)
            out.append((site["base"].rstrip("/") + "/", site_headers(n, site)))
    return out


def start_free_refresher(targets, countries, every=480):
    """Co kilka minut uzupełnia pulę, gdy działających darmowych proxy zostało mało (żyją krótko)."""
    def loop():
        while True:
            time.sleep(every)
            now = time.time()
            with _lock:
                live = sum(1 for x in _free_proxies if _proxy_dead.get(x, 0) <= now)
            if live < 4:
                try:
                    acquire_free_proxies(targets, countries=countries)
                except Exception as e:
                    log.warning("darmowe proxy: odświeżanie nie powiodło się: %s", short_err(e))
    threading.Thread(target=loop, daemon=True, name="free-proxy-refresh").start()


def proxy_for(netloc):
    """Proxy tylko dla sklepów z use_proxy (oszczędza transfer) albo dla wszystkich przy SCRAPER_PROXY_ALL=1."""
    return pick_proxy() if (PROXY_ALL or netloc in _proxy_hosts) else None


def proxy_kw(px):
    """Przygotowuje argumenty proxy dla curl_cffi z jawnym uwierzytelnianiem Iploop."""
    if not px:
        return {}
    # Iploop wymaga loginu "iploop" i klucza API jako hasła.
    # Wyciągamy klucz z adresu URL (część po "iploop:" i przed "@").
    match = re.search(r"://(?:iploop:)?([^@]+)@", px)
    api_key = match.group(1) if match else px
    return {
        "proxy": "http://proxy.iploop.io:8880",
        "proxy_auth": ("iploop", api_key),
    }


def allowed(url):
    host = "{0.scheme}://{0.netloc}".format(urlparse(url))
    nl = urlparse(url).netloc
    with _lock:
        if host not in _robots:
            rp, reason, net_fail = None, "brak odpowiedzi", False
            via_proxy = bool(_proxies) and (PROXY_ALL or nl in _proxy_hosts)
            attempts = min(10, max(3, _live_count() + 1)) if via_proxy else 3
            for _ in range(attempts):
                px = proxy_for(nl)
                try:
                    r = session().get(host + "/robots.txt", timeout=15, **proxy_kw(px))
                except requests.RequestException as e:
                    report_proxy(px, False)
                    reason, net_fail = short_err(e), True
                    continue
                report_proxy(px, True)
                net_fail = False
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
            if reason:
                note = f"robots.txt niedostępny ({reason})"
                _robots_note[nl] = note
                if net_fail:
                    # to błąd sieci/proxy, a nie decyzja sklepu: nie zapamiętujemy zakazu,
                    # kolejna kategoria spróbuje jeszcze raz (inne proxy)
                    log.warning("%s: %s - ta kategoria pominięta", host, note)
                    return False
                log.warning("%s: %s - pomijam ten host w tym przebiegu", host, note)
                rp = RobotFileParser()
                rp.disallow_all = True
            _robots[host] = rp
            cd = rp.crawl_delay(USER_AGENT) if rp else None
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
    if _proxies and (PROXY_ALL or host in _proxy_hosts):
        retries = max(retries, min(8, _live_count() + 1))  # kolejne próby = kolejne proxy
    for attempt in range(retries):
        throttle(host)
        px = None
        try:
            px = proxy_for(host)
            if px in _free_proxies and not url.startswith("https://"):
                _tls.last_fail = "adres HTTP nie przez darmowe proxy"  # po HTTP proxy widziałoby i mogło zmienić treść
                bump("nieudane")
                return None
            with _host_sem.get(host) or contextlib.nullcontext():
                r = session().get(url, timeout=(10, 20) if px else 25, cookies=cookies, headers=headers, **proxy_kw(px))
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
            last_err = short_err(e)
            proxied = px is not None
            log.warning("błąd sieci przez %s (próba %d/%d): %s | %s", mask(px), attempt + 1, retries, url, last_err)
            if proxied:
                continue
        time.sleep(2 ** attempt)
    bump("nieudane")
    _tls.last_fail = f"nieudane po {retries} próbach ({last_err})"
    return None


# ----------------------------- sitemap --------------------------------------
SITEMAP_FALLBACKS = ("/sitemap.xml", "/sitemap_index.xml", "/wp-sitemap.xml", "/sitemap-index.xml",
                     "/sitemap/sitemap_index.xml", "/sitemap/sitemap.xml", "/sitemaps/sitemap.xml",
                     "/product-sitemap.xml", "/sitemap_products_1.xml")
_ASSET_RE = re.compile(r"\.(?:jpe?g|png|gif|webp|svg|ico|pdf|mp4|webm|css|js|zip|xml)(?:\?|$)", re.I)


def read_xml(url, headers=None):
    r = get(url, headers=headers)
    if not r:
        return None
    data = r.content
    # Sprawdzaj nagłówek gzip, a nie tylko końcówkę adresu
    if data[:2] == b"\x1f\x8b":
        try:
            data = gzip.decompress(data)
            log.debug("  dekompresja gzip: %s", url)
        except OSError:
            log.warning("  nie udało się zdekompresować gzip: %s", url)
            return None
    try:
        return ET.fromstring(data)
    except ET.ParseError:
        return None


def _is_loc(tag):
    """<loc> ze standardowej przestrzeni sitemap; pomija <image:loc>, <video:loc> itp."""
    return tag == "loc" or (tag.endswith("}loc") and "sitemaps.org" in tag)


def _walk_sitemaps(roots, site, hdrs, info):
    seen, out, stack = set(), [], list(reversed(roots))
    flt = site.get("sitemap_filter")
    while stack and len(seen) < 10000:  # zwiększony limit
        sm = stack.pop()
        if sm in seen:
            continue
        seen.add(sm)
        tree = read_xml(sm, hdrs)
        if tree is None:
            log.warning("  sitemapa niedostępna lub nieczytelna: %s (%s)", sm, getattr(_tls, "last_fail", "?"))
            info["failed"].append(sm)
            continue
        # Buduj pełne adresy URL, nawet jeśli w XML-u są względne
        locs = [urljoin(sm, el.text.strip()) for el in tree.iter() if _is_loc(el.tag) and el.text]
        if "sitemapindex" in tree.tag:
            kids = [u for u in locs if not flt or re.search(flt, u)]
            stack.extend(reversed(kids))
            info["children"] += len(kids)
            log.info("  indeks sitemap %s: %d podsitemap", sm, len(kids))
        else:
            pages = [u for u in locs if not _ASSET_RE.search(u)]
            out.extend(pages)
            log.info("  sitemapa %s: %d adresów", sm, len(pages))
    info["sitemaps"] += len(seen)
    return out


def sitemap_urls(site, info=None, name=""):
    """Adresy stron z sitemap sklepu: robots.txt (Sitemap:), a gdy brak - typowe lokalizacje."""
    info = info if info is not None else {}
    info.update({"sitemaps": 0, "children": 0, "failed": [], "tried": []})
    hdrs = site_headers(name, site) if name else None
    base = site["base"].rstrip("/")
    roots = list(site.get("sitemaps", []))
    if not roots:
        r = get(base + "/robots.txt", headers=hdrs)
        if r:
            roots = re.findall(r"(?im)^sitemap:\s*(\S+)", r.text)
    if roots:
        info["tried"] = roots
        out = _walk_sitemaps(roots, site, hdrs, info)
    else:
        out = []
        for path in SITEMAP_FALLBACKS:
            info["tried"].append(base + path)
            out = _walk_sitemaps([base + path], site, hdrs, info)
            if out:
                log.info("  sitemapa znaleziona pod %s (brak wpisu Sitemap w robots.txt)", base + path)
                break
    info["total"] = len(set(out))
    pattern = site.get("url_regex")
    if pattern:
        before = len(out)
        out = [u for u in out if re.search(pattern, u)]
        log.info("  filtr url_regex: %d -> %d adresów", before, len(out))
    return list(dict.fromkeys(out))


# ----------------------------- parsowanie -----------------------------------
# Cena w dowolnym zapisie. Kolejność alternatyw ma znaczenie:
#  1) liczba z grupami tysięcy (spacja / kropka / przecinek + dokładnie 3 cyfry) i opcjonalnymi groszami 1-2 cyfry
#  2) zwykła liczba z opcjonalnymi groszami
_PRICE_RE = re.compile(
    r"(?<![\d.,])(?:[1-9]\d{0,2}(?:[ \u00a0\u202f.,]\d{3})+(?:[.,]\d{1,2})?|\d+(?:[.,]\d{1,2})?)(?!\d)")


def parse_price(text):
    """Cena z tekstu: 1 299,00 | 1.299,00 | 1,299.00 | 1299.00 | 1,612.00 zł | 49,9 | 1299. None gdy brak ceny albo <= 0."""
    if text is None:
        return None
    if isinstance(text, (int, float)):
        v = float(text)
    else:
        m = _PRICE_RE.search(str(text))
        if not m:
            return None
        tok = m.group(0)
        dec = re.search(r"[.,](\d{1,2})$", tok)  # ostatni separator + 1-2 cyfry = grosze
        whole, frac = (tok[:dec.start()], dec.group(1)) if dec else (tok, "")
        whole = re.sub(r"[ \u00a0\u202f.,]", "", whole)
        v = float(f"{whole}.{frac or '0'}")
    return v if 0 < v < 1_000_000 else None


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
    """Węzły Product (bez wchodzenia w środek Product) oraz informacja, czy w danych jest lista ItemList."""
    if isinstance(node, list):
        for x in node:
            yield from walk_jsonld(x)
    elif isinstance(node, dict):
        t = node.get("@type")
        types = t if isinstance(t, list) else [t]
        if "Product" in types:
            yield node
            return  # produkty powiązane/warianty w środku nie liczą się jako osobne produkty strony
        if "ItemList" in types:
            yield {"@type": "ItemList", "n": len(node.get("itemListElement") or [])}
        for v in node.values():
            if isinstance(v, (list, dict)):
                yield from walk_jsonld(v)


def from_jsonld(soup):
    prods, has_list = [], False
    for tag in soup.find_all("script", type="application/ld+json"):
        try:
            data = json.loads(tag.string or tag.get_text() or "")
        except json.JSONDecodeError:
            continue
        for node in walk_jsonld(data):
            if node.get("@type") == "ItemList":
                has_list = has_list or node.get("n", 0) >= 3
            else:
                prods.append(node)
    # strona kategorii/listy: wiele Product w ItemList - to nie jest strona jednego produktu
    if not prods or (len(prods) >= 3 and has_list) or len(prods) >= 8:
        return None
    prod = prods[0]
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
        "code_raw": prod.get("mpn"),  # kod producenta; SKU sklepu celowo pomijamy
        "price": parse_price(price),
        "currency": offers.get("priceCurrency") or "PLN",
        "availability": norm_availability(offers.get("availability")),
    }


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


# ----------------------------- kody produktów -------------------------------
# Kod = oznaczenie producenta/modelu (np. PXO310, TB118, PF-2/R). Wyciągamy go z nazwy, adresu, jawnych
# oznaczeń ("Kod: ...") i opcjonalnego selektora sklepu. Śmieci typu "20 strzałów", "25mm", "36s",
# "2x36", "F2", "T1", "1.4G", "CE1234" są odrzucane. Lepiej nie mieć kodu niż mieć zły.
_UNITS = (r"MM|CM|M|G|KG|ML|L|SZT|S|SEK|SEC|MIN|H|X|V|W|HZ|PCS|SHOT|SHOTS|STRZ\w*|STRZAL\w*|ST|K|CAL|CALI|CALA|CALE|"
          r"INCH|PLN|ZL|LAT|KAL|KALIBER|KULI|KULA|KUL")
_UNIT_RE = re.compile(rf"^\d+(?:X\d+)*(?:{_UNITS})?$")           # 36S, 25MM, 2X36, 5X20MM, 14G
_UNIT_LEAD_RE = re.compile(rf"^(?:X)\d+(?:{_UNITS})?$")           # X36
_BLACK_RE = re.compile(r"^(?:F[1-4]|T[12]|P[12]|KAT\d|3D|4K|2K|HD|XL{1,2}|XS|RGB\d*|USB\d*|LED\d*|"
                       r"(?:CE|UN|EN|EAN|ISO|PN|DIN)\d*)$")
_MARK_RE = re.compile(r"(?:kod(?:\s+produktu)?|nr\s*kat(?:alogowy)?\.?|numer\s+katalogowy|symbol|indeks|sku|"
                      r"art(?:ykuł)?\.?|ref\.?|model)\s*[:#]?\s*([A-Za-z0-9][A-Za-z0-9\-_/.]{2,20})", re.I)
_SLUG_CODE_RE = re.compile(r"^[a-z]{2,5}\d{2,6}[a-z]{0,2}$")


def _fold(text):
    """Wielkie litery bez polskich znaków - wspólna normalizacja dla kodów i wyszukiwania."""
    text = (text or "").upper().replace("Ł", "L")
    text = unicodedata.normalize("NFKD", text)
    return "".join(c for c in text if not unicodedata.combining(c))


def _code_candidate(token, marker=False, trusted=False, slug=False):
    """(wyświetlany, klucz, punkty) albo None. trusted = jawne źródło (kod z selektora/JSON-LD)."""
    disp = token.strip(" \t.,;:()[]{}<>\"'!?*+")
    if not 3 <= len(disp) <= 18 or not re.fullmatch(r"[\w][\w\-_/.]*[\w]", disp, re.U):
        return None
    key = re.sub(r"[^0-9A-Z]", "", _fold(disp))
    if not 3 <= len(key) <= 16 or not any(c.isdigit() for c in key):
        return None
    if _UNIT_RE.match(key) and not key.isdigit() or _UNIT_LEAD_RE.match(key) or _BLACK_RE.match(key):
        return None
    letters, digits = sum(c.isalpha() for c in key), sum(c.isdigit() for c in key)
    if letters == 0:  # same cyfry: tylko jawny kod (>=4 cyfry) albo długi numer (EAN itp.), nie rok
        if not ((marker or trusted) and len(key) >= 4) and len(key) < 8:
            return None
        if re.fullmatch(r"(?:19|20)\d\d", key):
            return None
    elif not (marker or trusted or slug):
        # z samej nazwy tylko tokeny "wyglądające jak kod": bez małych liter albo ze znakami łączącymi
        if any(c.islower() for c in disp) and not re.search(r"[-_/]", disp):
            return None
    score = 1
    if letters >= 2 and digits >= 2:
        score += 2
    elif letters >= 1 and digits >= 2:
        score += 1
    if 4 <= len(key) <= 12:
        score += 1
    if letters and not any(c.islower() for c in disp):
        score += 1
    if letters and digits and re.search(r"[-_/]", disp):
        score += 1
    if marker:
        score += 4
    if trusted:
        score += 2
    return disp.upper(), key, score


def extract_code(name, url=None, hint=None, sku=None, min_score=4):
    """Zwraca (kod, klucz) albo (None, None). klucz = same wielkie litery i cyfry (do łączenia między sklepami)."""
    cands = []
    if sku:
        c = _code_candidate(str(sku), trusted=True)
        if c:
            cands.append(c)
    text = " ".join(x for x in (name, hint) if x)
    for m in _MARK_RE.finditer(text):
        c = _code_candidate(m.group(1), marker=True)
        if c:
            cands.append(c)
    for tok in re.split(r"[\s,;()\[\]{}|]+", name or ""):
        c = _code_candidate(tok) if tok else None
        if c:
            cands.append(c)
    if url:
        seg = urlparse(url).path.rstrip("/").rsplit("/", 1)[-1]
        seg = re.sub(r"\.(?:html?|php)$", "", seg.lower())
        for tok in re.split(r"[-_+]", seg):
            if _SLUG_CODE_RE.match(tok):
                c = _code_candidate(tok, slug=True)
                if c:
                    cands.append(c)
    cands = [c for c in cands if c[2] >= min_score]
    if not cands:
        return None, None
    best = max(cands, key=lambda c: c[2])  # remis: pierwszy znaleziony
    return best[0], best[1]


# ----------------------------- baza -----------------------------------------
PARSER_VERSION = 2  # zwiększ, gdy zmienia się sposób czytania cen: historia cen jest wtedy archiwizowana i liczona od nowa


def db():
    con = sqlite3.connect(DB_PATH)
    con.executescript("""
    CREATE TABLE IF NOT EXISTS products(
      url TEXT PRIMARY KEY, site TEXT, name TEXT, code TEXT, code_key TEXT,
      first_seen TEXT, last_seen TEXT);
    CREATE TABLE IF NOT EXISTS prices(
      id INTEGER PRIMARY KEY AUTOINCREMENT, url TEXT, ts TEXT,
      price REAL, currency TEXT, availability TEXT);
    CREATE INDEX IF NOT EXISTS ix_prices_url ON prices(url, ts);
    CREATE TABLE IF NOT EXISTS nonproduct(url TEXT PRIMARY KEY, ts TEXT);
    """)
    cols = {r[1] for r in con.execute("PRAGMA table_info(products)")}
    if "code" not in cols:  # migracja starej bazy (kolumna sku) -> kody produktów
        con.execute("ALTER TABLE products ADD COLUMN code TEXT")
        con.execute("ALTER TABLE products ADD COLUMN code_key TEXT")
        rows = con.execute("SELECT url, name FROM products").fetchall()
        for url, name in rows:  # stary SKU sklepu ignorujemy - kody liczymy z nazwy i adresu
            code, key = extract_code(name, url)
            con.execute("UPDATE products SET code=?, code_key=? WHERE url=?", (code, key, url))
        log.info("migracja bazy: dodano kody produktów (%d produktów)", len(rows))
    if "sku" in cols:
        try:
            con.execute("ALTER TABLE products DROP COLUMN sku")
        except sqlite3.OperationalError:
            pass  # starszy SQLite: kolumna zostaje nieużywana
    con.execute("CREATE INDEX IF NOT EXISTS ix_products_code ON products(code_key)")
    con.execute("CREATE TABLE IF NOT EXISTS meta(k TEXT PRIMARY KEY, v TEXT)")
    row = con.execute("SELECT v FROM meta WHERE k = 'parser_version'").fetchone()
    if not row or int(row[0]) < PARSER_VERSION:
        n = con.execute("SELECT COUNT(*) FROM prices").fetchone()[0]
        if n:  # ceny z poprzedniego parsera mogły być błędne (np. 1 zł zamiast 1612 zł) - nie mieszamy ich z nowymi
            con.execute("DROP TABLE IF EXISTS prices_backup")
            con.execute("DROP INDEX IF EXISTS ix_prices_url")
            con.execute("ALTER TABLE prices RENAME TO prices_backup")
            con.execute("""CREATE TABLE prices(id INTEGER PRIMARY KEY AUTOINCREMENT, url TEXT, ts TEXT,
                           price REAL, currency TEXT, availability TEXT)""")
            con.execute("CREATE INDEX ix_prices_url ON prices(url, ts)")
            log.warning("zmiana parsera cen: historia (%d wpisów) przeniesiona do tabeli prices_backup, "
                        "ceny liczone od nowa", n)
        con.execute("INSERT OR REPLACE INTO meta(k, v) VALUES('parser_version', ?)", (str(PARSER_VERSION),))
    con.commit()
    return con


_suspicious = []  # (url, stara cena, nowa cena) - skoki >= 5x, zwykle znak błędu parsera cen


def save(con, site_name, url, d):
    now = datetime.now(timezone.utc).isoformat(timespec="seconds")
    code, key = extract_code(d["name"], url, d.get("hint"), d.get("code_raw"))
    con.execute("""INSERT INTO products(url,site,name,code,code_key,first_seen,last_seen)
                   VALUES(?,?,?,?,?,?,?)
                   ON CONFLICT(url) DO UPDATE SET name=excluded.name, code=excluded.code,
                   code_key=excluded.code_key, last_seen=excluded.last_seen""",
                (url, site_name, d["name"], code, key, now, now))
    last = con.execute("SELECT price, availability FROM prices WHERE url=? "
                       "ORDER BY id DESC LIMIT 1", (url,)).fetchone()
    cur = (d["price"], d.get("availability"))
    if last and last[0] and d["price"] and (d["price"] / last[0] >= 5 or d["price"] / last[0] <= 0.2):
        _suspicious.append((url, last[0], d["price"]))
        if len(_suspicious) <= 25:
            log.warning("PODEJRZANA ZMIANA CENY %.2f -> %.2f | %s | %s", last[0], d["price"], d["name"], url)
    if last != cur:
        con.execute("INSERT INTO prices(url,ts,price,currency,availability) VALUES(?,?,?,?,?)",
                    (url, now, d["price"], d.get("currency", "PLN"), d.get("availability")))
        return True
    return False


# ----------------------------- komendy --------------------------------------
def report_problems(problems, label):
    """problems: lista (sklep, miejsce, powód). Grupuje takie same powody i zapisuje też w podsumowaniu przebiegu
    (na telefonie to jedna strona zamiast przewijania logu)."""
    if not problems:
        return
    groups = {}
    for n, where, reason in problems:
        g = groups.setdefault((n, re.sub(r"\d+", "#", reason)[:90]), [0, where, reason])
        g[0] += 1
    log.warning("PROBLEMY (%s) - wyszukaj w logu: PROBLEM", label)
    lines = []
    for (n, _), (cnt, where, reason) in groups.items():
        txt = f"[{n}] x{cnt}: {reason}" + (f" | np. {where}" if where else "")
        log.warning("PROBLEM %s", txt)
        lines.append(txt)
    path = os.environ.get("GITHUB_STEP_SUMMARY")
    if path:
        with open(path, "a", encoding="utf-8") as f:
            f.write(f"\n### Problemy ({label})\n" + "".join(f"- {l}\n" for l in lines))


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
        raw_text = tile.get_text(" ", strip=True)
        text = raw_text.lower()
        out = False
        if cfg.get("in_stock") and not has(tile, cfg["in_stock"]):
            out = True  # brak elementu "dostępny" (np. przycisku koszyka)
        if cfg.get("out_of_stock") and has(tile, cfg["out_of_stock"]):
            out = True
        if any(t.lower() in text for t in cfg.get("out_text", [])):
            out = True
        products.append({
            "name": name.strip(), "currency": "PLN",
            "hint": raw_text[:400], "code_raw": _pick(tile, cfg.get("code")),
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
    m = re.search(rb"<title[^>]*>(.*?)</title>", r.content, re.I | re.S)
    title = re.sub(r"\s+", " ", m.group(1).decode("utf-8", "replace")).strip()[:80] if m else "?"
    hdr = r.headers
    guard = "Cloudflare" if ("cf-ray" in hdr or "cloudflare" in hdr.get("server", "").lower()) else hdr.get("server", "?")
    return f"HTTP {r.status_code}, {len(r.content)} B, title={title!r}, serwer/ochrona={guard}"


def _esc(c):
    try:
        return sv.escape(c)
    except Exception:
        return c


def _sig(t):
    return t.name + "".join("." + _esc(c) for c in (t.get("class") or [])[:3])


def outline(tile, limit=12):
    """Zarys kafelka: tagi/klasy elementów z tekstem, linkiem, alt albo data-price (pod konfigurację selektorów)."""
    parts = []
    for el in [tile] + tile.find_all(True):
        bits, info = _sig(el), False
        if el.get("href"):
            bits, info = bits + "[href]", True
        if el.get("alt"):
            bits, info = bits + f"[alt={el['alt'][:25]!r}]", True
        if el.get("data-price"):
            bits, info = bits + f"[data-price={el['data-price']}]", True
        own = " ".join("".join(el.find_all(string=True, recursive=False)).split())
        if len(own) >= 3:
            bits, info = bits + f" {own[:30]!r}", True
        if el is tile or info:
            parts.append(bits)
        if len(parts) >= limit:
            break
    return " > ".join(parts)


def pagination_hint(content):
    """Jak strona wskazuje kolejne strony: <link rel=next> albo link o tekście '2'."""
    try:
        soup = BeautifulSoup(content, "lxml")
        out = []
        ln = soup.find("link", attrs={"rel": "next"})
        if ln is not None and ln.get("href"):
            out.append("rel=next -> " + ln["href"][:120])
        for a in soup.find_all("a", href=True):
            if a.get_text(strip=True) == "2" and a["href"].strip() not in ("", "#"):
                out.append('link "2" -> ' + a["href"][:120])
                break
        return "; ".join(out)
    except Exception:
        return ""


def suggest_selectors(content):
    """Gdy selektor 'item' nic nie znajduje: zgaduje kafelek (powtarzający się element z ceną) i pokazuje
    jego zarys, żeby dało się poprawić konfigurację bez wklejania całego HTML."""
    try:
        soup = BeautifulSoup(content, "lxml")
        price_re = re.compile(r"\d[\d\s.]*[,.]\d{2}(?:\s*(?:zł|pln))?", re.I)
        cands, first = Counter(), {}
        for text in soup.find_all(string=price_re):
            node = cur = text.parent
            if node is None or node.name in ("script", "style"):
                continue
            for _ in range(8):
                par = cur.parent
                if par is None or par.name in ("body", "html", "[document]"):
                    break
                if sum(1 for c in par.find_all(recursive=False) if c.name == cur.name and _sig(c) == _sig(cur)) >= 3:
                    key = _sig(cur)
                    first.setdefault(key, cur)
                    cands[key] += 1
                    break
                cur = par
        if not cands:
            return "brak powtarzalnych kafelków z ceną w HTML (produkty mogą się ładować przez JavaScript)"
        return " || ".join(f"item={k} ({n}x) kafelek: {outline(first[k])}" for k, n in cands.most_common(3))[:1500]
    except Exception as e:  # diagnostyka nie może psuć scrapowania
        return f"nie udało się zanalizować ({e})"


_NEXT_TEXTS = {"»", "›", ">", "→", "następna", "następny", "następna strona", "dalej", "kolejna", "next", "nast.", "nast"}


def find_next_link(content, cur_url, ordinal):
    """Adres następnej strony listy: <link/a rel=next>, link o numerze ordinal+1 albo 'Następna'/'»'."""
    try:
        soup = BeautifulSoup(content, "lxml")
        cands = []
        ln = soup.find("link", attrs={"rel": "next"}) or soup.find("a", attrs={"rel": "next"})
        if ln is not None and ln.get("href"):
            cands.append(ln["href"])
        anchors = soup.find_all("a", href=True)
        cands += [a["href"] for a in anchors if a.get_text(strip=True) == str(ordinal + 1)]
        cands += [a["href"] for a in anchors if a.get_text(strip=True).lower() in _NEXT_TEXTS]
        for href in cands:
            href = href.strip()
            if not href or href.startswith(("#", "javascript:")):
                continue
            absu = urljoin(cur_url, href)
            if absu.split("#")[0] != cur_url.split("#")[0]:
                return absu
    except Exception:
        pass
    return None


def listing_category(name, site, cfg, cat_url, q, stats):
    """Wątek roboczy: przechodzi strony jednej kategorii i wrzuca produkty do kolejki."""
    start = cfg.get("start", 1)
    nxt = cfg.get("next", "{url}?page={page}")
    first = cfg.get("first")
    max_pages = cfg.get("max_pages", 400)
    hdrs = site_headers(name, site)
    seen, page, total, reason, last_r = set(), start, 0, None, None
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
            last_r = r
            n_tiles, items = parse_listing(r.content, url, cfg)
            new, on_page = [], set()
            for it in items:
                if it["url"] not in seen and it["url"] not in on_page:
                    new.append(it)
                    on_page.add(it["url"])
            if page == start and n_tiles == 0:
                reason = ("0 kafelków: " + diag(r) + " | podpowiedź: " + suggest_selectors(r.content)
                          + " | paginacja: " + (pagination_hint(r.content) or "?"))
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
        # szablon adresu stron nie zadziałał (1 strona), ale strona wskazuje kolejne: idziemy za linkami
        if total and page - start == 1 and last_r is not None:
            visited, cur, ordinal, extra = {last_r.url}, last_r, 1, 0
            while ordinal < max_pages:
                nxt_url = find_next_link(cur.content, cur.url, ordinal)
                if not nxt_url or nxt_url in visited:
                    break
                visited.add(nxt_url)
                r = get(nxt_url, stats, cookies=site.get("cookies"), headers=hdrs)
                if not r:
                    break
                n_tiles, items = parse_listing(r.content, nxt_url, cfg)
                new = [it for it in dict((it["url"], it) for it in items).values() if it["url"] not in seen]
                if not new:
                    break
                seen.update(it["url"] for it in new)
                total += len(new)
                q.put(("items", name, cat_url, start + ordinal, new))
                ordinal, extra, cur = ordinal + 1, extra + 1, r
            if extra:
                page = start + ordinal
                log.info("[%s] paginacja przez linki 'następna strona' (szablon adresu nie działał): +%d stron w %s",
                         name, extra, cat_url.rstrip("/").rsplit("/", 1)[-1])
    except Exception as e:  # nigdy nie wieszamy głównego wątku
        reason = f"wyjątek: {e}"
        log.warning("[%s] błąd w kategorii %s: %s", name, cat_url, e)
    finally:
        if not reason and last_r is not None and total and page - start == 1:
            ph = pagination_hint(last_r.content)
            if ph:  # strona wskazuje kolejne strony, a my skończyliśmy po jednej: zły parametr paginacji?
                reason = f"UWAGA tylko 1 strona ({total} prod.), ale strona wskazuje kolejne: {ph}"
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
                    if d["availability"] == "out_of_stock":
                        st["niedostepne"] += 1  # kontrola: 0 niedostępnych przy setkach produktów = zły selektor dostępności
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
    report_problems([(n, cat, reason) for n in names for cat, reason in problems[n]], "listing")
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


def url_group(url):
    """Grupa adresów (pierwszy człon ścieżki, cyfry -> #; prefiks języka /pl/ + drugi człon)."""
    segs = [x for x in urlparse(url).path.split("/") if x]
    if not segs:
        return "/"
    g = re.sub(r"\d+", "#", segs[0].lower())
    if re.fullmatch(r"[a-z]{2}", segs[0].lower()) and len(segs) > 1:
        g += "/" + re.sub(r"\d+", "#", segs[1].lower())
    return g[:40]


def page_brief(content):
    """Krótki opis strony bez produktu: tytuł i czy są dane JSON-LD (do diagnozy w logu)."""
    m = re.search(rb"<title[^>]*>(.*?)</title>", content, re.I | re.S)
    title = re.sub(r"\s+", " ", m.group(1).decode("utf-8", "replace")).strip()[:70] if m else "?"
    has_ld = b"application/ld+json" in content
    has_prod = b'"Product"' in content
    return f"title={title!r}, JSON-LD={'tak' if has_ld else 'nie'}, Product w JSON-LD={'tak' if has_prod else 'nie'}"


def fetch_one(url, site, stats, hdrs=None, skip=None):
    """Praca wątku roboczego: pobierz + sparsuj. Zwraca (url, dane, status, opis, grupa)."""
    grp = url_group(url)
    if skip is not None and grp in skip:
        return url, None, "skipped", "", grp
    _tls.last_fail = "?"
    r = get(url, stats, cookies=site.get("cookies"), headers=hdrs)
    if not r:
        return url, None, "fetch", _tls.last_fail, grp
    try:
        d = extract(r.content, site)
    except Exception as e:
        return url, None, "parse", f"{e.__class__.__name__}: {e}"[:100], grp
    if d:
        return url, d, "ok", "", grp
    return url, None, "nonproduct", page_brief(r.content), grp


GROUP_SKIP_AFTER = 40  # tyle stron z grupy bez ani jednego produktu = reszta grupy pomijana w tym przebiegu


def sitemap_driver(name, site, known_np, args, q):
    """Wątek sklepu: sitemapa -> lista adresów -> równoległe pobieranie; wyniki trafiają do kolejki."""
    hdrs = site_headers(name, site)
    gets, skip, gstat = Counter(), set(), {}
    try:
        info = {}
        urls = sitemap_urls(site, info, name)
        total = len(urls)
        urls = [u for u in urls if u not in known_np]
        info["cached"] = total - len(urls)
        if args.max:
            urls = urls[: args.max]
        q.put(("plan", name, len(urls), info, gets))
        pool = ThreadPoolExecutor(max_workers=args.workers)
        try:
            for url, d, status, brief, grp in pool.map(lambda u: fetch_one(u, site, gets, hdrs, skip), urls):
                gs = gstat.setdefault(grp, [0, 0])
                if status == "ok":
                    gs[0] += 1
                elif status == "nonproduct":
                    gs[1] += 1
                if gs[0] == 0 and gs[1] >= GROUP_SKIP_AFTER and grp not in skip:
                    skip.add(grp)
                    q.put(("skipgrp", name, grp))
                q.put(("res", name, url, d, status, brief, grp))
        finally:
            pool.shutdown(wait=False, cancel_futures=True)
    except Exception as e:  # jeden sklep nie może zatrzymać reszty
        q.put(("error", name, f"{e.__class__.__name__}: {str(e)[:150]}"))
    finally:
        q.put(("done", name, gstat))


def run_sitemap(con, names, args):
    """Wszystkie sklepy naraz: sitemapa -> strony produktów (JSON-LD). Zapis do bazy w jednym wątku."""
    t0 = time.time()
    known = set()
    if not args.recheck:
        cutoff = (datetime.now(timezone.utc) - timedelta(days=NONPRODUCT_TTL_DAYS)).isoformat(timespec="seconds")
        known = {u for (u,) in con.execute("SELECT url FROM nonproduct WHERE ts > ?", (cutoff,))}
    q = queue.Queue()
    log.info("TRYB SITEMAP: %d sklepów, wątki na sklep: %d, odstęp: %.2fs, znanych nie-produktów w cache: %d",
             len(names), args.workers, DELAY, len(known))
    shops = ThreadPoolExecutor(max_workers=max(len(names), 1))
    for n in names:
        shops.submit(sitemap_driver, n, SITES[n], known, args, q)
    st = {n: Counter() for n in names}
    gets = {n: Counter() for n in names}
    plan, started = {}, {n: time.time() for n in names}
    prods = {n: [] for n in names}
    nps = {n: [] for n in names}
    seen_np = Counter()
    fails = {n: Counter() for n in names}
    problems, finished = [], set()
    pending, last_beat, nres = len(names), time.time(), 0

    def finish(n, gstat):
        merged = Counter(st[n])
        merged.update(gets[n])
        checked, prod = st[n]["sprawdzone"], st[n]["produkty"]
        top = sorted(gstat.items(), key=lambda kv: -(kv[1][0] + kv[1][1]))[:6]
        log.info("[%s] KONIEC w %s | %s", n, fmt_dur(time.time() - started[n]),
                 ", ".join(f"{k}={v}" for k, v in sorted(merged.items())) or "brak danych")
        if top:
            log.info("[%s] grupy adresów (produkty/nie-produkty): %s", n, ", ".join(f"{g}: {a}/{b}" for g, (a, b) in top))
        if prods[n]:
            log.info("[%s] przykładowe produkty: %s", n, " | ".join(prods[n]))
        if checked and prod == 0:
            msg = f"0 produktów ze {checked} sprawdzonych stron"
            if fails[n]:
                msg += "; błędy pobierania: " + ", ".join(f"{k} x{v}" for k, v in fails[n].most_common(3))
            if nps[n]:
                msg += f" | przykład strony bez produktu: {nps[n][0][0]} ({nps[n][0][1]})"
            problems.append((n, msg))
        elif checked >= 30 and prod < 0.3 * checked:
            problems.append((n, f"tylko {prod} produktów na {checked} sprawdzonych stron - warto ustawić url_regex; "
                                f"grupy (produkty/nie): " + ", ".join(f"{g}: {a}/{b}" for g, (a, b) in top)))
        finished.add(n)

    try:
        while pending:
            try:
                msg = q.get(timeout=5)
            except queue.Empty:
                msg = None
            if msg:
                kind, n = msg[0], msg[1]
                if kind == "plan":
                    _, _, count, info, g = msg
                    plan[n], gets[n], started[n] = count, g, time.time()
                    log.info("[%s] sitemapy: %d (indeksy: %d) | adresów: %d, w cache nie-produktów: %d, do sprawdzenia: %d",
                             n, info["sitemaps"], info["children"], info["total"], info["cached"], count)
                    if info["total"] == 0:
                        extra = f"; nieczytelne: {len(info['failed'])}" if info["failed"] else ""
                        problems.append((n, "brak adresów w sitemapie; sprawdzone: " + (", ".join(info["tried"][:5]) or "-") + extra))
                elif kind == "res":
                    _, _, url, d, status, brief, grp = msg
                    nres += 1
                    s_ = st[n]
                    s_["sprawdzone"] += 1
                    if status == "ok":
                        s_["produkty"] += 1
                        if d.get("price") is None:
                            s_["bez_ceny"] += 1
                        if d.get("availability") == "out_of_stock":
                            s_["niedostepne"] += 1
                        if save(con, n, url, d):
                            s_["zmiany_w_historii"] += 1
                            log.debug("zapisano: %s | %s | %s", d["name"], d["price"], d.get("availability"))
                        con.execute("DELETE FROM nonproduct WHERE url = ?", (url,))
                        if len(prods[n]) < 2:
                            prods[n].append(url)
                    elif status == "nonproduct":
                        s_["to_nie_produkt"] += 1
                        con.execute("INSERT OR REPLACE INTO nonproduct(url, ts) VALUES(?, ?)",
                                    (url, datetime.now(timezone.utc).isoformat(timespec="seconds")))
                        seen_np[n] += 1
                        if len(nps[n]) < 4:
                            nps[n].append((url, brief))
                        elif random.random() < 4 / seen_np[n]:
                            nps[n][random.randrange(4)] = (url, brief)
                    elif status == "skipped":
                        s_["pominiete_grupa"] += 1
                    elif status == "fetch":
                        s_["nieudane_strony"] += 1
                        fails[n][brief[:60] or "?"] += 1
                    elif status == "parse":
                        s_["blad_parsowania"] += 1
                        log.warning("[%s] błąd parsowania %s: %s", n, url, brief)
                    if nres % 200 == 0:
                        con.commit()
                elif kind == "skipgrp":
                    log.info("[%s] pomijam grupę adresów %r: %d stron bez żadnego produktu", n, msg[2], GROUP_SKIP_AFTER)
                elif kind == "error":
                    log.error("[%s] błąd sklepu: %s", n, msg[2])
                    problems.append((n, "błąd: " + msg[2]))
                elif kind == "done":
                    pending -= 1
                    finish(n, msg[2])
            if time.time() - last_beat >= 20:
                last_beat = time.time()
                for n in names:
                    if n in finished or n not in plan:
                        continue
                    i, total = st[n]["sprawdzone"], plan[n]
                    el = time.time() - started[n]
                    rate = i / el if el else 0
                    eta = (total - i) / rate if rate else 0
                    log.info("[%s] %d/%d (%.0f%%) | produkty: %d | zmiany: %d | nie-produkty: %d | pominięte: %d | błędy: %d | %.1f str/s | zostało ~%s",
                             n, i, total, 100 * i / max(total, 1), st[n]["produkty"], st[n]["zmiany_w_historii"],
                             st[n]["to_nie_produkt"], st[n]["pominiete_grupa"],
                             gets[n]["nieudane"] + st[n]["blad_parsowania"], rate, fmt_dur(eta))
    finally:
        shops.shutdown(wait=False, cancel_futures=True)
        con.commit()
    report_problems([(n, "", m_) for n, m_ in problems], "sitemap")
    log.info("TRYB SITEMAP zakończony w %s", fmt_dur(time.time() - t0))
    out = []
    for n in names:
        merged = Counter(st[n])
        merged.update(gets[n])
        out.append((n, st[n]["sprawdzone"], merged))
    return out


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
                _host_sem[h] = threading.Semaphore(int(site.get("max_parallel", 4)))  # proxy nie lubią 12 naraz
    if (env("SCRAPER_PROXY_SOURCE", "") or "").lower() == "geonode":
        targets = free_proxy_targets(names)
        if not targets:
            log.info("darmowe proxy: żaden z wybranych sklepów nie ma use_proxy - pomijam")
        else:
            countries = tuple(c.strip().upper() for c in (env("SCRAPER_PROXY_COUNTRY", "") or "").split(",") if c.strip())
            acquire_free_proxies(targets, countries=countries)
            start_free_refresher(targets, countries)
    if _proxies and not PROXY_ALL and not _proxy_hosts:
        log.warning("podano proxy, ale żaden wybrany sklep nie ma use_proxy (ustaw SCRAPER_PROXY_ALL=1, by użyć dla wszystkich)")
    in_actions = bool(os.environ.get("GITHUB_ACTIONS"))
    summary = []
    mode = (args.mode or "sitemap").lower()
    if mode not in ("sitemap", "listing", "auto"):
        raise SystemExit(f"Nieznany tryb {mode!r}: użyj sitemap, listing albo auto")
    listing_names, sitemap_names, auto_names = [], [], []
    for n in names:
        m_ = (SITES[n].get("mode") or mode).lower()  # "mode" w konfiguracji sklepu ma pierwszeństwo
        if m_ == "sitemap" or not SITES[n].get("listing"):
            sitemap_names.append(n)
        else:
            listing_names.append(n)
            if m_ == "auto":
                auto_names.append(n)
    forced = [n for n in names if SITES[n].get("mode")]
    log.info("tryb: %s | listing: %d sklepów, sitemap: %d sklepów%s", mode, len(listing_names), len(sitemap_names),
             f" | tryb ustawiony w konfiguracji sklepu: {', '.join(n + '=' + SITES[n]['mode'] for n in forced)}" if forced else "")
    if listing_names:
        if in_actions:
            print("::group::tryb listing", flush=True)
        res = run_listing(con, listing_names, args)
        if in_actions:
            print("::endgroup::", flush=True)
        if auto_names:  # sklepy w trybie auto, w których listing nic nie dał, przechodzą na sitemapę
            fallback = [n for (n, _pages, st_) in res if n in auto_names and st_["produkty"] == 0]
            if fallback:
                log.warning("tryb auto: listing nie dał produktów dla %s - przechodzę na sitemapę", ", ".join(fallback))
                res = [r for r in res if r[0] not in fallback]
                sitemap_names += fallback
        summary += res
    if sitemap_names:
        if in_actions:
            print("::group::tryb sitemap", flush=True)
        summary += run_sitemap(con, sitemap_names, args)
        if in_actions:
            print("::endgroup::", flush=True)

    if _suspicious:
        log.warning("PODEJRZANE ZMIANY CEN (skok >= 5x): %d szt. - jeśli to masowe, parser cen zawodzi dla jakiegoś sklepu",
                    len(_suspicious))
    log.info("===== PODSUMOWANIE =====")
    for name, n, st in summary:
        log.info("%-14s sprawdzone: %5d | produkty: %5d | zmiany: %5d | błędy: %d",
                 name, n, st["produkty"], st["zmiany_w_historii"],
                 st["nieudane"] + st["blad_parsowania"] + st["nieudane_strony"])
    path = os.environ.get("GITHUB_STEP_SUMMARY")
    if path:
        with open(path, "a", encoding="utf-8") as f:
            f.write("| sklep | sprawdzone | produkty | zmiany | błędy |\n|---|---|---|---|---|\n")
            for name, n, st in summary:
                f.write(f"| {name} | {n} | {st['produkty']} | {st['zmiany_w_historii']} | "
                        f"{st['nieudane'] + st['blad_parsowania'] + st['nieudane_strony']} |\n")


def cmd_export(args):
    con = db()
    rows = con.execute("""
      SELECT p.site, p.name, p.code, p.url, pr.price, pr.currency,
             pr.availability, pr.ts
      FROM products p JOIN prices pr ON pr.id =
        (SELECT MAX(id) FROM prices WHERE url = p.url)
      ORDER BY p.site, p.name""").fetchall()
    with open(args.path, "w", newline="", encoding="utf-8-sig") as f:
        w = csv.writer(f, delimiter=";")
        w.writerow(["sklep", "produkt", "kod", "link", "cena", "waluta", "dostepnosc", "zmiana_ts"])
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
    s.add_argument("--mode", default=env("SCRAPER_MODE", "sitemap"), help="sitemap (domyślnie) | listing | auto = listing, a gdy nic nie da - sitemapa; ENV: SCRAPER_MODE")
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
