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
    SCRAPER_ONLY=pirohit,lider   SCRAPER_MAX=2   SCRAPER_WORKERS=16   SCRAPER_DELAY=0.5
    SCRAPER_PROXY_SOURCE=geonode   darmowe proxy z Geonode, tylko dla sklepów z use_proxy (opcje: SCRAPER_PROXY_COUNTRY=PL,DE  SCRAPER_FREE_PROXY_COUNT=12)
    SCRAPER_MODE=auto|smart|sitemap|listing   SCRAPER_VERBOSE=1   SCRAPER_RECHECK=1   SCRAPER_PROXY_ALL=1   SCRAPER_DB=sciezka/do/bazy.db

Jak to działa (tryb sitemap; tryb listing czyta strony kategorii - patrz SITES):
  1. Adresy produktów bierze z sitemap.xml sklepu (robots.txt -> Sitemap:).
  2. Dane czyta z JSON-LD (schema.org Product/Offer), potem z meta tagów,
     a na końcu z selektorów CSS podanych w konfiguracji sklepu.
  3. Zapisuje do SQLite; nowy wpis w historii powstaje tylko gdy zmieni się
     cena lub dostępność.
  4. Szanuje robots.txt i robi odstępy między zapytaniami.

Uwagi o proxy:
  - Dla HTTPS: używane są TYLKO SOCKS5/SOCKS4 lub proxy z sekretów (zaufane).
    HTTP proxy z Proxifly/Geonode są odrzucane dla HTTPS (robią SSL MITM).
  - Proxifly: HTTPS -> SOCKS5 -> all, do 2000 adresów; trigger przy 403 (max raz/2min).
  - Bailout: 20 kolejnych fails przez proxy dla hosta -> direct (host nie lubi proxy).
"""
import argparse
import contextlib
import csv
import gzip
import html as htmllib
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
from urllib.parse import urlencode, urljoin, urlparse
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
USER_AGENT = "Mozilla/5.0 (compatible; FajerwerkiPrices/1.0" + (f"; +kontakt: {env('SCRAPER_CONTACT')}" if env("SCRAPER_CONTACT") else "") + ")"
DELAY = float(env('SCRAPER_DELAY', 0.5))   # min. odstęp (s) między ZAPYTANIAMI do jednego hosta (wspólny dla wszystkich wątków)
WORKERS = int(env('SCRAPER_WORKERS', 16))   # większy bufor żądań; DELAY nadal ogranicza tempo per host
BROWSER_UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) "
              "Chrome/124.0.0.0 Safari/537.36")
BROWSER_UA_SPEC = (env("SCRAPER_BROWSER_UA", "") or "").lower()  # "" = nikt, "1" = wszystkie, albo lista sklepów
NONPRODUCT_TTL_DAYS = 14  # tyle dni pamiętamy, że dany adres NIE jest produktem

# ---------------------------------------------------------------------------
# KONFIGURACJA SKLEPÓW – dodawaj kolejne wpisy.
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
    "odpalaj": {
        "base": "https://odpalaj.pl",
        "listing": {**_PRESTA, "categories": ["https://odpalaj.pl/pl/2-wszystko"],
            "item": "article.product-miniature",
            "name": "h2.product-title a", "link": "h2.product-title a@href", "price": "span.price",
            "out_of_stock": "ul.product-flags li.out_of_stock", "out_text": ["brak na stanie"]},
    },
    "pirohit": {
        "base": "https://pirohit.pl", "use_proxy": True,
        "mode": "listing",
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
        # item bez wd-loop-item-NNN (to ID produktu), name z .wd-entities-title, price z bdi
        "base": "https://pyroking.pl", "cookies": {"currency": "PLN"},
        "mode": "api",
        "store_api": {"endpoint": "https://pyroking.pl/wp-json/wc/store/v1/products"},
        "listing": {"next": "{url}page/{page}/", "start": 1,
            "item": "div.wd-product",
            "name": [".wd-entities-title a", "h3 a"],
            "link": ["a.wd-product-img-link@href", ".wd-entities-title a@href"],
            "price": ["bdi", "span.price ins .woocommerce-Price-amount", ".woocommerce-Price-amount"],
            "out_of_stock": ".outofstock",
            "categories": [
                "https://pyroking.pl/sklep/wyrzutnie-fajerwerkow/",
                "https://pyroking.pl/sklep/dymy/",
                "https://pyroking.pl/sklep/petardy/",
                "https://pyroking.pl/sklep/rakiety/",
                "https://pyroking.pl/sklep/stroboskopy-i-ognie-wroclawskie/",
                "https://pyroking.pl/sklep/wulkany-fontanny/",
                "https://pyroking.pl/sklep/flary/",
                "https://pyroking.pl/sklep/race/",
                "https://pyroking.pl/sklep/race-pistoletowe/",
                "https://pyroking.pl/sklep/emitery-dzwieku/",
                "https://pyroking.pl/sklep/odstraszacze-zwierzat-hukery/",
                "https://pyroking.pl/sklep/oprawa-meczowa-stadionowa/",
                "https://pyroking.pl/sklep/gatlingi/",
                "https://pyroking.pl/sklep/rzymskie-ognie/",
                "https://pyroking.pl/sklep/single-shoty/",
                "https://pyroking.pl/sklep/zimne-ognie/",
                "https://pyroking.pl/sklep/pyro-cartel/",
                "https://pyroking.pl/sklep/danger-hobby/",
                "https://pyroking.pl/sklep/pirotechnika-sceniczna-eventowa/",
                "https://pyroking.pl/sklep/systemy-zdalnego-odpalania-akcesoria/",
                "https://pyroking.pl/sklep/wielopaki/",
                "https://pyroking.pl/sklep/pirobajery/",
                "https://pyroking.pl/sklep/promocje/",
            ]},
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
        "mode": "sitemap",
        "delay": 0.35,          # było domyślne 0.5 = 2.5x szybciej
        "max_parallel": 24,    # więcej równoległych
        "headers": {"Referer": "https://fajerwerkilider.pl/",
                    "Accept-Language": "pl-PL,pl;q=0.9,en-US;q=0.8,en;q=0.7"},
    },
    "pyrostar": {
        "base": "https://pyrostar.pl",
        "listing": {**_IDO, "price": "strong.price.--main", "in_stock": "button.add_to_basket__button-listing",
            "out_of_stock": "span.--disable", "categories": ["https://pyrostar.pl/pl/menu/oferta-232.html"]},
    },
    "pirozaur": {
        # PrestaShop niestandardowy: item z .js-product.product.col-xs-12, name z img@alt
        # (bo a[href] łapie "Szybki podgląd" jako nazwę)
        "base": "https://www.pirozaur.pl", "delay": 1.0,
        "listing": {"next": "{url}?page={page}", "start": 1,
            "categories": ["https://www.pirozaur.pl/2-strona-glowna"],
            "item": "div.js-product.product.col-xs-12",
            "name": ["img@alt", "h2.product-title a", "h3.product-title a", ".product-title a"],
            "link": ["a.thumbnail.product-thumbnail@href", "a.product-thumbnail@href"],
            "price": ["span.price", ".product-price .price"],
            "out_of_stock": ".product-unavailable, li.out_of_stock, button[data-button-action='add-to-cart'][disabled]",
            "out_text": ["nie ma takiej ilości", "wyprzedan", "brak w magazynie"]},
    },
    "sklepzpetardami": {
        "base": "https://sklepzpetardami.pl", "use_proxy": True,
        "mode": "listing",
        "max_parallel": 2,
        "delay": 1.0,
        "browser_ua": True,
        "listing": {**_PRESTA, "categories": ["https://sklepzpetardami.pl/kategoria-produktu/oferta/"],
            "item": "article.product-miniature",
            "name": "div.tvproduct-name a", "link": "div.tvproduct-name a@href", "price": "span.price",
            "out_of_stock": "button.add-to-cart.tvproduct-out-of-stock, button.add-to-cart.disable, button.add-to-cart[disabled]"},
    },
    "piroman": {
        # PrestaShop niestandardowy: item z .ajax_block_product, name z div.product-meta
        "base": "https://piroman.pl",
        "listing": {"next": "{url}?page={page}", "start": 1,
            "item": "div.ajax_block_product.col-sp-12.col-xs-6",
            "name": ["div.product-meta a[href]", "div.product-meta > a"],
            "link": ["a.thumbnail.product-thumbnail@href", "a.product-thumbnail@href"],
            "price": ["div.p-price", ".p-price"],
            "out_of_stock": "button.add-to-cart.disabled, li.available_date",
            "out_text": ["powiadom", "niedostępny", "brak w magazynie"],
            "categories": [
                "https://piroman.pl/10-strefa-kibica",
                "https://piroman.pl/12-nowosci",
                "https://piroman.pl/19-promocje",
                "https://piroman.pl/13-petardy",
                "https://piroman.pl/22-race",
                "https://piroman.pl/15-gatlingi-rzymskie-ognie",
                "https://piroman.pl/16-swiece-granaty-dymne",
                "https://piroman.pl/17-wulkany-fontanny",
                "https://piroman.pl/43-halloween-z-shezzerem",
                "https://piroman.pl/45-piroukasz-poleca-petardy",
                "https://piroman.pl/14-rakiety-",
                "https://piroman.pl/18-wyrzutnie-baterie-fajerwerkow",
                "https://piroman.pl/37-single-shoty",
                "https://piroman.pl/20-pirobajery",
                "https://piroman.pl/44-zimne-ognie",
                "https://piroman.pl/24-odstraszanie-zwierzyny",
                "https://piroman.pl/21-odstraszacze-w-plynie",
                "https://piroman.pl/11-sznury-hukowe",
            ]},
    },
    "hurtowniaas": {
        "base": "https://fajerwerkigorzow.pl",
        "mode": "api",
        "store_api": {"endpoint": "https://fajerwerkigorzow.pl/wp-json/wc/store/v1/products"},
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
        # Shoper: paginacja {url}/{page} (bez ?page=), item product-tile (web component)
        "base": "https://fajerwerki.shop.pl", "use_proxy": True,
        "mode": "listing",
        "browser_ua": True,
        "listing": {"next": "{url}/{page}", "start": 1,
            "item": ["product-tile.product-tile", "product-tile"],
            "name": ["h3.product-tile__name", "a.link_no-underline", "h2", "h3"],
            "name_fallback": ["img[alt]@alt"],
            "link": ["a.link_no-underline@href", "a[href*='.html']@href", "a@href"],
            "link_fallback": ["a[href]@href"],
            "price": ["span.price__value.price__value_bold", "span.price__value"],
            "out_text": ["niedostępn", "powiadom o dostępności", "powiadom mnie", "brak towaru", "wyprzedan"],
            "categories": [
                "https://fajerwerki.shop.pl/strefa-kibica.html",
                "https://fajerwerki.shop.pl/emiter-dzwieku.html",
                "https://fajerwerki.shop.pl/pl/menu/miny-dymne-194.html",
                "https://fajerwerki.shop.pl/pl/menu/fontanny-tortowe-195.html",
                "https://fajerwerki.shop.pl/pl/menu/odstraszacze-zwierzyny-196.html",
                "https://fajerwerki.shop.pl/petardy.html",
                "https://fajerwerki.shop.pl/pl/menu/single-shoty-mozdzierze-157.html",
                "https://fajerwerki.shop.pl/pl/menu/palniki-zarowe-158.html",
                "https://fajerwerki.shop.pl/pl/menu/rzymskie-ognie-159.html",
                "https://fajerwerki.shop.pl/pl/menu/wulkany-fontanny-160.html",
                "https://fajerwerki.shop.pl/pl/menu/swiece-dymne-161.html",
                "https://fajerwerki.shop.pl/pl/menu/pirobajery-baczki-cyrkoblitze-162.html",
                "https://fajerwerki.shop.pl/pl/menu/zimne-ognie-163.html",
                "https://fajerwerki.shop.pl/pl/menu/rakiety-164.html",
                "https://fajerwerki.shop.pl/pl/menu/race-sygnalowe-startowce-165.html",
                "https://fajerwerki.shop.pl/pl/menu/artykuly-weselne-party-gender-party-166.html",
                "https://fajerwerki.shop.pl/pl/menu/pirotechnika-sceniczna-167.html",
                "https://fajerwerki.shop.pl/pl/menu/lonty-i-zapalniki-splonka-168.html",
                "https://fajerwerki.shop.pl/pl/menu/gadzety-fun-gadzet-169.html",
                "https://fajerwerki.shop.pl/ciche-fajerwerki.html",
                "https://fajerwerki.shop.pl/pl/menu/gazy-pieprzowe-171.html",
                "https://fajerwerki.shop.pl/pl/menu/napoje-172.html",
                "https://fajerwerki.shop.pl/pl/menu/tajemnicze-boxy-173.html",
                "https://fajerwerki.shop.pl/pl/menu/wypozyczalnia-sprzetu-174.html",
                "https://fajerwerki.shop.pl/pl/c/pokazy-profesjonalne/88",
                "https://fajerwerki.shop.pl/pl/menu/produkty-bez-rabatu-175.html",
                "https://fajerwerki.shop.pl/pl/menu/wyrzutnie-180.html",
                "https://fajerwerki.shop.pl/pl/menu/enola-gaye-177.html",
                "https://fajerwerki.shop.pl/pl/menu/systemy-odpalania-pirotechniki-186.html",
                "https://fajerwerki.shop.pl/pl/menu/artykuly-survivalowe-179.html",
                "https://fajerwerki.shop.pl/pl/menu/katowe-wyrzutnie-189.html",
                "https://fajerwerki.shop.pl/pl/menu/zestawy-zlozone-dso-compound-181.html",
                "https://fajerwerki.shop.pl/pl/menu/wyrzutnie-25-99-strzalow-190.html",
                "https://fajerwerki.shop.pl/pl/menu/wyrzutnie-50mm-182.html",
                "https://fajerwerki.shop.pl/pl/menu/wyrzutnie-100-500-strzalow-191.html",
                "https://fajerwerki.shop.pl/pl/menu/wyrzutnie-1-25-strzalow-192.html",
                "https://fajerwerki.shop.pl/pl/menu/singleline-183.html",
                "https://fajerwerki.shop.pl/pl/menu/dymy-i-pozoracja-184.html",
                "https://fajerwerki.shop.pl/pl/menu/paintball-185.html",
                "https://fajerwerki.shop.pl/pl/menu/tpro-show-193.html",
                "https://fajerwerki.shop.pl/pl/menu/rekawice-187.html",
                "https://fajerwerki.shop.pl/pl/menu/latarki-188.html",
            ]},
    },
    "pyrotech": {
        "base": "https://hurtownia-fajerwerki.pl", "sitemaps": ["https://hurtownia-fajerwerki.pl/sitemap.xml.gz"],
        "listing": {**_IDO, "price": "strong.price.--main", "out_of_stock": "span.--disable",
            "categories": ["https://hurtownia-fajerwerki.pl/pol_m_Fajerwerki-157.html"]},
    },
    "pirozone": {
        # item li.product, name z a.product-title (motyw custom z rating)
        "base": "https://pirozone.pl", "delay": 0.7, "use_proxy": True,
        "mode": "api",
        "store_api": {"endpoint": "https://pirozone.pl/wp-json/wc/store/v1/products"},
        "browser_ua": True,
        "listing": {"next": "{url}page/{page}/", "start": 1,
            "item": "li.product",
            "name": ["a.product-title", "h3.woocommerce-loop-product__title a", "h3.woocommerce-loop-product__title"],
            "link": ["a.ct-media-container@href", "a.product-title@href", "a.woocommerce-LoopProduct-link@href"],
            "price": ["span.woocommerce-Price-amount.amount", ".woocommerce-Price-amount"],
            "in_stock": ".instock", "out_of_stock": ".outofstock",
            "categories": [
                "https://pirozone.pl/fajerwerki-menu-glowne/",
            ]},
    },
    "firefactory": {
        "base": "https://www.firefactory.pl",
        "mode": "api",
        "store_api": {"endpoint": "https://www.firefactory.pl/wp-json/wc/store/v1/products"},
        "listing": {**_WOO, "name": "h2.woocommerce-loop-product__title", "link": "a.woocommerce-LoopProduct-link@href",
            "price": ["ins", "span.woocommerce-Price-amount"], "out_text": ["dowiedz się więcej"],
            "categories": ["https://www.firefactory.pl/sklep/"]},
    },
    "obornicka": {
        "base": "https://www.fajerwerki-obornicka.pl",
        "mode": "api",
        "store_api": {"endpoint": "https://www.fajerwerki-obornicka.pl/wp-json/wc/store/v1/products"},
        "listing": {**_WOO, "name": "h2.woocommerce-loop-product__title", "link": "a.woocommerce-LoopProduct-link@href",
            "price": ["span.price ins bdi", "span.price bdi"], "out_text": ["brak w magazynie"],
            "categories": ["https://www.fajerwerki-obornicka.pl/home/sklep/"]},
    },
    "piroandrzej": {
        # Custom (nieznana platforma): item .Okno, name z img@alt (bo a[href] łapie "zobacz szczegóły"),
        # price .CenaAktualna. Paginacja /s=N.
        "base": "https://piroandrzej.pl",
        "mode": "sitemap",
        "listing": {"next": "{url}/s={page}", "start": 1,
            "item": "div.Okno.OknoRwd",
            "name": ["img@alt", "a[href]"],
            "link": ["a[href]@href", "a.Zoom@href"],
            "price": ["span.CenaAktualna"],
            "categories": [
                "https://piroandrzej.pl/dymy-c-14.html",
                "https://piroandrzej.pl/flary-c-12.html",
                "https://piroandrzej.pl/lonty-i-zapalniki-c-6.html",
                "https://piroandrzej.pl/petardy-c-3.html",
                "https://piroandrzej.pl/pirobajery-c-5.html",
                "https://piroandrzej.pl/race-pistoletowe-c-10.html",
                "https://piroandrzej.pl/rakiety-c-2.html",
                "https://piroandrzej.pl/rzymskie-ognie-c-7.html",
                "https://piroandrzej.pl/single-shoty-c-8.html",
                "https://piroandrzej.pl/wulkany-i-fontanny-c-4.html",
                "https://piroandrzej.pl/wyrzutnie-c-1.html",
                "https://piroandrzej.pl/zestawy-promocyjne-c-15.html",
                "https://piroandrzej.pl/zimne-ognie-c-11.html",
            ]},
    },
    "pironet": {
        "base": "https://pironet.pl",
        "mode": "api",
        "store_api": {"endpoint": "https://pironet.pl/wp-json/wc/store/v1/products"},
        "browser_ua": True,                     # Cloudflare czasem przepuszcza Chrome UA
        "use_proxy": True, "max_parallel": 2,
        "delay": 1.0,                           # wolno, żeby nie dostać 429
        "sitemaps": ["https://pironet.pl/product-sitemap.xml"],   # TYLKO produkty, bez tagów
        "url_regex": r"^https://pironet\.pl/sklep/[^/]+/?$",  # /sklep/<slug-produktu>/
    },
    "piroart": {
        # item li.product (fallback li), name a[href] (pierwszy z tekstem)
        "base": "https://piroart.pl", "use_proxy": True, "browser_ua": True,
        "mode": "api",
        "store_api": {"endpoint": "https://piroart.pl/wp-json/wc/store/v1/products"},
        "sitemaps": ["https://piroart.pl/sitemap_index.xml"],
        "listing": {**_WOO,
            "item": ["li.product", "li"],
            "name": ["h2.woocommerce-loop-product__title a", "h3 a", "a[href]"],
            "link": ["a.woocommerce-LoopProduct-link@href", "a[href]@href"],
            "price": ["span.woocommerce-Price-amount.amount", ".woocommerce-Price-amount"],
            "categories": [
                "https://piroart.pl/petardy/",
                "https://piroart.pl/wyrzutnie/",
                "https://piroart.pl/art-rozne/",
                "https://piroart.pl/dymy/",
                "https://piroart.pl/emitery/",
                "https://piroart.pl/gotowe-zestawy-dso/",
                "https://piroart.pl/race-pistoletowe/",
                "https://piroart.pl/rzymskie-ognie/",
                "https://piroart.pl/strefa-ultras/",
                "https://piroart.pl/wulkany-i-fontanny/",
                "https://piroart.pl/zapalniczki-zarowe/",
                "https://piroart.pl/zestawy-rakiety/",
                "https://piroart.pl/zimne-ognie/",
                "https://piroart.pl/silenty/",
                "https://piroart.pl/okazje/",
                "https://piroart.pl/hurtownia/",
            ]},
    },
    "petardyshop": {
        "base": "https://petardyshop.pl", "delay": 0.2,
        "mode": "api",
        "store_api": {"endpoint": "https://petardyshop.pl/wp-json/wc/store/v1/products"},
        "listing": {"next": "{url}page/{page}/", "start": 1,
            "item": "div.fusion-product-wrapper",
            "name": ["h3.product-title a", "h3.product-title"],
            "link": ["h3.product-title a@href", "a.fusion-link-wrapper@href"],
            "price": ["span.price .woocommerce-Price-amount bdi",
                      "span.price ins .woocommerce-Price-amount",
                      ".woocommerce-Price-amount bdi"],
            "in_stock": "a.add_to_cart_button",
            "out_of_stock": ".outofstock, a.add_to_cart_button[disabled]",
            "categories": ["https://petardyshop.pl/sklep/"]},
    },
    "biegun": {
        "base": "https://fajerwerkibiegun.pl",
        "delay": 0.5, "max_parallel": 4, "use_proxy": True, "browser_ua": True,
        "mode": "listing",
        "listing": {"first": "{url}", "next": "{url}?page={page}", "start": 1,
            "item": "article.product-miniature",
            "name": "h3.product-title a", "link": "h3.product-title a@href",
            "price": "span.product-price", "in_stock": "button.add-to-cart",
            "categories": [
                "https://fajerwerkibiegun.pl/pl/3-wyrzutnie",
                "https://fajerwerkibiegun.pl/pl/27-wyrzutnie-do-200-pln",
                "https://fajerwerkibiegun.pl/pl/33-wyrzutnie-od-200-pln",
                "https://fajerwerkibiegun.pl/pl/15-petardy",
                "https://fajerwerkibiegun.pl/pl/40-swiece-dymne",
                "https://fajerwerkibiegun.pl/pl/45-race-flary",
                "https://fajerwerkibiegun.pl/pl/44-stroboskopy",
                "https://fajerwerkibiegun.pl/pl/43-pirotechnika-sceniczna",
                "https://fajerwerkibiegun.pl/pl/29-rzymskie-ognie",
                "https://fajerwerkibiegun.pl/pl/14-fontanny",
                "https://fajerwerkibiegun.pl/pl/24-rakiety",
                "https://fajerwerkibiegun.pl/pl/36-zimne-ognie",
                "https://fajerwerkibiegun.pl/pl/38-pirobajery",
                "https://fajerwerkibiegun.pl/pl/47-amunicja",
                "https://fajerwerkibiegun.pl/pl/39-lonty-rury-systemy",
                "https://fajerwerkibiegun.pl/pl/30-mozdzierze-single-",
            ]},
    },
    "fajerwerkimarket": {
        "base": "https://www.fajerwerkimarket.pl",
        "delay": 0.5, "max_parallel": 4,
        "mode": "listing",
        "listing": {"first": "{url}", "next": "{url}/{page}", "start": 1,
            "item": "div.product",
            "name": "a.product_name", "link": "a.product_name@href",
            "price": "div.info-right .price", "in_stock": "a.basket_add_link",
            "categories": [
                "https://www.fajerwerkimarket.pl/category/nowa-kategoria-198",
                "https://www.fajerwerkimarket.pl/category/petardy",
                "https://www.fajerwerkimarket.pl/category/petardy-emitery-dzwieku",
                "https://www.fajerwerkimarket.pl/category/artykuly-rozne",
                "https://www.fajerwerkimarket.pl/category/single-shoty",
                "https://www.fajerwerkimarket.pl/category/motyle",
                "https://www.fajerwerkimarket.pl/category/co-poleca-machony-flash",
                "https://www.fajerwerkimarket.pl/category/bombowa-wyprzedaz-flary",
                "https://www.fajerwerkimarket.pl/category/fontanny",
                "https://www.fajerwerkimarket.pl/category/rakiety",
                "https://www.fajerwerkimarket.pl/category/zestawy",
                "https://www.fajerwerkimarket.pl/category/strefa-kibica-dymy",
                "https://www.fajerwerkimarket.pl/category/wspolpraca-zimne-ognie",
                "https://www.fajerwerkimarket.pl/category/rzymskie-ognie",
                "https://www.fajerwerkimarket.pl/category/karabinki-163",
                "https://www.fajerwerkimarket.pl/category/wyrzutnie",
                "https://www.fajerwerkimarket.pl/category/wyrzutnie-wyrzutnie-katowe",
                "https://www.fajerwerkimarket.pl/category/bombowe-zestawy-za-1-grosz",
                "https://www.fajerwerkimarket.pl/category/zestawy-do-samodzielnego-odpalenia",
                "https://www.fajerwerkimarket.pl/category/artykuly-do-pokazow-weselnych",
                "https://www.fajerwerkimarket.pl/category/zapalniczki",
                "https://www.fajerwerkimarket.pl/category/animal-friendly",
                "https://www.fajerwerkimarket.pl/category/artykuly-sceniczne",
                "https://www.fajerwerkimarket.pl/category/efekt-dzienny",
            ]},
    },
    "funke-store": {
        "base": "https://funke-store.com",
        "use_proxy": True, "browser_ua": True,
        "mode": "api",
        "store_api": {"endpoint": "https://funke-store.com/wp-json/wc/store/v1/products"},
    },
    "funkezone": {
        "base": "https://funkezone.com",
        "mode": "api",
        "store_api": {"endpoint": "https://funkezone.com/wp-json/wc/store/v1/products"},
    },
    "pirolux": {
        "base": "https://pirolux.com.pl",
        "mode": "sitemap",
        "delay": 1.0,
        "sitemaps": ["https://pirolux.com.pl/sitemap-produkty.xml"],
        "url_regex": r"^https://(?:www\.)?pirolux\.com\.pl/[^/]+-p\d+$",
    },
    "piroshop": {
        "base": "https://piroshop.pl",
        "mode": "sitemap",
        "browser_ua": True, "use_proxy": True,
        "delay": 1.0, "max_parallel": 1,
        "sitemaps": ["https://piroshop.pl/1_pl_0_sitemap.xml"],
        "url_regex": r"^https://piroshop\.pl/pl/.+/\d+-[^/]+\.html$",
    },
    "pirotechnika.net": {
        "base": "https://pirotechnika.net",
        "mode": "api",
        "use_proxy": True, "delay": 1.0, "max_parallel": 2,
        "store_api": {"endpoint": "https://pirotechnika.net/wp-json/wc/store/v1/products"},
    },
    "taniefajerwerki": {
        "base": "https://taniefajerwerki.pl",
        "delay": 0.4, "max_parallel": 4,
        "mode": "listing",
        "listing": {"first": "{url}", "next": "{url}?page={page}", "start": 1,
            "item": "li.product",
            "name": "h3.kw-details-title", "link": "a[href]@href",
            "price": ["div.price ins span.amount", "div.price span.amount"],
            "in_stock": "button.btn-buy",
            "categories": [
                "https://taniefajerwerki.pl/kategoria/wyrzutnie/59",
                "https://taniefajerwerki.pl/kategoria/petardy/65",
                "https://taniefajerwerki.pl/kategoria/rakiety/61",
                "https://taniefajerwerki.pl/kategoria/rzymskie-ognie/62",
                "https://taniefajerwerki.pl/kategoria/fontanny/63",
                "https://taniefajerwerki.pl/kategoria/dymyrace/93",
                "https://taniefajerwerki.pl/kategoria/pirotechnika-sceniczna/89",
                "https://taniefajerwerki.pl/kategoria/strefa-kibica/85",
                "https://taniefajerwerki.pl/kategoria/mozdzierze/66",
                "https://taniefajerwerki.pl/kategoria/emiter-dzwieku/98",
                "https://taniefajerwerki.pl/kategoria/zimne-ognie/64",
                "https://taniefajerwerki.pl/kategoria/miny-dymne/214",
                "https://taniefajerwerki.pl/kategoria/piro-bajery/80",
                "https://taniefajerwerki.pl/kategoria/zestawy-do-samodzielnej-obslugi/83",
                "https://taniefajerwerki.pl/kategoria/systemy-pirotechniczne/92",
            ]},
    },
    "vitis": {
        "base": "https://fajerwerkiopole.pl",
        "mode": "listing",
        "listing": {
            "first": "{url}", "next": "{url}?page={page}", "start": 1, "max_pages": 1,
            "item": "article.product-miniature",
            "name": ".product-title a", "link": ".product-title a@href",
            "price": "span.price", "in_stock": ".availability-list-in-stock",
            "categories": [
                "https://fajerwerkiopole.pl/pl/3-petardy-hukowe",
                "https://fajerwerkiopole.pl/pl/6-wyrzutnie",
                "https://fajerwerkiopole.pl/pl/11-zimne-ognie",
                "https://fajerwerkiopole.pl/pl/12-inne-art-pirotechniczne",
                "https://fajerwerkiopole.pl/pl/14-rakiety-i-zestawy",
                "https://fajerwerkiopole.pl/pl/15-przeceny-i-promocje",
                "https://fajerwerkiopole.pl/pl/16-emiter-dzwieku",
                "https://fajerwerkiopole.pl/pl/17-sznur-hukowy-huker",
                "https://fajerwerkiopole.pl/pl/18-dymy-pirotechniczne",
                "https://fajerwerkiopole.pl/pl/19-rzymskie-ognie",
                "https://fajerwerkiopole.pl/pl/20-stroboskopy",
                "https://fajerwerkiopole.pl/pl/21-zapaliniki-pirotechniczne",
            ],
        },
    },
    "ultrasstore": {
        "base": "https://ultrasstore.com",
        "mode": "listing",
        "listing": {
            "first": "{url}", "next": "{url}?page={page}", "start": 1, "max_pages": 1,
            "currency": "PLN", "in_stock": "button.an_productattributes-add-to-cart-btn",
            "item": "article.product-miniature",
            "name": "h3.product-title a", "link": "h3.product-title a@href",
            "price": "span.price",
            "categories": [
                "https://ultrasstore.com/pl/62-petardy",
                "https://ultrasstore.com/pl/29-race",
                "https://ultrasstore.com/pl/63-smoke-bombs-",
                "https://ultrasstore.com/pl/28-stroboskopy",
                "https://ultrasstore.com/pl/36-rakiety",
                "https://ultrasstore.com/pl/57-rzymskie-ognie",
                "https://ultrasstore.com/pl/56-fontanny",
                "https://ultrasstore.com/pl/35-single-shot",
                "https://ultrasstore.com/pl/52-ognie-wroclawskie",
                "https://ultrasstore.com/pl/34-naboje-pistoletowe",
            ],
        },
    },
    "wybuchy": {
        "base": "https://wybuchy.pl",
        "mode": "api",
        "store_api": {"endpoint": "https://wybuchy.pl/wp-json/wc/store/v1/products"},
    },
}

_tls = threading.local()
_lock = threading.RLock()
_stats_lock = threading.Lock()
_robots, _crawl_delay, _next_slot = {}, {}, {}
_robots_note = {}
_proxies, _proxy_i, _proxy_fail, _proxy_dead = [], 0, Counter(), {}
_host_sem = {}
_proxy_strikes = Counter()
_min_delay, _proxy_hosts = {}, set()
PROXY_ALL = env('SCRAPER_PROXY_ALL') == '1'
PROXY_MAX_FAILS = 3
PROXY_PAUSE = 120

# --- Adaptacyjne tempo per host ---------------------------------------------
_host_delay = {}
_host_last_ease = {}
_host_successes = Counter()      # licznik sukcesów z rzędu (do resetu delay)
_warn_last = {}
_warn_count = Counter()
_host_gate = {}
_gate_lock = threading.Lock()
_host_proxy_fails = Counter()   # host -> consecutive proxy fails (przez wywołania get)

class _AdaptiveGate:
    def __init__(self, n):
        self.max = n
        self.active = 0
        self.cv = threading.Condition()

    def __enter__(self):
        with self.cv:
            while self.active >= self.max:
                self.cv.wait()
            self.active += 1
        return self

    def __exit__(self, *a):
        with self.cv:
            self.active -= 1
            self.cv.notify()

    def shrink(self, n):
        with self.cv:
            self.max = max(1, min(self.max, n))

    def grow(self, n):
        with self.cv:
            if n > self.max:
                self.max = n
                self.cv.notify_all()


def _gate(host):
    with _gate_lock:
        g = _host_gate.get(host)
        if g is None:
            g = _AdaptiveGate(WORKERS)
            _host_gate[host] = g
        return g


def _base_delay(host):
    return max(DELAY, _min_delay.get(host, 0.0))


def _bump_delay(host, factor, cap=20.0):
    with _lock:
        cur = _host_delay.get(host) or _base_delay(host)
        new = min(cap, cur * factor)
        if new > cur * 1.1:
            log.debug("spowalniam %s: %.2fs → %.2fs", host, cur, new)
        _host_delay[host] = new
        _host_successes[host] = 0


def _maybe_ease(host, gate):
    with _lock:
        now = time.time()
        if now - _host_last_ease.get(host, 0) < 1.0:
            return
        _host_last_ease[host] = now
        base = _base_delay(host)
        cur = _host_delay.get(host, base)
        if cur > base * 1.02:
            _host_delay[host] = max(base, cur * 0.5)
    if gate.max < WORKERS:
        gate.grow(min(WORKERS, gate.max + 1))


def _warn_rate_limited(host, kind, msg, every=30.0):
    now = time.time()
    key = (host, kind)
    with _lock:
        if now - _warn_last.get(key, 0) < every:
            _warn_count[key] += 1
            return
        skipped = _warn_count.pop(key, 0)
        _warn_last[key] = now
    log.warning("%s%s", msg, f" [+{skipped} podobnych]" if skipped else "")


def session():
    sess = getattr(_tls, "s", None)
    if sess is None:
        sess = requests.Session()
        sess.headers.update({"User-Agent": USER_AGENT, "Accept-Language": "pl-PL,pl;q=0.9"})
        _tls.s = sess
    return sess


# ----------------------------- sieć -----------------------------------------
def mask(px):
    if not px:
        return "bezpośrednio"
    try:
        return f"proxy#{_proxies.index(px) + 1}"
    except ValueError:
        return "proxy"


def short_err(e):
    msg = str(e)
    msg = re.sub(r"//[^/@\s]+@", "//***@", msg)
    msg = re.sub(r"\b\d{1,3}(?:\.\d{1,3}){3}(?::\d+)?\b", "<ip>", msg)
    m = re.search(r"(Tunnel connection failed: \d+ [^'\")]+|Connection refused|Connection reset[^'\")]*|"
                  r"timed out|Name or service not known|Temporary failure in name resolution|"
                  r"Remote end closed connection[^'\")]*|certificate verify failed[^'\")]*|Connection aborted[^'\")]*)", msg)
    detail = m.group(1) if m else re.sub(r"\s+", " ", msg)[-100:].strip(" ()'\"")
    return f"{e.__class__.__name__}: {detail}"[:160]


def setup_proxies(args):
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
    with _lock:
        return sum(1 for px in _proxies if _proxy_dead.get(px, 0) <= now)


def _is_safe_proxy_for_https(px):
    """SOCKS tuneluje surowe bajty (bez MITM). HTTP/HTTPS proxy mogą robić SSL
    interception - dla HTTPS ich unikamy (poza proxy z sekretów)."""
    return px.startswith(("socks5", "socks4"))

def pick_proxy(url_scheme="https"):
    global _proxy_i
    if not _proxies:
        return None
    with _lock:
        now = time.time()
        if url_scheme == "https":
            safe = [px for px in _proxies
                    if _is_safe_proxy_for_https(px) and _proxy_dead.get(px, 0) <= now]
            if safe:
                px = safe[_proxy_i % len(safe)]
                _proxy_i += 1
                return px
            # Fallback: TYLKO user proxy z SOCKS (bez HTTP - robi MITM na HTTPS)
            user_socks = [px for px in _proxies
                         if px not in _free_proxies
                         and _is_safe_proxy_for_https(px)
                         and _proxy_dead.get(px, 0) <= now]
            if user_socks:
                px = user_socks[_proxy_i % len(user_socks)]
                _proxy_i += 1
                return px
            return None  # direct lepiej niż HTTPS przez HTTP proxy (MITM)
        for _ in range(len(_proxies)):
            px = _proxies[_proxy_i % len(_proxies)]
            _proxy_i += 1
            if _proxy_dead.get(px, 0) <= now:
                return px
        return min(_proxies, key=lambda x: _proxy_dead.get(x, 0))


def report_proxy(px, ok, dead=False):
    if not px:
        return
    with _lock:
        if ok:
            _proxy_fail[px] = 0
            _proxy_dead.pop(px, None)
            return
        if dead:
            _proxy_dead[px] = time.time() + PROXY_PAUSE
            _proxy_fail[px] = 0
            _proxy_strikes[px] += 1
            if px in _free_proxies and _proxy_strikes[px] >= 2:
                try:
                    _proxies.remove(px)
                except ValueError:
                    pass
                _free_proxies.discard(px)
                _proxy_dead.pop(px, None)
            return
        _proxy_fail[px] += 1
        if _proxy_fail[px] >= PROXY_MAX_FAILS:
            _proxy_fail[px] = 0
            _proxy_dead[px] = time.time() + PROXY_PAUSE
            _proxy_strikes[px] += 1
            if px in _free_proxies and _proxy_strikes[px] >= 2:
                label = mask(px)
                try:
                    _proxies.remove(px)
                except ValueError:
                    pass
                _free_proxies.discard(px)
                _proxy_dead.pop(px, None)
                log.debug("%s (darmowe) usunięte (zostało %d)", label, len(_proxies))
            else:
                log.debug("%s w pauzie %d s (aktywnych: %d z %d)",
                          mask(px), PROXY_PAUSE, _live_count(), len(_proxies))


GEONODE_API = os.environ.get("GEONODE_API", "https://proxylist.geonode.com/api/proxy-list")
_free_proxies = set()

# --- Proxifly fallback (multi-source: HTTPS -> SOCKS5 -> all) --------------
PROXIFLY_SOCKS5_JSON = (
    "https://cdn.jsdelivr.net/gh/proxifly/free-proxy-list@main/"
    "proxies/protocols/socks5/data.json"
)
# Kraje preferowane (blisko Polski = niższe opóźnienia)
PROXIFLY_QUALITY_COUNTRIES = {"PL", "DE", "CZ", "SK", "NL", "FR", "GB"}
# Ile maksymalnie dodać w jednym przebiegu (żeby nie zapchać rotacji)
PROXIFLY_MAX_QUALITY = 200
_fallback_lock = threading.Lock()
_last_fallback_fetch = 0.0
FALLBACK_INTERVAL = 180
_403_lock = threading.Lock()
_last_403_fetch = 0.0
_403_INTERVAL = 120

_socks_cached = None


def _socks_ok():
    global _socks_cached
    if _socks_cached is None:
        try:
            import socks  # noqa: F401
            _socks_cached = True
        except ImportError:
            _socks_cached = False
    return _socks_cached


def _do_fetch_proxifly(tag=""):
    """Pobiera TYLKO SOCKS5 z Proxifly (bezpieczne dla HTTPS).
    Filtruje po krajach blisko Polski, ogranicza liczbę.
    """
    if not _socks_ok():
        log.warning("Proxifly%s: PySocks nie zainstalowany – pomijam SOCKS5", tag)
        return 0

    try:
        r = requests.get(PROXIFLY_SOCKS5_JSON, timeout=25,
                         headers={"User-Agent": USER_AGENT})
        r.raise_for_status()
        data = r.json()
    except (requests.RequestException, ValueError) as e:
        log.warning("Proxifly%s: nie udało się pobrać JSON SOCKS5: %s",
                    tag, short_err(e))
        return 0

    added = []
    for item in data:
        proxy = item.get("proxy")
        if not proxy or not proxy.startswith("socks5://"):
            continue
        country = (item.get("geolocation") or {}).get("country", "")
        # Preferuj kraje blisko Polski
        if country and country not in PROXIFLY_QUALITY_COUNTRIES:
            continue
        # score obecnie zawsze 1, ale na przyszłość – odrzucaj śmieci
        if item.get("score", 1) < 1:
            continue
        added.append(proxy)
        if len(added) >= PROXIFLY_MAX_QUALITY:
            break

    # Jeśli filtr kraju dał 0 – awaryjnie bierz dowolne SOCKS5
    if not added:
        log.info("Proxifly%s: brak proxy z preferowanych krajów – "
                 "biorę dowolne SOCKS5", tag)
        for item in data:
            proxy = item.get("proxy")
            if proxy and proxy.startswith("socks5://"):
                added.append(proxy)
                if len(added) >= PROXIFLY_MAX_QUALITY:
                    break

    with _lock:
        new_count = 0
        for px in added:
            if px not in _proxies:
                _proxies.append(px)
                _free_proxies.add(px)
                new_count += 1

    log.info("Proxifly%s: dodano %d nowych SOCKS5 (łącznie w puli: %d)",
             tag, new_count, len(_proxies))
    return new_count


def fetch_proxifly_proxies(limit=2000):
    global _last_fallback_fetch
    with _fallback_lock:
        if time.time() - _last_fallback_fetch < FALLBACK_INTERVAL:
            return 0
        _last_fallback_fetch = time.time()
    return _do_fetch_proxifly()


def _on_403_detected():
    global _last_403_fetch
    now = time.time()
    with _403_lock:
        if now - _last_403_fetch < _403_INTERVAL:
            return
        _last_403_fetch = now
    log.info("wykryto 403 (blokada?) – pobieram świeże proxy z Proxifly w tle")
    threading.Thread(target=_do_fetch_proxifly, args=(" (403)",), daemon=True).start()


def ensure_fallback_proxies():
    if not _proxies or _live_count() == 0:
        fetch_proxifly_proxies()


def geonode_candidates(countries=()):
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
            scheme = "http"
        elif "socks5" in protos and socks_ok:
            scheme = "socks5h"
        elif "socks4" in protos and socks_ok:
            scheme = "socks4a"
        else:
            skipped["socks bez PySocks" if protos & {"socks4", "socks5"} else "inny protokół"] += 1
            continue
        prio = 0 if "https" in protos else (1 if scheme == "socks5h" else 2)
        cands.append((prio, round(-up / 10), round(float(it.get("responseTime") or 9999) / 200), f"{scheme}://{ip}:{port}"))
    random.shuffle(cands)
    cands.sort(key=lambda c: c[:3])
    log.info("darmowe proxy (Geonode): %d na liście, %d kandydatów po filtrach%s", len(data), len(cands),
             (", odrzucone: " + ", ".join(f"{k} {v}" for k, v in skipped.items())) if skipped else "")
    return [c[3] for c in cands]


def _check_proxy(px, targets):
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


def acquire_free_proxies(targets, want=None, budget=None, countries=()):
    want = want or int(env("SCRAPER_FREE_PROXY_COUNT", 12))
    budget = budget or int(env("SCRAPER_FREE_PROXY_SECONDS", 90))
    t0 = time.time()
    cands = [c for c in geonode_candidates(countries) if c not in _proxies][:400]
    if not cands:
        return []
    found = []
    pool = ThreadPoolExecutor(max_workers=40)
    futs = {pool.submit(_check_proxy, px, targets): px for px in cands}
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
    log.info("darmowe proxy: sprawdzono %d kandydatów w %.0f s, działa %d (cel: %d) - łącznie w rotacji: %d",
             len(futs), time.time() - t0, len(found), want, len(_proxies))
    if not found:
        log.warning("darmowe proxy: żaden kandydat nie przepuścił stron sklepów")
    return [px for _, px in found]


def free_proxy_targets(names):
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


def proxy_for(netloc, url_scheme="https"):
    if not (PROXY_ALL or netloc in _proxy_hosts):
        return None
    return pick_proxy(url_scheme)


def proxy_kw(px):
    return {"proxies": {"http": px, "https": px}} if px else {}


def allowed(url):
    host = "{0.scheme}://{0.netloc}".format(urlparse(url))
    nl = urlparse(url).netloc
    with _lock:
        if host not in _robots:
            rp, reason, net_fail = None, "brak odpowiedzi", False
            via_proxy = bool(_proxies) and (PROXY_ALL or nl in _proxy_hosts)
            attempts = min(10, max(3, _live_count() + 1)) if via_proxy else 3
            for _ in range(attempts):
                px = proxy_for(nl, "https")
                try:
                    r = session().get(host + "/robots.txt", timeout=15, **proxy_kw(px))
                except requests.RequestException as e:
                    report_proxy(px, False, dead=True)
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
                    reason = None
                break
            if reason:
                note = f"robots.txt niedostępny ({reason})"
                _robots_note[nl] = note
                if net_fail:
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
    with _lock:
        base = _base_delay(host)
        delay = max(base, _host_delay.get(host, base))
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
    url_scheme = urlparse(url).scheme
    last_err = "?"
    if _proxies and (PROXY_ALL or host in _proxy_hosts):
        retries = max(retries, min(8, _live_count() + 1))
    gate = _gate(host)
    proxy_fails = 0
    for attempt in range(retries):
        ensure_fallback_proxies()
        throttle(host)
        px = None
        try:
            px = proxy_for(host, url_scheme)
            if px in _free_proxies and url_scheme != "https":
                _tls.last_fail = "adres HTTP nie przez darmowe proxy"
                bump("nieudane")
                return None
            to = (10, 20) if px else (8, 20)
            with gate:
                with _host_sem.get(host) or contextlib.nullcontext():
                    r = session().get(url, timeout=to, cookies=cookies, headers=headers, **proxy_kw(px))
            code = r.status_code
            if code == 200:
                report_proxy(px, True)
                proxy_fails = 0
                with _lock:
                    _host_proxy_fails[host] = 0
                    _host_successes[host] += 1
                    base_d = _base_delay(host)
                    if _host_successes[host] >= 10 and _host_delay.get(host, base_d) > base_d * 2:
                        _host_delay[host] = base_d
                        _host_successes[host] = 0
                _maybe_ease(host, gate)
                bump("pobrane_ok")
                return r
            if code == 429:
                report_proxy(px, True)
                wait = 5.0
                ra = r.headers.get("Retry-After")
                if ra:
                    try:
                        wait = min(60.0, float(ra))
                    except (ValueError, TypeError):
                        pass
                _bump_delay(host, 2.0)
                gate.shrink(max(2, gate.max // 2))
                _warn_rate_limited(host, "429", f"HTTP 429 {host} – spowalniam, czekam {wait:.0f}s")
                bump("http_429")
                last_err = f"HTTP 429 (retry after {wait:.0f}s)"
                time.sleep(min(wait, 20.0))
                continue
            if code == 403:
                bump("http_403")
                _tls.last_fail = f"HTTP 403 (server: {r.headers.get('server', '?')})"
                _on_403_detected()
                if px is not None:
                    report_proxy(px, False, dead=True)
                    proxy_fails += 1
                    if proxy_fails >= 20 and host in _proxy_hosts:
                        _proxy_hosts.discard(host)
                        log.warning("%s: 20 kolejnych 403 przez proxy – przełączam na direct", host)
                    _warn_rate_limited(host, "403",
                                       f"HTTP 403 przez {mask(px)} – próbuję kolejne proxy: {url}", every=60)
                    continue
                if _proxies and host not in _proxy_hosts:
                    log.warning("HTTP 403 bez proxy dla %s – włączam proxy dla tego hosta", host)
                    _proxy_hosts.add(host)
                    if host not in _host_sem:
                        _host_sem[host] = threading.Semaphore(4)
                    continue
                log.debug("HTTP 403 (bez proxy, brak proxy do przełączenia): %s", url)
                return None
            if code in (404, 410):
                bump(f"http_{code}")
                _tls.last_fail = f"HTTP {code}"
                log.debug("HTTP %s: %s", code, url)
                return None
            last_err = f"HTTP {code}"
            _warn_rate_limited(host, f"http_{code}", f"HTTP {code} (próba {attempt + 1}/{retries}): {url}", every=30)
            if code >= 500:
                # nie bumpujemy delay - to błąd serwera, nie rate-limit
                pass
        except requests.exceptions.SSLError as e:
            report_proxy(px, False, dead=True)
            last_err = short_err(e)
            with _lock:
                _host_proxy_fails[host] += 1
                if _host_proxy_fails[host] >= 20 and host in _proxy_hosts:
                    _proxy_hosts.discard(host)
                    _host_proxy_fails[host] = 0
                    log.warning("%s: 20 kolejnych failów proxy – przełączam na direct", host)
            continue
        except requests.Timeout as e:
            report_proxy(px, False, dead=(px is not None))
            last_err = short_err(e)
            if px is None:
                _bump_delay(host, 1.3, cap=10.0)
            else:
                with _lock:
                    _host_proxy_fails[host] += 1
                    if _host_proxy_fails[host] >= 20 and host in _proxy_hosts:
                        _proxy_hosts.discard(host)
                        _host_proxy_fails[host] = 0
                        log.warning("%s: 20 kolejnych failów proxy – przełączam na direct", host)
            if px is None and attempt >= 1:
                break
            continue
        except requests.ConnectionError as e:
            report_proxy(px, False, dead=(px is not None))
            last_err = short_err(e)
            if px is None:
                _bump_delay(host, 1.3, cap=10.0)
            else:
                with _lock:
                    _host_proxy_fails[host] += 1
                    if _host_proxy_fails[host] >= 20 and host in _proxy_hosts:
                        _proxy_hosts.discard(host)
                        _host_proxy_fails[host] = 0
                        log.warning("%s: 20 kolejnych failów proxy – przełączam na direct", host)
            continue
        except requests.RequestException as e:
            report_proxy(px, False)
            last_err = short_err(e)
            _warn_rate_limited(host, type(e).__name__,
                               f"błąd sieci przez {mask(px)} (próba {attempt + 1}/{retries}): {url} | {last_err}", every=30)
            if px is not None:
                continue
        time.sleep(2 ** attempt)
    bump("nieudane")
    _tls.last_fail = f"nieudane po {retries} próbach ({last_err})"
    return None


# ----------------------------- sitemap --------------------------------------
SITEMAP_FALLBACKS = ("/sitemap.xml", "/sitemap_index.xml", "/sitemap.xml.gz", "/sitemap_index.xml.gz", "/wp-sitemap.xml",
                     "/sitemap-index.xml", "/sitemap-index.xml.gz", "/sitemap/sitemap_index.xml", "/sitemap/sitemap.xml",
                     "/sitemaps/sitemap.xml", "/sitemaps.xml", "/product-sitemap.xml", "/sitemap_products_1.xml")
_ASSET_RE = re.compile(r"\.(?:jpe?g|png|gif|webp|svg|ico|pdf|mp4|webm|css|js|zip|xml)(?:\?|$)", re.I)


def _is_loc(tag):
    return tag == "loc" or (tag.endswith("}loc") and not any(x in tag.lower() for x in ("image", "video", "news", "xhtml")))


def read_sitemap(url, headers=None):
    r = get(url, headers=headers)
    if not r:
        return None
    data = r.content
    for _ in range(2):
        if data[:2] == b"\x1f\x8b":
            try:
                data = gzip.decompress(data)
            except (OSError, EOFError):
                return None
    data = data.lstrip(b"\xef\xbb\xbf \t\r\n")
    try:
        tree = ET.fromstring(data)
        locs = [el.text.strip() for el in tree.iter() if _is_loc(el.tag) and el.text and el.text.strip()]
        return tree.tag.lower().endswith("sitemapindex"), locs
    except ET.ParseError:
        locs = [htmllib.unescape(m.decode("utf-8", "replace")).strip()
                for m in re.findall(rb"<loc>\s*(?:<!\[CDATA\[)?(.*?)(?:\]\]>)?\s*</loc>", data, re.S | re.I)]
        if not locs:
            return None
        return b"sitemapindex" in data[:3000].lower(), locs


def _walk_sitemaps(roots, site, hdrs, info):
    seen, out, stack = set(), [], list(reversed(roots))
    flt = site.get("sitemap_filter")
    while stack and len(seen) < 300:
        sm = stack.pop()
        if sm in seen:
            continue
        seen.add(sm)
        # ODRZUĆ: sitemapy tagów/atrybutów/author/stron — nie zawierają produktów
        if re.search(r"/(?:product[_-]?tag|post[_-]?tag|product_cat[_-]tag|tag[_-]sitemap|"
                     r"author[_-]?sitemap|product_brand|product_shipping)", sm, re.I):
            continue
        res = read_sitemap(sm, hdrs)
        if res is None:
            log.warning("  sitemapa niedostępna lub nieczytelna: %s (%s)", sm, getattr(_tls, "last_fail", "?"))
            info["failed"].append(sm)
            info["reasons"].append(getattr(_tls, "last_fail", "?"))
            continue
        is_index, locs = res
        locs = [urljoin(sm, u) for u in locs]
        if is_index:
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
    info = info if info is not None else {}
    info.update({"sitemaps": 0, "children": 0, "failed": [], "reasons": [], "tried": []})
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
        filtered = [u for u in out if re.search(pattern, u)]
        if not filtered and out:
            log.warning("  url_regex nie pasuje do ŻADNEGO z %d adresów, przykłady: %s",
                        before, ", ".join(out[:3]))
        out = filtered
        log.info("  filtr url_regex: %d -> %d adresów", before, len(out))
    return list(dict.fromkeys(out))


# ----------------------------- parsowanie -----------------------------------
_PRICE_RE = re.compile(
    r"(?<![\d.,])(?:[1-9]\d{0,2}(?:[ \u00a0\u202f.,]\d{3})+(?:[.,]\d{1,2})?|\d+(?:[.,]\d{1,2})?)(?!\d)")


def parse_price(text):
    if text is None:
        return None
    if isinstance(text, (int, float)):
        v = float(text)
    else:
        m = _PRICE_RE.search(str(text))
        if not m:
            return None
        tok = m.group(0)
        dec = re.search(r"[.,](\d{1,2})$", tok)
        whole, frac = (tok[:dec.start()], dec.group(1)) if dec else (tok, "")
        whole = re.sub(r"[ \u00a0\u202f.,]", "", whole)
        v = float(f"{whole}.{frac or '0'}")
    return round(v, 2) if 0 < v < 1_000_000 else None


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
            return
        if "ItemList" in types:
            yield {"@type": "ItemList", "n": len(node.get("itemListElement") or [])}
            return  # NIE schodź w itemListElement - to rekomendacje, nie produkty strony
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
        "code_raw": prod.get("mpn"),
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
    if d.get("price") is None:
        els = soup.find_all(attrs={"itemprop": "price"})
        if len(els) == 1:
            d["price"] = parse_price(els[0].get("content") or els[0].get_text(" ", strip=True))
    if not d.get("availability"):
        el = soup.find(attrs={"itemprop": "availability"})
        if el is not None:
            d["availability"] = norm_availability(el.get("href") or el.get("content") or el.get_text(" ", strip=True))
    if not d.get("name"):
        d["name"] = meta(soup, "og:title") or (soup.h1.get_text(strip=True) if soup.h1 else None)
    if site.get("selectors"):
        s = from_selectors(soup, site["selectors"])
        for k, v in s.items():
            if v is not None and (d.get(k) is None or site.get("prefer_selectors")):
                d[k] = v
    if not d.get("name"):
        return None
    if d.get("price") is None and not d.get("_ld"):
        return None
    return d


# ----------------------------- kody produktów -------------------------------
_UNITS = (r"MM|CM|M|G|KG|ML|L|SZT|S|SEK|SEC|MIN|H|X|V|W|HZ|PCS|SHOT|SHOTS|STRZ\w*|STRZAL\w*|ST|K|CAL|CALI|CALA|CALE|"
          r"INCH|PLN|ZL|LAT|KAL|KALIBER|KULI|KULA|KUL")
_UNIT_RE = re.compile(rf"^\d+(?:X\d+)*(?:{_UNITS})?$")
_UNIT_LEAD_RE = re.compile(rf"^(?:X)\d+(?:{_UNITS})?$")
_BLACK_RE = re.compile(r"^(?:F[1-4]|T[12]|P[12]|KAT\d|3D|4K|2K|HD|XL{1,2}|XS|RGB\d*|USB\d*|LED\d*|"
                       r"(?:CE|UN|EN|EAN|ISO|PN|DIN)\d*)$")
_MARK_RE = re.compile(r"(?:kod(?:\s+produktu)?|nr\s*kat(?:alogowy)?\.?|numer\s+katalogowy|symbol|indeks|sku|"
                      r"art(?:ykuł)?\.?|ref\.?|model)\s*[:#]?\s*([A-Za-z0-9][A-Za-z0-9\-_/.]{2,20})", re.I)
_SLUG_CODE_RE = re.compile(r"^[a-z]{2,5}\d{2,6}[a-z]{0,2}$")


def _fold(text):
    text = (text or "").upper().replace("Ł", "L")
    text = unicodedata.normalize("NFKD", text)
    return "".join(c for c in text if not unicodedata.combining(c))


def _code_candidate(token, marker=False, trusted=False, slug=False):
    disp = token.strip(" \t.,;:()[]{}<>\"'!?*+")
    if not 3 <= len(disp) <= 18 or not re.fullmatch(r"[\w][\w\-_/.]*[\w]", disp, re.U):
        return None
    key = re.sub(r"[^0-9A-Z]", "", _fold(disp))
    if not 3 <= len(key) <= 16 or not any(c.isdigit() for c in key):
        return None
    if _UNIT_RE.match(key) and not key.isdigit() or _UNIT_LEAD_RE.match(key) or _BLACK_RE.match(key):
        return None
    letters, digits = sum(c.isalpha() for c in key), sum(c.isdigit() for c in key)
    if letters == 0:
        if not ((marker or trusted) and len(key) >= 4) and len(key) < 8:
            return None
        if re.fullmatch(r"(?:19|20)\d\d", key):
            return None
    elif not (marker or trusted or slug):
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
    best = max(cands, key=lambda c: c[2])
    return best[0], best[1]


# ----------------------------- baza -----------------------------------------
PARSER_VERSION = 2


def db():
    con = sqlite3.connect(DB_PATH)
    con.executescript("""
    CREATE TABLE IF NOT EXISTS products(
      url TEXT PRIMARY KEY, site TEXT, name TEXT, code TEXT, code_key TEXT,
      first_seen TEXT, last_seen TEXT);
    CREATE TABLE IF NOT EXISTS prices(
      id INTEGER PRIMARY KEY AUTOINCREMENT, url TEXT, ts TEXT,
      price REAL, currency TEXT, availability TEXT, scan_id INTEGER);
    CREATE INDEX IF NOT EXISTS ix_prices_url ON prices(url, ts);
    CREATE TABLE IF NOT EXISTS scrape_runs(
      id INTEGER PRIMARY KEY AUTOINCREMENT, site TEXT, started_at TEXT,
      completed_at TEXT, status TEXT, products_checked INTEGER DEFAULT 0);
    CREATE TABLE IF NOT EXISTS nonproduct(url TEXT PRIMARY KEY, ts TEXT);
    """)
    cols = {r[1] for r in con.execute("PRAGMA table_info(products)")}
    if "code" not in cols:
        con.execute("ALTER TABLE products ADD COLUMN code TEXT")
        con.execute("ALTER TABLE products ADD COLUMN code_key TEXT")
        rows = con.execute("SELECT url, name FROM products").fetchall()
        for url, name in rows:
            code, key = extract_code(name, url)
            con.execute("UPDATE products SET code=?, code_key=? WHERE url=?", (code, key, url))
        log.info("migracja bazy: dodano kody produktów (%d produktów)", len(rows))
    if "sku" in cols:
        try:
            con.execute("ALTER TABLE products DROP COLUMN sku")
        except sqlite3.OperationalError:
            pass
    con.execute("CREATE INDEX IF NOT EXISTS ix_products_code ON products(code_key)")
    con.execute("CREATE TABLE IF NOT EXISTS meta(k TEXT PRIMARY KEY, v TEXT)")
    row = con.execute("SELECT v FROM meta WHERE k = 'parser_version'").fetchone()
    if not row or int(row[0]) < PARSER_VERSION:
        n = con.execute("SELECT COUNT(*) FROM prices").fetchone()[0]
        if n:
            con.execute("DROP TABLE IF EXISTS prices_backup")
            con.execute("DROP INDEX IF EXISTS ix_prices_url")
            con.execute("ALTER TABLE prices RENAME TO prices_backup")
            con.execute("""CREATE TABLE prices(id INTEGER PRIMARY KEY AUTOINCREMENT, url TEXT, ts TEXT,
                           price REAL, currency TEXT, availability TEXT)""")
            con.execute("CREATE INDEX ix_prices_url ON prices(url, ts)")
            log.warning("zmiana parsera cen: historia (%d wpisów) przeniesiona do tabeli prices_backup, "
                        "ceny liczone od nowa", n)
        con.execute("INSERT OR REPLACE INTO meta(k, v) VALUES('parser_version', ?)", (str(PARSER_VERSION),))
    price_cols = {r[1] for r in con.execute("PRAGMA table_info(prices)")}
    if "scan_id" not in price_cols:
        con.execute("ALTER TABLE prices ADD COLUMN scan_id INTEGER")
    con.execute("CREATE INDEX IF NOT EXISTS ix_scrape_runs_site_start ON scrape_runs(site, started_at)")
    con.commit()
    return con


_suspicious = []
_active_scan_ids = {}


def save(con, site_name, url, d):
    now = datetime.now(timezone.utc).isoformat(timespec="seconds")
    code, key = extract_code(d["name"], url, d.get("hint"), d.get("code_raw"))
    con.execute("""INSERT INTO products(url,site,name,code,code_key,first_seen,last_seen)
                   VALUES(?,?,?,?,?,?,?)
                   ON CONFLICT(url) DO UPDATE SET name=excluded.name, code=excluded.code,
                   code_key=excluded.code_key, last_seen=excluded.last_seen""",
                (url, site_name, d["name"], code, key, now, now))
    scan_id = _active_scan_ids.get(site_name)
    if scan_id is not None:
        con.execute("UPDATE scrape_runs SET products_checked = products_checked + 1 WHERE id = ?",
                    (scan_id,))
    last = con.execute("SELECT price, availability FROM prices WHERE url=? "
                       "ORDER BY id DESC LIMIT 1", (url,)).fetchone()
    cur = (d["price"], d.get("availability"))
    # porównanie z tolerancją - float po round-tripie przez SQLite może się różnić
    if last is not None:
        changed = False
        if last[0] is not None and d["price"] is not None:
            if abs(last[0] - d["price"]) > 0.005:
                changed = True
        elif last[0] != d["price"]:
            changed = True
        if last[1] != d.get("availability"):
            changed = True
    else:
        changed = True
    if last and last[0] and d["price"] and (d["price"] / last[0] >= 5 or d["price"] / last[0] <= 0.2):
        _suspicious.append((url, last[0], d["price"]))
        if len(_suspicious) <= 25:
            log.warning("PODEJRZANA ZMIANA CENY %.2f -> %.2f | %s | %s", last[0], d["price"], d["name"], url)
    if changed:
        con.execute(
            "INSERT INTO prices(url,ts,price,currency,availability,scan_id) VALUES(?,?,?,?,?,?)",
            (url, now, d["price"], d.get("currency", "PLN"), d.get("availability"), scan_id),
        )
        return True
    return False


# ----------------------------- komendy --------------------------------------
def report_problems(problems, label):
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
    if not spec:
        return None
    for one in ([spec] if isinstance(spec, str) else spec):
        if not isinstance(one, str):
            continue
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
    return tile.select_one(css) is not None or sv.match(css, tile)


def parse_listing(html, page_url, cfg):
    soup = BeautifulSoup(html, "lxml")
    sel = cfg["item"]
    tiles = []
    for one in ([sel] if isinstance(sel, str) else sel):
        tiles = soup.select(one)
        if tiles:
            break
    products = []
    for tile in tiles:
        name = _pick(tile, cfg["name"]) or _pick(tile, cfg.get("name_fallback"))
        href = _pick(tile, cfg["link"]) or _pick(tile, cfg.get("link_fallback"))
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
            out = True
        if cfg.get("out_of_stock") and has(tile, cfg["out_of_stock"]):
            out = True
        if any(t.lower() in text for t in cfg.get("out_text", [])):
            out = True
        products.append({
            "name": name.strip(), "currency": cfg.get("currency", "PLN"),
            "hint": raw_text[:400], "code_raw": _pick(tile, cfg.get("code")),
            "availability": "out_of_stock" if out else "in_stock",
            "price": parse_price(raw_price),
            "url": urljoin(page_url, href.strip()),
        })
    return len(tiles), products


def site_headers(name, site):
    h = dict(site.get("headers") or {})
    wanted = {x.strip() for x in BROWSER_UA_SPEC.split(",") if x.strip()}
    if site.get("browser_ua") or "1" in wanted or name.lower() in wanted:
        h.setdefault("User-Agent", BROWSER_UA)
        h.setdefault("Accept", "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8")
        h.setdefault("Accept-Language", "pl-PL,pl;q=0.9,en-US;q=0.8,en;q=0.7")
    return h or None


def diag(r):
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
    except Exception as e:
        return f"nie udało się zanalizować ({e})"


_NEXT_TEXTS = {"»", "›", ">", "→", "następna", "następny", "następna strona", "dalej", "kolejna", "next", "nast.", "nast"}


def find_next_link(content, cur_url, ordinal):
    try:
        soup = BeautifulSoup(content, "lxml")
        cands = []
        ln = soup.find("link", attrs={"rel": "next"}) or soup.find("a", attrs={"rel": "next"})
        if ln is not None and ln.get("href"):
            cands.append(ln["href"])
        anchors = soup.find_all("a", href=True)
        cands += [a["href"] for a in anchors if a.get_text(strip=True) == str(ordinal + 1)]
        cands += [a["href"] for a in anchors if a.get_text(strip=True).lower() in _NEXT_TEXTS]
        cands += [a["href"] for a in anchors if "następn" in (a.get("aria-label") or "").lower()]
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
                reason = f"{n_tiles} kafelków, ale selektory name/link nic nie wyciągają | np. {outline(tiles[0]) if (tiles := __import__('bs4').BeautifulSoup(r.content, 'lxml').select(cfg['item'] if isinstance(cfg['item'], str) else cfg['item'][0])) else '?'}"
                log.warning("[%s] %s: %s", name, reason, url)
            if not new:
                break
            seen.update(it["url"] for it in new)
            total += len(new)
            q.put(("items", name, cat_url, page, new))
            page += 1
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
    except Exception as e:
        reason = f"wyjątek: {e}"
        log.warning("[%s] błąd w kategorii %s: %s", name, cat_url, e)
    finally:
        if not reason and last_r is not None and total and page - start == 1:
            ph = pagination_hint(last_r.content)
            if ph:
                reason = f"UWAGA tylko 1 strona ({total} prod.), ale strona wskazuje kolejne: {ph}"
        q.put(("done", name, cat_url, page - start, total, reason))


def run_listing(con, names, args):
    t0 = time.time()
    per_shop = {n: list(SITES[n]["listing"]["categories"]) for n in names}
    tasks = []
    while any(per_shop.values()):
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
    px_shops = [n for n in names if SITES[n].get("use_proxy") or PROXY_ALL]
    if px_shops:
        log.info("proxy dla: %s", ", ".join(px_shops))
    pool = ThreadPoolExecutor(max_workers=args.workers)
    for n, cat in tasks:
        cfg = dict(SITES[n]["listing"])
        if args.max:
            cfg["max_pages"] = args.max
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
                        st["niedostepne"] += 1
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


def parse_store_api_product(raw):
    if not isinstance(raw, dict):
        return None
    name = htmllib.unescape(str(raw.get("name") or "")).strip()
    url = str(raw.get("permalink") or "").strip()
    if not name or not url:
        return None

    prices = raw.get("prices") or {}
    price = None
    raw_price = prices.get("price")
    if raw_price is not None:
        try:
            minor_unit = max(0, min(6, int(prices.get("currency_minor_unit", 2))))
            price = round(int(raw_price) / (10 ** minor_unit), 2)
            if not 0 < price < 1_000_000:
                price = None
        except (TypeError, ValueError, OverflowError):
            price = None

    in_stock = raw.get("is_in_stock")
    availability = "in_stock" if in_stock is True else (
        "out_of_stock" if in_stock is False else None
    )
    return {
        "name": name,
        "currency": prices.get("currency_code") or "PLN",
        "hint": "",
        "code_raw": raw.get("sku"),
        "availability": availability,
        "price": price,
        "url": url,
    }


def store_api_driver(name, site, args, q, stats):
    cfg = site["store_api"]
    endpoint = cfg["endpoint"]
    page_size = min(100, max(1, int(cfg.get("per_page", 100))))
    max_pages = args.max or int(cfg.get("max_pages", 10000))
    headers = dict(site_headers(name, site) or {})
    headers["Accept"] = "application/json"
    pages = products = 0
    reason = None
    try:
        for page in range(1, max_pages + 1):
            url = endpoint + ("&" if "?" in endpoint else "?") + urlencode({
                "per_page": page_size,
                "page": page,
                "_fields": "id,name,permalink,sku,prices,is_in_stock",
            })
            response = get(url, stats, headers=headers)
            if response is None:
                reason = getattr(_tls, "last_fail", "błąd pobierania API")
                break
            try:
                payload = response.json()
            except ValueError as e:
                reason = f"niepoprawny JSON API: {e.__class__.__name__}"
                break
            if not isinstance(payload, list):
                reason = "API zwróciło nieoczekiwany format (oczekiwano listy produktów)"
                break
            parsed = [item for item in (parse_store_api_product(row) for row in payload) if item]
            skipped = len(payload) - len(parsed)
            if skipped:
                log.warning("[%s] API: pominięto %d niekompletnych rekordów na stronie %d",
                            name, skipped, page)
            pages += 1
            products += len(parsed)
            q.put(("api_page", name, page, parsed))
            if len(payload) < page_size:
                break
        else:
            reason = f"osiągnięto limit {max_pages} stron API"
    except Exception as e:
        reason = f"{e.__class__.__name__}: {str(e)[:150]}"
    finally:
        q.put(("api_done", name, pages, products, reason))


def run_store_api(con, names, args):
    t0 = time.time()
    stats = {n: Counter() for n in names}
    gets = {n: Counter() for n in names}
    problems = []
    q = queue.Queue()
    log.info("TRYB STORE API: %d sklepów, stron na sklep maks.: %s, odstęp: %.2fs",
             len(names), args.max or "bez limitu", DELAY)
    shops = ThreadPoolExecutor(max_workers=max(1, len(names)))
    for name in names:
        shops.submit(store_api_driver, name, SITES[name], args, q, gets[name])
    pending = len(names)
    try:
        while pending:
            try:
                msg = q.get(timeout=5)
            except queue.Empty:
                continue
            if msg[0] == "api_page":
                _, name, page, items = msg
                stats[name]["strony"] += 1
                for item in items:
                    stats[name]["produkty"] += 1
                    if item["price"] is None:
                        stats[name]["bez_ceny"] += 1
                    if item["availability"] == "out_of_stock":
                        stats[name]["niedostepne"] += 1
                    if save(con, name, item["url"], item):
                        stats[name]["zmiany_w_historii"] += 1
                    log.debug("[%s] API strona %d: %s | %s",
                              name, page, item["name"], item["price"])
            else:
                _, name, pages, products, reason = msg
                pending -= 1
                if reason:
                    problems.append((name, SITES[name]["store_api"]["endpoint"], reason))
                elif not products:
                    problems.append((name, SITES[name]["store_api"]["endpoint"],
                                     "API zwróciło 0 produktów"))
                stats[name]["nieudane"] += gets[name]["nieudane"] + int(bool(reason))
                log.info("[%s] API gotowe: %d stron, %d produktów%s",
                         name, pages, products, f" | problem: {reason}" if reason else "")
                con.commit()
    finally:
        shops.shutdown(wait=False, cancel_futures=True)
        con.commit()
    report_problems(problems, "Store API")
    log.info("TRYB STORE API zakończony w %s", fmt_dur(time.time() - t0))
    return [(name, stats[name]["strony"], stats[name]) for name in names]


def resolve_sites(args):
    if not args.site:
        skipped = [n for n in SITES if SITES[n].get("skip")]
        if skipped:
            log.info("pomijam sklepy z flagą skip: %s (włącz przez --site nazwa)", ", ".join(skipped))
        return [n for n in SITES if not SITES[n].get("skip")]
    wanted = [x.lower() for x in re.split(r"[,\s]+", args.site) if x]
    lookup = {k.lower(): k for k in SITES}
    bad = [w for w in wanted if w not in lookup]
    if bad:
        raise SystemExit(f"Nieznane sklepy: {bad}")
    return [lookup[w] for w in wanted]


def url_group(url):
    segs = [x for x in urlparse(url).path.split("/") if x]
    if not segs:
        return "/"
    g = re.sub(r"\d+", "#", segs[0].lower())
    if re.fullmatch(r"[a-z]{2}", segs[0].lower()) and len(segs) > 1:
        g += "/" + re.sub(r"\d+", "#", segs[1].lower())
    return g[:40]


def page_brief(content):
    m = re.search(rb"<title[^>]*>(.*?)</title>", content, re.I | re.S)
    title = re.sub(r"\s+", " ", m.group(1).decode("utf-8", "replace")).strip()[:70] if m else "?"
    has_ld = b"application/ld+json" in content
    has_prod = b'"Product"' in content
    return f"title={title!r}, JSON-LD={'tak' if has_ld else 'nie'}, Product w JSON-LD={'tak' if has_prod else 'nie'}"


def fetch_one(url, site, stats, hdrs=None, skip=None):
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


GROUP_SKIP_AFTER = 40


def sitemap_driver(name, site, known_np, args, q):
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
            # as_completed zamiast map: nie blokujemy na najwolniejszym URL-u.
            futs = {pool.submit(fetch_one, u, site, gets, hdrs, skip): u for u in urls}
            for fut in as_completed(futs):
                url, d, status, brief, grp = fut.result()
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
    except Exception as e:
        q.put(("error", name, f"{e.__class__.__name__}: {str(e)[:150]}"))
    finally:
        q.put(("done", name, gstat))


def run_sitemap(con, names, args):
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
                        reasons = sorted(set(info["reasons"]))
                        extra = f"; powód: {', '.join(reasons)}" if reasons else ""
                        hint = (" | wskazówka: 403 = serwer odrzuca klienta - sprawdź browser_ua/use_proxy"
                                if any("403" in r for r in reasons) else "")
                        problems.append((n, "brak adresów w sitemapie; sprawdzone: " + (", ".join(info["tried"][:5]) or "-") + extra + hint))
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
    scan_ids = {}
    scan_completed = False
    try:
        names = resolve_sites(args)
        started_at = datetime.now(timezone.utc).isoformat(timespec="seconds")
        for name in names:
            cursor = con.execute(
                "INSERT INTO scrape_runs(site,started_at,status) VALUES(?,?,'running')",
                (name, started_at),
            )
            scan_ids[name] = cursor.lastrowid
        _active_scan_ids.update(scan_ids)
        con.commit()
        for n in names:
            site = SITES[n]
            hosts = {urlparse(site["base"]).netloc}
            hosts |= {urlparse(c).netloc for c in site.get("listing", {}).get("categories", [])}
            for h in hosts:
                if site.get("delay"):
                    _min_delay[h] = max(_min_delay.get(h, 0.0), float(site["delay"]))
                if site.get("use_proxy"):
                    _proxy_hosts.add(h)
                # max_parallel działa też bez proxy (np. lider ma 24, ale go nie używa)
                if site.get("use_proxy") or site.get("max_parallel"):
                    _host_sem[h] = threading.Semaphore(int(site.get("max_parallel", 4)))
        if (env("SCRAPER_PROXY_SOURCE", "") or "").lower() == "geonode":
            targets = free_proxy_targets(names)
            if not targets:
                log.info("darmowe proxy: żaden z wybranych sklepów nie ma use_proxy - pomijam")
            else:
                countries = tuple(c.strip().upper() for c in (env("SCRAPER_PROXY_COUNTRY", "") or "").split(",") if c.strip())
                acquire_free_proxies(targets, countries=countries)
                start_free_refresher(targets, countries)
        if _proxies and not PROXY_ALL and not _proxy_hosts:
            log.warning("podano proxy, ale żaden wybrany sklep nie ma use_proxy (ustaw SCRAPER_PROXY_ALL=1)")
        in_actions = bool(os.environ.get("GITHUB_ACTIONS"))
        summary = []
        mode = (args.mode or "auto").lower()
        if mode not in ("smart", "sitemap", "listing", "api", "auto"):
            raise SystemExit(f"Nieznany tryb {mode!r}: użyj smart, sitemap, listing, api albo auto")
        api_names, listing_names, sitemap_names, fallback_ok = [], [], [], []
        for n in names:
            m_ = (SITES[n].get("mode") or mode).lower()
            has_listing = bool(SITES[n].get("listing"))
            has_api = bool(SITES[n].get("store_api"))
            if m_ == "api" and has_api:
                api_names.append(n)
            elif m_ == "listing" and has_listing:
                listing_names.append(n)
            elif m_ == "auto" and has_listing:
                listing_names.append(n)
            else:
                sitemap_names.append(n)
                if m_ == "smart" and has_listing:
                    fallback_ok.append(n)
        auto_names = [n for n in listing_names if (SITES[n].get("mode") or mode).lower() == "auto"]
        forced = [n for n in names if SITES[n].get("mode")]
        log.info("tryb: %s | Store API: %d sklepów, sitemapa: %d sklepów, kategorie: %d sklepów%s",
                 mode, len(api_names), len(sitemap_names), len(listing_names),
                 f" | tryb ustawiony w konfiguracji sklepu: {', '.join(n + '=' + SITES[n]['mode'] for n in forced)}" if forced else "")
        ua_shops = [n for n in names if "User-Agent" in (site_headers(n, SITES[n]) or {})]
        px_shops = [n for n in names if SITES[n].get("use_proxy") or PROXY_ALL]
        log.info("ustawienia: User-Agent przeglądarki dla: %s | proxy (%d szt.) dla: %s",
                 ", ".join(ua_shops) or "nikt", len(_proxies), ", ".join(px_shops) or "nikt")
        if api_names:
            if in_actions:
                print("::group::tryb Store API", flush=True)
            summary += run_store_api(con, api_names, args)
            if in_actions:
                print("::endgroup::", flush=True)
        if listing_names:
            if in_actions:
                print("::group::tryb listing", flush=True)
            res = run_listing(con, listing_names, args)
            if in_actions:
                print("::endgroup::", flush=True)
            fallback = [n for (n, _p, st_) in res if n in auto_names and st_["produkty"] == 0]
            if fallback:
                log.warning("tryb auto: kategorie nie dały produktów dla %s - przechodzę na sitemapę", ", ".join(fallback))
                res = [r for r in res if r[0] not in fallback]
                sitemap_names += fallback
            summary += res
        if sitemap_names:
            if in_actions:
                print("::group::tryb sitemap", flush=True)
            res = run_sitemap(con, sitemap_names, args)
            if in_actions:
                print("::endgroup::", flush=True)
            fallback = [n for (n, _c, st_) in res if n in fallback_ok and st_["produkty"] == 0]
            if fallback:
                log.warning("tryb smart: sitemapa nie dała produktów dla %s - przechodzę na strony kategorii", ", ".join(fallback))
                res = [r for r in res if r[0] not in fallback]
                if in_actions:
                    print("::group::tryb listing (zapasowy)", flush=True)
                res += run_listing(con, fallback, args)
                if in_actions:
                    print("::endgroup::", flush=True)
            summary += res

        if _suspicious:
            log.warning("PODEJRZANE ZMIANY CEN (skok >= 5x): %d szt.", len(_suspicious))
            for url, old, new in _suspicious[:10]:
                log.warning("  %.2f -> %.2f | %s", old, new, url)
            if len(_suspicious) > 10:
                log.warning("  ... i %d więcej", len(_suspicious) - 10)
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
        scan_completed = True
    finally:
        completed_at = datetime.now(timezone.utc).isoformat(timespec="seconds")
        for name, scan_id in scan_ids.items():
            con.execute(
                "UPDATE scrape_runs SET completed_at = ?, status = ? WHERE id = ?",
                (completed_at, "complete" if scan_completed else "failed", scan_id),
            )
            _active_scan_ids.pop(name, None)
        con.commit()
        con.close()


def cmd_export(args):
    con = db()
    try:
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
    finally:
        con.close()


def cmd_history(args):
    con = db()
    try:
        for ts, price, cur, av in con.execute(
                "SELECT ts, price, currency, availability FROM prices WHERE url=? ORDER BY id", (args.url,)):
            price_s = f"{price:>9.2f}" if price is not None else "     brak"
            print(f"{ts}  {price_s} {cur}  {av}")
    finally:
        con.close()


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    ap.add_argument("-v", "--verbose", action="store_true", help="loguj każdy adres (poziom DEBUG)")
    sub = ap.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("scrape")
    s.add_argument("--site", default=env("SCRAPER_ONLY"), help="sklepy po przecinku (domyślnie wszystkie; ENV: SCRAPER_ONLY)")
    s.add_argument("--max", type=int, default=int(env("SCRAPER_MAX", 0)) or None,
                   help="limit: adresów (sitemap) / stron na kategorię (listing) / stron API na sklep; ENV: SCRAPER_MAX")
    s.add_argument("--workers", type=int, default=WORKERS, help="liczba równoległych wątków")
    s.add_argument("--delay", type=float, default=DELAY, help="min. odstęp między zapytaniami do hosta (s)")
    s.add_argument("--proxy", action="append", help="adres proxy (http://user:haslo@host:port lub socks5://...), można podać wiele razy")
    s.add_argument("--proxy-file", help="plik z proxy, jedno na linię")
    s.add_argument("--mode", default=env("SCRAPER_MODE", "auto"), help="auto (domyślnie) = kategorie najpierw, a gdy nic nie da - sitemapa | listing | sitemap | api | smart; API jest wybierane automatycznie dla sklepów z obsługą Store API; ENV: SCRAPER_MODE")
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
        argv.append("scrape")
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
