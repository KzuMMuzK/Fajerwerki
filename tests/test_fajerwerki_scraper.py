import unittest
import queue
import sqlite3
import tempfile
from collections import Counter
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import Mock, patch
from urllib.parse import parse_qs, urlparse

import fajerwerki_scraper as scraper


class ListingParserTests(unittest.TestCase):
    def test_shoper_card_uses_image_alt_when_title_is_missing(self):
        html = """
        <product-tile class="product-tile">
          <a class="link_no-underline" href="/produkt/test.html">
            <img alt="Duże Rakiety JR73 Nuclear">
          </a>
          <span class="price__value price__value_bold">109,00 zł</span>
        </product-tile>
        """

        count, products = scraper.parse_listing(
            html,
            "https://fajerwerki.shop.pl/kategoria/1",
            scraper.SITES["szopik"]["listing"],
        )

        self.assertEqual(count, 1)
        self.assertEqual(len(products), 1)
        self.assertEqual(products[0]["name"], "Duże Rakiety JR73 Nuclear")
        self.assertEqual(products[0]["url"], "https://fajerwerki.shop.pl/produkt/test.html")
        self.assertEqual(products[0]["price"], 109.0)

    def test_listing_detects_sale_price_and_explicit_sale_badges(self):
        examples = (
            ("""<article class="product"><a href="/sale">Produkt</a><span class="price">
                <del><span class="woocommerce-Price-amount">199,00 zł</span></del>
                <ins><span class="woocommerce-Price-amount">149,00 zł</span></ins></span></article>""",
             ".woocommerce-Price-amount", 149.0),
            ("""<article class="product"><a href="/sale">Produkt</a>
                <span class="badge onsale">Promocja</span><span class="price">149,00 zł</span></article>""",
             ".price", 149.0),
        )

        for html, price_selector, expected_price in examples:
            with self.subTest(html=html):
                cfg = {
                    "item": "article.product", "name": "a", "link": "a@href",
                    "price": price_selector,
                }
                count, products = scraper.parse_listing(html, "https://shop.example/", cfg)
                self.assertEqual(count, 1)
                self.assertEqual(products[0]["price"], expected_price)
                self.assertEqual(products[0]["promo"], 1)

    def test_biegun_listing_reads_name_code_link_and_price_from_category_card(self):
        count, products = scraper.parse_listing(
            """<article class="product-miniature">
              <h3 class="product-title"><a href="/pl/item">Produkt</a></h3>
              <div class="product-reference"><a href="/pl/item">TXB821</a></div>
              <span class="product-price" content="14.4">14,40&nbsp;zł</span>
              <ins><span class="unrelated-price">0,01 zł</span></ins>
            </article>""",
            "https://fajerwerkibiegun.pl/pl/wyrzutnie-do-200-pln",
            scraper.SITES["biegun"]["listing"],
        )

        self.assertEqual(count, 1)
        self.assertEqual(products[0]["name"], "Produkt")
        self.assertEqual(products[0]["url"], "https://fajerwerkibiegun.pl/pl/item")
        self.assertEqual(products[0]["code_raw"], "TXB821")
        self.assertEqual(products[0]["price"], 14.4)

    def test_biegun_configuration_keeps_browser_ua_and_categories(self):
        site = scraper.SITES["biegun"]

        self.assertTrue(site["browser_ua"])
        self.assertEqual(site["mode"], "listing")
        self.assertEqual(len(site["listing"]["categories"]), 16)
        self.assertEqual(site["listing"]["price"], "span.product-price")
        self.assertNotIn("detail_price_for_listing", site)
        self.assertNotIn("prefer_gross_price_metadata", site)
        self.assertNotIn("detail_code_for_new_products", site)

    def test_listing_ignores_ins_price_when_shop_selector_does_not_match(self):
        count, products = scraper.parse_listing(
            """<article class="product-miniature">
              <h3 class="product-title"><a href="/item">Produkt</a></h3>
              <ins><span class="unrelated-price">459,69 zł</span></ins>
            </article>""",
            "https://fajerwerkibiegun.pl/pl/",
            {
                **scraper.SITES["biegun"]["listing"],
                "price": "span.product-price",
                "item": "article.product-miniature",
            },
        )

        self.assertEqual(count, 1)
        self.assertIsNone(products[0]["price"])

    def test_biegun_listing_prefers_visible_gross_price_over_net_content_attribute(self):
        count, products = scraper.parse_listing(
            """<article class="product-miniature">
              <h3 class="product-title"><a href="/item">Produkt</a></h3>
              <span class="product-price" content="11.707317">14,40 zł</span>
              <ins><span class="unrelated-price">0,01 zł</span></ins>
            </article>""",
            "https://fajerwerkibiegun.pl/pl/",
            scraper.SITES["biegun"]["listing"],
        )

        self.assertEqual(count, 1)
        self.assertEqual(products[0]["price"], 14.4)

    def test_biegun_listing_parses_prestashop_json_rendered_products(self):
        response = {
            "rendered_products_top": "<div class='products-selection'>",
            "rendered_products": """<div id="products">
              <div class="js-product-miniature-wrapper">
                <article class="product-miniature">
                  <h3 class="product-title"><a href="https://fajerwerkibiegun.pl/pl/item">Produkt</a></h3>
                  <div class="product-reference"><a href="https://fajerwerkibiegun.pl/pl/item">TXB821</a></div>
                  <span class="product-price" content="14.4">14,40 zł</span>
                </article>
              </div>
            </div>""",
            "rendered_products_bottom": "",
            "products": [{"id_product": 2736}],
        }

        count, products = scraper.parse_listing(
            scraper.json.dumps(response).encode("utf-8"),
            "https://fajerwerkibiegun.pl/pl/3-wyrzutnie",
            scraper.SITES["biegun"]["listing"],
        )

        self.assertEqual(count, 1)
        self.assertEqual(products[0]["name"], "Produkt")
        self.assertEqual(products[0]["price"], 14.4)
        self.assertEqual(products[0]["code_raw"], "TXB821")

    def test_listing_keeps_sale_status_unknown_without_a_promotion_marker(self):
        count, products = scraper.parse_listing(
            """<article class="product"><a href="/item">Produkt</a>
               <span class="price">149,00 zł</span></article>""",
            "https://shop.example/",
            {"item": "article.product", "name": "a", "link": "a@href", "price": ".price"},
        )

        self.assertEqual(count, 1)
        self.assertIsNone(products[0]["promo"])

    def test_product_page_price_selector_ignores_struck_price_and_unrelated_ins(self):
        result = scraper.extract(
            """<html><h1>Produkt</h1>
              <span class="woocommerce-Price-amount"><del>199,00 zł</del></span>
              <span class="woocommerce-Price-amount">149,00 zł</span>
              <ins>0,01 zł</ins></html>""",
            {"selectors": {"name": "h1", "price": ".woocommerce-Price-amount"}},
        )

        self.assertEqual(result["price"], 149.0)


class ListingPageFailureTests(unittest.TestCase):
    def test_mid_category_page_failure_is_reported_with_page_number_and_reason(self):
        html = """<article class="product-miniature">
          <h3 class="product-title"><a href="/item">Produkt</a></h3>
          <span class="product-price">14,40 zł</span>
        </article>"""
        first_page = SimpleNamespace(
            content=html.encode(),
            url="https://fajerwerkibiegun.pl/pl/3-wyrzutnie?id_currency=1",
        )

        requested_urls = []

        def get_page(url, *_args, **_kwargs):
            requested_urls.append(url)
            if "page=2" in url:
                scraper._tls.last_fail = "HTTP 503"
                return None
            return first_page

        events = queue.Queue()
        with patch.object(scraper, "get", side_effect=get_page):
            scraper.listing_category(
                "biegun",
                scraper.SITES["biegun"],
                scraper.SITES["biegun"]["listing"],
                "https://fajerwerkibiegun.pl/pl/3-wyrzutnie",
                events,
                Counter(),
            )

        messages = [events.get_nowait(), events.get_nowait()]
        self.assertEqual(messages[0][0], "items")
        self.assertEqual(messages[1][0], "done")
        self.assertEqual(messages[0][4][0]["price"], 14.4)
        self.assertFalse(any("/pl/item" in url for url in requested_urls))
        self.assertIn("stronie 2", messages[1][5])
        self.assertIn("HTTP 503", messages[1][5])


class AccessHandlingTests(unittest.TestCase):
    def test_direct_403_is_reported_as_failed_request(self):
        response = Mock(status_code=403, headers={"server": "Cloudflare"})
        session = Mock()
        session.return_value.get.return_value = response
        host = "blocked.example"

        with (
            patch.object(scraper, "allowed", return_value=True),
            patch.object(scraper, "ensure_fallback_proxies"),
            patch.object(scraper, "throttle"),
            patch.object(scraper, "session", session),
            patch.object(scraper, "proxy_for", return_value=None),
            patch.object(scraper, "report_proxy") as report_proxy,
            patch.object(scraper, "_proxies", []),
            patch.object(scraper, "_proxy_hosts", set()),
        ):
            stats = Counter()
            result = scraper.get(f"https://{host}/", stats=stats, retries=5)

        self.assertIsNone(result)
        session.return_value.get.assert_called_once()
        report_proxy.assert_not_called()
        self.assertEqual(stats["http_403"], 1)
        self.assertEqual(stats["nieudane"], 1)

    def test_403_rotates_through_all_configured_proxies(self):
        proxies = [f"socks5://proxy{index}:1080" for index in range(9)]
        responses = [Mock(status_code=403, headers={"server": "Cloudflare"}) for _ in range(8)]
        responses.append(Mock(status_code=200, headers={}))
        session = Mock()
        session.return_value.get.side_effect = responses
        host = "blocked.example"

        with (
            patch.object(scraper, "allowed", return_value=True),
            patch.object(scraper, "ensure_fallback_proxies"),
            patch.object(scraper, "throttle"),
            patch.object(scraper, "session", session),
            patch.object(scraper, "_proxies", proxies),
            patch.object(scraper, "_proxy_hosts", {host}),
            patch.object(scraper, "_free_proxies", set()),
            patch.object(scraper, "_proxy_dead", {}),
            patch.object(scraper, "_proxy_fail", Counter()),
            patch.object(scraper, "_proxy_strikes", Counter()),
            patch.object(scraper, "_proxy_i", 0),
        ):
            result = scraper.get(f"https://{host}/", retries=3)

        self.assertEqual(result.status_code, 200)
        requests = session.return_value.get.call_args_list
        self.assertEqual(len(requests), 9)
        attempted = [request.kwargs["proxies"]["https"] for request in requests]
        self.assertEqual(len(set(attempted[:8])), 8)
        self.assertNotIn(attempted[-1], attempted[:8])

    def test_reported_403_stores_keep_proxy_and_browser_ua_fallback(self):
        names = {
            "pironet", "funke-store", "pirozone", "sklepzpetardami", "biegun",
        }

        for name in names:
            with self.subTest(shop=name):
                site = scraper.SITES[name]
                self.assertTrue(site.get("use_proxy"))
                self.assertTrue(site.get("browser_ua"))
                self.assertIn("User-Agent", scraper.site_headers(name, site) or {})

        targets = {urlparse(url).netloc for url, _headers in scraper.free_proxy_targets(names)}
        self.assertEqual(targets, {
            "pironet.pl",
            "funke-store.com",
            "pirozone.pl",
            "sklepzpetardami.pl",
            "fajerwerkibiegun.pl",
        })


class BiegunCurrencyTests(unittest.TestCase):
    def test_get_preserves_original_category_url_without_currency_overrides(self):
        response = Mock(
            status_code=200,
            headers={"Content-Type": "text/html"},
            content=b'<html><body class="currency-eur"></body></html>',
            url="https://fajerwerkibiegun.pl/pl/items?page=2",
        )
        session = Mock()
        session.return_value.get.return_value = response
        url = "https://fajerwerkibiegun.pl/pl/items?page=2"
        with (
            patch.object(scraper, "allowed", return_value=True),
            patch.object(scraper, "ensure_fallback_proxies"),
            patch.object(scraper, "throttle"),
            patch.object(scraper, "session", session),
            patch.object(scraper, "_proxies", []),
            patch.object(scraper, "proxy_for", return_value=None),
        ):
            result = scraper.get(url, retries=1)

        self.assertIs(result, response)
        self.assertEqual(session.return_value.get.call_args.args[0], url)


class StoreApiTests(unittest.TestCase):
    def test_only_verified_store_apis_are_enabled(self):
        expected = {
            "pyroking",
            "hurtowniaas",
            "pirozone",
            "firefactory",
            "obornicka",
            "pironet",
            "piroart",
            "petardyshop",
            "funke-store",
            "funkezone",
            "pirotechnika.net",
            "wybuchy",
        }
        configured = {
            name for name, site in scraper.SITES.items()
            if site.get("store_api") and site.get("mode") == "api"
        }

        self.assertEqual(configured, expected)

    def test_new_listing_stores_parse_verified_product_cards(self):
        examples = {
            "biegun": (
                """<article class="product-miniature">
                  <h3 class="product-title"><a href="/produkt/test.html">Test Biegun</a></h3>
                  <span class="product-price">14,40 zł</span>
                  <button class="add-to-cart">Dodaj do koszyka</button>
                </article>""",
                "https://fajerwerkibiegun.pl/pl/3-wyrzutnie",
                14.4,
            ),
            "fajerwerkimarket": (
                """<div class="product">
                  <a class="product_name" href="/test.html">Test Market</a>
                  <div class="info-right"><div class="price">52,00 zł / szt.</div>
                    <a class="basket_add_link" href="/basket/add/1/1">Do koszyka</a>
                  </div>
                </div>""",
                "https://www.fajerwerkimarket.pl/category/petardy",
                52.0,
            ),
            "taniefajerwerki": (
                """<li class="product"><a href="/produkt/test/1">
                  <h3 class="kw-details-title">Test Tanie</h3>
                  <div class="price"><ins><span class="amount">1,19 zł</span></ins></div>
                </a><button class="btn-buy">Do koszyka</button></li>""",
                "https://taniefajerwerki.pl/kategoria/petardy/65",
                1.19,
            ),
        }

        for shop, (html, page_url, expected_price) in examples.items():
            with self.subTest(shop=shop):
                count, products = scraper.parse_listing(
                    html, page_url, scraper.SITES[shop]["listing"]
                )
                self.assertEqual(count, 1)
                self.assertEqual(len(products), 1)
                self.assertEqual(products[0]["price"], expected_price)
                self.assertEqual(products[0]["availability"], "in_stock")

    def test_vitis_and_ultrasstore_listing_cards_parse_with_correct_currency(self):
        examples = {
            "vitis": (
                """<article class="product-miniature">
                  <span class="product-title"><a href="/pl/produkt/test.html">Test Vitis</a></span>
                  <span class="price">14,00 zł</span>
                  <span class="availability-list availability-list-in-stock">na stanie</span>
                </article>""",
                "https://fajerwerkiopole.pl/pl/3-petardy-hukowe",
                14.0,
                "PLN",
            ),
            "ultrasstore": (
                """<article class="product-miniature">
                  <h3 class="product-title"><a href="/pl/petardy/1-test.html">Test Ultras</a></h3>
                  <span class="price">10,62 zł</span>
                  <button class="an_productattributes-add-to-cart-btn">Do koszyka</button>
                </article>""",
                "https://ultrasstore.com/pl/62-petardy",
                10.62,
                "PLN",
            ),
        }

        for shop, (html, page_url, expected_price, expected_currency) in examples.items():
            with self.subTest(shop=shop):
                cfg = scraper.SITES[shop]["listing"]
                if shop == "ultrasstore":
                    cfg = {**cfg, "currency": expected_currency}
                count, products = scraper.parse_listing(html, page_url, cfg)
                self.assertEqual(count, 1)
                self.assertEqual(len(products), 1)
                self.assertEqual(products[0]["price"], expected_price)
                self.assertEqual(products[0]["currency"], expected_currency)
                self.assertEqual(products[0]["availability"], "in_stock")

    def test_vitis_and_ultrasstore_are_enabled_for_full_scrapes(self):
        self.assertFalse(scraper.SITES["ultrasstore"].get("skip", False))
        self.assertFalse(scraper.SITES["vitis"].get("skip", False))

    def test_sitemap_shop_product_filters_are_configured(self):
        self.assertIn("pirolux", scraper.SITES)
        self.assertIn("https://pirolux.com.pl/sitemap-produkty.xml",
                      scraper.SITES["pirolux"]["sitemaps"])
        self.assertIn("https://piroshop.pl/1_pl_0_sitemap.xml",
                      scraper.SITES["piroshop"]["sitemaps"])

    def test_parses_store_api_minor_units_and_availability(self):
        product = scraper.parse_store_api_product({
            "name": "P20 Petardy Explosive &#8211; 10 szt.",
            "permalink": "https://piroart.pl/shop/p20/",
            "sku": "4412",
            "prices": {
                "price": "1410",
                "currency_code": "PLN",
                "currency_minor_unit": 2,
            },
            "is_in_stock": False,
        })

        self.assertEqual(product["name"], "P20 Petardy Explosive – 10 szt.")
        self.assertEqual(product["price"], 14.1)
        self.assertEqual(product["currency"], "PLN")
        self.assertEqual(product["code_raw"], "4412")
        self.assertEqual(product["availability"], "out_of_stock")

    def test_store_api_detects_sale_price_from_regular_price(self):
        product = scraper.parse_store_api_product({
            "name": "Promocyjny produkt",
            "permalink": "https://piroart.pl/shop/promo/",
            "prices": {
                "price": "14900", "regular_price": "19900", "sale_price": "14900",
                "currency_code": "PLN", "currency_minor_unit": 2,
            },
            "is_in_stock": True,
        })

        self.assertEqual(product["price"], 149.0)
        self.assertEqual(product["promo"], 1)

    def test_driver_paginates_until_api_returns_partial_page(self):
        site = {
            "base": "https://example.test",
            "store_api": {
                "endpoint": "https://example.test/wp-json/wc/store/v1/products",
                "per_page": 2,
            },
        }
        pages = [
            [
                {"name": "A", "permalink": "https://example.test/a", "prices": {"price": "100", "currency_minor_unit": 2}},
                {"name": "B", "permalink": "https://example.test/b", "prices": {"price": "200", "currency_minor_unit": 2}},
            ],
            [
                {"name": "C", "permalink": "https://example.test/c", "prices": {"price": "300", "currency_minor_unit": 2}},
            ],
        ]
        responses = [Mock() for _ in pages]
        for response, payload in zip(responses, pages):
            response.json.return_value = payload
        args, events, stats = SimpleNamespace(max=None), queue.Queue(), Counter()

        with patch.object(scraper, "get", side_effect=responses) as get:
            scraper.store_api_driver("example", site, args, events, stats)

        page_events = [events.get_nowait(), events.get_nowait(), events.get_nowait()]
        self.assertEqual([event[0] for event in page_events], ["api_page", "api_page", "api_done"])
        self.assertEqual(page_events[-1][2:5], (2, 3, None))
        self.assertEqual(get.call_count, 2)
        first_params = parse_qs(urlparse(get.call_args_list[0].args[0]).query)
        second_params = parse_qs(urlparse(get.call_args_list[1].args[0]).query)
        self.assertEqual(first_params["page"], ["1"])
        self.assertEqual(second_params["page"], ["2"])
        self.assertEqual(first_params["per_page"], ["2"])

    def test_runner_saves_products_from_api_pages(self):
        product = {
            "name": "Produkt API",
            "url": "https://piroart.pl/shop/produkt-api/",
            "price": 12.34,
            "availability": "in_stock",
        }

        def send_page(name, site, args, events, stats):
            events.put(("api_page", name, 1, [product]))
            events.put(("api_done", name, 1, 1, None))

        connection = sqlite3.connect(":memory:")
        try:
            with (
                patch.object(scraper, "store_api_driver", side_effect=send_page),
                patch.object(scraper, "save", return_value=True) as save,
            ):
                result = scraper.run_store_api(
                    connection, ["piroart"], SimpleNamespace(max=None)
                )

            save.assert_called_once_with(connection, "piroart", product["url"], product)
            self.assertEqual(result[0][0:2], ("piroart", 1))
            self.assertEqual(result[0][2]["produkty"], 1)
            self.assertEqual(result[0][2]["zmiany_w_historii"], 1)
        finally:
            connection.close()


class ScanHistoryTests(unittest.TestCase):
    def test_database_migrates_scan_tracking_and_saves_scan_ids(self):
        with tempfile.TemporaryDirectory() as temp_dir:
            db_path = str(Path(temp_dir) / "prices.db")
            old_db = sqlite3.connect(db_path)
            old_db.executescript("""
                CREATE TABLE products(
                    url TEXT PRIMARY KEY,site TEXT,name TEXT,code TEXT,code_key TEXT,
                    first_seen TEXT,last_seen TEXT
                );
                CREATE TABLE prices(
                    id INTEGER PRIMARY KEY AUTOINCREMENT,url TEXT,ts TEXT,
                    price REAL,currency TEXT,availability TEXT
                );
                CREATE TABLE meta(k TEXT PRIMARY KEY,v TEXT);
                INSERT INTO meta VALUES('parser_version','2');
            """)
            old_db.close()
            with patch.object(scraper, "DB_PATH", db_path):
                connection = scraper.db()
                try:
                    columns = {row[1] for row in connection.execute("PRAGMA table_info(prices)")}
                    self.assertIn("scan_id", columns)
                    product_columns = {
                        row[1] for row in connection.execute("PRAGMA table_info(products)")
                    }
                    self.assertIn("promo", product_columns)
                    cursor = connection.execute(
                        "INSERT INTO scrape_runs(site,started_at,status) VALUES('shop','2026-10-31','running')"
                    )
                    scan_id = cursor.lastrowid
                    scraper._active_scan_ids["shop"] = scan_id
                    scraper.save(connection, "shop", "https://shop.example/item", {
                        "name": "Produkt test", "price": 12.5, "availability": "in_stock",
                        "currency": "PLN", "promo": 1,
                    })
                    connection.commit()
                    self.assertEqual(
                        connection.execute("SELECT scan_id FROM prices").fetchone()[0],
                        scan_id,
                    )
                    self.assertEqual(
                        connection.execute("SELECT products_checked FROM scrape_runs").fetchone()[0],
                        1,
                    )
                    self.assertEqual(
                        connection.execute("SELECT promo FROM products").fetchone()[0],
                        1,
                    )
                finally:
                    scraper._active_scan_ids.pop("shop", None)
                    connection.close()


if __name__ == "__main__":
    unittest.main()
