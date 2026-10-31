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
            patch.object(scraper, "_on_403_detected"),
            patch.object(scraper, "_proxies", []),
            patch.object(scraper, "_proxy_hosts", set()),
        ):
            result = scraper.get(f"https://{host}/", retries=5)

        self.assertIsNone(result)
        session.return_value.get.assert_called_once()
        report_proxy.assert_not_called()


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
                    cursor = connection.execute(
                        "INSERT INTO scrape_runs(site,started_at,status) VALUES('shop','2026-10-31','running')"
                    )
                    scan_id = cursor.lastrowid
                    scraper._active_scan_ids["shop"] = scan_id
                    scraper.save(connection, "shop", "https://shop.example/item", {
                        "name": "Produkt test", "price": 12.5, "availability": "in_stock",
                        "currency": "PLN",
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
                finally:
                    scraper._active_scan_ids.pop("shop", None)
                    connection.close()


if __name__ == "__main__":
    unittest.main()
