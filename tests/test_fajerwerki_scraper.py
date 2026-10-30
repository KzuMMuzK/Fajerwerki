import unittest
import queue
import sqlite3
from collections import Counter
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


if __name__ == "__main__":
    unittest.main()
