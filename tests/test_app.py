# import io
# import os
# import sqlite3
# import tempfile
# import unittest
# from unittest.mock import patch

# from PIL import Image
# from werkzeug.datastructures import FileStorage

# import app as price_app


# class ProductDeduplicationTests(unittest.TestCase):
#     def test_collapses_identical_offers_but_keeps_distinct_prices(self):
#         older = (
#             "https://shop.example/item-2", "shop", "  Produkt   Test ", "SKU1", "SKU1",
#             "2026-10-01", "2026-10-10", 10.0, "in_stock", "2026-10-10", "PLN",
#             None, None, 10.0, 10.0, 1,
#         )
#         newer = (
#             "https://shop.example/item", "shop", "produkt test", "SKU1", "SKU1",
#             "2026-10-01", "2026-10-11", 10.0, "in_stock", "2026-10-10", "PLN",
#             None, None, 10.0, 10.0, 1,
#         )
#         different_price = (
#             "https://shop.example/item-sale", "shop", "Produkt Test", "SKU1", "SKU1",
#             "2026-10-01", "2026-10-11", 9.0, "in_stock", "2026-10-11", "PLN",
#             None, None, 9.0, 9.0, 1,
#         )
#         older_minimum = (
#             "https://shop.example/alias", "shop", "Produkt Test", "SKU1", "SKU1",
#             "2026-10-01", "2026-10-09", 10.0, "in_stock", "2026-10-09", "PLN",
#             None, None, 4.0, 14.0, 1,
#         )

#         rows = price_app._deduplicate_product_rows(
#             [older, newer, older_minimum, different_price]
#         )

#         self.assertEqual(len(rows), 2)
#         representative = next(row for row in rows if row[7] == 10.0)
#         self.assertEqual(representative[0], newer[0])
#         self.assertEqual(representative[13:15], (4.0, 14.0))
#         self.assertIn(different_price, rows)
#         self.assertNotIn(older, rows)

#     def test_promotion_status_is_preserved_when_duplicate_rows_are_merged(self):
#         unknown = (
#             "https://shop.example/item", "shop", "Produkt", "SKU1", "SKU1",
#             "2026-10-01", "2026-10-11", 10.0, "in_stock", "2026-10-11", "PLN",
#             None, None, 10.0, 10.0, 1, None,
#         )
#         promoted = (*unknown[:6], "2026-10-10", *unknown[7:16], 1)

#         rows = price_app._deduplicate_product_rows([unknown, promoted])

#         self.assertEqual(len(rows), 1)
#         self.assertEqual(rows[0][16], 1)


# class ComparisonAndBasketTests(unittest.TestCase):
#     def setUp(self):
#         price_app.app.secret_key = "test-secret"
#         store_read = patch.object(
#             price_app.store, "read", side_effect=lambda callback: callback({"coupons": {}})
#         )
#         store_read.start()
#         self.addCleanup(store_read.stop)
#         self.connection = sqlite3.connect(":memory:")
#         self.connection.row_factory = sqlite3.Row
#         self.connection.execute("""
#             CREATE TABLE items(
#                 url TEXT, site TEXT, name TEXT, name_norm TEXT, code TEXT, code_key TEXT,
#                 first_seen TEXT, last_seen TEXT, price REAL, avail TEXT, changed_at TEXT,
#                 currency TEXT, prev_price REAL, prev_avail TEXT, min_price REAL, max_price REAL,
#                 n_changes INTEGER, drop_pct REAL, key_shops INTEGER, key_min REAL,
#                 o_name TEXT, o_price REAL, o_avail TEXT, o_code TEXT, o_key TEXT, o_prev REAL,
#                 o_drop REAL, hidden INTEGER, rank INTEGER, note TEXT, edited INTEGER,
#                 promo INTEGER
#             )
#         """)
#         self.connection.execute("CREATE TABLE meta(k TEXT, v TEXT)")
#         self._insert("a-x", "alpha", "Produkt X", "SKU123", 10)
#         self._insert("a-x-duplicate", "alpha", "Produkt X", "SKU123", 5)
#         self._insert("b-x", "beta", "Produkt X", "SKU123", 4)
#         self._insert("a-y", "alpha", "Produkt Y", "SKU456", 3)
#         self._insert("b-y", "beta", "Produkt Y", "SKU456", 9)

#     def tearDown(self):
#         self.connection.close()

#     def _insert(self, suffix, site, name, code, price, availability="in_stock", min_price=None):
#         if min_price is None:
#             min_price = price
#         self.connection.execute(
#             """INSERT INTO items(
#                 url, site, name, name_norm, code, code_key, price, avail, changed_at,
#                 currency, key_shops, key_min, hidden, min_price
#             ) VALUES(?, ?, ?, ?, ?, ?, ?, ?, '2026-10-30T12:00:00+00:00',
#                      'PLN', 2, ?, 0, ?)""",
#             (f"https://{site}.example/{suffix}", site, name, name.lower(), code, code,
#              price, availability, price, min_price),
#         )
#         self.connection.commit()

#     def test_comparison_keeps_only_the_best_offer_per_shop(self):
#         with price_app.app.test_request_context("/compare?k=sku123"):
#             price_app.g.user = None
#             with patch.object(price_app, "conn", return_value=self.connection), \
#                     patch.object(price_app, "render_template", return_value="rendered") as render:
#                 result = price_app.compare()

#         self.assertEqual(result, "rendered")
#         rows = render.call_args.kwargs["rows"]
#         self.assertEqual({row["site"] for row in rows}, {"alpha", "beta"})
#         self.assertEqual(len(rows), 2)
#         self.assertEqual({row["site"]: row["price"] for row in rows}, {"alpha": 5, "beta": 4})

#     def test_deals_aggregate_one_offer_per_shop_before_comparing(self):
#         self._insert("c-x", "gamma", "Produkt X", "SKU123", 20)
#         with price_app.app.test_request_context("/deals"):
#             price_app.g.user = None
#             with patch.object(price_app, "conn", return_value=self.connection), \
#                     patch.object(price_app, "render_template", return_value="rendered") as render:
#                 result = price_app.deals()

#         self.assertEqual(result, "rendered")
#         deals = render.call_args.kwargs["rows"]
#         deal = next(row for row in deals if row["code_key"] == "SKU123")
#         self.assertEqual(deal["n_avail"], 3)
#         self.assertEqual(deal["pmin"], 4)
#         self.assertEqual(deal["pmax"], 20)

#     def test_deals_filter_search_and_savings(self):
#         self._insert("c-x", "gamma", "Produkt X", "SKU123", 20)
#         with price_app.app.test_request_context(
#             "/deals?q=SKU123&ms=10&shops=2&saving=10&sort=amount&page=1"
#         ):
#             price_app.g.user = None
#             with patch.object(price_app, "conn", return_value=self.connection), \
#                     patch.object(price_app, "render_template", wraps=price_app.render_template) as render:
#                 result = price_app.deals()

#         self.assertIn("Okazje", result)
#         self.assertIn("80.0% taniej", result)
#         context = render.call_args.kwargs
#         self.assertEqual(context["total"], 1)
#         self.assertEqual(context["query"], "SKU123")
#         self.assertEqual(context["sort"], "amount")
#         self.assertEqual(context["rows"][0]["saving"], 16)
#         self.assertEqual(context["rows"][0]["saving_pct"], 80)

#     def test_basket_route_renders_historical_and_unavailable_options(self):
#         self._insert("available-z", "alpha", "Produkt Z", "SKU999", 20, min_price=5)
#         self._insert("unavailable-z", "beta", "Produkt Z", "SKU999", 3,
#                      availability="out_of_stock", min_price=2)
#         price_app.app.secret_key = "test-secret"
#         with price_app.app.test_request_context(
#             "/basket?products=SKU999&price_mode=historical&unavailable=1"
#         ):
#             price_app.g.user = None
#             with patch.object(price_app, "conn", return_value=self.connection):
#                 result = price_app.basket()

#         self.assertIn("Najniższe historyczne", result)
#         self.assertIn("Uwzględnij produkty obecnie niedostępne", result)
#         self.assertIn("2,00", result)

#     def test_product_search_returns_refreshable_results_fragment(self):
#         with price_app.app.test_request_context("/?q=Produkt&_partial=1"):
#             price_app.g.user = None
#             with patch.object(price_app, "conn", return_value=self.connection):
#                 result = price_app.index()

#         self.assertIn('id="product-results"', result)
#         self.assertIn("Produkt X", result)
#         self.assertNotIn("<!doctype html>", result.lower())

#     def test_product_detail_renders_coupon_controls_near_main_price(self):
#         coupon_data = {"coupons": {
#             "coupon-1": {
#                 "shop": "alpha", "code": "RABAT10", "discount": "10%",
#                 "active": True, "excludes_promos": False,
#             }
#         }}
#         with price_app.app.test_request_context("/p?u=https://alpha.example/a-x"):
#             price_app.g.user = None
#             with (
#                 patch.object(price_app, "conn", return_value=self.connection),
#                 patch.object(price_app, "history", return_value=[]),
#                 patch.object(price_app.store, "read",
#                              side_effect=lambda callback: callback(coupon_data)),
#             ):
#                 result = price_app.product()

#         self.assertIn('data-coupon-shop-group="alpha"', result)
#         self.assertIn('data-store-coupon', result)
#         self.assertIn('data-discount-value="10.0"', result)
#         self.assertIn("Cena jest szacunkowa dla jednej sztuki", result)

#     def test_content_security_policy_allows_same_origin_dynamic_requests(self):
#         response = price_app.app.test_client().get("/health")

#         self.assertIn("connect-src 'self'", response.headers["Content-Security-Policy"])

#     def test_basket_returns_refreshable_results_fragment(self):
#         with price_app.app.test_request_context("/basket?products=SKU123&_partial=1"):
#             price_app.g.user = None
#             with patch.object(price_app, "conn", return_value=self.connection):
#                 result = price_app.basket()

#         self.assertIn('id="basket-results"', result)
#         self.assertIn("Najtańszy miks sklepów", result)
#         self.assertNotIn("<!doctype html>", result.lower())

#     def test_cheapest_filter_uses_available_cross_shop_minimum(self):
#         with price_app.app.test_request_context("/?cheapest=1"):
#             price_app.g.user = None
#             _, where, args = price_app.build_filters()

#         self.assertIn("price = key_min", where)
#         self.assertIn("avail = 'in_stock'", where)
#         self.assertEqual(args, [])

#     def test_basket_finds_best_mix_and_cheapest_complete_shop(self):
#         plan = price_app._plan_basket(self.connection, ["SKU123", "SKU456"], "beta")

#         self.assertEqual(plan["mix_total"], 7)
#         self.assertEqual(plan["mix_missing"], 0)
#         self.assertEqual(plan["best_store"], {"site": "alpha", "total": 8, "missing": 0})
#         self.assertEqual(plan["selected_total"], {"site": "beta", "total": 13, "missing": 0})
#         self.assertEqual([line["cheapest"]["site"] for line in plan["lines"]], ["beta", "alpha"])

#     def test_basket_warns_when_a_code_has_multiple_variants_in_a_shop(self):
#         self._insert("variant-a", "alpha", "Wyrzutnia niebieska", "SKU789", 10)
#         self._insert("variant-b", "alpha", "Wyrzutnia czerwona", "SKU789", 12)

#         _, _, _, warning = price_app._basket_product(self.connection, "sku789")

#         self.assertIn("kilka nazw/wariantów", warning)

#     def test_basket_price_modes_and_unavailable_switch(self):
#         self._insert("available", "alpha", "Produkt Z", "SKU999", 20, min_price=5)
#         self._insert("unavailable", "beta", "Produkt Z", "SKU999", 3,
#                      availability="out_of_stock", min_price=2)

#         _, current, _, _ = price_app._basket_product(self.connection, "SKU999")
#         _, historical, _, _ = price_app._basket_product(
#             self.connection, "SKU999", "historical"
#         )
#         _, historical_all, _, _ = price_app._basket_product(
#             self.connection, "SKU999", "historical", include_unavailable=True
#         )

#         self.assertEqual({offer["site"]: offer["basket_price"] for offer in current},
#                          {"alpha": 20})
#         self.assertEqual({offer["site"]: offer["basket_price"] for offer in historical},
#                          {"alpha": 5})
#         self.assertEqual({offer["site"]: offer["basket_price"] for offer in historical_all},
#                          {"alpha": 5, "beta": 2})

#     def test_basket_route_renders_input_and_calculated_plan(self):
#         price_app.app.secret_key = "test-secret"
#         with price_app.app.test_request_context(
#             "/basket?products=SKU123%0ASKU456&site=beta"
#         ):
#             price_app.g.user = None
#             with patch.object(price_app, "conn", return_value=self.connection), \
#                     patch.object(price_app, "render_template", wraps=price_app.render_template) as render:
#                 result = price_app.basket()

#         self.assertIn("Planer koszyka", result)
#         context = render.call_args.kwargs
#         self.assertEqual(context["selected_site"], "beta")
#         self.assertEqual(context["plan"]["mix_total"], 7)
#         self.assertEqual(context["plan"]["selected_total"]["total"], 13)


# class ChangesFilterTests(unittest.TestCase):
#     def setUp(self):
#         store_read = patch.object(
#             price_app.store, "read", side_effect=lambda callback: callback({"coupons": {}})
#         )
#         store_read.start()
#         self.addCleanup(store_read.stop)
#         connection = sqlite3.connect(":memory:")
#         connection.row_factory = sqlite3.Row
#         connection.executescript("""
#             CREATE TABLE items(
#                 url TEXT, site TEXT, name TEXT, name_norm TEXT, code TEXT, code_key TEXT,
#                 first_seen TEXT, last_seen TEXT, price REAL, avail TEXT, changed_at TEXT,
#                 currency TEXT, prev_price REAL, prev_avail TEXT, min_price REAL, max_price REAL,
#                 n_changes INTEGER, drop_pct REAL, key_shops INTEGER, key_min REAL,
#                 o_name TEXT, o_price REAL, o_avail TEXT, o_code TEXT, o_key TEXT, o_prev REAL,
#                 o_drop REAL, hidden INTEGER, rank INTEGER, note TEXT, edited INTEGER
#             );
#             CREATE TABLE change_events(
#                 url TEXT, site TEXT, name TEXT, name_norm TEXT, code TEXT, code_key TEXT,
#                 ts TEXT, price REAL, availability TEXT, currency TEXT,
#                 prev_price REAL, prev_availability TEXT, scan_id INTEGER
#             );
#             CREATE TABLE scan_options(
#                 scan_id INTEGER PRIMARY KEY, site TEXT, started_at TEXT,
#                 completed_at TEXT, status TEXT
#             );
#             CREATE TABLE meta(k TEXT, v TEXT);
#         """)
#         self.connection = connection
#         self.addCleanup(connection.close)
#         scan_ids = {
#             ("alpha", "2026-10-29"): -1,
#             ("alpha", "2026-10-30"): -2,
#             ("beta", "2026-10-29"): -3,
#             ("beta", "2026-10-30"): -4,
#         }
#         for (site, date), scan_id in scan_ids.items():
#             connection.execute(
#                 """INSERT INTO scan_options(scan_id,site,started_at,completed_at,status)
#                    VALUES(?,?,? || 'T00:00:00+00:00',? || 'T23:59:59+00:00','legacy')""",
#                 (scan_id, site, date, date),
#             )
#         for site in ("alpha", "beta"):
#             url = f"https://{site}.example/item"
#             connection.execute(
#                 """INSERT INTO items(url,site,name,name_norm,code,code_key,price,avail,
#                     changed_at,prev_price,prev_avail,drop_pct,hidden)
#                     VALUES(?,?, 'Produkt X','produkt x','SKU123','SKU123',10,'in_stock',
#                     '2026-10-30T12:00:00+00:00',20,'in_stock',50,0)""",
#                 (url, site),
#             )
#             for date, before, after in (
#                 ("2026-10-29", 25, 20),
#                 ("2026-10-30", 20, 10),
#             ):
#                 connection.execute(
#                     """INSERT INTO change_events(
#                         url,site,name,name_norm,code,code_key,ts,price,availability,currency,
#                         prev_price,prev_availability,scan_id
#                     ) VALUES(?,?, 'Produkt X','produkt x','SKU123','SKU123',?,?,'in_stock',
#                              'PLN',?,'in_stock',?)""",
#                     (url, site, f"{date}T12:00:00+00:00", after, before,
#                      scan_ids[(site, date)]),
#                 )
#         connection.commit()

#     def test_last_scan_filter_is_scoped_to_selected_shop(self):
#         with price_app.app.test_request_context(
#             "/changes?site=alpha&t=drops&scan_mode=last&scan=-2"
#         ):
#             price_app.g.user = None
#             with (
#                 patch.object(price_app, "conn", return_value=self.connection),
#                 patch.object(price_app, "render_template", return_value="rendered") as render,
#             ):
#                 result = price_app.changes()

#         self.assertEqual(result, "rendered")
#         context = render.call_args.kwargs
#         self.assertEqual(context["site"], "alpha")
#         self.assertEqual(context["counts"]["drops"], 1)
#         self.assertEqual([row["site"] for row in context["rows"]], ["alpha"])
#         self.assertEqual(len(context["rows"]), 1)

#     def test_change_events_are_paginated_after_filters(self):
#         for index in range(205):
#             url = f"https://alpha.example/change-{index}"
#             self.connection.execute(
#                 """INSERT INTO items(url,site,name,name_norm,hidden)
#                    VALUES(?, 'alpha', ?, ?, 0)""",
#                 (url, f"Zmiana {index}", f"zmiana {index}"),
#             )
#             self.connection.execute(
#                 """INSERT INTO change_events(
#                     url,site,name,name_norm,ts,price,availability,prev_price,
#                     prev_availability,scan_id
#                 ) VALUES(?, 'alpha', ?, ?, '2026-10-30T12:00:00+00:00',
#                          1, 'in_stock', ?, 'in_stock', -2)""",
#                 (url, f"Zmiana {index}", f"zmiana {index}", 1000 + index),
#             )
#         self.connection.commit()

#         with price_app.app.test_request_context(
#             "/changes?site=alpha&t=drops&scan_mode=last&scan=-2&page=2"
#         ):
#             price_app.g.user = None
#             with (
#                 patch.object(price_app, "conn", return_value=self.connection),
#                 patch.object(price_app, "render_template", return_value="rendered") as render,
#             ):
#                 result = price_app.changes()

#         self.assertEqual(result, "rendered")
#         context = render.call_args.kwargs
#         self.assertEqual(context["total"], 206)
#         self.assertEqual(context["page"], 2)
#         self.assertEqual(context["pages"], 5)
#         self.assertEqual(len(context["rows"]), 50)
#         self.assertEqual(context["rows"][0]["name"], "Zmiana 154")
#         self.assertEqual(context["rows"][-1]["name"], "Zmiana 105")

#     def test_date_range_filters_events_inclusive_of_both_dates(self):
#         with price_app.app.test_request_context(
#             "/changes?site=alpha&scan_mode=range&date_from=2026-10-29&date_to=2026-10-30"
#         ):
#             price_app.g.user = None
#             with (
#                 patch.object(price_app, "conn", return_value=self.connection),
#                 patch.object(price_app, "render_template", return_value="rendered") as render,
#             ):
#                 result = price_app.changes()

#         self.assertEqual(result, "rendered")
#         context = render.call_args.kwargs
#         self.assertEqual(context["counts"]["drops"], 2)
#         self.assertEqual(len(context["rows"]), 2)
#         self.assertEqual(
#             {row["changed_at"][:10] for row in context["rows"]},
#             {"2026-10-29", "2026-10-30"},
#         )

#     def test_old_scan_number_parameter_does_not_limit_last_scan(self):
#         with price_app.app.test_request_context(
#             "/changes?site=alpha&scan_mode=last&scan=94"
#         ):
#             price_app.g.user = None
#             with (
#                 patch.object(price_app, "conn", return_value=self.connection),
#                 patch.object(price_app, "render_template", return_value="rendered") as render,
#             ):
#                 result = price_app.changes()

#         self.assertEqual(result, "rendered")
#         context = render.call_args.kwargs
#         self.assertEqual(context["counts"]["drops"], 1)
#         self.assertEqual({row["changed_at"][:10] for row in context["rows"]}, {"2026-10-30"})

#     def test_shop_selection_is_rendered_and_preserved_between_tabs(self):
#         price_app.app.secret_key = "test-secret"
#         with price_app.app.test_request_context(
#             "/changes?site=alpha&t=drops&scan_mode=range&date_from=2026-10-29&date_to=2026-10-30"
#         ):
#             price_app.g.user = None
#             html = price_app.render_template(
#                 "changes.html",
#                 rows=[],
#                 shops=[{"site": "alpha"}],
#                 site="alpha",
#                 t="drops",
#                 counts={"drops": 1, "rises": 0, "back": 0, "gone": 0},
#                 page=1,
#                 pages=2,
#                 total=60,
#                 per_page=50,
#                 scan_mode="range",
#                 date_from="2026-10-29",
#                 date_to="2026-10-30",
#                 tab="changes",
#                 last_seen=None,
#                 refresh_error=None,
#             )

#         self.assertIn('value="alpha" selected>alpha</option>', html)
#         self.assertIn("site=alpha", html)
#         self.assertIn(
#             'href="/changes?site=alpha&amp;t=drops&amp;scan_mode=range&amp;date_from=2026-10-29&amp;date_to=2026-10-30&amp;page=2"',
#             html,
#         )
#         self.assertIn("Ostatni skan", html)
#         self.assertIn("Od–do", html)
#         self.assertNotIn("Wybierz skany", html)
#         self.assertNotIn('name="scan"', html)


# class CouponTests(unittest.TestCase):
#     def setUp(self):
#         price_app.app.secret_key = "test-secret"
#         self.data = {"coupons": {}, "audit": []}

#     def _image_upload(self):
#         image = Image.new("RGB", (80, 40), "white")
#         stream = io.BytesIO()
#         image.save(stream, format="PNG")
#         stream.seek(0)
#         return stream, "coupon.png"

#     def test_ocr_code_candidates_are_deduplicated_and_reject_noise(self):
#         self.assertEqual(
#             price_app._coupon_code_candidates("Kod: RABAT20. PROMO_2026 RABAT20 OOOO 10%"),
#             ["RABAT20", "PROMO_2026"],
#         )

#     def test_coupon_percent_and_shop_name_are_normalized_for_price_cards(self):
#         self.assertEqual(price_app._coupon_percent("10% zniżki"), 10)
#         self.assertEqual(price_app._coupon_percent("rabat 10%"), 10)
#         self.assertIsNone(price_app._coupon_percent("10% albo 20%"))
#         self.assertIsNone(price_app._coupon_percent("20 zł rabatu"))
#         self.assertEqual(price_app._coupon_amount("20 zł rabatu"), 20)
#         self.assertIsNone(price_app._coupon_amount("10% do 20 zł"))
#         self.assertEqual(price_app._coupon_shop_key("Fajerwerki Biegun"), "biegun")
#         self.assertEqual(price_app._coupon_shop_key("Biegun"), "biegun")

#     def test_product_card_renders_store_coupon_checkbox_and_estimate(self):
#         item = {
#             "site": "biegun", "hidden": False, "code": None, "promo": None,
#             "rank": None, "note": None, "edited": False, "url": "https://shop.test/item",
#             "name": "Produkt", "price": 100.0, "prev_price": None, "key_shops": 1,
#             "changed_at": "2026-11-02T10:00:00+00:00", "avail": "in_stock",
#         }
#         coupons = {
#             "biegun": [{
#                 "id": "coupon-1", "code": "RABAT10", "discount": "10%",
#                 "percent": 10, "amount": None, "discount_kind": "percent",
#                 "discount_value": 10, "excludes_promos": False,
#             }]
#         }

#         with price_app.app.test_request_context("/"):
#             template = price_app.app.jinja_env.from_string(
#                 "{% from 'card.html' import card with context %}{{ card(it) }}"
#             )
#             result = template.render(
#                 it=item,
#                 coupons_by_shop=coupons,
#                 coupon_shop_key=price_app._coupon_shop_key,
#                 is_admin=False,
#             )

#         self.assertIn('data-store-coupon', result)
#         self.assertIn('data-coupon-id="coupon-1"', result)
#         self.assertIn('data-discount-kind="percent"', result)
#         self.assertIn('data-discount-value="10"', result)
#         self.assertIn("Uwzględnij RABAT10", result)
#         self.assertIn("data-coupon-discounted", result)
#         self.assertIn("data-copy-coupon", result)

#     def test_coupon_rows_include_only_unambiguous_discount_values(self):
#         rows = price_app._coupon_rows({
#             "coupons": {
#                 "percent": {"shop": "Biegun", "code": "RABAT10", "discount": "10%"},
#                 "amount": {"shop": "Biegun", "code": "RABAT20", "discount": "20 zł"},
#                 "ambiguous": {"shop": "Biegun", "code": "RABAT", "discount": "10% lub 20%"},
#             }
#         }, active_only=True)

#         supported = {row["id"]: row for row in rows if row["discount_value"] is not None}
#         self.assertEqual(supported["percent"]["discount_kind"], "percent")
#         self.assertEqual(supported["percent"]["discount_value"], 10)
#         self.assertEqual(supported["amount"]["discount_kind"], "amount")
#         self.assertEqual(supported["amount"]["discount_value"], 20)
#         self.assertIsNone(next(row for row in rows if row["id"] == "ambiguous")["discount_value"])

#     def test_coupon_image_is_normalized_and_rejects_non_images(self):
#         image = Image.new("RGB", (80, 40), "white")
#         stream = io.BytesIO()
#         image.save(stream, format="PNG")
#         stream.seek(0)
#         normalized = price_app._coupon_image(FileStorage(stream=stream, filename="coupon.png"))
#         self.assertTrue(normalized.startswith(b"\xff\xd8"))
#         with self.assertRaisesRegex(ValueError, "Nie udało się odczytać"):
#             price_app._coupon_image(FileStorage(stream=io.BytesIO(b"not an image"), filename="bad.png"))

#     def test_admin_can_save_image_source_and_publish_coupon(self):
#         image_stream, filename = self._image_upload()
#         with price_app.app.test_request_context(
#             "/admin/coupons",
#             method="POST",
#             data={
#                 "shop": "Sklep", "code": "RABAT20", "discount": "20% zniżki",
#                 "terms": "Od 100 zł", "valid_until": "", "source": "",
#                 "excludes_promos": "1",
#                 "image": (image_stream, filename),
#             },
#             content_type="multipart/form-data",
#         ):
#             price_app.g.user = {"id": "admin", "role": "admin"}
#             with patch.object(price_app.store, "update", side_effect=lambda fn, _message: fn(self.data)):
#                 response = price_app.admin_coupons()

#         self.assertEqual(response.status_code, 302)
#         coupon = next(iter(self.data["coupons"].values()))
#         self.assertEqual(coupon["code"], "RABAT20")
#         self.assertTrue(coupon["image"])
#         self.assertTrue(coupon["active"])
#         self.assertTrue(coupon["excludes_promos"])
#         self.assertEqual(self.data["audit"][0]["action"], "coupon_add")

#     def test_ocr_endpoint_returns_text_and_code_suggestions(self):
#         image_stream, filename = self._image_upload()
#         with price_app.app.test_request_context(
#             "/admin/coupons/ocr",
#             method="POST",
#             data={"image": (image_stream, filename)},
#             content_type="multipart/form-data",
#         ):
#             price_app.g.user = {"id": "admin", "role": "admin"}
#             with patch.object(price_app.pytesseract, "image_to_string", return_value="Kod RABAT20") as ocr:
#                 response = price_app.admin_coupon_ocr()

#         payload = response.get_json()
#         self.assertEqual(payload["codes"], ["RABAT20"])
#         self.assertEqual(payload["text"], "Kod RABAT20")
#         ocr.assert_called_once()

#     def test_coupon_listing_hides_expired_and_inactive_coupons(self):
#         self.data["coupons"] = {
#             "active": {"shop": "Sklep", "code": "NOWY20", "discount": "20%",
#                        "valid_until": "", "active": True, "created": "2026-10-30"},
#             "expired": {"shop": "Sklep", "code": "STARY20", "discount": "20%",
#                         "valid_until": "2020-01-01", "active": True},
#             "inactive": {"shop": "Sklep", "code": "STOP20", "discount": "20%",
#                          "valid_until": "", "active": False},
#         }
#         with price_app.app.test_request_context("/coupons"):
#             price_app.g.user = {"id": "member"}
#             with patch.object(price_app.store, "read", side_effect=lambda fn: fn(self.data)):
#                 result = price_app.coupons()

#         self.assertIn("NOWY20", result)
#         self.assertNotIn("STARY20", result)
#         self.assertNotIn("STOP20", result)
#         self.assertIn("brak etykiety nie potwierdza", result)

#     def test_admin_coupon_page_renders_upload_and_ocr_controls(self):
#         with price_app.app.test_request_context("/admin/coupons"):
#             price_app.g.user = {"id": "admin", "role": "admin"}
#             with patch.object(price_app.store, "read", side_effect=lambda fn: fn(self.data)):
#                 result = price_app.admin_coupons()

#         self.assertIn('enctype="multipart/form-data"', result)
#         self.assertIn("Odczytaj tekst ze zdjęcia", result)
#         self.assertIn("/admin/coupons/ocr", result)

#     def test_derived_database_keeps_scraped_promotion_status(self):
#         with tempfile.TemporaryDirectory() as temp_dir:
#             src = os.path.join(temp_dir, "source.db")
#             dst = os.path.join(temp_dir, "derived.db")
#             connection = sqlite3.connect(src)
#             connection.executescript("""
#                 CREATE TABLE products(
#                     url TEXT, site TEXT, name TEXT, code TEXT, code_key TEXT,
#                     first_seen TEXT, last_seen TEXT, promo INTEGER
#                 );
#                 CREATE TABLE prices(
#                     id INTEGER PRIMARY KEY, url TEXT, ts TEXT, price REAL,
#                     currency TEXT, availability TEXT, scan_id INTEGER
#                 );
#                 INSERT INTO products VALUES(
#                     'https://shop.example/item','shop','Produkt','SKU1','SKU1',
#                     '2026-10-01','2026-10-02',1
#                 );
#                 INSERT INTO prices VALUES
#                     (1,'https://shop.example/item','2026-10-01T10:00:00Z',20,'PLN','in_stock',1),
#                     (2,'https://shop.example/item','2026-10-02T10:00:00Z',10,'PLN','in_stock',2);
#             """)
#             connection.close()

#             with patch.object(price_app.store, "read", side_effect=RuntimeError("test")):
#                 price_app._build_derived(src, dst)

#             connection = sqlite3.connect(dst)
#             try:
#                 self.assertEqual(connection.execute("SELECT promo FROM items").fetchone()[0], 1)
#             finally:
#                 connection.close()


# if __name__ == "__main__":
#     unittest.main()
