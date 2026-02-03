# dvd_vhs_tracker.py
# Single-file Tkinter + SQLite DVD/VHS POS with:
# - Inventory, formats, coupons, discounts (line + order), taxes
# - Cart with inline qty/line-discount editing
# - Sales + receipt storage, TXT/PDF export (PDF via reportlab if installed)
# - Returns/refunds (restock inventory)
# - Reports: daily/monthly, top titles/customers, by format, tax export
# - Users + roles (admin/clerk), store/receipt settings, backup/restore
# - Add Title dialog supports scanning:
#     * UPC/EAN barcode -> auto lookup title/studio (UPCItemDB trial, needs internet)
#     * Price-only sticker (digits like 1299) -> parse price
#
# NOTE:
# - If you have an existing old DB schema, this file includes a best-effort migration
#   for an older sales schema that had sales.book_id. If migration cannot be applied,
#   you may need to delete dvd_vhs_tracker.db and re-run.
#
# Tested for logical correctness, but I cannot run this on your machine.

import os
import re
import csv
import json
import shutil
import sqlite3
import hashlib
import hmac
import secrets
import time
import urllib.error
import urllib.request
import urllib.parse
import tkinter as tk
from tkinter import ttk, messagebox, filedialog
from datetime import datetime, date, timedelta
from typing import Optional, Dict, Any, List, Tuple


DB_PATH = "dvd_vhs_tracker.db"
USER_AGENT = "DVDVHSPOS/1.0 (+https://openai.com)"


# -------------------------- Money helpers (integer cents) --------------------------
def dollars_to_cents(s: str) -> int:
    s = (s or "").strip()
    if not s:
        raise ValueError("empty")
    if s.startswith("$"):
        s = s[1:].strip()
    if s.count(".") > 1:
        raise ValueError("bad format")
    if "." in s:
        left, right = s.split(".", 1)
        left = left.strip() or "0"
        right = (right.strip() + "00")[:2]
    else:
        left, right = s, "00"
    if not left.isdigit() or not right.isdigit():
        raise ValueError("bad digits")
    return int(left) * 100 + int(right)


def cents_to_money(cents: int) -> str:
    return f"${cents / 100:,.2f}"


def now_ts() -> str:
    return datetime.now().strftime("%Y-%m-%d %H:%M:%S")


def today_ymd() -> str:
    return date.today().strftime("%Y-%m-%d")


# -------------------------- Password hashing (PBKDF2) --------------------------
def pbkdf2_hash(password: str, salt: Optional[bytes] = None) -> Tuple[bytes, bytes]:
    if salt is None:
        salt = secrets.token_bytes(16)
    dk = hashlib.pbkdf2_hmac("sha256", password.encode("utf-8"), salt, 200_000)
    return salt, dk


def pbkdf2_verify(password: str, salt: bytes, digest: bytes) -> bool:
    dk = hashlib.pbkdf2_hmac("sha256", password.encode("utf-8"), salt, 200_000)
    return hmac.compare_digest(dk, digest)


# -------------------------- PDF receipts (optional) --------------------------
def export_pdf_text(text: str, path: str, title: str = "Receipt") -> None:
    try:
        from reportlab.lib.pagesizes import letter
        from reportlab.pdfgen import canvas
    except Exception as e:
        raise RuntimeError("reportlab not installed") from e

    c = canvas.Canvas(path, pagesize=letter)
    w, h = letter
    c.setTitle(title)

    x, y = 50, h - 50
    line_h = 12

    for line in text.splitlines():
        if y < 50:
            c.showPage()
            y = h - 50
        c.drawString(x, y, line)
        y -= line_h

    c.save()


# -------------------------- Barcode / scan helpers --------------------------
BARCODE_RE = re.compile(r"\d{8,14}")

def normalize_barcode(raw: str) -> Optional[str]:
    """
    Normalize any scan containing a UPC/EAN-style barcode.
    - Extracts the first 8-14 digit run
    Returns the barcode string or None if not found.
    """
    if not raw:
        return None
    s = raw.strip()
    if s.isdigit() and 8 <= len(s) <= 14:
        return s
    match = BARCODE_RE.search(s)
    if match:
        return match.group(0)
    return None

def parse_price_from_scan(raw: str) -> Optional[str]:
    """
    Parse a price from a scan string (heuristics).
    Supports:
      - "$12.99" or "12.99"
      - digits-only like "1299" => $12.99 (treat as cents)
    """
    if not raw:
        return None
    s = raw.strip()

    # Direct dollar format
    if re.fullmatch(r"\$?\d+(\.\d{1,2})?", s):
        val = float(s.replace("$", ""))
        return f"{val:.2f}"

    digits = re.sub(r"\D", "", s)
    if not digits:
        return None

    # Price-only stickers often 3-6 digits representing cents
    if 3 <= len(digits) <= 6:
        cents = int(digits)
        return f"{cents / 100:.2f}"

    return None


def parse_scan_barcode_and_price(raw: str) -> Tuple[Optional[str], Optional[str]]:
    """
    Extract barcode and optional price from:
    - UPC/EAN barcode (8-14 digits)
    - Mixed scans that include price stickers
    """
    if not raw:
        return None, None

    digits = re.sub(r"\D", "", raw)
    barcode = normalize_barcode(raw)
    price = None

    # If no price parsed, try price parsing heuristics unless raw is just barcode digits
    if price is None:
        if barcode and digits and digits.isdigit() and len(digits) in (8, 12, 13, 14):
            price = None
        else:
            price = parse_price_from_scan(raw)

    return barcode, price



def fetch_json_with_retry(url: str, timeout: int = 8, retries: int = 2) -> Tuple[Optional[Dict[str, Any]], Optional[str]]:
    last_error = None
    for attempt in range(retries + 1):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
            with urllib.request.urlopen(req, timeout=timeout) as resp:
                return json.loads(resp.read().decode("utf-8")), None
        except urllib.error.HTTPError as err:
            last_error = f"HTTP {err.code}"
            if err.code in (429, 500, 502, 503, 504) and attempt < retries:
                retry_after = err.headers.get("Retry-After")
                try:
                    delay = int(retry_after) if retry_after else 1 + attempt * 2
                except ValueError:
                    delay = 1 + attempt * 2
                time.sleep(delay)
                continue
            return None, last_error
        except Exception:
            last_error = "request failed"
            return None, last_error
    return None, last_error


def fetch_title_info_upcitemdb(barcode: str) -> Optional[Dict[str, str]]:
    """
    Lookup title/studio via UPCItemDB trial API.
    Requires internet access. Returns {"title":..., "studio":...} or None.
    """
    if not barcode:
        return None
    url = "https://api.upcitemdb.com/prod/trial/lookup?" + urllib.parse.urlencode({
        "upc": barcode,
    })
    data, _error = fetch_json_with_retry(url)
    if not data:
        return None

    items = data.get("items") or []
    if not items:
        return None

    item = items[0] or {}
    title = (item.get("title") or "").strip()
    studio = (item.get("brand") or item.get("manufacturer") or "").strip()
    if not title:
        return None
    return {"title": title, "studio": studio}


# -------------------------- DB Layer --------------------------
class DB:
    def __init__(self, path: str = DB_PATH):
        self.path = path
        self._init_db()

    def _connect(self):
        conn = sqlite3.connect(self.path)
        conn.execute("PRAGMA foreign_keys = ON;")
        return conn

    def _table_exists(self, conn, name: str) -> bool:
        cur = conn.cursor()
        cur.execute("SELECT name FROM sqlite_master WHERE type='table' AND name=?;", (name,))
        return cur.fetchone() is not None

    def _columns(self, conn, table: str) -> List[str]:
        cur = conn.cursor()
        cur.execute(f"PRAGMA table_info({table});")
        return [r[1] for r in cur.fetchall()]

    def _try_migrate_old_sales_schema(self, conn) -> None:
        """
        If an old schema exists where sales has book_id (single-item sales),
        migrate to new schema (sales header + sale_items).
        This is best-effort for the known old column set.
        """
        if not self._table_exists(conn, "sales"):
            return
        cols = self._columns(conn, "sales")
        if "book_id" not in cols:
            return  # already new schema

        # Known old columns we expect
        expected = {"id", "created_at", "customer_id", "book_id", "quantity",
                    "unit_price_cents", "subtotal_cents", "tax_rate", "tax_cents",
                    "total_cents", "receipt_text"}
        if not expected.issubset(set(cols)):
            # Unknown old schema; safest is to stop and ask user to reset DB
            raise RuntimeError(
                "Detected an older 'sales' table with book_id but unknown columns. "
                "Please delete dvd_vhs_tracker.db and re-run, or provide your sales schema for a custom migration."
            )

        cur = conn.cursor()

        # Create new tables with temporary names
        cur.execute("""
            CREATE TABLE IF NOT EXISTS sales_new (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                receipt_no TEXT NOT NULL UNIQUE,
                created_at TEXT NOT NULL,
                customer_id INTEGER NOT NULL,
                subtotal_cents INTEGER NOT NULL,
                discount_cents INTEGER NOT NULL DEFAULT 0,
                coupon_code TEXT,
                tax_rate REAL NOT NULL,
                tax_cents INTEGER NOT NULL,
                total_cents INTEGER NOT NULL,
                payment_method TEXT NOT NULL DEFAULT 'cash',
                payment_status TEXT NOT NULL DEFAULT 'paid',
                note TEXT,
                receipt_text TEXT NOT NULL,
                is_void INTEGER NOT NULL DEFAULT 0,
                FOREIGN KEY(customer_id) REFERENCES customers(id) ON DELETE RESTRICT
            );
        """)

        cur.execute("""
            CREATE TABLE IF NOT EXISTS sale_items_new (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                sale_id INTEGER NOT NULL,
                book_id INTEGER NOT NULL,
                quantity INTEGER NOT NULL CHECK(quantity > 0),
                unit_price_cents INTEGER NOT NULL,
                unit_cost_cents INTEGER NOT NULL DEFAULT 0,
                line_subtotal_cents INTEGER NOT NULL,
                line_discount_cents INTEGER NOT NULL DEFAULT 0,
                line_total_cents INTEGER NOT NULL,
                FOREIGN KEY(sale_id) REFERENCES sales_new(id) ON DELETE CASCADE,
                FOREIGN KEY(book_id) REFERENCES books(id) ON DELETE RESTRICT
            );
        """)

        # Copy old sales -> sales_new, create a simple receipt_no sequence
        prefix = "R"
        cur.execute("SELECT IFNULL(MAX(id),0) FROM sales;")
        max_id = int(cur.fetchone()[0])

        cur.execute("""
            SELECT id, created_at, customer_id, book_id, quantity, unit_price_cents,
                   subtotal_cents, tax_rate, tax_cents, total_cents, receipt_text
            FROM sales;
        """)
        rows = cur.fetchall()

        for (sid, created_at, customer_id, book_id, qty, unit_price, subtotal, tax_rate, tax_cents, total, receipt_text) in rows:
            receipt_no = f"{prefix}{int(sid):06d}"
            cur.execute("""
                INSERT INTO sales_new(
                    id, receipt_no, created_at, customer_id,
                    subtotal_cents, discount_cents, coupon_code,
                    tax_rate, tax_cents, total_cents,
                    payment_method, payment_status, note, receipt_text, is_void
                )
                VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,0);
            """, (
                int(sid), receipt_no, created_at, int(customer_id),
                int(subtotal), 0, None,
                float(tax_rate), int(tax_cents), int(total),
                "cash", "paid", "", receipt_text
            ))

            line_sub = int(unit_price) * int(qty)
            line_total = int(subtotal)  # old subtotal was line total for single item
            cur.execute("""
                INSERT INTO sale_items_new(
                    sale_id, book_id, quantity, unit_price_cents, unit_cost_cents,
                    line_subtotal_cents, line_discount_cents, line_total_cents
                )
                VALUES(?,?,?,?,?,?,?,?);
            """, (int(sid), int(book_id), int(qty), int(unit_price), 0, int(line_sub), 0, int(line_total)))

        # Replace old tables
        cur.execute("DROP TABLE sales;")
        cur.execute("ALTER TABLE sales_new RENAME TO sales;")
        cur.execute("ALTER TABLE sale_items_new RENAME TO sale_items;")

        conn.commit()

    def _init_db(self):
        with self._connect() as conn:
            cur = conn.cursor()

            # Minimal prerequisites for migration (customers/books must exist or old schema won't be workable)
            cur.execute("""
                CREATE TABLE IF NOT EXISTS customers (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    name TEXT NOT NULL,
                    email TEXT NOT NULL,
                    is_active INTEGER NOT NULL DEFAULT 1,
                    UNIQUE(name, email)
                );
            """)
            cur.execute("""
                CREATE TABLE IF NOT EXISTS books (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    isbn TEXT UNIQUE,
                    title TEXT NOT NULL,
                    author TEXT NOT NULL,
                    category_id INTEGER,
                    location TEXT,
                    price_cents INTEGER NOT NULL DEFAULT 0,
                    cost_cents INTEGER NOT NULL DEFAULT 0,
                    stock_qty INTEGER NOT NULL DEFAULT 0,
                    is_active INTEGER NOT NULL DEFAULT 1
                );
            """)
            conn.commit()

            # Migration if needed
            self._try_migrate_old_sales_schema(conn)

            # Full schema
            cur.execute("""
                CREATE TABLE IF NOT EXISTS settings (
                    key TEXT PRIMARY KEY,
                    value TEXT NOT NULL
                );
            """)

            cur.execute("""
                CREATE TABLE IF NOT EXISTS users (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    username TEXT NOT NULL UNIQUE,
                    salt BLOB NOT NULL,
                    digest BLOB NOT NULL,
                    role TEXT NOT NULL CHECK(role IN ('admin','clerk')),
                    is_active INTEGER NOT NULL DEFAULT 1
                );
            """)

            cur.execute("""
                CREATE TABLE IF NOT EXISTS categories (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    name TEXT NOT NULL UNIQUE,
                    is_active INTEGER NOT NULL DEFAULT 1
                );
            """)

            # Add missing FK on books.category_id if old books table lacks it (SQLite can't add FK; we just keep column)
            cur.execute("""
                CREATE TABLE IF NOT EXISTS coupons (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    code TEXT NOT NULL UNIQUE,
                    kind TEXT NOT NULL CHECK(kind IN ('percent','fixed')),
                    value REAL NOT NULL CHECK(value >= 0),
                    is_active INTEGER NOT NULL DEFAULT 1,
                    expires_on TEXT
                );
            """)

            cur.execute("""
                CREATE TABLE IF NOT EXISTS sales (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    receipt_no TEXT NOT NULL UNIQUE,
                    created_at TEXT NOT NULL,
                    customer_id INTEGER NOT NULL,
                    subtotal_cents INTEGER NOT NULL,
                    discount_cents INTEGER NOT NULL DEFAULT 0,
                    coupon_code TEXT,
                    tax_rate REAL NOT NULL,
                    tax_cents INTEGER NOT NULL,
                    total_cents INTEGER NOT NULL,
                    payment_method TEXT NOT NULL CHECK(payment_method IN ('cash','card','other')),
                    payment_status TEXT NOT NULL CHECK(payment_status IN ('paid','unpaid','partial')),
                    note TEXT,
                    receipt_text TEXT NOT NULL,
                    is_void INTEGER NOT NULL DEFAULT 0,
                    FOREIGN KEY(customer_id) REFERENCES customers(id) ON DELETE RESTRICT
                );
            """)

            cur.execute("""
                CREATE TABLE IF NOT EXISTS sale_items (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    sale_id INTEGER NOT NULL,
                    book_id INTEGER NOT NULL,
                    quantity INTEGER NOT NULL CHECK(quantity > 0),
                    unit_price_cents INTEGER NOT NULL,
                    unit_cost_cents INTEGER NOT NULL,
                    line_subtotal_cents INTEGER NOT NULL,
                    line_discount_cents INTEGER NOT NULL DEFAULT 0,
                    line_total_cents INTEGER NOT NULL,
                    FOREIGN KEY(sale_id) REFERENCES sales(id) ON DELETE CASCADE,
                    FOREIGN KEY(book_id) REFERENCES books(id) ON DELETE RESTRICT
                );
            """)

            cur.execute("""
                CREATE TABLE IF NOT EXISTS returns (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    created_at TEXT NOT NULL,
                    sale_id INTEGER NOT NULL,
                    reason TEXT,
                    refund_method TEXT NOT NULL CHECK(refund_method IN ('cash','card','other')),
                    refund_cents INTEGER NOT NULL CHECK(refund_cents >= 0),
                    refund_tax_cents INTEGER NOT NULL DEFAULT 0,
                    receipt_text TEXT NOT NULL,
                    FOREIGN KEY(sale_id) REFERENCES sales(id) ON DELETE RESTRICT
                );
            """)

            cur.execute("""
                CREATE TABLE IF NOT EXISTS return_items (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    return_id INTEGER NOT NULL,
                    book_id INTEGER NOT NULL,
                    quantity INTEGER NOT NULL CHECK(quantity > 0),
                    unit_price_cents INTEGER NOT NULL,
                    line_total_cents INTEGER NOT NULL,
                    FOREIGN KEY(return_id) REFERENCES returns(id) ON DELETE CASCADE,
                    FOREIGN KEY(book_id) REFERENCES books(id) ON DELETE RESTRICT
                );
            """)

            conn.commit()

            if "refund_tax_cents" not in self._columns(conn, "returns"):
                cur.execute("ALTER TABLE returns ADD COLUMN refund_tax_cents INTEGER NOT NULL DEFAULT 0;")
                conn.commit()

            if "location" not in self._columns(conn, "books"):
                cur.execute("ALTER TABLE books ADD COLUMN location TEXT;")
                conn.commit()

            # Seed settings
            defaults = {
                "store_name": "My DVD/VHS Store",
                "store_address": "123 Main St",
                "store_phone": "(000) 000-0000",
                "receipt_footer": "Thank you! Returns with receipt within 14 days.",
                "receipt_prefix": "R",
                "tax_rate_default": "0.00",
            }
            for k, v in defaults.items():
                cur.execute("INSERT OR IGNORE INTO settings(key,value) VALUES(?,?);", (k, v))

            # Seed admin if no users
            cur.execute("SELECT COUNT(*) FROM users;")
            if int(cur.fetchone()[0]) == 0:
                salt, dg = pbkdf2_hash("admin")
                cur.execute(
                    "INSERT INTO users(username,salt,digest,role,is_active) VALUES(?,?,?,?,1);",
                    ("admin", salt, dg, "admin"),
                )
            conn.commit()

    # -------- Settings --------
    def get_setting(self, key: str) -> str:
        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute("SELECT value FROM settings WHERE key=?;", (key,))
            r = cur.fetchone()
            return r[0] if r else ""

    def set_setting(self, key: str, value: str) -> None:
        with self._connect() as conn:
            conn.execute(
                "INSERT INTO settings(key,value) VALUES(?,?) "
                "ON CONFLICT(key) DO UPDATE SET value=excluded.value;",
                (key, value),
            )
            conn.commit()

    # -------- Auth / users --------
    def auth_user(self, username: str, password: str) -> Optional[Dict[str, Any]]:
        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute("SELECT id, salt, digest, role, is_active FROM users WHERE username=?;", (username,))
            row = cur.fetchone()
            if not row:
                return None
            uid, salt, dg, role, active = row
            if not int(active):
                return None
            if not pbkdf2_verify(password, salt, dg):
                return None
            return {"id": int(uid), "username": username, "role": role}

    def list_users(self) -> List[Tuple[int, str, str, int]]:
        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute("SELECT id, username, role, is_active FROM users ORDER BY username;")
            return [(int(a), b, c, int(d)) for (a, b, c, d) in cur.fetchall()]

    def add_user(self, username: str, password: str, role: str) -> None:
        salt, dg = pbkdf2_hash(password)
        with self._connect() as conn:
            conn.execute(
                "INSERT INTO users(username,salt,digest,role,is_active) VALUES(?,?,?,?,1);",
                (username.strip(), salt, dg, role),
            )
            conn.commit()

    def set_user_active(self, user_id: int, active: int) -> None:
        with self._connect() as conn:
            conn.execute("UPDATE users SET is_active=? WHERE id=?;", (int(active), int(user_id)))
            conn.commit()

    def reset_password(self, user_id: int, new_password: str) -> None:
        salt, dg = pbkdf2_hash(new_password)
        with self._connect() as conn:
            conn.execute("UPDATE users SET salt=?, digest=? WHERE id=?;", (salt, dg, int(user_id)))
            conn.commit()

    # -------- Categories --------
    def list_categories(self, include_inactive: bool = False) -> List[Tuple[int, str, int]]:
        with self._connect() as conn:
            cur = conn.cursor()
            if include_inactive:
                cur.execute("SELECT id, name, is_active FROM categories ORDER BY name;")
            else:
                cur.execute("SELECT id, name, is_active FROM categories WHERE is_active=1 ORDER BY name;")
            return [(int(a), b, int(c)) for (a, b, c) in cur.fetchall()]

    def add_category(self, name: str) -> None:
        with self._connect() as conn:
            conn.execute("INSERT INTO categories(name,is_active) VALUES(?,1);", (name.strip(),))
            conn.commit()

    def set_category_active(self, cat_id: int, active: int) -> None:
        with self._connect() as conn:
            conn.execute("UPDATE categories SET is_active=? WHERE id=?;", (int(active), int(cat_id)))
            conn.commit()

    # -------- Titles --------
    def list_books(
        self,
        search: str = "",
        in_stock_only: bool = False,
        include_inactive: bool = False,
        category_id: Optional[int] = None
    ) -> List[Tuple[int, Optional[str], str, str, Optional[str], int, int, int, int, Optional[str]]]:
        """
        Returns:
          (id, isbn, title, author, location, price_cents, cost_cents, stock_qty, is_active, category_name)
        """
        s = (search or "").strip()
        where = []
        params: List[Any] = []

        if s:
            where.append("(b.title LIKE ? OR b.author LIKE ? OR IFNULL(b.isbn,'') LIKE ?)")
            like = f"%{s}%"
            params += [like, like, like]

        if in_stock_only:
            where.append("b.stock_qty > 0")

        if not include_inactive:
            where.append("b.is_active = 1")  # FIX: qualified

        if category_id is not None:
            where.append("b.category_id = ?")
            params.append(int(category_id))

        wsql = ("WHERE " + " AND ".join(where)) if where else ""

        sql = f"""
            SELECT
                b.id, b.isbn, b.title, b.author, b.location,
                b.price_cents, b.cost_cents, b.stock_qty, b.is_active,
                c.name
            FROM books b
            LEFT JOIN categories c ON c.id = b.category_id
            {wsql}
            ORDER BY b.title;
        """
        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute(sql, params)
            rows = cur.fetchall()
            out = []
            for r in rows:
                out.append((
                    int(r[0]),
                    r[1],
                    str(r[2]),
                    str(r[3]),
                    r[4],
                    int(r[5]),
                    int(r[6]),
                    int(r[7]),
                    int(r[8]),
                    r[9]
                ))
            return out

    def get_book(self, book_id: int):
        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute("""
                SELECT id, isbn, title, author, category_id, location, price_cents, cost_cents, stock_qty, is_active
                FROM books WHERE id=?;
            """, (int(book_id),))
            return cur.fetchone()

    def get_book_by_isbn(self, isbn: str):
        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute("""
                SELECT id, isbn, title, author, category_id, location, price_cents, cost_cents, stock_qty, is_active
                FROM books WHERE isbn=?;
            """, (isbn,))
            return cur.fetchone()

    def add_book(self, isbn, title, author, category_id, location, price_cents, cost_cents, stock_qty, is_active=1):
        with self._connect() as conn:
            conn.execute("""
                INSERT INTO books(isbn,title,author,category_id,location,price_cents,cost_cents,stock_qty,is_active)
                VALUES(?,?,?,?,?,?,?,?,?);
            """, (isbn or None, title.strip(), author.strip(), category_id, location, int(price_cents), int(cost_cents), int(stock_qty), int(is_active)))
            conn.commit()

    def update_book(self, book_id, isbn, title, author, category_id, location, price_cents, cost_cents, stock_qty, is_active):
        with self._connect() as conn:
            conn.execute("""
                UPDATE books
                SET isbn=?, title=?, author=?, category_id=?, location=?, price_cents=?, cost_cents=?, stock_qty=?, is_active=?
                WHERE id=?;
            """, (isbn or None, title.strip(), author.strip(), category_id, location, int(price_cents), int(cost_cents), int(stock_qty), int(is_active), int(book_id)))
            conn.commit()

    def delete_book(self, book_id: int) -> None:
        with self._connect() as conn:
            conn.execute("DELETE FROM books WHERE id=?;", (int(book_id),))
            conn.commit()

    def adjust_stock(self, book_id: int, delta: int) -> None:
        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute("SELECT stock_qty FROM books WHERE id=?;", (int(book_id),))
            row = cur.fetchone()
            if not row:
                raise ValueError("title missing")
            new_qty = int(row[0]) + int(delta)
            if new_qty < 0:
                raise ValueError("insufficient stock")
            cur.execute("UPDATE books SET stock_qty=? WHERE id=?;", (new_qty, int(book_id)))
            conn.commit()

    def set_book_active(self, book_id: int, active: int) -> None:
        with self._connect() as conn:
            conn.execute("UPDATE books SET is_active=? WHERE id=?;", (int(active), int(book_id)))
            conn.commit()

    # -------- Customers --------
    def list_customers(self, search: str = "", include_inactive: bool = False):
        s = (search or "").strip()
        where = []
        params: List[Any] = []

        if s:
            where.append("(name LIKE ? OR email LIKE ?)")
            like = f"%{s}%"
            params += [like, like]

        if not include_inactive:
            where.append("is_active = 1")

        wsql = ("WHERE " + " AND ".join(where)) if where else ""
        sql = f"SELECT id, name, email, is_active FROM customers {wsql} ORDER BY name;"

        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute(sql, params)
            return [(int(a), b, c, int(d)) for (a, b, c, d) in cur.fetchall()]

    def get_customer(self, customer_id: int):
        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute("SELECT id, name, email, is_active FROM customers WHERE id=?;", (int(customer_id),))
            return cur.fetchone()

    def add_customer(self, name: str, email: str, is_active: int = 1) -> None:
        with self._connect() as conn:
            conn.execute("INSERT INTO customers(name,email,is_active) VALUES(?,?,?);", (name.strip(), email.strip(), int(is_active)))
            conn.commit()

    def update_customer(self, customer_id: int, name: str, email: str, is_active: int) -> None:
        with self._connect() as conn:
            conn.execute("UPDATE customers SET name=?, email=?, is_active=? WHERE id=?;",
                         (name.strip(), email.strip(), int(is_active), int(customer_id)))
            conn.commit()

    def set_customer_active(self, customer_id: int, active: int) -> None:
        with self._connect() as conn:
            conn.execute("UPDATE customers SET is_active=? WHERE id=?;", (int(active), int(customer_id)))
            conn.commit()

    # -------- Coupons --------
    def list_coupons(self):
        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute("SELECT id, code, kind, value, is_active, expires_on FROM coupons ORDER BY code;")
            return [(int(a), b, c, float(d), int(e), f) for (a, b, c, d, e, f) in cur.fetchall()]

    def add_coupon(self, code, kind, value, is_active, expires_on):
        with self._connect() as conn:
            conn.execute("""
                INSERT INTO coupons(code,kind,value,is_active,expires_on)
                VALUES(?,?,?,?,?);
            """, (code.strip().upper(), kind, float(value), int(is_active), expires_on or None))
            conn.commit()

    def update_coupon(self, coupon_id, code, kind, value, is_active, expires_on):
        with self._connect() as conn:
            conn.execute("""
                UPDATE coupons SET code=?, kind=?, value=?, is_active=?, expires_on=? WHERE id=?;
            """, (code.strip().upper(), kind, float(value), int(is_active), expires_on or None, int(coupon_id)))
            conn.commit()

    def get_coupon_by_code(self, code: str) -> Optional[Dict[str, Any]]:
        code = (code or "").strip().upper()
        if not code:
            return None
        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute("SELECT id, code, kind, value, is_active, expires_on FROM coupons WHERE code=?;", (code,))
            row = cur.fetchone()
            if not row:
                return None
            cid, ccode, kind, val, active, expires_on = row
            if not int(active):
                return None
            if expires_on:
                try:
                    exp = datetime.strptime(expires_on, "%Y-%m-%d").date()
                    if date.today() > exp:
                        return None
                except Exception:
                    pass
            return {"id": int(cid), "code": ccode, "kind": kind, "value": float(val)}

    # -------- Sales / Returns / Receipts --------
    def next_receipt_no(self) -> str:
        prefix = self.get_setting("receipt_prefix") or "R"
        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute("SELECT receipt_no FROM sales ORDER BY id DESC LIMIT 1;")
            row = cur.fetchone()
            if not row:
                return f"{prefix}000001"
            last = str(row[0])
            digits = "".join(ch for ch in last if ch.isdigit())
            n = int(digits) + 1 if digits else 1
            return f"{prefix}{n:06d}"

    def _build_sale_receipt_text(
        self,
        receipt_no: str,
        created_at: str,
        customer_name: str,
        customer_email: str,
        lines: List[Dict[str, Any]],
        item_total_before_order_discount: int,
        order_discount_cents: int,
        coupon_code: Optional[str],
        coupon_discount_cents: int,
        discounted_subtotal_cents: int,
        tax_rate: float,
        tax_cents: int,
        total_cents: int,
        payment_method: str,
        payment_status: str,
        note: str
    ) -> str:
        store = self.get_setting("store_name")
        addr = self.get_setting("store_address")
        phone = self.get_setting("store_phone")
        footer = self.get_setting("receipt_footer")

        out = []
        out.append(store)
        out.append(addr)
        out.append(phone)
        out.append("=" * 64)
        out.append(f"Receipt: {receipt_no}")
        out.append(f"Date:    {created_at}")
        out.append(f"Customer:{customer_name}  <{customer_email}>")
        out.append("-" * 64)
        out.append(f"{'Title':34} {'Qty':>3} {'Unit':>10} {'Line':>10}")
        out.append("-" * 64)

        for r in lines:
            t = r["title"]
            if len(t) > 34:
                t = t[:33] + "…"
            out.append(f"{t:34} {r['qty']:>3} {cents_to_money(r['unit_price']):>10} {cents_to_money(r['line_total']):>10}")
            if r.get("line_disc", 0) > 0:
                out.append(f"{'  line discount':34} {'':>3} {'':>10} -{cents_to_money(r['line_disc']):>9}")

        out.append("-" * 64)
        if order_discount_cents > 0:
            out.append(f"{'Order discount:':>52} -{cents_to_money(order_discount_cents):>10}")
        if coupon_code and coupon_discount_cents > 0:
            out.append(f"{('Coupon ' + coupon_code + ':'):>52} -{cents_to_money(coupon_discount_cents):>10}")

        out.append(f"{'Subtotal (items):':>52} {cents_to_money(item_total_before_order_discount):>10}")
        out.append(f"{'Subtotal (after discounts):':>52} {cents_to_money(discounted_subtotal_cents):>10}")
        out.append(f"{('Tax @ ' + str(tax_rate)):>52} {cents_to_money(tax_cents):>10}")
        out.append(f"{'TOTAL:':>52} {cents_to_money(total_cents):>10}")
        out.append("-" * 64)
        out.append(f"Payment: {payment_method} / {payment_status}")
        if note:
            out.append(f"Note: {note}")
        out.append("=" * 64)
        out.append(footer)
        return "\n".join(out)

    def create_sale(
        self,
        customer_id: int,
        cart_items: List[Dict[str, Any]],
        tax_rate: float,
        order_discount_cents: int,
        coupon_code: Optional[str],
        payment_method: str,
        payment_status: str,
        note: str
    ) -> Tuple[int, str, str]:
        if not cart_items:
            raise ValueError("cart empty")
        if tax_rate < 0:
            raise ValueError("tax rate < 0")
        if order_discount_cents < 0:
            raise ValueError("order discount < 0")

        created_at = now_ts()
        receipt_no = self.next_receipt_no()

        with self._connect() as conn:
            cur = conn.cursor()

            # customer
            cur.execute("SELECT id, name, email FROM customers WHERE id=? AND is_active=1;", (int(customer_id),))
            cust = cur.fetchone()
            if not cust:
                raise ValueError("customer missing/inactive")
            _, cust_name, cust_email = cust

            # Build line items, validate stock
            lines = []
            item_total = 0
            for it in cart_items:
                book_id = int(it["book_id"])
                qty = int(it["qty"])
                if qty <= 0:
                    raise ValueError("bad qty")

                cur.execute("""
                    SELECT title, author, price_cents, cost_cents, stock_qty, is_active
                    FROM books WHERE id=?;
                """, (book_id,))
                b = cur.fetchone()
                if not b:
                    raise ValueError("title missing")
                title, author, price_cents, cost_cents, stock_qty, is_active = b
                if not int(is_active):
                    raise ValueError(f"title archived: {title}")
                if int(stock_qty) < qty:
                    raise ValueError(f"insufficient stock for '{title}' (have {stock_qty}, need {qty})")

                unit_price = int(it.get("unit_price_cents", price_cents))
                unit_cost = int(it.get("unit_cost_cents", cost_cents))

                line_sub = unit_price * qty
                line_disc = int(it.get("line_discount_cents", 0))
                if line_disc < 0 or line_disc > line_sub:
                    raise ValueError(f"bad line discount for '{title}'")
                line_total = line_sub - line_disc

                item_total += line_total
                lines.append({
                    "book_id": book_id,
                    "title": str(title),
                    "qty": qty,
                    "unit_price": unit_price,
                    "unit_cost": unit_cost,
                    "line_sub": line_sub,
                    "line_disc": line_disc,
                    "line_total": line_total,
                })

            # coupon
            coupon_discount = 0
            applied_coupon = None
            if coupon_code:
                cpn = self.get_coupon_by_code(coupon_code)
                if cpn and item_total > 0:
                    applied_coupon = cpn["code"]
                    if cpn["kind"] == "percent":
                        coupon_discount = int(round(item_total * (cpn["value"] / 100.0)))
                    else:
                        # fixed: treat as dollars if small
                        coupon_discount = int(round(cpn["value"] * 100.0)) if cpn["value"] < 1000 else int(cpn["value"])
                    coupon_discount = min(coupon_discount, item_total)

            total_order_discount = min(order_discount_cents + coupon_discount, item_total)
            discounted_subtotal = item_total - total_order_discount

            # distribute order-level discount across lines proportionally
            distributed = [0] * len(lines)
            if item_total > 0 and total_order_discount > 0:
                for i, ln in enumerate(lines):
                    share = ln["line_total"] / item_total
                    distributed[i] = int(round(total_order_discount * share))
                drift = total_order_discount - sum(distributed)
                if distributed:
                    distributed[-1] += drift

            # tax/total
            tax_cents = int(round(discounted_subtotal * float(tax_rate)))
            total_cents = discounted_subtotal + tax_cents

            receipt_text = self._build_sale_receipt_text(
                receipt_no=receipt_no,
                created_at=created_at,
                customer_name=cust_name,
                customer_email=cust_email,
                lines=lines,
                item_total_before_order_discount=item_total,
                order_discount_cents=order_discount_cents,
                coupon_code=applied_coupon,
                coupon_discount_cents=coupon_discount,
                discounted_subtotal_cents=discounted_subtotal,
                tax_rate=float(tax_rate),
                tax_cents=tax_cents,
                total_cents=total_cents,
                payment_method=payment_method,
                payment_status=payment_status,
                note=note or "",
            )

            # insert sale header
            cur.execute("""
                INSERT INTO sales(
                    receipt_no, created_at, customer_id,
                    subtotal_cents, discount_cents, coupon_code,
                    tax_rate, tax_cents, total_cents,
                    payment_method, payment_status, note, receipt_text, is_void
                )
                VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,0);
            """, (
                receipt_no, created_at, int(customer_id),
                int(discounted_subtotal), int(total_order_discount), applied_coupon,
                float(tax_rate), int(tax_cents), int(total_cents),
                payment_method, payment_status, note or "", receipt_text
            ))
            sale_id = int(cur.lastrowid)

            # insert items + decrement stock
            for i, ln in enumerate(lines):
                od = distributed[i]
                line_sub = ln["unit_price"] * ln["qty"]
                line_disc = ln["line_disc"] + od
                if line_disc > line_sub:
                    line_disc = line_sub
                line_total = line_sub - line_disc

                cur.execute("""
                    INSERT INTO sale_items(
                        sale_id, book_id, quantity,
                        unit_price_cents, unit_cost_cents,
                        line_subtotal_cents, line_discount_cents, line_total_cents
                    )
                    VALUES(?,?,?,?,?,?,?,?);
                """, (
                    sale_id, int(ln["book_id"]), int(ln["qty"]),
                    int(ln["unit_price"]), int(ln["unit_cost"]),
                    int(line_sub), int(line_disc), int(line_total)
                ))

                cur.execute("UPDATE books SET stock_qty = stock_qty - ? WHERE id=?;", (int(ln["qty"]), int(ln["book_id"])))

            conn.commit()
            return sale_id, receipt_no, receipt_text

    def list_sales(self, limit: int = 300):
        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute("""
                SELECT s.id, s.receipt_no, s.created_at, c.name, s.total_cents, s.payment_status, s.is_void
                FROM sales s
                JOIN customers c ON c.id = s.customer_id
                ORDER BY s.id DESC
                LIMIT ?;
            """, (int(limit),))
            return [(int(a), b, c, d, int(e), f, int(g)) for (a, b, c, d, e, f, g) in cur.fetchall()]

    def get_sale_receipt(self, sale_id: int):
        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute("SELECT receipt_text, receipt_no, created_at FROM sales WHERE id=?;", (int(sale_id),))
            return cur.fetchone()

    def get_sale_items(self, sale_id: int):
        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute("""
                SELECT si.book_id, b.title, si.quantity, si.unit_price_cents, si.line_total_cents
                FROM sale_items si
                JOIN books b ON b.id = si.book_id
                WHERE si.sale_id=?
                ORDER BY si.id;
            """, (int(sale_id),))
            return [(int(a), b, int(c), int(d), int(e)) for (a, b, c, d, e) in cur.fetchall()]

    def customer_history(self, customer_id: int):
        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute("""
                SELECT id, receipt_no, created_at, total_cents, payment_status
                FROM sales
                WHERE customer_id=?
                ORDER BY id DESC;
            """, (int(customer_id),))
            return [(int(a), b, c, int(d), e) for (a, b, c, d, e) in cur.fetchall()]

    def create_return(self, sale_id: int, items: List[Tuple[int, int]], reason: str, refund_method: str):
        if not items:
            raise ValueError("no return items")

        created_at = now_ts()

        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute("SELECT id, receipt_no, is_void, tax_rate FROM sales WHERE id=?;", (int(sale_id),))
            s = cur.fetchone()
            if not s:
                raise ValueError("sale missing")
            _, receipt_no, is_void, tax_rate = s
            if int(is_void):
                raise ValueError("cannot return voided sale")

            cur.execute("""
                SELECT book_id, quantity, unit_price_cents
                FROM sale_items
                WHERE sale_id=?;
            """, (int(sale_id),))
            orig = cur.fetchall()
            orig_map = {int(bid): {"qty": int(q), "unit": int(u)} for (bid, q, u) in orig}

            refund_subtotal_cents = 0
            receipt_lines = []
            for book_id, qty in items:
                book_id = int(book_id)
                qty = int(qty)
                if qty <= 0:
                    raise ValueError("bad qty")
                if book_id not in orig_map:
                    raise ValueError("title not in original sale")
                if qty > orig_map[book_id]["qty"]:
                    raise ValueError("return qty exceeds sold qty")
                unit = orig_map[book_id]["unit"]
                line_total = unit * qty
                refund_subtotal_cents += line_total
                receipt_lines.append((book_id, qty, unit, line_total))

            refund_tax_cents = int(round(refund_subtotal_cents * float(tax_rate)))
            refund_total_cents = refund_subtotal_cents + refund_tax_cents

            header = []
            store = self.get_setting("store_name")
            header.append(store)
            header.append("=" * 64)
            header.append(f"RETURN RECEIPT (original {receipt_no})")
            header.append(f"Date: {created_at}")
            header.append(f"Reason: {reason or ''}")
            header.append("-" * 64)
            header.append(f"{'Title':34} {'Qty':>3} {'Unit':>10} {'Line':>10}")
            header.append("-" * 64)

            for (book_id, qty, unit, line_total) in receipt_lines:
                cur.execute("SELECT title FROM books WHERE id=?;", (int(book_id),))
                t = cur.fetchone()
                title = t[0] if t else f"Title #{book_id}"
                if len(title) > 34:
                    title = title[:33] + "…"
                header.append(f"{title:34} {qty:>3} {cents_to_money(unit):>10} {cents_to_money(line_total):>10}")

            header.append("-" * 64)
            header.append(f"{'Subtotal:':>52} {cents_to_money(refund_subtotal_cents):>10}")
            header.append(f"{('Tax @ ' + str(tax_rate)):>52} {cents_to_money(refund_tax_cents):>10}")
            header.append(f"{'REFUND:':>52} {cents_to_money(refund_total_cents):>10}")
            header.append(f"Refund method: {refund_method}")
            header.append("=" * 64)
            receipt_text = "\n".join(header)

            cur.execute("""
                INSERT INTO returns(created_at, sale_id, reason, refund_method, refund_cents, refund_tax_cents, receipt_text)
                VALUES(?,?,?,?,?,?,?);
            """, (created_at, int(sale_id), reason or "", refund_method, int(refund_total_cents), int(refund_tax_cents), receipt_text))
            return_id = int(cur.lastrowid)

            for (book_id, qty, unit, line_total) in receipt_lines:
                cur.execute("""
                    INSERT INTO return_items(return_id, book_id, quantity, unit_price_cents, line_total_cents)
                    VALUES(?,?,?,?,?);
                """, (return_id, int(book_id), int(qty), int(unit), int(line_total)))

                cur.execute("UPDATE books SET stock_qty = stock_qty + ? WHERE id=?;", (int(qty), int(book_id)))

            conn.commit()
            return return_id, receipt_text

    def list_returns(self, limit: int = 200):
        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute("""
                SELECT r.id, r.created_at, s.receipt_no, r.refund_cents, r.refund_method
                FROM returns r
                JOIN sales s ON s.id = r.sale_id
                ORDER BY r.id DESC
                LIMIT ?;
            """, (int(limit),))
            return [(int(a), b, c, int(d), e) for (a, b, c, d, e) in cur.fetchall()]

    def get_return_receipt(self, return_id: int):
        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute("SELECT receipt_text, created_at FROM returns WHERE id=?;", (int(return_id),))
            return cur.fetchone()

    # -------- CSV Export helper --------
    def export_table_to_csv(self, query: str, headers: List[str], path: str, params: Tuple = ()) -> None:
        with self._connect() as conn, open(path, "w", newline="", encoding="utf-8") as f:
            cur = conn.cursor()
            cur.execute(query, params)
            rows = cur.fetchall()
            w = csv.writer(f)
            w.writerow(headers)
            w.writerows(rows)

    # -------- Reports --------
    def report_daily(self, days: int = 30):
        start = (date.today() - timedelta(days=days)).strftime("%Y-%m-%d")
        with self._connect() as conn:
            cur = conn.cursor()
            has_refund_tax = "refund_tax_cents" in self._columns(conn, "returns")
            cur.execute("""
                SELECT substr(created_at,1,10) AS day,
                       SUM(total_cents) AS revenue_cents,
                       SUM(tax_cents) AS tax_cents,
                       COUNT(*) AS sale_count
                FROM sales
                WHERE is_void=0 AND substr(created_at,1,10) >= ?
                GROUP BY day
                ORDER BY day DESC;
            """, (start,))
            sales_rows = cur.fetchall()
            sales = {d: (int(rev or 0), int(tax or 0), int(scnt or 0)) for (d, rev, tax, scnt) in sales_rows}

            if has_refund_tax:
                cur.execute("""
                    SELECT substr(created_at,1,10) AS day,
                           SUM(refund_cents) AS refund_cents,
                           SUM(refund_tax_cents) AS refund_tax_cents,
                           COUNT(*) AS return_count
                    FROM returns
                    WHERE substr(created_at,1,10) >= ?
                    GROUP BY day
                    ORDER BY day DESC;
                """, (start,))
                returns = {d: (int(rc or 0), int(rtax or 0), int(cnt or 0)) for (d, rc, rtax, cnt) in cur.fetchall()}
            else:
                cur.execute("""
                    SELECT substr(created_at,1,10) AS day,
                           SUM(refund_cents) AS refund_cents,
                           COUNT(*) AS return_count
                    FROM returns
                    WHERE substr(created_at,1,10) >= ?
                    GROUP BY day
                    ORDER BY day DESC;
                """, (start,))
                returns = {d: (int(rc or 0), 0, int(cnt or 0)) for (d, rc, cnt) in cur.fetchall()}

            out = []
            all_days = sorted(set(sales.keys()) | set(returns.keys()), reverse=True)
            for d in all_days:
                rev_i, tax_i, scnt = sales.get(d, (0, 0, 0))
                refund, refund_tax, rcnt = returns.get(d, (0, 0, 0))
                net = rev_i - refund
                net_tax = tax_i - refund_tax
                out.append((d, int(scnt or 0), rcnt, rev_i, refund, net, net_tax))
            return out

    def report_monthly(self):
        with self._connect() as conn:
            cur = conn.cursor()
            has_refund_tax = "refund_tax_cents" in self._columns(conn, "returns")
            cur.execute("""
                SELECT substr(created_at,1,7) AS month,
                       SUM(total_cents) AS revenue_cents,
                       SUM(tax_cents) AS tax_cents,
                       COUNT(*) AS sale_count
                FROM sales
                WHERE is_void=0
                GROUP BY month
                ORDER BY month DESC;
            """)
            sales = {a: (int(b or 0), int(c or 0), int(d or 0)) for (a, b, c, d) in cur.fetchall()}

            if has_refund_tax:
                cur.execute("""
                    SELECT substr(created_at,1,7) AS month,
                           SUM(refund_cents) AS refund_cents,
                           SUM(refund_tax_cents) AS refund_tax_cents
                    FROM returns
                    GROUP BY month
                    ORDER BY month DESC;
                """)
                returns = {a: (int(b or 0), int(c or 0)) for (a, b, c) in cur.fetchall()}
            else:
                cur.execute("""
                    SELECT substr(created_at,1,7) AS month,
                           SUM(refund_cents) AS refund_cents
                    FROM returns
                    GROUP BY month
                    ORDER BY month DESC;
                """)
                returns = {a: (int(b or 0), 0) for (a, b) in cur.fetchall()}

            out = []
            all_months = sorted(set(sales.keys()) | set(returns.keys()), reverse=True)
            for month in all_months:
                rev, tax, scnt = sales.get(month, (0, 0, 0))
                refund, refund_tax = returns.get(month, (0, 0))
                net_rev = rev - refund
                net_tax = tax - refund_tax
                out.append((month, net_rev, net_tax, scnt))
            return out

    def report_top_books(self, limit: int = 10):
        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute("""
                WITH sold AS (
                    SELECT b.id AS book_id,
                           b.title AS title,
                           SUM(si.quantity) AS units,
                           SUM(si.line_total_cents) AS revenue_cents,
                           SUM((si.unit_price_cents - si.unit_cost_cents) * si.quantity - si.line_discount_cents) AS profit_cents
                    FROM sale_items si
                    JOIN sales s ON s.id = si.sale_id
                    JOIN books b ON b.id = si.book_id
                    WHERE s.is_void=0
                    GROUP BY b.id
                ),
                sale_cost AS (
                    SELECT sale_id, book_id, MAX(unit_cost_cents) AS unit_cost_cents
                    FROM sale_items
                    GROUP BY sale_id, book_id
                ),
                returned AS (
                    SELECT ri.book_id AS book_id,
                           SUM(ri.quantity) AS units,
                           SUM(ri.line_total_cents) AS revenue_cents,
                           SUM((ri.unit_price_cents - sc.unit_cost_cents) * ri.quantity) AS profit_cents
                    FROM return_items ri
                    JOIN returns r ON r.id = ri.return_id
                    JOIN sale_cost sc ON sc.sale_id = r.sale_id AND sc.book_id = ri.book_id
                    GROUP BY ri.book_id
                )
                SELECT sold.title,
                       sold.units - IFNULL(returned.units, 0) AS units,
                       sold.revenue_cents - IFNULL(returned.revenue_cents, 0) AS revenue_cents,
                       sold.profit_cents - IFNULL(returned.profit_cents, 0) AS profit_cents
                FROM sold
                LEFT JOIN returned ON returned.book_id = sold.book_id
                ORDER BY revenue_cents DESC
                LIMIT ?;
            """, (int(limit),))
            return [(a, int(b or 0), int(c or 0), int(d or 0)) for (a, b, c, d) in cur.fetchall()]

    def report_top_customers(self, limit: int = 10):
        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute("""
                WITH refunds AS (
                    SELECT s.customer_id AS customer_id,
                           SUM(r.refund_cents) AS refund_cents
                    FROM returns r
                    JOIN sales s ON s.id = r.sale_id
                    WHERE s.is_void=0
                    GROUP BY s.customer_id
                )
                SELECT c.name,
                       COUNT(*) AS sales,
                       SUM(s.total_cents) - IFNULL(refunds.refund_cents, 0) AS revenue_cents
                FROM sales s
                JOIN customers c ON c.id = s.customer_id
                LEFT JOIN refunds ON refunds.customer_id = s.customer_id
                WHERE s.is_void=0
                GROUP BY c.id
                ORDER BY revenue_cents DESC
                LIMIT ?;
            """, (int(limit),))
            return [(a, int(b or 0), int(c or 0)) for (a, b, c) in cur.fetchall()]

    def report_by_category(self):
        with self._connect() as conn:
            cur = conn.cursor()
            cur.execute("""
                WITH sold AS (
                    SELECT IFNULL(cat.name,'Uncategorized') AS category,
                           SUM(si.line_total_cents) AS revenue_cents,
                           SUM((si.unit_price_cents - si.unit_cost_cents) * si.quantity - si.line_discount_cents) AS profit_cents
                    FROM sale_items si
                    JOIN sales s ON s.id = si.sale_id
                    JOIN books b ON b.id = si.book_id
                    LEFT JOIN categories cat ON cat.id = b.category_id
                    WHERE s.is_void=0
                    GROUP BY category
                ),
                sale_cost AS (
                    SELECT sale_id, book_id, MAX(unit_cost_cents) AS unit_cost_cents
                    FROM sale_items
                    GROUP BY sale_id, book_id
                ),
                returned AS (
                    SELECT IFNULL(cat.name,'Uncategorized') AS category,
                           SUM(ri.line_total_cents) AS revenue_cents,
                           SUM((ri.unit_price_cents - sc.unit_cost_cents) * ri.quantity) AS profit_cents
                    FROM return_items ri
                    JOIN returns r ON r.id = ri.return_id
                    JOIN sale_cost sc ON sc.sale_id = r.sale_id AND sc.book_id = ri.book_id
                    JOIN books b ON b.id = ri.book_id
                    LEFT JOIN categories cat ON cat.id = b.category_id
                    GROUP BY category
                )
                SELECT sold.category,
                       sold.revenue_cents - IFNULL(returned.revenue_cents, 0) AS revenue_cents,
                       sold.profit_cents - IFNULL(returned.profit_cents, 0) AS profit_cents
                FROM sold
                LEFT JOIN returned ON returned.category = sold.category
                ORDER BY revenue_cents DESC;
            """)
            return [(a, int(b or 0), int(c or 0)) for (a, b, c) in cur.fetchall()]


# -------------------------- UI: dialogs --------------------------
class Dialog:
    @staticmethod
    def ask_fields(root, title, fields, initial=None, password_keys=None):
        """
        fields: list of (label, key)
        initial: dict key->value
        password_keys: set/list of keys whose entry should show='*'
        """
        dlg = tk.Toplevel(root)
        dlg.title(title)
        dlg.transient(root)
        dlg.grab_set()
        dlg.resizable(False, False)

        frm = ttk.Frame(dlg, padding=12)
        frm.pack(fill="both", expand=True)

        entries = {}
        password_keys = set(password_keys or [])

        for r, (label, key) in enumerate(fields):
            ttk.Label(frm, text=label).grid(row=r, column=0, sticky="w", pady=4)
            show = "*" if key in password_keys else ""
            e = ttk.Entry(frm, width=48, show=show)
            e.grid(row=r, column=1, pady=4)
            if initial and key in initial and initial[key] is not None:
                e.insert(0, str(initial[key]))
            entries[key] = e

        if fields:
            entries[fields[0][1]].focus_set()

        out = {"data": None}

        def ok():
            out["data"] = {k: entries[k].get().strip() for _, k in fields}
            dlg.destroy()

        def cancel():
            dlg.destroy()

        btns = ttk.Frame(frm)
        btns.grid(row=len(fields), column=0, columnspan=2, sticky="e", pady=(10, 0))
        ttk.Button(btns, text="Cancel", command=cancel).pack(side="right")
        ttk.Button(btns, text="OK", command=ok).pack(side="right", padx=8)

        root.wait_window(dlg)
        return out["data"]

    @staticmethod
    def show_text(root, title, text):
        win = tk.Toplevel(root)
        win.title(title)
        win.geometry("820x620")
        win.transient(root)

        t = tk.Text(win, wrap="none")
        t.pack(fill="both", expand=True, padx=10, pady=10)
        t.insert("1.0", text)
        t.configure(state="disabled")

        ttk.Button(win, text="Close", command=win.destroy).pack(pady=(0, 10))


# -------------------------- App --------------------------
class App:
    def __init__(self):
        self.db = DB(DB_PATH)
        self.user = None  # dict{id,username,role}
        self.cart: Dict[int, Dict[str, Any]] = {}
        self.last_format_choice = ""

        self.root = tk.Tk()
        self.root.title("DVD/VHS POS (Fixed)")
        self.root.geometry("1200x720")

        self._login()

        self.notebook = ttk.Notebook(self.root)
        self.notebook.pack(fill="both", expand=True, padx=10, pady=10)

        self._build_books_tab()
        self._build_customers_tab()
        self._build_pos_tab()
        self._build_sales_tab()
        self._build_reports_tab()
        self._build_admin_tab()

        self.refresh_all()

    # ---------------- Login ----------------
    def _login(self):
        while True:
            data = Dialog.ask_fields(
                self.root,
                "Login",
                [("Username", "u"), ("Password", "p")],
                initial={"u": "admin"},
                password_keys={"p"},
            )
            if data is None:
                raise SystemExit
            u = data["u"]
            p = data["p"]
            auth = self.db.auth_user(u, p)
            if auth:
                self.user = auth
                self.root.title(f"DVD/VHS POS — {auth['username']} ({auth['role']})")
                return
            messagebox.showerror("Login failed", "Invalid username/password or inactive user.")

    def _require_admin(self) -> bool:
        if self.user["role"] != "admin":
            messagebox.showerror("Permission denied", "Admin only.")
            return False
        return True

    # ---------------- Titles tab ----------------
    def _build_books_tab(self):
        tab = ttk.Frame(self.notebook)
        self.notebook.add(tab, text="DVD/VHS")
        self.books_tab = tab

        top = ttk.Frame(tab)
        top.pack(fill="x", padx=10, pady=10)

        self.book_search = tk.StringVar()
        self.book_instock = tk.IntVar(value=0)
        self.book_inactive = tk.IntVar(value=0)

        ttk.Label(top, text="Search:").pack(side="left")
        e = ttk.Entry(top, textvariable=self.book_search, width=28)
        e.pack(side="left", padx=(6, 12))
        e.bind("<KeyRelease>", lambda _e: self.refresh_books())

        ttk.Checkbutton(top, text="In stock only", variable=self.book_instock, command=self.refresh_books).pack(side="left")
        ttk.Checkbutton(top, text="Include archived", variable=self.book_inactive, command=self.refresh_books).pack(side="left", padx=10)

        ttk.Button(top, text="Add (scan supported)", command=self.add_book).pack(side="left", padx=(20, 0))
        ttk.Button(top, text="Edit", command=self.edit_book).pack(side="left", padx=6)
        ttk.Button(top, text="Archive/Unarchive", command=self.toggle_book_active).pack(side="left", padx=6)
        ttk.Button(top, text="Delete", command=self.delete_book).pack(side="left", padx=6)
        ttk.Button(top, text="Restock", command=self.restock_book).pack(side="left", padx=6)
        ttk.Button(top, text="Export CSV", command=self.export_books_csv).pack(side="right")

        self.books_tree = ttk.Treeview(
            tab,
            columns=("isbn", "title", "author", "category", "location", "price", "cost", "stock", "active"),
            show="headings",
            height=18,
        )
        for col, lbl, w, anchor in [
            ("isbn", "Barcode", 140, "w"),
            ("title", "Title", 300, "w"),
            ("author", "Studio", 180, "w"),
            ("category", "Format", 130, "w"),
            ("location", "Location", 140, "w"),
            ("price", "Price", 90, "e"),
            ("cost", "Cost", 90, "e"),
            ("stock", "Stock", 70, "center"),
            ("active", "Active", 70, "center"),
        ]:
            self.books_tree.heading(col, text=lbl)
            self.books_tree.column(col, width=w, anchor=anchor)

        self.books_tree.pack(fill="both", expand=True, padx=10, pady=(0, 10))
        self.books_tree.bind("<Double-1>", lambda _e: self.edit_book())

    def refresh_books(self):
        for i in self.books_tree.get_children():
            self.books_tree.delete(i)

        rows = self.db.list_books(
            search=self.book_search.get(),
            in_stock_only=bool(self.book_instock.get()),
            include_inactive=bool(self.book_inactive.get()),
        )
        for (bid, isbn, title, author, location, price, cost, stock, active, catname) in rows:
            self.books_tree.insert(
                "", "end", iid=str(bid),
                values=(isbn or "", title, author, catname or "", location or "", cents_to_money(price), cents_to_money(cost), stock, "yes" if active else "no")
            )

        self._refresh_pos_books()

    def _selected_book_id(self) -> Optional[int]:
        sel = self.books_tree.selection()
        return int(sel[0]) if sel else None

    def add_book(self):
        """
        Add title dialog with scan support:
        - scan string can include UPC/EAN barcode or price-only barcode.
        - lookup via UPCItemDB if barcode present.
        """
        dlg = tk.Toplevel(self.root)
        dlg.title("Add Title (scan barcode/price)")
        dlg.transient(self.root)
        dlg.grab_set()
        dlg.resizable(False, False)

        frame = ttk.Frame(dlg, padding=12)
        frame.pack(fill="both", expand=True)

        scan_var = tk.StringVar(value="")
        isbn_var = tk.StringVar(value="")
        title_var = tk.StringVar(value="")
        author_var = tk.StringVar(value="")
        cat_var = tk.StringVar(value=self.last_format_choice)
        location_var = tk.StringVar(value="")
        price_var = tk.StringVar(value="0.00")
        cost_var = tk.StringVar(value="0.00")
        stock_var = tk.StringVar(value="1")
        add_another_var = tk.IntVar(value=0)

        def show_status(msg: str):
            status_lbl.configure(text=msg)

        def do_parse_scan():
            raw = scan_var.get().strip()
            if not raw:
                messagebox.showerror("Scan needed", "Scan something into the Scan field.", parent=dlg)
                return
            barcode, price = parse_scan_barcode_and_price(raw)
            if barcode:
                isbn_var.set(barcode)
            if price:
                price_var.set(price)
            if not barcode and not price:
                messagebox.showerror("Unrecognized", "Could not parse barcode or price from scan.", parent=dlg)
                return
            show_status(f"Parsed scan → Barcode: {barcode or '(none)'}  Price: {price or '(none)'}")

            # auto-lookup if barcode found
            if barcode:
                info = fetch_title_info_upcitemdb(barcode)
                if info:
                    title_var.set(info.get("title", ""))
                    author_var.set(info.get("studio", ""))
                    show_status("Parsed + barcode lookup OK (title/studio filled).")
                else:
                    show_status("Parsed barcode, but lookup failed (enter title/studio manually).")

        def do_lookup_barcode():
            barcode = normalize_barcode(isbn_var.get())
            if not barcode:
                messagebox.showerror("Invalid barcode", "No valid barcode detected in Barcode field.", parent=dlg)
                return
            isbn_var.set(barcode)
            info = fetch_title_info_upcitemdb(barcode)
            if not info:
                messagebox.showerror("Lookup failed", "Could not fetch metadata (no result or no internet).", parent=dlg)
                return
            title_var.set(info.get("title", ""))
            author_var.set(info.get("studio", ""))
            show_status("Barcode lookup OK (title/studio filled).")

        def do_parse_price_field():
            p = parse_price_from_scan(price_var.get())
            if not p:
                messagebox.showerror("Price not recognized", "Could not parse price from Price field.", parent=dlg)
                return
            price_var.set(p)
            show_status("Price parsed/normalized.")

        # Layout
        r = 0
        ttk.Label(frame, text="Scan (barcode or price-only):").grid(row=r, column=0, sticky="w", pady=4)
        scan_entry = ttk.Entry(frame, textvariable=scan_var, width=46)
        scan_entry.grid(row=r, column=1, pady=4, sticky="w")
        ttk.Button(frame, text="Parse Scan", command=do_parse_scan).grid(row=r, column=2, padx=8)
        r += 1

        ttk.Label(frame, text="Barcode:").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Entry(frame, textvariable=isbn_var, width=46).grid(row=r, column=1, pady=4, sticky="w")
        ttk.Button(frame, text="Lookup Barcode", command=do_lookup_barcode).grid(row=r, column=2, padx=8)
        r += 1

        ttk.Label(frame, text="Title:").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Entry(frame, textvariable=title_var, width=46).grid(row=r, column=1, pady=4, sticky="w")
        r += 1

        ttk.Label(frame, text="Studio:").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Entry(frame, textvariable=author_var, width=46).grid(row=r, column=1, pady=4, sticky="w")
        r += 1

        ttk.Label(frame, text="Format (optional, e.g., DVD/VHS):").grid(row=r, column=0, sticky="w", pady=4)
        format_entry = ttk.Entry(frame, textvariable=cat_var, width=46)
        format_entry.grid(row=r, column=1, pady=4, sticky="w")
        format_choices = ("DVD", "Blu-ray", "VHS")
        format_vars = {choice: tk.IntVar(value=1 if self.last_format_choice == choice else 0) for choice in format_choices}

        def sync_format_choice(choice: str) -> None:
            for name, var in format_vars.items():
                var.set(1 if name == choice else 0)
            cat_var.set(choice)
            self.last_format_choice = choice

        def on_format_toggle(choice: str) -> None:
            if format_vars[choice].get():
                sync_format_choice(choice)
            elif cat_var.get().strip() == choice:
                cat_var.set("")
                self.last_format_choice = ""

        format_box = ttk.Frame(frame)
        format_box.grid(row=r, column=2, padx=8, sticky="w")
        for choice in format_choices:
            ttk.Checkbutton(
                format_box,
                text=choice,
                variable=format_vars[choice],
                command=lambda c=choice: on_format_toggle(c),
            ).pack(side="left")
        r += 1

        def on_format_entry_change(*_args):
            current = cat_var.get().strip()
            matched = next((c for c in format_choices if c.lower() == current.lower()), None)
            if matched:
                if self.last_format_choice != matched:
                    sync_format_choice(matched)
            else:
                for var in format_vars.values():
                    var.set(0)
                if current:
                    self.last_format_choice = current

        cat_var.trace_add("write", on_format_entry_change)

        ttk.Label(frame, text="Location (optional):").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Entry(frame, textvariable=location_var, width=46).grid(row=r, column=1, pady=4, sticky="w")
        r += 1

        ttk.Label(frame, text="Price (e.g. 12.99):").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Entry(frame, textvariable=price_var, width=46).grid(row=r, column=1, pady=4, sticky="w")
        price_btns = ttk.Frame(frame)
        price_btns.grid(row=r, column=2, padx=8, sticky="w")
        ttk.Button(price_btns, text="Parse Price", command=do_parse_price_field).pack(side="left")
        r += 1

        ttk.Label(frame, text="Cost (e.g. 7.50):").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Entry(frame, textvariable=cost_var, width=46).grid(row=r, column=1, pady=4, sticky="w")
        r += 1

        ttk.Label(frame, text="Stock qty:").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Entry(frame, textvariable=stock_var, width=46).grid(row=r, column=1, pady=4, sticky="w")
        r += 1

        ttk.Checkbutton(frame, text="Add another after save", variable=add_another_var).grid(
            row=r, column=0, columnspan=2, sticky="w", pady=(4, 0)
        )
        r += 1

        status_lbl = ttk.Label(frame, text="", foreground="#444")
        status_lbl.grid(row=r, column=0, columnspan=3, sticky="w", pady=(8, 0))
        r += 1

        def on_add():
            isbn = normalize_barcode(isbn_var.get()) or None
            title = title_var.get().strip()
            author = author_var.get().strip()
            cat_name = cat_var.get().strip()
            location = location_var.get().strip() or None
            price_s = price_var.get().strip()
            cost_s = cost_var.get().strip()
            stock_s = stock_var.get().strip()

            if not title or not author:
                messagebox.showerror("Missing data", "Title and Studio are required.", parent=dlg)
                return

            try:
                price_cents = dollars_to_cents(price_s)
                cost_cents = dollars_to_cents(cost_s)
                stock = int(stock_s)
                if stock < 0:
                    raise ValueError
            except Exception:
                messagebox.showerror("Bad input", "Check price/cost/stock values.", parent=dlg)
                return

            if cat_name:
                self.last_format_choice = cat_name
            else:
                self.last_format_choice = ""

            # category: auto-create if provided
            cat_id = None
            if cat_name:
                try:
                    self.db.add_category(cat_name)
                except sqlite3.IntegrityError:
                    pass
                cats_all = self.db.list_categories(include_inactive=True)
                for (cid, name, _active) in cats_all:
                    if name == cat_name:
                        cat_id = cid
                        break

            try:
                if isbn:
                    existing = self.db.get_book_by_isbn(isbn)
                    if existing:
                        self.db.adjust_stock(int(existing[0]), 1)
                    else:
                        self.db.add_book(isbn, title, author, cat_id, location, price_cents, cost_cents, stock, 1)
                else:
                    self.db.add_book(isbn, title, author, cat_id, location, price_cents, cost_cents, stock, 1)
            except sqlite3.IntegrityError as e:
                messagebox.showerror("DB error", f"Could not add title.\n\n{e}", parent=dlg)
                return

            self.refresh_books()
            self.refresh_reports()
            if add_another_var.get():
                isbn_var.set("")
                title_var.set("")
                author_var.set("")
                price_var.set("0.00")
                cost_var.set("0.00")
                stock_var.set("1")
                scan_var.set("")
                scan_entry.focus_set()
                show_status("Added. Ready for another title.")
            else:
                dlg.destroy()

        btns = ttk.Frame(frame)
        btns.grid(row=r, column=0, columnspan=3, sticky="e", pady=(10, 0))
        ttk.Button(btns, text="Cancel", command=dlg.destroy).pack(side="right")
        add_btn = ttk.Button(btns, text="Add Title", command=on_add)
        add_btn.pack(side="right", padx=8)

        def on_scan_enter(_event):
            do_parse_scan()
            add_btn.focus_set()
            return "break"

        dlg.bind("<Return>", lambda _e: on_add())
        scan_entry.bind("<Return>", on_scan_enter)
        scan_entry.focus_set()
        self.root.wait_window(dlg)

    def edit_book(self):
        bid = self._selected_book_id()
        if not bid:
            messagebox.showerror("No selection", "Select a title.")
            return
        row = self.db.get_book(bid)
        if not row:
            messagebox.showerror("Missing", "Title not found.")
            return

        _id, isbn, title, author, cat_id, location, price, cost, stock, active = row

        catname = ""
        if cat_id:
            for (cid, nm, _ac) in self.db.list_categories(include_inactive=True):
                if cid == cat_id:
                    catname = nm
                    break

        dlg = tk.Toplevel(self.root)
        dlg.title("Edit Title")
        dlg.transient(self.root)
        dlg.grab_set()
        dlg.resizable(False, False)

        frame = ttk.Frame(dlg, padding=12)
        frame.pack(fill="both", expand=True)

        isbn_var = tk.StringVar(value=isbn or "")
        title_var = tk.StringVar(value=title)
        author_var = tk.StringVar(value=author)
        cat_var = tk.StringVar(value=catname)
        location_var = tk.StringVar(value=location or "")
        price_var = tk.StringVar(value=f"{int(price)/100:.2f}")
        cost_var = tk.StringVar(value=f"{int(cost)/100:.2f}")
        stock_var = tk.StringVar(value=str(stock))
        active_var = tk.IntVar(value=1 if int(active) else 0)

        def show_status(msg: str):
            status_lbl.configure(text=msg)

        def do_parse_price_field():
            p = parse_price_from_scan(price_var.get())
            if not p:
                messagebox.showerror("Price not recognized", "Could not parse price from Price field.", parent=dlg)
                return
            price_var.set(p)
            show_status("Price parsed/normalized.")

        r = 0
        ttk.Label(frame, text="Barcode (optional):").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Entry(frame, textvariable=isbn_var, width=46).grid(row=r, column=1, pady=4, sticky="w")
        r += 1

        ttk.Label(frame, text="Title:").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Entry(frame, textvariable=title_var, width=46).grid(row=r, column=1, pady=4, sticky="w")
        r += 1

        ttk.Label(frame, text="Studio:").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Entry(frame, textvariable=author_var, width=46).grid(row=r, column=1, pady=4, sticky="w")
        r += 1

        ttk.Label(frame, text="Format (optional, e.g., DVD/VHS):").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Entry(frame, textvariable=cat_var, width=46).grid(row=r, column=1, pady=4, sticky="w")
        r += 1

        ttk.Label(frame, text="Location (optional):").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Entry(frame, textvariable=location_var, width=46).grid(row=r, column=1, pady=4, sticky="w")
        r += 1

        ttk.Label(frame, text="Price (e.g. 12.99):").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Entry(frame, textvariable=price_var, width=46).grid(row=r, column=1, pady=4, sticky="w")
        price_btns = ttk.Frame(frame)
        price_btns.grid(row=r, column=2, padx=8, sticky="w")
        ttk.Button(price_btns, text="Parse Price", command=do_parse_price_field).pack(side="left")
        r += 1

        ttk.Label(frame, text="Cost (e.g. 7.50):").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Entry(frame, textvariable=cost_var, width=46).grid(row=r, column=1, pady=4, sticky="w")
        r += 1

        ttk.Label(frame, text="Stock qty:").grid(row=r, column=0, sticky="w", pady=4)
        ttk.Entry(frame, textvariable=stock_var, width=46).grid(row=r, column=1, pady=4, sticky="w")
        r += 1

        ttk.Checkbutton(frame, text="Active", variable=active_var).grid(row=r, column=1, sticky="w", pady=4)
        r += 1

        status_lbl = ttk.Label(frame, text="", foreground="#444")
        status_lbl.grid(row=r, column=0, columnspan=3, sticky="w", pady=(8, 0))
        r += 1

        def on_save():
            isbn_val = normalize_barcode(isbn_var.get()) or None
            title_val = title_var.get().strip()
            author_val = author_var.get().strip()
            cat_name = cat_var.get().strip()
            location_val = location_var.get().strip() or None
            price_s = price_var.get().strip()
            cost_s = cost_var.get().strip()
            stock_s = stock_var.get().strip()

            if not title_val or not author_val:
                messagebox.showerror("Missing data", "Title and Studio are required.", parent=dlg)
                return

            try:
                price2 = dollars_to_cents(price_s)
                cost2 = dollars_to_cents(cost_s)
                stock2 = int(stock_s)
                active2 = 1 if active_var.get() else 0
                if stock2 < 0:
                    raise ValueError
            except Exception:
                messagebox.showerror("Bad input", "Check price/cost/stock/active.", parent=dlg)
                return

            cat_id2 = None
            if cat_name:
                try:
                    self.db.add_category(cat_name)
                except sqlite3.IntegrityError:
                    pass
                cats = self.db.list_categories(include_inactive=True)
                cat_id2 = next((c[0] for c in cats if c[1] == cat_name), None)

            try:
                self.db.update_book(bid, isbn_val, title_val, author_val, cat_id2, location_val, price2, cost2, stock2, active2)
            except sqlite3.IntegrityError as e:
                messagebox.showerror("DB error", f"Could not update.\n\n{e}", parent=dlg)
                return

            dlg.destroy()
            self.refresh_books()
            self.refresh_reports()

        btns = ttk.Frame(frame)
        btns.grid(row=r, column=0, columnspan=3, sticky="e", pady=(10, 0))
        ttk.Button(btns, text="Cancel", command=dlg.destroy).pack(side="right")
        ttk.Button(btns, text="Save", command=on_save).pack(side="right", padx=8)

        self.root.wait_window(dlg)
        return

    def delete_book(self):
        bid = self._selected_book_id()
        if not bid:
            messagebox.showerror("No selection", "Select a title.")
            return
        row = self.db.get_book(bid)
        if not row:
            messagebox.showerror("Missing", "Title not found.")
            return
        title = row[2]
        if not messagebox.askyesno("Delete Title", f"Delete '{title}' permanently?"):
            return
        try:
            self.db.delete_book(bid)
        except sqlite3.IntegrityError:
            messagebox.showerror("Delete failed", "Cannot delete a title with related sales/returns. Archive instead.")
            return
        self.refresh_books()

    def toggle_book_active(self):
        bid = self._selected_book_id()
        if not bid:
            messagebox.showerror("No selection", "Select a title.")
            return
        row = self.db.get_book(bid)
        if not row:
            return
        active = int(row[9])
        self.db.set_book_active(bid, 0 if active else 1)
        self.refresh_books()

    def restock_book(self):
        bid = self._selected_book_id()
        if not bid:
            messagebox.showerror("No selection", "Select a title.")
            return
        data = Dialog.ask_fields(self.root, "Restock Title", [("Add quantity (positive integer)", "qty")], initial={"qty": "1"})
        if not data:
            return
        try:
            qty = int(data["qty"])
            if qty <= 0:
                raise ValueError
        except Exception:
            messagebox.showerror("Bad qty", "Enter a positive integer.")
            return
        try:
            self.db.adjust_stock(bid, qty)
        except Exception as e:
            messagebox.showerror("Stock error", str(e))
            return
        self.refresh_books()

    def export_books_csv(self):
        path = filedialog.asksaveasfilename(defaultextension=".csv", filetypes=[("CSV", "*.csv")], title="Export Titles CSV")
        if not path:
            return
        q = """
            SELECT IFNULL(isbn,''), title, author, IFNULL(location,''), price_cents, cost_cents, stock_qty, is_active
            FROM books
            ORDER BY title;
        """
        self.db.export_table_to_csv(
            q,
            ["barcode", "title", "studio", "location", "price_cents", "cost_cents", "stock_qty", "is_active"],
            path,
        )
        messagebox.showinfo("Exported", f"Saved:\n{path}")

    # ---------------- Customers tab ----------------
    def _build_customers_tab(self):
        tab = ttk.Frame(self.notebook)
        self.notebook.add(tab, text="Customers")
        self.customers_tab = tab

        top = ttk.Frame(tab)
        top.pack(fill="x", padx=10, pady=10)

        self.cust_search = tk.StringVar()
        self.cust_inactive = tk.IntVar(value=0)

        ttk.Label(top, text="Search:").pack(side="left")
        e = ttk.Entry(top, textvariable=self.cust_search, width=28)
        e.pack(side="left", padx=(6, 12))
        e.bind("<KeyRelease>", lambda _e: self.refresh_customers())

        ttk.Checkbutton(top, text="Include archived", variable=self.cust_inactive, command=self.refresh_customers).pack(side="left")

        ttk.Button(top, text="Add", command=self.add_customer).pack(side="left", padx=(20, 0))
        ttk.Button(top, text="Edit", command=self.edit_customer).pack(side="left", padx=6)
        ttk.Button(top, text="Archive/Unarchive", command=self.toggle_customer_active).pack(side="left", padx=6)
        ttk.Button(top, text="History", command=self.view_customer_history).pack(side="left", padx=6)
        ttk.Button(top, text="Export CSV", command=self.export_customers_csv).pack(side="right")

        self.customers_tree = ttk.Treeview(tab, columns=("name", "email", "active"), show="headings", height=18)
        self.customers_tree.heading("name", text="Name")
        self.customers_tree.heading("email", text="Email")
        self.customers_tree.heading("active", text="Active")
        self.customers_tree.column("name", width=260)
        self.customers_tree.column("email", width=460)
        self.customers_tree.column("active", width=80, anchor="center")
        self.customers_tree.pack(fill="both", expand=True, padx=10, pady=(0, 10))
        self.customers_tree.bind("<Double-1>", lambda _e: self.edit_customer())

    def refresh_customers(self):
        for i in self.customers_tree.get_children():
            self.customers_tree.delete(i)
        rows = self.db.list_customers(self.cust_search.get(), include_inactive=bool(self.cust_inactive.get()))
        for cid, name, email, active in rows:
            self.customers_tree.insert("", "end", iid=str(cid), values=(name, email, "yes" if active else "no"))
        self._refresh_pos_customers()

    def _selected_customer_id(self) -> Optional[int]:
        sel = self.customers_tree.selection()
        return int(sel[0]) if sel else None

    def add_customer(self):
        data = Dialog.ask_fields(self.root, "Add Customer", [("Name", "name"), ("Email", "email")])
        if not data:
            return
        try:
            self.db.add_customer(data["name"], data["email"], 1)
        except sqlite3.IntegrityError as e:
            messagebox.showerror("DB error", f"Could not add customer.\n\n{e}")
            return
        self.refresh_customers()

    def edit_customer(self):
        cid = self._selected_customer_id()
        if not cid:
            messagebox.showerror("No selection", "Select a customer.")
            return
        row = self.db.get_customer(cid)
        if not row:
            return
        _id, name, email, active = row
        data = Dialog.ask_fields(self.root, "Edit Customer", [
            ("Name", "name"),
            ("Email", "email"),
            ("Active? (yes/no)", "active"),
        ], initial={"name": name, "email": email, "active": "yes" if int(active) else "no"})
        if not data:
            return
        active2 = 1 if data["active"].lower() in ("yes", "y", "1", "true") else 0
        try:
            self.db.update_customer(cid, data["name"], data["email"], active2)
        except sqlite3.IntegrityError as e:
            messagebox.showerror("DB error", f"Could not update.\n\n{e}")
            return
        self.refresh_customers()

    def toggle_customer_active(self):
        cid = self._selected_customer_id()
        if not cid:
            messagebox.showerror("No selection", "Select a customer.")
            return
        row = self.db.get_customer(cid)
        if not row:
            return
        active = int(row[3])
        self.db.set_customer_active(cid, 0 if active else 1)
        self.refresh_customers()

    def view_customer_history(self):
        cid = self._selected_customer_id()
        if not cid:
            messagebox.showerror("No selection", "Select a customer.")
            return
        row = self.db.get_customer(cid)
        if not row:
            return
        _id, name, email, _a = row
        hist = self.db.customer_history(cid)
        lines = [f"Purchase history for {name} <{email}>", "=" * 60]
        for sid, rno, ts, total, status in hist:
            lines.append(f"{ts}  {rno:10}  {cents_to_money(total):>10}  {status}")
        if not hist:
            lines.append("(no sales)")
        Dialog.show_text(self.root, "Customer History", "\n".join(lines))

    def export_customers_csv(self):
        path = filedialog.asksaveasfilename(defaultextension=".csv", filetypes=[("CSV", "*.csv")], title="Export Customers CSV")
        if not path:
            return
        q = "SELECT name, email, is_active FROM customers ORDER BY name;"
        self.db.export_table_to_csv(q, ["name", "email", "is_active"], path)
        messagebox.showinfo("Exported", f"Saved:\n{path}")

    # ---------------- POS tab ----------------
    def _build_pos_tab(self):
        tab = ttk.Frame(self.notebook)
        self.notebook.add(tab, text="POS")
        self.pos_tab = tab

        top = ttk.Frame(tab)
        top.pack(fill="x", padx=10, pady=10)

        ttk.Label(top, text="Scan/Type Barcode or Title:").pack(side="left")
        self.scan_var = tk.StringVar()
        scan_entry = ttk.Entry(top, textvariable=self.scan_var, width=40)
        scan_entry.pack(side="left", padx=(6, 12))
        scan_entry.bind("<Return>", lambda _e: self.scan_add())

        ttk.Label(top, text="Qty:").pack(side="left")
        self.scan_qty_var = tk.StringVar(value="1")
        ttk.Entry(top, textvariable=self.scan_qty_var, width=6).pack(side="left", padx=(6, 12))

        ttk.Button(top, text="Add from scan", command=self.scan_add).pack(side="left")
        ttk.Button(top, text="Clear cart", command=self.clear_cart).pack(side="left", padx=8)

        body = ttk.Frame(tab)
        body.pack(fill="both", expand=True, padx=10, pady=(0, 10))

        left = ttk.Frame(body)
        left.pack(side="left", fill="both", expand=False, padx=(0, 10))
        right = ttk.Frame(body)
        right.pack(side="left", fill="both", expand=True)

        ttk.Label(left, text="Customer (required)").pack(anchor="w")
        self.pos_customer_tree = ttk.Treeview(left, columns=("name", "email"), show="headings", height=8)
        self.pos_customer_tree.heading("name", text="Name")
        self.pos_customer_tree.heading("email", text="Email")
        self.pos_customer_tree.column("name", width=220)
        self.pos_customer_tree.column("email", width=260)
        self.pos_customer_tree.pack(fill="x", pady=(4, 10))

        ttk.Label(left, text="Titles (double-click to add)").pack(anchor="w")
        self.pos_books_tree = ttk.Treeview(left, columns=("isbn", "title", "price", "stock"), show="headings", height=14)
        self.pos_books_tree.heading("isbn", text="Barcode")
        self.pos_books_tree.heading("title", text="Title")
        self.pos_books_tree.heading("price", text="Price")
        self.pos_books_tree.heading("stock", text="Stock")
        self.pos_books_tree.column("isbn", width=140)
        self.pos_books_tree.column("title", width=280)
        self.pos_books_tree.column("price", width=90, anchor="e")
        self.pos_books_tree.column("stock", width=60, anchor="center")
        self.pos_books_tree.pack(fill="x", pady=(4, 6))
        self.pos_books_tree.bind("<Double-1>", lambda _e: self.add_selected_book_to_cart())

        addrow = ttk.Frame(left)
        addrow.pack(fill="x", pady=(0, 10))
        ttk.Label(addrow, text="Add qty:").pack(side="left")
        self.add_qty_var = tk.StringVar(value="1")
        ttk.Entry(addrow, textvariable=self.add_qty_var, width=6).pack(side="left", padx=(6, 10))
        ttk.Button(addrow, text="Add Selected Title", command=self.add_selected_book_to_cart).pack(side="left")

        # Cart
        cartbox = ttk.LabelFrame(right, text="Cart (double-click Qty/LineDisc to edit)")
        cartbox.pack(fill="x", pady=(0, 10))

        self.cart_tree = ttk.Treeview(cartbox, columns=("title", "qty", "unit", "linedisc", "line"), show="headings", height=10)
        self.cart_tree.heading("title", text="Title")
        self.cart_tree.heading("qty", text="Qty")
        self.cart_tree.heading("unit", text="Unit")
        self.cart_tree.heading("linedisc", text="Line Disc")
        self.cart_tree.heading("line", text="Line Total")
        self.cart_tree.column("title", width=360)
        self.cart_tree.column("qty", width=60, anchor="center")
        self.cart_tree.column("unit", width=90, anchor="e")
        self.cart_tree.column("linedisc", width=90, anchor="e")
        self.cart_tree.column("line", width=110, anchor="e")
        self.cart_tree.pack(fill="x", padx=10, pady=10)
        self.cart_tree.bind("<Double-1>", self._cart_inline_edit)

        btnrow = ttk.Frame(cartbox)
        btnrow.pack(fill="x", padx=10, pady=(0, 10))
        ttk.Button(btnrow, text="Remove Selected", command=self.remove_selected_cart).pack(side="left")
        ttk.Button(btnrow, text="+1", command=lambda: self.bump_cart_qty(1)).pack(side="left", padx=6)
        ttk.Button(btnrow, text="-1", command=lambda: self.bump_cart_qty(-1)).pack(side="left", padx=6)

        # Totals / checkout
        totals = ttk.LabelFrame(right, text="Checkout")
        totals.pack(fill="x")

        row1 = ttk.Frame(totals)
        row1.pack(fill="x", padx=10, pady=8)

        ttk.Label(row1, text="Order discount ($):").pack(side="left")
        self.order_disc_var = tk.StringVar(value="0.00")
        ttk.Entry(row1, textvariable=self.order_disc_var, width=10).pack(side="left", padx=(6, 12))

        ttk.Label(row1, text="Coupon code:").pack(side="left")
        self.coupon_var = tk.StringVar(value="")
        ttk.Entry(row1, textvariable=self.coupon_var, width=14).pack(side="left", padx=(6, 12))
        ttk.Button(row1, text="Apply", command=self.refresh_cart).pack(side="left")

        ttk.Label(row1, text="Tax rate:").pack(side="left", padx=(12, 0))
        self.tax_var = tk.StringVar(value=self.db.get_setting("tax_rate_default") or "0.00")
        ttk.Entry(row1, textvariable=self.tax_var, width=10).pack(side="left", padx=(6, 0))

        row2 = ttk.Frame(totals)
        row2.pack(fill="x", padx=10, pady=(0, 8))

        ttk.Label(row2, text="Payment method:").pack(side="left")
        self.pay_method = tk.StringVar(value="cash")
        ttk.Combobox(row2, textvariable=self.pay_method, values=["cash", "card", "other"], width=10, state="readonly").pack(side="left", padx=(6, 12))

        ttk.Label(row2, text="Payment status:").pack(side="left")
        self.pay_status = tk.StringVar(value="paid")
        ttk.Combobox(row2, textvariable=self.pay_status, values=["paid", "unpaid", "partial"], width=10, state="readonly").pack(side="left", padx=(6, 12))

        ttk.Label(row2, text="Note:").pack(side="left")
        self.note_var = tk.StringVar(value="")
        ttk.Entry(row2, textvariable=self.note_var, width=30).pack(side="left", padx=(6, 0))

        row3 = ttk.Frame(totals)
        row3.pack(fill="x", padx=10, pady=(0, 10))

        self.sub_lbl = ttk.Label(row3, text="Subtotal: $0.00")
        self.sub_lbl.pack(side="left", padx=(0, 14))
        self.tax_lbl = ttk.Label(row3, text="Tax: $0.00")
        self.tax_lbl.pack(side="left", padx=(0, 14))
        self.total_lbl = ttk.Label(row3, text="Total: $0.00")
        self.total_lbl.pack(side="left", padx=(0, 14))
        ttk.Button(row3, text="Finalize Sale", command=self.finalize_sale).pack(side="right")

    def _refresh_pos_customers(self):
        if not hasattr(self, "pos_customer_tree"):
            return
        for i in self.pos_customer_tree.get_children():
            self.pos_customer_tree.delete(i)
        for cid, name, email, active in self.db.list_customers("", include_inactive=False):
            self.pos_customer_tree.insert("", "end", iid=str(cid), values=(name, email))

    def _refresh_pos_books(self):
        if not hasattr(self, "pos_books_tree"):
            return
        for i in self.pos_books_tree.get_children():
            self.pos_books_tree.delete(i)
        for (bid, isbn, title, author, location, price, cost, stock, active, cat) in self.db.list_books("", in_stock_only=False, include_inactive=False):
            self.pos_books_tree.insert("", "end", iid=str(bid), values=(isbn or "", title, cents_to_money(price), stock))

    def scan_add(self):
        text = self.scan_var.get().strip()
        if not text:
            return
        try:
            qty_raw = self.scan_qty_var.get().strip()
            qty = int(qty_raw) if qty_raw else 1
            if qty <= 0:
                raise ValueError
        except Exception:
            messagebox.showerror("Bad qty", "Scan qty must be a positive integer.")
            return

        # Try barcode exact first
        barcode = normalize_barcode(text)
        rows = self.db.list_books(search=barcode or text, in_stock_only=False, include_inactive=False)

        pick = None
        if barcode:
            for r in rows:
                if (r[1] or "") == barcode:
                    pick = r
                    break
        if pick is None and rows:
            pick = rows[0]

        if not pick:
            messagebox.showerror("Not found", "No matching title found.")
            return

        bid = int(pick[0])
        self._add_to_cart(bid, qty)
        self.scan_var.set("")
        self.scan_qty_var.set("1")
        self.refresh_cart()

    def add_selected_book_to_cart(self):
        sel = self.pos_books_tree.selection()
        if not sel:
            messagebox.showerror("No selection", "Select a title.")
            return
        try:
            qty = int(self.add_qty_var.get().strip())
            if qty <= 0:
                raise ValueError
        except Exception:
            messagebox.showerror("Bad qty", "Quantity must be a positive integer.")
            return
        self._add_to_cart(int(sel[0]), qty)
        self.refresh_cart()

    def _add_to_cart(self, book_id: int, qty: int):
        b = self.db.get_book(book_id)
        if not b:
            raise ValueError("title missing")
        _id, isbn, title, author, cat_id, location, price, cost, stock, active = b
        if not int(active):
            raise ValueError("archived")
        if book_id in self.cart:
            self.cart[book_id]["qty"] += qty
        else:
            self.cart[book_id] = {
                "title": title,
                "qty": qty,
                "unit_price": int(price),
                "unit_cost": int(cost),
                "line_disc": 0
            }

    def clear_cart(self):
        self.cart.clear()
        self.refresh_cart()

    def remove_selected_cart(self):
        sel = self.cart_tree.selection()
        if not sel:
            return
        bid = int(sel[0])
        if bid in self.cart:
            del self.cart[bid]
        self.refresh_cart()

    def bump_cart_qty(self, delta: int):
        sel = self.cart_tree.selection()
        if not sel:
            return
        bid = int(sel[0])
        if bid not in self.cart:
            return
        self.cart[bid]["qty"] += int(delta)
        if self.cart[bid]["qty"] <= 0:
            del self.cart[bid]
        self.refresh_cart()

    def _cart_inline_edit(self, event):
        region = self.cart_tree.identify("region", event.x, event.y)
        if region != "cell":
            return
        row_id = self.cart_tree.identify_row(event.y)
        col = self.cart_tree.identify_column(event.x)
        if not row_id:
            return
        if col not in ("#2", "#4"):
            return

        x, y, w, h = self.cart_tree.bbox(row_id, col)
        colname = self.cart_tree["columns"][int(col[1:]) - 1]
        old = self.cart_tree.set(row_id, colname)

        entry = ttk.Entry(self.cart_tree)
        entry.place(x=x, y=y, width=w, height=h)
        entry.insert(0, old.replace("$", "").strip())
        entry.focus_set()

        def commit(_e=None):
            val = entry.get().strip()
            entry.destroy()
            bid = int(row_id)
            if bid not in self.cart:
                return
            try:
                if col == "#2":
                    q = int(val)
                    if q <= 0:
                        raise ValueError
                    self.cart[bid]["qty"] = q
                else:
                    disc = dollars_to_cents(val) if val else 0
                    line_sub = self.cart[bid]["unit_price"] * self.cart[bid]["qty"]
                    if disc < 0 or disc > line_sub:
                        raise ValueError
                    self.cart[bid]["line_disc"] = disc
            except Exception:
                messagebox.showerror("Invalid", "Bad value.")
            self.refresh_cart()

        entry.bind("<Return>", commit)
        entry.bind("<FocusOut>", commit)

    def refresh_cart(self):
        for i in self.cart_tree.get_children():
            self.cart_tree.delete(i)

        coupon = self.db.get_coupon_by_code(self.coupon_var.get())
        coupon_code = coupon["code"] if coupon else None

        try:
            order_disc = dollars_to_cents(self.order_disc_var.get()) if self.order_disc_var.get().strip() else 0
        except Exception:
            order_disc = 0

        try:
            tax_rate = float(self.tax_var.get().strip())
            if tax_rate < 0:
                raise ValueError
        except Exception:
            tax_rate = 0.0

        item_total = 0
        for bid, it in self.cart.items():
            qty = int(it["qty"])
            unit = int(it["unit_price"])
            line_sub = unit * qty
            line_disc = min(max(int(it.get("line_disc", 0)), 0), line_sub)
            line_total = line_sub - line_disc
            item_total += line_total

            self.cart_tree.insert("", "end", iid=str(bid), values=(
                it["title"], qty, cents_to_money(unit), cents_to_money(line_disc), cents_to_money(line_total)
            ))

        coupon_disc = 0
        if coupon_code and item_total > 0:
            if coupon["kind"] == "percent":
                coupon_disc = int(round(item_total * (coupon["value"] / 100.0)))
            else:
                coupon_disc = int(round(coupon["value"] * 100.0)) if coupon["value"] < 1000 else int(coupon["value"])
            coupon_disc = min(coupon_disc, item_total)

        total_discount = min(order_disc + coupon_disc, item_total)
        sub_after = item_total - total_discount
        tax_cents = int(round(sub_after * tax_rate))
        total = sub_after + tax_cents

        self.sub_lbl.configure(text=f"Subtotal: {cents_to_money(sub_after)}")
        self.tax_lbl.configure(text=f"Tax: {cents_to_money(tax_cents)}")
        self.total_lbl.configure(text=f"Total: {cents_to_money(total)}")

    def finalize_sale(self):
        csel = self.pos_customer_tree.selection()
        if not csel:
            messagebox.showerror("Customer required", "Select a customer.")
            return
        if not self.cart:
            messagebox.showerror("Cart empty", "Add items first.")
            return

        customer_id = int(csel[0])

        cart_items = []
        for bid, it in self.cart.items():
            cart_items.append({
                "book_id": int(bid),
                "qty": int(it["qty"]),
                "unit_price_cents": int(it["unit_price"]),
                "unit_cost_cents": int(it["unit_cost"]),
                "line_discount_cents": int(it.get("line_disc", 0)),
            })

        try:
            tax_rate = float(self.tax_var.get().strip())
            if tax_rate < 0:
                raise ValueError
        except Exception:
            messagebox.showerror("Bad tax rate", "Tax rate must be non-negative (e.g. 0.07).")
            return

        try:
            order_disc = dollars_to_cents(self.order_disc_var.get()) if self.order_disc_var.get().strip() else 0
        except Exception:
            messagebox.showerror("Bad discount", "Order discount must be a valid dollar amount.")
            return

        coupon_code = self.coupon_var.get().strip().upper() or None
        pay_method = self.pay_method.get()
        pay_status = self.pay_status.get()
        note = self.note_var.get().strip()

        try:
            sale_id, receipt_no, receipt_text = self.db.create_sale(
                customer_id=customer_id,
                cart_items=cart_items,
                tax_rate=tax_rate,
                order_discount_cents=order_disc,
                coupon_code=coupon_code,
                payment_method=pay_method,
                payment_status=pay_status,
                note=note
            )
        except Exception as e:
            messagebox.showerror("Sale failed", str(e))
            return

        self.clear_cart()
        self.refresh_sales()
        self.refresh_books()     # stock changed
        self.refresh_reports()
        Dialog.show_text(self.root, f"Receipt {receipt_no}", receipt_text)

    # ---------------- Sales & Returns tab ----------------
    def _build_sales_tab(self):
        tab = ttk.Frame(self.notebook)
        self.notebook.add(tab, text="Sales & Returns")
        self.sales_tab = tab

        top = ttk.Frame(tab)
        top.pack(fill="x", padx=10, pady=10)

        ttk.Button(top, text="Refresh", command=self.refresh_sales).pack(side="left")
        ttk.Button(top, text="View Receipt", command=self.view_sale_receipt).pack(side="left", padx=6)
        ttk.Button(top, text="Export Receipt TXT", command=self.export_sale_txt).pack(side="left", padx=6)
        ttk.Button(top, text="Export Receipt PDF", command=self.export_sale_pdf).pack(side="left", padx=6)

        ttk.Separator(top, orient="vertical").pack(side="left", fill="y", padx=10)

        ttk.Button(top, text="Create Return (selected sale)", command=self.create_return_ui).pack(side="left")
        ttk.Button(top, text="View Return Receipt", command=self.view_return_receipt).pack(side="left", padx=6)
        ttk.Button(top, text="Export Return PDF", command=self.export_return_pdf).pack(side="left", padx=6)

        body = ttk.Frame(tab)
        body.pack(fill="both", expand=True, padx=10, pady=(0, 10))

        left = ttk.Frame(body)
        left.pack(side="left", fill="both", expand=True, padx=(0, 10))
        right = ttk.Frame(body)
        right.pack(side="left", fill="both", expand=True)

        ttk.Label(left, text="Sales").pack(anchor="w")
        self.sales_tree = ttk.Treeview(left, columns=("rno", "ts", "cust", "total", "status", "void"), show="headings", height=18)
        for c, l, w, a in [
            ("rno", "Receipt", 100, "w"),
            ("ts", "Date/Time", 160, "w"),
            ("cust", "Customer", 220, "w"),
            ("total", "Total", 100, "e"),
            ("status", "Pay", 80, "center"),
            ("void", "Void", 60, "center"),
        ]:
            self.sales_tree.heading(c, text=l)
            self.sales_tree.column(c, width=w, anchor=a)
        self.sales_tree.pack(fill="both", expand=True)
        self.sales_tree.bind("<Double-1>", lambda _e: self.view_sale_receipt())

        ttk.Label(right, text="Returns").pack(anchor="w")
        self.returns_tree = ttk.Treeview(right, columns=("ts", "orig", "refund", "method"), show="headings", height=18)
        for c, l, w, a in [
            ("ts", "Date/Time", 160, "w"),
            ("orig", "Original Receipt", 120, "w"),
            ("refund", "Refund", 100, "e"),
            ("method", "Method", 80, "center"),
        ]:
            self.returns_tree.heading(c, text=l)
            self.returns_tree.column(c, width=w, anchor=a)
        self.returns_tree.pack(fill="both", expand=True)
        self.returns_tree.bind("<Double-1>", lambda _e: self.view_return_receipt())

    def refresh_sales(self):
        for i in self.sales_tree.get_children():
            self.sales_tree.delete(i)
        for sid, rno, ts, cust, total, status, is_void in self.db.list_sales(400):
            self.sales_tree.insert("", "end", iid=str(sid), values=(rno, ts, cust, cents_to_money(total), status, "yes" if is_void else "no"))

        for i in self.returns_tree.get_children():
            self.returns_tree.delete(i)
        for rid, ts, orig_rno, refund, method in self.db.list_returns(300):
            self.returns_tree.insert("", "end", iid=str(rid), values=(ts, orig_rno, cents_to_money(refund), method))

    def _selected_sale_id(self) -> Optional[int]:
        sel = self.sales_tree.selection()
        return int(sel[0]) if sel else None

    def view_sale_receipt(self):
        sid = self._selected_sale_id()
        if not sid:
            messagebox.showerror("No selection", "Select a sale.")
            return
        row = self.db.get_sale_receipt(sid)
        if not row:
            messagebox.showerror("Missing", "Receipt not found.")
            return
        receipt_text, rno, ts = row
        Dialog.show_text(self.root, f"Receipt {rno}", receipt_text)

    def export_sale_txt(self):
        sid = self._selected_sale_id()
        if not sid:
            messagebox.showerror("No selection", "Select a sale.")
            return
        row = self.db.get_sale_receipt(sid)
        if not row:
            return
        receipt_text, rno, _ = row
        path = filedialog.asksaveasfilename(defaultextension=".txt", filetypes=[("Text", "*.txt")], initialfile=f"{rno}.txt")
        if not path:
            return
        with open(path, "w", encoding="utf-8") as f:
            f.write(receipt_text)
        messagebox.showinfo("Saved", f"Saved:\n{path}")

    def export_sale_pdf(self):
        sid = self._selected_sale_id()
        if not sid:
            messagebox.showerror("No selection", "Select a sale.")
            return
        row = self.db.get_sale_receipt(sid)
        if not row:
            return
        receipt_text, rno, _ = row
        path = filedialog.asksaveasfilename(defaultextension=".pdf", filetypes=[("PDF", "*.pdf")], initialfile=f"{rno}.pdf")
        if not path:
            return
        try:
            export_pdf_text(receipt_text, path, title=rno)
        except Exception as e:
            messagebox.showerror("PDF error", f"{e}\n\nInstall reportlab: pip install reportlab")
            return
        messagebox.showinfo("Saved", f"Saved:\n{path}")

    def create_return_ui(self):
        sid = self._selected_sale_id()
        if not sid:
            messagebox.showerror("No selection", "Select a sale.")
            return

        items = self.db.get_sale_items(sid)
        if not items:
            messagebox.showerror("No items", "No sale items found.")
            return

        dlg = tk.Toplevel(self.root)
        dlg.title("Create Return")
        dlg.geometry("720x460")
        dlg.transient(self.root)
        dlg.grab_set()

        ttk.Label(dlg, text="Enter return qty for each item (0 = not returned)").pack(anchor="w", padx=10, pady=(10, 0))

        frame = ttk.Frame(dlg, padding=10)
        frame.pack(fill="both", expand=True)

        rows = []
        for i, (book_id, title, qty, unit, line_total) in enumerate(items):
            ttk.Label(frame, text=title).grid(row=i, column=0, sticky="w", pady=4)
            ttk.Label(frame, text=f"Sold: {qty} @ {cents_to_money(unit)}").grid(row=i, column=1, sticky="w", pady=4)
            var = tk.StringVar(value="0")
            ttk.Entry(frame, textvariable=var, width=6).grid(row=i, column=2, pady=4)
            rows.append((book_id, qty, var))

        reason_var = tk.StringVar(value="")
        method_var = tk.StringVar(value="cash")

        bottom = ttk.Frame(dlg, padding=10)
        bottom.pack(fill="x")
        ttk.Label(bottom, text="Reason:").pack(side="left")
        ttk.Entry(bottom, textvariable=reason_var, width=30).pack(side="left", padx=(6, 12))
        ttk.Label(bottom, text="Refund method:").pack(side="left")
        ttk.Combobox(bottom, textvariable=method_var, values=["cash", "card", "other"], width=10, state="readonly").pack(side="left", padx=(6, 12))

        def do_return():
            pick = []
            for book_id, sold_qty, var in rows:
                try:
                    rq = int(var.get().strip())
                except Exception:
                    rq = 0
                if rq > 0:
                    if rq > sold_qty:
                        messagebox.showerror("Bad qty", "Return qty cannot exceed sold qty.", parent=dlg)
                        return
                    pick.append((book_id, rq))
            if not pick:
                messagebox.showerror("No items", "You must return at least one item.", parent=dlg)
                return
            try:
                rid, receipt_text = self.db.create_return(sid, pick, reason_var.get().strip(), method_var.get())
            except Exception as e:
                messagebox.showerror("Return failed", str(e), parent=dlg)
                return
            dlg.destroy()
            self.refresh_sales()
            self.refresh_books()
            self.refresh_reports()
            Dialog.show_text(self.root, f"Return #{rid}", receipt_text)

        ttk.Button(bottom, text="Cancel", command=dlg.destroy).pack(side="right")
        ttk.Button(bottom, text="Create Return", command=do_return).pack(side="right", padx=8)

        self.root.wait_window(dlg)

    def _selected_return_id(self) -> Optional[int]:
        sel = self.returns_tree.selection()
        return int(sel[0]) if sel else None

    def view_return_receipt(self):
        rid = self._selected_return_id()
        if not rid:
            messagebox.showerror("No selection", "Select a return.")
            return
        row = self.db.get_return_receipt(rid)
        if not row:
            return
        receipt_text, ts = row
        Dialog.show_text(self.root, f"Return #{rid}", receipt_text)

    def export_return_pdf(self):
        rid = self._selected_return_id()
        if not rid:
            messagebox.showerror("No selection", "Select a return.")
            return
        row = self.db.get_return_receipt(rid)
        if not row:
            return
        receipt_text, _ = row
        path = filedialog.asksaveasfilename(defaultextension=".pdf", filetypes=[("PDF", "*.pdf")], initialfile=f"return_{rid}.pdf")
        if not path:
            return
        try:
            export_pdf_text(receipt_text, path, title=f"Return {rid}")
        except Exception as e:
            messagebox.showerror("PDF error", f"{e}\n\nInstall reportlab: pip install reportlab")
            return
        messagebox.showinfo("Saved", f"Saved:\n{path}")

    # ---------------- Reports tab ----------------
    def _build_reports_tab(self):
        tab = ttk.Frame(self.notebook)
        self.notebook.add(tab, text="Reports")
        self.reports_tab = tab

        top = ttk.Frame(tab)
        top.pack(fill="x", padx=10, pady=10)
        ttk.Button(top, text="Refresh", command=self.refresh_reports).pack(side="left")
        ttk.Button(top, text="Export Sales CSV", command=self.export_sales_csv).pack(side="right")
        ttk.Button(top, text="Export Tax CSV", command=self.export_tax_csv).pack(side="right", padx=8)

        body = ttk.Frame(tab)
        body.pack(fill="both", expand=True, padx=10, pady=(0, 10))

        left = ttk.Frame(body)
        left.pack(side="left", fill="both", expand=True, padx=(0, 10))
        right = ttk.Frame(body)
        right.pack(side="left", fill="both", expand=True)

        daily = ttk.LabelFrame(left, text="Daily (last 30 days) — revenue, refunds, net, tax")
        daily.pack(fill="both", expand=True, pady=(0, 10))
        self.daily_tree = ttk.Treeview(daily, columns=("day", "sales", "returns", "rev", "refund", "net", "tax"), show="headings", height=10)
        for c, l, w, a in [
            ("day", "Day", 110, "w"),
            ("sales", "Sales", 60, "center"),
            ("returns", "Returns", 70, "center"),
            ("rev", "Revenue", 100, "e"),
            ("refund", "Refunds", 100, "e"),
            ("net", "Net", 100, "e"),
            ("tax", "Tax", 90, "e"),
        ]:
            self.daily_tree.heading(c, text=l)
            self.daily_tree.column(c, width=w, anchor=a)
        self.daily_tree.pack(fill="both", expand=True, padx=10, pady=10)

        monthly = ttk.LabelFrame(left, text="Monthly totals")
        monthly.pack(fill="both", expand=True)
        self.monthly_tree = ttk.Treeview(monthly, columns=("month", "sales", "rev", "tax"), show="headings", height=8)
        for c, l, w, a in [
            ("month", "Month", 110, "w"),
            ("sales", "Sales", 60, "center"),
            ("rev", "Revenue", 120, "e"),
            ("tax", "Tax", 100, "e"),
        ]:
            self.monthly_tree.heading(c, text=l)
            self.monthly_tree.column(c, width=w, anchor=a)
        self.monthly_tree.pack(fill="both", expand=True, padx=10, pady=10)

        topbooks = ttk.LabelFrame(right, text="Top titles (revenue + profit)")
        topbooks.pack(fill="both", expand=True, pady=(0, 10))
        self.top_books = ttk.Treeview(topbooks, columns=("title", "units", "rev", "profit"), show="headings", height=8)
        for c, l, w, a in [
            ("title", "Title", 260, "w"),
            ("units", "Units", 70, "center"),
            ("rev", "Revenue", 120, "e"),
            ("profit", "Profit", 120, "e"),
        ]:
            self.top_books.heading(c, text=l)
            self.top_books.column(c, width=w, anchor=a)
        self.top_books.pack(fill="both", expand=True, padx=10, pady=10)

        topcust = ttk.LabelFrame(right, text="Top customers (revenue)")
        topcust.pack(fill="both", expand=True, pady=(0, 10))
        self.top_customers = ttk.Treeview(topcust, columns=("name", "sales", "rev"), show="headings", height=6)
        for c, l, w, a in [
            ("name", "Customer", 220, "w"),
            ("sales", "Sales", 60, "center"),
            ("rev", "Revenue", 120, "e"),
        ]:
            self.top_customers.heading(c, text=l)
            self.top_customers.column(c, width=w, anchor=a)
        self.top_customers.pack(fill="both", expand=True, padx=10, pady=10)

        bycat = ttk.LabelFrame(right, text="By format (revenue + profit)")
        bycat.pack(fill="both", expand=True)
        self.by_category = ttk.Treeview(bycat, columns=("cat", "rev", "profit"), show="headings", height=6)
        for c, l, w, a in [
            ("cat", "Format", 220, "w"),
            ("rev", "Revenue", 120, "e"),
            ("profit", "Profit", 120, "e"),
        ]:
            self.by_category.heading(c, text=l)
            self.by_category.column(c, width=w, anchor=a)
        self.by_category.pack(fill="both", expand=True, padx=10, pady=10)

    def refresh_reports(self):
        for t in (self.daily_tree, self.monthly_tree, self.top_books, self.top_customers, self.by_category):
            for i in t.get_children():
                t.delete(i)

        for d, scnt, rcnt, rev, refund, net, tax in self.db.report_daily(30):
            self.daily_tree.insert("", "end", values=(d, scnt, rcnt, cents_to_money(rev), cents_to_money(refund), cents_to_money(net), cents_to_money(tax)))

        for month, rev, tax, scnt in self.db.report_monthly():
            self.monthly_tree.insert("", "end", values=(month, scnt, cents_to_money(rev), cents_to_money(tax)))

        for title, units, rev, profit in self.db.report_top_books(10):
            self.top_books.insert("", "end", values=(title, units, cents_to_money(rev), cents_to_money(profit)))

        for name, sales, rev in self.db.report_top_customers(10):
            self.top_customers.insert("", "end", values=(name, sales, cents_to_money(rev)))

        for cat, rev, profit in self.db.report_by_category():
            self.by_category.insert("", "end", values=(cat, cents_to_money(rev), cents_to_money(profit)))

    def export_sales_csv(self):
        path = filedialog.asksaveasfilename(defaultextension=".csv", filetypes=[("CSV", "*.csv")], title="Export Sales CSV")
        if not path:
            return
        q = """
            SELECT receipt_no, created_at, customer_id, subtotal_cents, discount_cents, coupon_code, tax_rate, tax_cents,
                   total_cents, payment_method, payment_status, note, is_void
            FROM sales
            ORDER BY id DESC;
        """
        self.db.export_table_to_csv(q,
            ["receipt_no", "created_at", "customer_id", "subtotal_cents", "discount_cents", "coupon_code", "tax_rate", "tax_cents",
             "total_cents", "payment_method", "payment_status", "note", "is_void"], path)
        messagebox.showinfo("Exported", f"Saved:\n{path}")

    def export_tax_csv(self):
        path = filedialog.asksaveasfilename(defaultextension=".csv", filetypes=[("CSV", "*.csv")], title="Export Tax CSV")
        if not path:
            return
        with self.db._connect() as conn:
            has_refund_tax = "refund_tax_cents" in self.db._columns(conn, "returns")
        q = """
            WITH sales_daily AS (
                SELECT substr(created_at,1,10) AS day,
                       SUM(tax_cents) AS tax_cents,
                       SUM(total_cents) AS total_cents
                FROM sales
                WHERE is_void=0
                GROUP BY day
            ),
            returns_daily AS (
                SELECT substr(created_at,1,10) AS day,
                       SUM(refund_cents) AS refund_cents,
                       SUM({refund_tax_col}) AS refund_tax_cents
                FROM returns
                GROUP BY day
            )
            SELECT COALESCE(sales_daily.day, returns_daily.day) AS day,
                   IFNULL(sales_daily.tax_cents, 0) - IFNULL(returns_daily.refund_tax_cents, 0) AS tax_cents,
                   IFNULL(sales_daily.total_cents, 0) - IFNULL(returns_daily.refund_cents, 0) AS total_cents
            FROM sales_daily
            LEFT JOIN returns_daily ON returns_daily.day = sales_daily.day
            UNION
            SELECT COALESCE(sales_daily.day, returns_daily.day) AS day,
                   IFNULL(sales_daily.tax_cents, 0) - IFNULL(returns_daily.refund_tax_cents, 0) AS tax_cents,
                   IFNULL(sales_daily.total_cents, 0) - IFNULL(returns_daily.refund_cents, 0) AS total_cents
            FROM returns_daily
            LEFT JOIN sales_daily ON sales_daily.day = returns_daily.day
            ORDER BY day DESC;
        """
        refund_tax_col = "refund_tax_cents" if has_refund_tax else "0"
        q = q.format(refund_tax_col=refund_tax_col)
        self.db.export_table_to_csv(q, ["day", "tax_cents", "total_cents"], path)
        messagebox.showinfo("Exported", f"Saved:\n{path}")

    # ---------------- Admin tab ----------------
    def _build_admin_tab(self):
        tab = ttk.Frame(self.notebook)
        self.notebook.add(tab, text="Admin")
        self.admin_tab = tab

        banner = ttk.Label(tab, text="Admin tools (requires admin role for changes).")
        banner.pack(anchor="w", padx=10, pady=(10, 0))

        body = ttk.Frame(tab)
        body.pack(fill="both", expand=True, padx=10, pady=10)

        left = ttk.Frame(body)
        left.pack(side="left", fill="both", expand=True, padx=(0, 10))
        right = ttk.Frame(body)
        right.pack(side="left", fill="both", expand=True)

        settings = ttk.LabelFrame(left, text="Store / Receipt Settings")
        settings.pack(fill="x", pady=(0, 10))

        self.set_store = tk.StringVar(value=self.db.get_setting("store_name"))
        self.set_addr = tk.StringVar(value=self.db.get_setting("store_address"))
        self.set_phone = tk.StringVar(value=self.db.get_setting("store_phone"))
        self.set_footer = tk.StringVar(value=self.db.get_setting("receipt_footer"))
        self.set_prefix = tk.StringVar(value=self.db.get_setting("receipt_prefix"))
        self.set_taxdef = tk.StringVar(value=self.db.get_setting("tax_rate_default"))

        def row(parent, label, var, show: str = ""):
            r = ttk.Frame(parent)
            r.pack(fill="x", padx=10, pady=4)
            ttk.Label(r, text=label, width=18).pack(side="left")
            ttk.Entry(r, textvariable=var, width=50, show=show).pack(side="left")

        row(settings, "Store name:", self.set_store)
        row(settings, "Address:", self.set_addr)
        row(settings, "Phone:", self.set_phone)
        row(settings, "Footer:", self.set_footer)
        row(settings, "Receipt prefix:", self.set_prefix)
        row(settings, "Default tax:", self.set_taxdef)
        ttk.Button(settings, text="Save Settings", command=self.save_settings).pack(anchor="e", padx=10, pady=(6, 10))

        backup = ttk.LabelFrame(left, text="Backup / Restore")
        backup.pack(fill="x")
        bbtn = ttk.Frame(backup)
        bbtn.pack(fill="x", padx=10, pady=10)
        ttk.Button(bbtn, text="Backup DB", command=self.backup_db).pack(side="left")
        ttk.Button(bbtn, text="Restore DB", command=self.restore_db).pack(side="left", padx=8)

        cats = ttk.LabelFrame(right, text="Formats")
        cats.pack(fill="both", expand=True, pady=(0, 10))

        self.cat_tree = ttk.Treeview(cats, columns=("name", "active"), show="headings", height=6)
        self.cat_tree.heading("name", text="Name")
        self.cat_tree.heading("active", text="Active")
        self.cat_tree.column("name", width=220)
        self.cat_tree.column("active", width=80, anchor="center")
        self.cat_tree.pack(fill="x", padx=10, pady=10)

        catbtn = ttk.Frame(cats)
        catbtn.pack(fill="x", padx=10, pady=(0, 10))
        ttk.Button(catbtn, text="Add", command=self.add_category).pack(side="left")
        ttk.Button(catbtn, text="Toggle Active", command=self.toggle_category).pack(side="left", padx=8)
        ttk.Button(catbtn, text="Refresh", command=self.refresh_admin_lists).pack(side="right")

        coupons = ttk.LabelFrame(right, text="Coupons")
        coupons.pack(fill="both", expand=True, pady=(0, 10))

        self.coupon_tree = ttk.Treeview(coupons, columns=("code", "kind", "value", "active", "expires"), show="headings", height=6)
        for c, l, w, a in [
            ("code", "Code", 120, "w"),
            ("kind", "Kind", 80, "center"),
            ("value", "Value", 80, "e"),
            ("active", "Active", 70, "center"),
            ("expires", "Expires", 100, "w"),
        ]:
            self.coupon_tree.heading(c, text=l)
            self.coupon_tree.column(c, width=w, anchor=a)
        self.coupon_tree.pack(fill="x", padx=10, pady=10)

        cbtn = ttk.Frame(coupons)
        cbtn.pack(fill="x", padx=10, pady=(0, 10))
        ttk.Button(cbtn, text="Add", command=self.add_coupon).pack(side="left")
        ttk.Button(cbtn, text="Edit", command=self.edit_coupon).pack(side="left", padx=8)

        users = ttk.LabelFrame(right, text="Users")
        users.pack(fill="both", expand=True)

        self.user_tree = ttk.Treeview(users, columns=("username", "role", "active"), show="headings", height=6)
        for c, l, w, a in [
            ("username", "Username", 140, "w"),
            ("role", "Role", 80, "center"),
            ("active", "Active", 80, "center"),
        ]:
            self.user_tree.heading(c, text=l)
            self.user_tree.column(c, width=w, anchor=a)
        self.user_tree.pack(fill="x", padx=10, pady=10)

        ubtn = ttk.Frame(users)
        ubtn.pack(fill="x", padx=10, pady=(0, 10))
        ttk.Button(ubtn, text="Add User", command=self.add_user).pack(side="left")
        ttk.Button(ubtn, text="Toggle Active", command=self.toggle_user).pack(side="left", padx=8)
        ttk.Button(ubtn, text="Reset Password", command=self.reset_user_password).pack(side="left", padx=8)

    def refresh_admin_lists(self):
        for t in (self.cat_tree, self.coupon_tree, self.user_tree):
            for i in t.get_children():
                t.delete(i)

        for cid, name, active in self.db.list_categories(include_inactive=True):
            self.cat_tree.insert("", "end", iid=str(cid), values=(name, "yes" if active else "no"))

        for cid, code, kind, value, active, exp in self.db.list_coupons():
            val_str = f"{value:.2f}%" if kind == "percent" else f"${value:.2f}"
            self.coupon_tree.insert("", "end", iid=str(cid), values=(code, kind, val_str, "yes" if active else "no", exp or ""))

        for uid, username, role, active in self.db.list_users():
            self.user_tree.insert("", "end", iid=str(uid), values=(username, role, "yes" if active else "no"))

    def save_settings(self):
        if not self._require_admin():
            return
        self.db.set_setting("store_name", self.set_store.get().strip())
        self.db.set_setting("store_address", self.set_addr.get().strip())
        self.db.set_setting("store_phone", self.set_phone.get().strip())
        self.db.set_setting("receipt_footer", self.set_footer.get().strip())
        self.db.set_setting("receipt_prefix", self.set_prefix.get().strip() or "R")
        self.db.set_setting("tax_rate_default", self.set_taxdef.get().strip() or "0.00")
        self.tax_var.set(self.db.get_setting("tax_rate_default") or "0.00")
        messagebox.showinfo("Saved", "Settings saved.")

    def backup_db(self):
        path = filedialog.asksaveasfilename(
            defaultextension=".db",
            filetypes=[("SQLite DB", "*.db")],
            title="Backup DB",
            initialfile=f"dvd_vhs_backup_{today_ymd()}.db"
        )
        if not path:
            return
        try:
            shutil.copy2(DB_PATH, path)
        except Exception as e:
            messagebox.showerror("Backup failed", str(e))
            return
        messagebox.showinfo("Backup", f"Backup saved:\n{path}")

    def restore_db(self):
        if not self._require_admin():
            return
        path = filedialog.askopenfilename(filetypes=[("SQLite DB", "*.db"), ("All files", "*.*")], title="Select DB to restore")
        if not path:
            return
        if not messagebox.askyesno("Confirm", "This will overwrite your current DB. Continue?"):
            return
        try:
            shutil.copy2(path, DB_PATH)
        except Exception as e:
            messagebox.showerror("Restore failed", str(e))
            return
        messagebox.showinfo("Restore", "DB restored. Please restart the app.")
        self.root.destroy()

    def add_category(self):
        if not self._require_admin():
            return
        data = Dialog.ask_fields(self.root, "Add Format", [("Name", "name")])
        if not data:
            return
        try:
            self.db.add_category(data["name"])
        except sqlite3.IntegrityError as e:
            messagebox.showerror("DB error", str(e))
            return
        self.refresh_admin_lists()
        self.refresh_books()

    def toggle_category(self):
        if not self._require_admin():
            return
        sel = self.cat_tree.selection()
        if not sel:
            return
        cid = int(sel[0])
        cats = self.db.list_categories(include_inactive=True)
        cur = next((c for c in cats if c[0] == cid), None)
        if not cur:
            return
        active = int(cur[2])
        self.db.set_category_active(cid, 0 if active else 1)
        self.refresh_admin_lists()
        self.refresh_books()

    def add_coupon(self):
        if not self._require_admin():
            return
        data = Dialog.ask_fields(self.root, "Add Coupon", [
            ("Code (no spaces)", "code"),
            ("Kind (percent/fixed)", "kind"),
            ("Value (percent number OR dollars)", "value"),
            ("Active? (yes/no)", "active"),
            ("Expires on (YYYY-MM-DD or blank)", "exp"),
        ], initial={"kind": "percent", "value": "10", "active": "yes", "exp": ""})
        if not data:
            return
        kind = data["kind"].strip().lower()
        if kind not in ("percent", "fixed"):
            messagebox.showerror("Bad kind", "Kind must be percent or fixed.")
            return
        try:
            val = float(data["value"])
            if val < 0:
                raise ValueError
        except Exception:
            messagebox.showerror("Bad value", "Value must be >= 0.")
            return
        active = 1 if data["active"].lower() in ("yes", "y", "1", "true") else 0
        exp = data["exp"].strip() or None
        try:
            self.db.add_coupon(data["code"], kind, val, active, exp)
        except sqlite3.IntegrityError as e:
            messagebox.showerror("DB error", str(e))
            return
        self.refresh_admin_lists()

    def edit_coupon(self):
        if not self._require_admin():
            return
        sel = self.coupon_tree.selection()
        if not sel:
            return
        cid = int(sel[0])
        rows = self.db.list_coupons()
        row = next((r for r in rows if r[0] == cid), None)
        if not row:
            return
        _id, code, kind, value, active, exp = row
        init = {"code": code, "kind": kind, "value": str(value), "active": "yes" if active else "no", "exp": exp or ""}
        data = Dialog.ask_fields(self.root, "Edit Coupon", [
            ("Code", "code"),
            ("Kind (percent/fixed)", "kind"),
            ("Value", "value"),
            ("Active? (yes/no)", "active"),
            ("Expires on (YYYY-MM-DD or blank)", "exp"),
        ], initial=init)
        if not data:
            return
        kind2 = data["kind"].strip().lower()
        if kind2 not in ("percent", "fixed"):
            messagebox.showerror("Bad kind", "Kind must be percent or fixed.")
            return
        try:
            val2 = float(data["value"])
            if val2 < 0:
                raise ValueError
        except Exception:
            messagebox.showerror("Bad value", "Value must be >= 0.")
            return
        active2 = 1 if data["active"].lower() in ("yes", "y", "1", "true") else 0
        exp2 = data["exp"].strip() or None
        try:
            self.db.update_coupon(cid, data["code"], kind2, val2, active2, exp2)
        except sqlite3.IntegrityError as e:
            messagebox.showerror("DB error", str(e))
            return
        self.refresh_admin_lists()

    def add_user(self):
        if not self._require_admin():
            return
        data = Dialog.ask_fields(self.root, "Add User", [
            ("Username", "u"),
            ("Password", "p"),
            ("Role (admin/clerk)", "r"),
        ], initial={"r": "clerk"}, password_keys={"p"})
        if not data:
            return
        role = data["r"].strip().lower()
        if role not in ("admin", "clerk"):
            messagebox.showerror("Bad role", "Role must be admin or clerk.")
            return
        try:
            self.db.add_user(data["u"], data["p"], role)
        except sqlite3.IntegrityError as e:
            messagebox.showerror("DB error", str(e))
            return
        self.refresh_admin_lists()

    def toggle_user(self):
        if not self._require_admin():
            return
        sel = self.user_tree.selection()
        if not sel:
            return
        uid = int(sel[0])
        rows = self.db.list_users()
        row = next((r for r in rows if r[0] == uid), None)
        if not row:
            return
        active = int(row[3])
        self.db.set_user_active(uid, 0 if active else 1)
        self.refresh_admin_lists()

    def reset_user_password(self):
        if not self._require_admin():
            return
        sel = self.user_tree.selection()
        if not sel:
            return
        uid = int(sel[0])
        data = Dialog.ask_fields(self.root, "Reset Password", [("New password", "p")], password_keys={"p"})
        if not data:
            return
        self.db.reset_password(uid, data["p"])
        messagebox.showinfo("Done", "Password reset.")

    # ---------------- Global refresh ----------------
    def refresh_all(self):
        self.refresh_books()
        self.refresh_customers()
        self.refresh_cart()
        self.refresh_sales()
        self.refresh_reports()
        self.refresh_admin_lists()

    def run(self):
        self.root.mainloop()


if __name__ == "__main__":
    App().run()
