#!/usr/bin/env python3
"""Print all local Verso HTML chapters to one PDF (requires playwright and pypdf)."""
from __future__ import annotations
import asyncio
import functools
import http.server
import os
from pathlib import Path
import tempfile
import threading
from urllib.parse import urlsplit, unquote
from playwright.async_api import async_playwright
from pypdf import PdfReader, PdfWriter

ROOT = Path(__file__).resolve().parents[1]
HTML = ROOT / "_out" / "html"
OUTPUT = ROOT / "_out" / "beilinson-book.pdf"

class QuietHandler(http.server.SimpleHTTPRequestHandler):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, directory=str(HTML), **kwargs)
    def log_message(self, *args):
        pass

async def main():
    if not (HTML / "index.html").is_file():
        raise RuntimeError("Verso HTML missing: _out/html/index.html")
    server = http.server.ThreadingHTTPServer(("127.0.0.1", 0), QuietHandler)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    base = f"http://127.0.0.1:{server.server_port}"
    try:
        async with async_playwright() as playwright:
            browser = await playwright.chromium.launch(headless=True)
            try:
                page = await browser.new_page()
                pending = ["/"]
                seen = set()
                writer = PdfWriter()
                with tempfile.TemporaryDirectory() as tmp:
                    while pending:
                        route = pending.pop(0)
                        if route in seen:
                            continue
                        seen.add(route)
                        await page.goto(base + route, wait_until="networkidle")
                        await page.evaluate("document.fonts.ready")
                        # Follow links in document order, but never leave the local book.
                        links = await page.locator("a[href]").evaluate_all(
                            "(nodes) => nodes.map(n => n.href)"
                        )
                        for href in links:
                            u = urlsplit(href)
                            if u.netloc != urlsplit(base).netloc:
                                continue
                            path = unquote(u.path)
                            if path.endswith("/"):
                                target = path + "index.html"
                            elif path.endswith(".html"):
                                target = path
                            else:
                                continue
                            file = (HTML / target.lstrip("/")).resolve()
                            if not file.is_relative_to(HTML.resolve()) or not file.is_file():
                                continue
                            canonical = "/" + str(file.relative_to(HTML)).replace("index.html", "")
                            if canonical not in seen and canonical not in pending:
                                pending.append(canonical)
                        await page.emulate_media(media="print")
                        pdf_file = Path(tmp) / f"{len(seen):04d}.pdf"
                        await page.pdf(path=str(pdf_file), format="A4",
                                       print_background=True,
                                       margin={"top":"15mm","bottom":"15mm",
                                               "left":"17mm","right":"17mm"})
                        writer.append(str(pdf_file))
                    if not seen:
                        raise RuntimeError("No pages found")
                    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
                    with OUTPUT.open("wb") as f:
                        writer.write(f)
                print(f"PDF: {OUTPUT} ({len(seen)} HTML pages)")
            finally:
                await browser.close()
    finally:
        server.shutdown()
        server.server_close()

if __name__ == "__main__":
    asyncio.run(main())
