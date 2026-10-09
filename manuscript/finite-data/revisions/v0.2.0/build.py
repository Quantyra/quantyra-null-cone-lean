"""Build and render this manuscript without invoking Lean/Lake.

Usage: python manuscript/finite-data/revisions/v0.2.0/build.py --tectonic /path/to/tectonic
Requires PyMuPDF. Rendering does not declare visual review complete.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

import pymupdf as fitz

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--tectonic", default="tectonic")
args = parser.parse_args()
folder = Path(__file__).resolve().parent
root = folder.parents[3]
source = folder / "finite-sample-order-density.tex"
result = subprocess.run(
    [args.tectonic, "--keep-logs", "-o", str(folder), str(source)],
    cwd=root, capture_output=True,
)
(folder / "tex-build.log").write_bytes(result.stdout + result.stderr)
print((result.stdout + result.stderr).decode("utf-8", errors="replace"))
assert result.returncode == 0, "Tectonic compilation failed"
log = source.with_suffix(".log").read_text(encoding="utf-8")
problems = re.findall(
    r"^.*(?:Overfull|Underfull|undefined|Missing character|LaTeX Warning).*$",
    log, re.MULTILINE,
)
assert not problems, "\n".join(problems)
doc = fitz.open(source.with_suffix(".pdf"))
out = root / "tmp/s036-manuscript-review"
out.mkdir(parents=True, exist_ok=True)
sha = lambda b: hashlib.sha256(b).hexdigest()
page_hashes = {}
texts = []
for i, page in enumerate(doc):
    path = out / f"page-{i+1:02}.png"
    page.get_pixmap(matrix=fitz.Matrix(1.5, 1.5)).save(path)
    page_hashes[path.name] = sha(path.read_bytes())
    texts.append(f"\nPAGE {i+1}\n" + page.get_text())
    for block in page.get_text("blocks"):
        assert block[0] >= 30 and block[2] <= page.rect.width - 30, (
            "Text outside side margins", i+1, block[:4]
        )
for group in range((len(doc) + 1) // 2):
    sheet = fitz.open()
    page = sheet.new_page(width=1300, height=900)
    for j in range(2):
        n = 2 * group + j
        if n >= len(doc):
            break
        x = j * 650
        page.insert_text((x + 12, 17), f"Page {n+1}", fontsize=12)
        page.show_pdf_page(fitz.Rect(x+5, 25, x+645, 895), doc, n)
    page.get_pixmap().save(out / f"contact-{group+1:02}.png")
(out / "text.txt").write_text("".join(texts), encoding="utf-8", newline="\n")
assert "??" not in "".join(texts), "Unresolved PDF reference"
render = {
    "pages": len(doc),
    "tex_sha256": sha(source.read_bytes()),
    "pdf_sha256": sha(source.with_suffix(".pdf").read_bytes()),
    "page_render_sha256": page_hashes,
    "pymupdf_version": fitz.VersionBind,
    "layout_and_reference_diagnostics": problems,
    "visual_review_complete": False,
}
(out / "renders.json").write_text(
    json.dumps(render, indent=2) + "\n", encoding="utf-8", newline="\n"
)
print("Compiled", len(doc), "pages; inspect every page at", out)
