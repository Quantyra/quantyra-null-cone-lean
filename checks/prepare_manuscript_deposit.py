"""Freeze a separately citable manuscript bundle without publishing anything."""

import hashlib
import json
from pathlib import Path
import re
import zipfile

ROOT = Path(__file__).resolve().parents[1]
DESTINATION = ROOT / "manuscript/deposit"
METADATA = DESTINATION / "zenodo-metadata.json"


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


metadata = json.loads(METADATA.read_text(encoding="utf-8"))
assert metadata["upload_type"] == "publication"
assert metadata["publication_type"] == "preprint"
assert metadata["license"] == "cc-by-4.0"
assert metadata["creators"] == [
    {"name": "Fredriksen, Daniel Eric", "affiliation": "Quantyra Inc"}
]
version = metadata["version"]
assert re.fullmatch(r"\d+\.\d+\.\d+", version)
source = ROOT / "manuscript/finite-causal-order-reconstruction.tex"
pdf = source.with_suffix(".pdf")
assert f"version {version}" in source.read_text(encoding="utf-8")
assert pdf.read_bytes().startswith(b"%PDF-")
assert "doi" not in metadata, "A manuscript DOI must come from a real record"

payload = [source, pdf, ROOT / "manuscript/README.md", ROOT / "LICENSES/CC-BY-4.0.txt"]
manifest = {
    "title": metadata["title"],
    "version": version,
    "license": "CC-BY-4.0",
    "software_version_doi": "10.5281/zenodo.23202763",
    "metadata_sha256": sha256(METADATA),
    "files": {
        str(path.relative_to(ROOT)).replace("\\", "/"): {
            "sha256": sha256(path), "bytes": path.stat().st_size
        }
        for path in payload
    },
}
manifest_path = DESTINATION / "manifest.json"
manifest_path.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
bundle_path = DESTINATION / f"finite-causal-order-reconstruction-v{version}-source.zip"
with zipfile.ZipFile(bundle_path, "w", compression=zipfile.ZIP_DEFLATED) as archive:
    for path in [*payload, manifest_path, METADATA]:
        name = str(path.relative_to(ROOT)).replace("\\", "/")
        info = zipfile.ZipInfo(name, date_time=(2026, 10, 6, 0, 0, 0))
        info.compress_type = zipfile.ZIP_DEFLATED
        info.external_attr = 0o100644 << 16
        archive.writestr(info, path.read_bytes())

with zipfile.ZipFile(bundle_path) as archive:
    assert archive.testzip() is None
    for path in payload:
        name = str(path.relative_to(ROOT)).replace("\\", "/")
        assert hashlib.sha256(archive.read(name)).hexdigest() == sha256(path)

bundle_receipt = {
    "file": bundle_path.name, "sha256": sha256(bundle_path),
    "bytes": bundle_path.stat().st_size, "members": len(payload) + 2
}
(DESTINATION / "bundle.json").write_text(
    json.dumps(bundle_receipt, indent=2) + "\n", encoding="utf-8"
)
print("PASS: manuscript/source/license hashes and deterministic source ZIP")
print(json.dumps(bundle_receipt))
