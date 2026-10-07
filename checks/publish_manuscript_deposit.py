"""Publish the frozen S012 manuscript as its own Zenodo preprint record.

Requires an authorized --publish invocation; defaults to the migrated Quantyra
AWS secret, with explicit external token routes also supported. The separate
--check-credentials mode performs read-only GET checks. Persistent draft identity
prevents duplicate records on resumption. Never prints the credential or raw
authenticated responses.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
from urllib.parse import urlparse

import requests

ROOT = Path(__file__).resolve().parents[1]
# The supported embedded Windows Python omits the script directory from sys.path.
sys.path.insert(0, str(Path(__file__).resolve().parent))
PACKAGE = ROOT / "manuscript/deposit"
STATE = ROOT / "tmp/manuscript-deposit-state.json"
API = "https://zenodo.org/api"


def digest(data):
    return hashlib.sha256(data).hexdigest()


def trusted_api(url):
    parsed = urlparse(url)
    assert parsed.scheme == "https" and parsed.hostname == "zenodo.org"
    return url


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--commit", help="Commit containing the exact frozen payload")
mode = parser.add_mutually_exclusive_group()
mode.add_argument("--publish", action="store_true", help="Execute the authorized manuscript deposit")
mode.add_argument("--check-credentials", action="store_true", help="Read-only AWS/Zenodo GET checks; no deposit or local state writes")
parser.add_argument("--env-file", type=Path, help="Read ZENODO_ACCESS_TOKEN from a local file outside Git")
parser.add_argument("--aws-secret", default="quantyra/zenodo/access-token", help="AWS JSON secret (default: migrated Quantyra secret)")
parser.add_argument("--aws-profile", default="quantyra", help="AWS profile (default: quantyra; destination account enforced)")
parser.add_argument("--aws-region", default="us-east-1", help="AWS region (default: us-east-1)")
args = parser.parse_args()
if args.check_credentials:
    if args.env_file:
        parser.error("--check-credentials uses AWS only; --env-file is not allowed")
    from zenodo_credentials import aws_token, read_only_check
    token, credential_metadata = aws_token(args.aws_secret, args.aws_profile, args.aws_region)
    raise SystemExit(0 if read_only_check(token, credential_metadata) else 1)
if not args.commit:
    parser.error("--commit is required for payload verification or publication")
assert len(args.commit) == 40 and all(c in "0123456789abcdef" for c in args.commit)
def frozen_bytes(name):
    return subprocess.check_output(["git", "show", f"{args.commit}:{name}"], cwd=ROOT)


metadata_bytes = frozen_bytes("manuscript/deposit/zenodo-metadata.json")
metadata = json.loads(metadata_bytes)
manifest = json.loads(frozen_bytes("manuscript/deposit/manifest.json"))
bundle = json.loads(frozen_bytes("manuscript/deposit/bundle.json"))
pdf = ROOT / "manuscript/finite-causal-order-reconstruction.pdf"
source_zip = PACKAGE / bundle["file"]

for name, expected in manifest["files"].items():
    committed = frozen_bytes(name)
    assert digest(committed) == expected["sha256"], f"Commit does not freeze payload: {name}"
assert digest(source_zip.read_bytes()) == bundle["sha256"]
assert digest(metadata_bytes) == manifest["metadata_sha256"]
for path in (pdf, source_zip):
    committed = frozen_bytes(path.relative_to(ROOT).as_posix())
    assert digest(committed) == digest(path.read_bytes()), "Deposit package differs from frozen commit"
assert metadata["upload_type"] == "publication" and metadata["publication_type"] == "preprint"
assert metadata["version"] == manifest["version"]
print("PASS: selected commit freezes the manuscript payload")
if not args.publish:
    print("No upload performed. Destination: separate Zenodo publication/preprint, CC-BY-4.0.")
    raise SystemExit(0)

token = os.environ.get("ZENODO_ACCESS_TOKEN")
if not token and args.env_file:
    for line in args.env_file.read_text(encoding="utf-8-sig").splitlines():
        if line.strip().startswith("ZENODO_ACCESS_TOKEN="):
            token = line.strip().split("=", 1)[1].strip().strip("\"'")
            break
if not token and args.aws_secret:
    from zenodo_credentials import aws_token
    token, _ = aws_token(args.aws_secret, args.aws_profile, args.aws_region)
if not token:
    raise SystemExit("ZENODO_ACCESS_TOKEN is unavailable; no deposit created")
session = requests.Session()
session.headers["Authorization"] = f"Bearer {token}"


def request(method, url, **kwargs):
    response = session.request(method, trusted_api(url), timeout=60, **kwargs)
    if response.status_code >= 400:
        raise RuntimeError(f"Zenodo {method} failed with HTTP {response.status_code}; "
                           "no credential or raw account response is logged")
    return response


STATE.parent.mkdir(parents=True, exist_ok=True)
if STATE.exists():
    state = json.loads(STATE.read_text(encoding="utf-8"))
    assert state["source_commit"] == args.commit, "Resume with the original frozen commit"
    assert state["pdf_sha256"] == digest(pdf.read_bytes())
    assert state["metadata_sha256"] == manifest["metadata_sha256"]
    deposition = request("GET", f"{API}/deposit/depositions/{state['id']}").json()
else:
    # POST is deliberately not automatically retried. After an unknown outcome,
    # inspect authenticated deposits before attempting another creation.
    deposition = request("POST", f"{API}/deposit/depositions", json={}).json()
    state = {
        "id": deposition["id"], "source_commit": args.commit,
        "pdf_sha256": digest(pdf.read_bytes()),
        "metadata_sha256": manifest["metadata_sha256"]
    }
    STATE.write_text(json.dumps(state, indent=2) + "\n", encoding="utf-8")
    print(f"Created separate manuscript draft {state['id']}")

if not deposition.get("submitted", False):
    bucket = trusted_api(deposition["links"]["bucket"])
    for path in (pdf, source_zip):
        with path.open("rb") as stream:
            request("PUT", f"{bucket}/{path.name}", data=stream)
    deposition = request("PUT", f"{API}/deposit/depositions/{state['id']}",
                         json={"metadata": metadata}).json()
    deposition = request("POST", deposition["links"]["publish"]).json()

record = requests.get(f"{API}/records/{state['id']}", timeout=60)
record.raise_for_status()
record = record.json()
actual = record["metadata"]
assert actual["title"] == metadata["title"]
assert actual["version"] == metadata["version"]
assert actual["creators"] == metadata["creators"]
assert actual["resource_type"]["type"] == "publication"
assert actual["resource_type"].get("subtype") == "preprint"
assert actual["license"]["id"].lower() == "cc-by-4.0"
assert actual["access_right"] == "open"
assert actual["doi"] != "10.5281/zenodo.23202763"
assert any(item["identifier"] == "10.5281/zenodo.23202763" and
           item["relation"] == "references" for item in actual["related_identifiers"])
files = {entry["key"]: entry for entry in record["files"]}
verified_files = {}
for path in (pdf, source_zip):
    entry = files[path.name]
    url = entry["links"].get("self") or entry["links"].get("download")
    data = requests.get(trusted_api(url), timeout=60)
    data.raise_for_status()
    assert digest(data.content) == digest(path.read_bytes())
    checksum = entry["checksum"]
    assert checksum.startswith("md5:")
    assert hashlib.md5(data.content).hexdigest() == checksum[4:]
    verified_files[path.name] = {"sha256": digest(data.content), "zenodo_checksum": checksum}

receipt = {
    "id": record["id"], "doi": actual["doi"],
    "url": f"https://zenodo.org/records/{record['id']}",
    "source_commit": args.commit, "version": actual["version"],
    "resource_type": "publication/preprint", "license": "CC-BY-4.0",
    "software_version_doi": "10.5281/zenodo.23202763", "files": verified_files,
    "verified_metadata": ["title", "version", "creators", "type", "license", "open access",
                          "separate manuscript DOI", "software DOI relation"],
}
(PACKAGE / "published-record.json").write_text(
    json.dumps(receipt, indent=2) + "\n", encoding="utf-8"
)
print(json.dumps(receipt, indent=2))
