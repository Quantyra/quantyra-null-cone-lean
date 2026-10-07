"""Reserve, verify and publish manuscript 0.3.0 in the existing Zenodo family.

--reserve creates/reuses the new-version draft and stores only public identifiers.
Without --publish, --commit verifies the frozen payload without network writes.
The publication command resumes the reserved identity, verifies draft bytes before
publishing, and downloads both the new and historical files for verification.
Credentials remain in memory; authenticated response bodies are never logged.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
from urllib.parse import urlparse

import requests

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(Path(__file__).resolve().parent))
PACKAGE = ROOT / "manuscript/deposit/v0.3.0"
PREVIOUS = 23206773
API = "https://zenodo.org/api"
RESERVATION = PACKAGE / "draft-record.json"


def digest(data):
    return hashlib.sha256(data).hexdigest()


def trusted(url):
    p = urlparse(url)
    assert p.scheme == "https" and p.netloc == "zenodo.org"
    assert p.path.startswith("/api/") and not p.query and not p.fragment
    return url


def save(path, data):
    path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8", newline="\n")


def public_record(record_id):
    response = requests.get(f"{API}/records/{record_id}", timeout=60)
    response.raise_for_status()
    return response.json()


def public_files(record):
    result = {}
    for entry in record["files"]:
        response = requests.get(trusted(entry["links"]["self"]), timeout=60)
        response.raise_for_status()
        assert entry["checksum"] == "md5:" + hashlib.md5(response.content).hexdigest()
        result[entry["key"]] = {"sha256": digest(response.content),
                                "zenodo_checksum": entry["checksum"]}
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("--reserve", action="store_true")
    modes.add_argument("--publish", action="store_true")
    parser.add_argument("--commit")
    args = parser.parse_args()
    if args.reserve and args.commit:
        parser.error("--reserve does not accept --commit")
    if not args.reserve and not args.commit:
        parser.error("--commit is required for payload verification/publication")

    if not args.reserve:
        assert len(args.commit) == 40 and all(c in "0123456789abcdef" for c in args.commit)
        def frozen(path):
            name = path.relative_to(ROOT).as_posix()
            return subprocess.check_output(["git", "show", f"{args.commit}:{name}"], cwd=ROOT)
        metadata = json.loads(frozen(PACKAGE / "zenodo-metadata.json"))
        manifest = json.loads(frozen(PACKAGE / "manifest.json"))
        bundle = json.loads(frozen(PACKAGE / "bundle.json"))
        reservation = json.loads(frozen(RESERVATION))
        assert metadata["version"] == manifest["version"] == "0.3.0"
        assert metadata["upload_type"] == "publication" and metadata["publication_type"] == "preprint"
        assert metadata["license"] == "cc-by-4.0" and metadata["access_right"] == "open"
        assert digest(frozen(PACKAGE / "zenodo-metadata.json")) == manifest["metadata_sha256"]
        for name, expected in manifest["files"].items():
            assert digest(frozen(ROOT / name)) == expected["sha256"], name
        pdf = ROOT / "manuscript/finite-causal-order-reconstruction.pdf"
        source_zip = PACKAGE / bundle["file"]
        payload = [pdf, source_zip]
        assert digest(source_zip.read_bytes()) == bundle["sha256"]
        for path in payload:
            assert frozen(path) == path.read_bytes(), "Local upload differs from frozen commit"
        assert json.loads(RESERVATION.read_text()) == reservation
        assert reservation["previous_record"] == PREVIOUS
        print("PASS: frozen commit, metadata, manifest and upload bytes", flush=True)
        if not args.publish:
            print("Dry run: no service calls or writes")
            return

    from zenodo_credentials import aws_token
    token, _ = aws_token()
    session = requests.Session()
    session.headers["Authorization"] = f"Bearer {token}"
    def request(method, url, **kwargs):
        response = session.request(method, trusted(url), timeout=60, allow_redirects=False, **kwargs)
        if not 200 <= response.status_code < 300:
            raise RuntimeError(f"Zenodo {method} HTTP {response.status_code}; response body withheld")
        return response

    previous = public_record(PREVIOUS)
    assert previous["metadata"]["version"] == "0.2.0"
    previous_receipt = json.loads((ROOT / "manuscript/deposit/published-record.json").read_text())
    assert public_files(previous) == previous_receipt["files"]
    if args.reserve:
        if RESERVATION.exists():
            reservation = json.loads(RESERVATION.read_text())
            draft = request("GET", f"{API}/deposit/depositions/{reservation['id']}").json()
        else:
            parent = request("GET", f"{API}/deposit/depositions/{PREVIOUS}").json()
            assert parent["submitted"] and parent["metadata"]["version"] == "0.2.0"
            # The compatibility API's parent latest_draft link may still point
            # to the published record. Locate the existing unpublished family
            # member before any creation request (including after interruption).
            deposits = request("GET", f"{API}/deposit/depositions", params={"size": 100}).json()
            candidates = [d for d in deposits if not d["submitted"] and
                          str(d.get("conceptrecid")) == str(previous["conceptrecid"])]
            assert len(candidates) <= 1, "Multiple family drafts require inspection"
            latest = f"{API}/deposit/depositions/{candidates[0]['id']}" if candidates else None
            if latest is None:
                # Never automatically retry a POST after an unknown outcome.
                parent = request("POST", f"{API}/deposit/depositions/{PREVIOUS}/actions/newversion").json()
                latest = parent["links"]["latest_draft"]
            draft = request("GET", latest).json()
            assert not draft["submitted"] and draft["id"] != PREVIOUS
            assert str(draft["conceptrecid"]) == str(previous["conceptrecid"])
            assert draft["metadata"]["title"] == previous["metadata"]["title"]
            # Zenodo may clear the version field when cloning a record.
            assert draft["metadata"].get("version") in {None, "", "0.2.0", "0.3.0"}
            reservation = {"id": draft["id"], "previous_record": PREVIOUS,
                           "conceptrecid": str(previous["conceptrecid"]),
                           "conceptdoi": previous["conceptdoi"],
                           "doi": draft["metadata"]["prereserve_doi"]["doi"]}
            save(RESERVATION, reservation)
        print(json.dumps(reservation, indent=2))
        return

    record_id = reservation["id"]
    assert record_id != PREVIOUS
    deposition = request("GET", f"{API}/deposit/depositions/{record_id}").json()
    assert str(deposition["conceptrecid"]) == reservation["conceptrecid"]
    if not deposition["submitted"]:
        # Only remove obsolete inherited files in this new draft.
        expected = {p.name for p in payload}
        for entry in deposition["files"]:
            if entry["filename"] not in expected:
                assert entry["filename"] in previous_receipt["files"], "Unrecognized draft file"
                request("DELETE", f"{API}/deposit/depositions/{record_id}/files/{entry['id']}")
        # Multipart upload also works for new-version drafts before a bucket
        # link is exposed by Zenodo's legacy-API compatibility layer.
        for path in payload:
            if path.name in {e["filename"] for e in deposition["files"]}:
                entry = next(e for e in deposition["files"] if e["filename"] == path.name)
                request("DELETE", f"{API}/deposit/depositions/{record_id}/files/{entry['id']}")
            with path.open("rb") as stream:
                request("POST", f"{API}/deposit/depositions/{record_id}/files",
                        data={"name": path.name}, files={"file": (path.name, stream)})
        deposition = request("PUT", f"{API}/deposit/depositions/{record_id}",
                             json={"metadata": metadata}).json()
        draft_files = {e["filename"]: e for e in deposition["files"]}
        assert set(draft_files) == expected
        for path in payload:
            actual_md5 = draft_files[path.name]["checksum"].removeprefix("md5:")
            assert actual_md5 == hashlib.md5(path.read_bytes()).hexdigest()
        for key in ("title", "version", "creators", "publication_date", "description"):
            assert deposition["metadata"][key] == metadata[key], key
        assert deposition["metadata"]["prereserve_doi"]["doi"] == reservation["doi"]
        print(f"PASS: new draft {record_id}, both file checksums and metadata; publishing", flush=True)
        request("POST", deposition["links"]["publish"])

    record = public_record(record_id)
    actual = record["metadata"]
    for key in ("title", "version", "creators", "publication_date", "description", "access_right", "keywords"):
        assert actual[key] == metadata[key], key
    assert actual["resource_type"] == {"title": "Preprint", "type": "publication", "subtype": "preprint"}
    assert actual["license"]["id"].lower() == "cc-by-4.0"
    for relation in metadata["related_identifiers"]:
        assert relation in actual["related_identifiers"]
    assert actual["doi"] == reservation["doi"]
    assert str(record["conceptrecid"]) == reservation["conceptrecid"]
    verified = public_files(record)
    assert set(verified) == {p.name for p in payload}
    for path in payload:
        assert verified[path.name]["sha256"] == digest(path.read_bytes())
    assert public_files(public_record(PREVIOUS)) == previous_receipt["files"]
    software = public_record(23202763)
    assert software["metadata"]["version"] == "0.1.0"
    assert software["metadata"]["doi"] == "10.5281/zenodo.23202763"
    historical_software = json.loads((ROOT / "evidence/completion-2026-10-07/public-software-record.json").read_text())
    assert {(e["key"], e["checksum"]) for e in software["files"]} == {
        (e["key"], e["checksum"]) for e in historical_software["files"]}
    software_files = public_files(software)
    receipt = {"id": record_id, "doi": actual["doi"], "conceptdoi": record["conceptdoi"],
               "url": f"https://zenodo.org/records/{record_id}", "version": "0.3.0",
               "source_commit": args.commit, "proof_commit": "b7d762acc9c10ca881f8366f545f3998b0528448",
               "previous_record": PREVIOUS, "same_version_family_verified": True,
               "previous_manuscript_downloads_unchanged": True, "software_doi_version_preserved": True,
               "software_files": software_files,
               "verified_metadata": ["title", "version", "creators", "publication_date", "description",
                                     "access_right", "keywords", "resource_type", "license", "related_identifiers", "doi"],
               "files": verified}
    save(PACKAGE / "published-record.json", receipt)
    save(PACKAGE / "public-record.json", record)
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
