"""S035: publish the reviewed finite-data paper in its own Zenodo family.

Reuses the tested independent-record transport; no change to older publishers.
Reserve once, prepare locally, commit/push the frozen package, then publish.
AWS credentials remain in memory. No Lean/Lake command is invoked.
"""
from pathlib import Path
import hashlib
import json
import subprocess
import sys
import zipfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "checks"))
import publish_conformal_gauge as publication

publication.PAPER = ROOT / "manuscript/finite-data"
publication.PACKAGE = publication.PAPER / "deposit/v0.1.0"
publication.RESERVATION = publication.PACKAGE / "draft-record.json"
publication.INTENT = ROOT / "tmp/finite-data-create-intent.json"
publication.TITLE = "Finite-sample density reconstruction from a single causal order"
publication.PROOF = "6752732882862bc848c7a96722a7660456d6da38"
publication.BASELINE = "b2678573f937f4fb3322a80006e211d11221535d"
publication.OLD_FAMILIES = {"23206772", "23202762", "23249815"}
publication.OLD_RECORDS = {23206773, 23214579, 23225029, 23247720, 23202763, 23249816}
publication.STEM = "finite-sample-order-density"
PAPER, PACKAGE = publication.PAPER, publication.PACKAGE
sha, read, save = publication.sha, publication.read, publication.save
base_authenticated_request = publication.authenticated_request


def put_pdf_first(request, record_url, reservation):
    """Use Zenodo's documented file-order API before irreversible publication."""
    draft = request("GET", record_url).json()
    publication.validate_identity(draft, reservation)
    by_name = {entry["filename"]: entry for entry in draft["files"]}
    names = [publication.STEM + ".pdf", publication.STEM + "-v0.1.0-source.zip"]
    assert set(by_name) == set(names), "Unexpected publication files"
    ordered = request("PUT", record_url + "/files",
                      json=[{"id": by_name[name]["id"]} for name in names]).json()
    assert [entry["filename"] for entry in ordered] == names


def authenticated_request():
    request = base_authenticated_request()

    def wrapped(method, url, **kwargs):
        if method == "POST" and url.endswith("/actions/publish"):
            reservation = read(publication.RESERVATION)
            record_url = publication.API + "/deposit/depositions/" + str(reservation["id"])
            assert url == record_url + "/actions/publish"
            put_pdf_first(request, record_url, reservation)
        return request(method, url, **kwargs)
    return wrapped


def publication_source(original, doi):
    """Only publication-label changes; all mathematical text retained."""
    replacements = [
        (r"\date{8 October 2026\\Version 0.1.0 --- unpublished manuscript}",
         r"\date{9 October 2026\\Version 0.1.0\\"
         + r"\href{https://doi.org/" + doi + "}{" + doi + "}}"),
        ("This version is an\nunpublished manuscript with no assigned manuscript DOI.",
         "This version is published as a separate Zenodo preprint\nwith the DOI given on the title page."),
    ]
    for old, new in replacements:
        assert original.count(old) == 1, "Publication-label source mismatch"
        original = original.replace(old, new)
    return original


def prepare(metadata):
    assert not (PACKAGE / "published-record.json").exists(), "Published payload is immutable"
    reservation = read(publication.RESERVATION)
    source = (PACKAGE / (publication.STEM + ".tex")).read_text(encoding="utf-8")
    original = subprocess.check_output([
        "git", "show", f"{publication.BASELINE}:manuscript/finite-data/{publication.STEM}.tex"
    ], cwd=ROOT).decode("utf-8")
    assert source == publication_source(original, reservation["doi"])
    review = read(PACKAGE / "review.json")
    assert review["all_pages_visually_inspected"] == list(range(1, review["pages"] + 1))
    for suffix in (".pdf", ".tex"):
        name = publication.STEM + suffix
        assert review["files"][name] == sha((PACKAGE / name).read_bytes())
    excluded = {"manifest.json", "bundle.json", "published-record.json",
                "public-record.json", "resolution-check.json"}
    payload = [p for p in sorted(PACKAGE.iterdir())
               if p.is_file() and p.suffix != ".zip" and p.name not in excluded]
    # Archive retains the reviewed S034 package at its original paths as well.
    for name in ("finite-sample-order-density.tex", "finite-sample-order-density.pdf",
                 "finite-sample-order-density.log", "tex-build.log", "README.md",
                 "formal-map.json", "source-verification.json", "verification.md",
                 "review.json", "verify_sources.py", "build.py"):
        p = PAPER / name
        accepted = subprocess.check_output(
            ["git", "show", f"{publication.BASELINE}:{p.relative_to(ROOT).as_posix()}"], cwd=ROOT
        )
        assert accepted == p.read_bytes(), ("S034 artifact changed", name)
        payload.append(p)
    payload += [PAPER / "publish.py", PAPER / "test_publication.py"]
    payload += [ROOT / "checks" / name for name in
                ("publish_conformal_gauge.py", "publish_manuscript_version.py", "zenodo_credentials.py")]
    payload += [ROOT / "LICENSES/CC-BY-4.0.txt", ROOT / "LICENSE"]
    manifest = {
        "title": publication.TITLE, "version": "0.1.0", "doi": reservation["doi"],
        "proof_commit": publication.PROOF, "reviewed_draft_commit": publication.BASELINE,
        "mathematical_body_unchanged": True,
        "source_change_scope": "Title date/status/DOI and one publication-status sentence only",
        "metadata_sha256": sha((PACKAGE / "zenodo-metadata.json").read_bytes()),
        "files": {p.relative_to(ROOT).as_posix():
                  {"sha256": sha(p.read_bytes()), "bytes": p.stat().st_size} for p in payload},
    }
    save(PACKAGE / "manifest.json", manifest)
    archive_path = PACKAGE / (publication.STEM + "-v0.1.0-source.zip")
    with zipfile.ZipFile(archive_path, "w") as archive:
        for path in payload + [PACKAGE / "manifest.json"]:
            entry = zipfile.ZipInfo(path.relative_to(ROOT).as_posix(), (2026, 10, 9, 0, 0, 0))
            entry.compress_type = zipfile.ZIP_DEFLATED
            entry.external_attr = 0o100644 << 16
            archive.writestr(entry, path.read_bytes())
    with zipfile.ZipFile(archive_path) as archive:
        assert archive.testzip() is None
        for name, info in manifest["files"].items():
            assert sha(archive.read(name)) == info["sha256"]
    save(PACKAGE / "bundle.json", {
        "file": archive_path.name, "sha256": sha(archive_path.read_bytes()),
        "bytes": archive_path.stat().st_size, "members": len(payload) + 1,
    })
    print("PASS: publication-label-only changes, S034 preservation, reviewed PDF and deterministic archive")


previous_verify_public = publication.verify_public


def verify_public(commit, metadata, reservation, payload):
    # Check the second published family as well as the earlier reconstruction
    # and software records checked by the shared verifier.
    old = read(ROOT / "manuscript/conformal-gauge/deposit/v0.1.0/published-record.json")
    downloads = publication.public_files(publication.public_record(old["id"]))
    assert downloads == old["files"], "Earlier gauge manuscript downloads changed"
    previous_verify_public(commit, metadata, reservation, payload)
    receipt = read(PACKAGE / "published-record.json")
    receipt["prior_manuscript_and_software_downloads_unchanged"][str(old["id"])] = downloads
    save(PACKAGE / "published-record.json", receipt)
    print("PASS: both earlier published manuscript families and software preserved")


publication.prepare = prepare
publication.verify_public = verify_public
publication.authenticated_request = authenticated_request

if __name__ == "__main__":
    publication.main()
