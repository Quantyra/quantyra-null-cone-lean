"""Verify retained accepted identities, theorem reports and preservation.

This reads Lean sources and GCP evidence; it never invokes Lean or Lake.
Semantic correspondence is separately reviewed in review.json.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess

folder = Path(__file__).resolve().parent
root = folder.parents[1]
mapping = json.loads((folder / "formal-map.json").read_text(encoding="utf-8"))
evidence = root / "evidence/gcp" / mapping["gcp_run"]
capture = json.loads((evidence / "capture-manifest.json").read_text(encoding="utf-8"))
receipt = json.loads((evidence / "receipt.json").read_text(encoding="utf-8"))
sha = lambda b: hashlib.sha256(b).hexdigest()
assert receipt["acceptance"] and receipt["exit"] == 0
assert receipt["compile_host"] == "GCP" and receipt["audited_exports"] == 446
assert receipt["owned_warnings"] == 0
assert receipt["source_verified_before_and_after"]
assert receipt["dependency_identities_before_and_after"]
assert len(capture["source"]) == 135
checkout_eol = {}
for name, expected in capture["source"].items():
    data = (root / name).read_bytes()
    if sha(data) != expected:
        # Windows may check out LF Git text as CRLF. Preserve it and explicitly
        # record this representation difference; never normalize raw evidence.
        assert b"\r\n" in data and sha(data.replace(b"\r\n", b"\n")) == expected, (
            "Current capture mismatch beyond checkout EOL", name
        )
        checkout_eol[name] = {"checkout_sha256": sha(data), "accepted_lf_sha256": expected}
    committed = subprocess.check_output(
        ["git", "show", f"{mapping['proof_commit']}:{name}"], cwd=root
    )
    assert sha(committed) == expected, ("Proof revision mismatch", name)

audit = (evidence / "logs/audit.stdout.txt").read_text(encoding="utf-8")
build = (evidence / "logs/build.stdout.txt").read_text(encoding="utf-8")
assert "Build completed successfully (3027 jobs)." in build
assert "PASS: proof sources and final Lean dependency reports" in audit
axioms = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", audit)
axioms += [(name, "") for name in re.findall(r"'([^']+)' does not depend on any axioms", audit)]
assert len(axioms) == 446
accepted = {name for name, _ in axioms}
assert len(accepted) == 446
for name, values in axioms:
    assert set(v.strip() for v in values.split(",") if v.strip()) <= {
        "propext", "Classical.choice", "Quot.sound"
    }, name
tex = (folder / mapping["manuscript"]).read_text(encoding="utf-8")
names = set()
for claim in mapping["claims"]:
    assert r"\label{" + claim["tex_label"] + "}" in tex
    for export in claim["exports"]:
        assert export["file"] in capture["source"]
        name = export["name"]
        assert name in accepted, ("Missing accepted report", name)
        source = (root / export["file"]).read_text(encoding="utf-8")
        short = name.removeprefix("QuantyraNullCone.")
        assert re.search(r"\btheorem\s+" + re.escape(short) + r"\b", source), name
        names.add(name)

# Any earlier tracked file except these navigation/EOL files must be unchanged.
# This protects both published manuscript families, all raw evidence and the study.
allowed = {".gitattributes", "README.md", "notes/manuscript-portfolio.md"}
changed = subprocess.check_output(
    ["git", "diff", "--name-only", mapping["preservation_baseline"]], cwd=root
).decode().splitlines()
unexpected = [p for p in changed if p not in allowed and not p.startswith("manuscript/finite-data/")]
assert not unexpected, ("Changed protected files", unexpected)
tracked = subprocess.check_output(
    ["git", "ls-tree", "-r", "--name-only", mapping["preservation_baseline"]], cwd=root
).decode().splitlines()
protected = [p for p in tracked if p not in allowed]
result = {
    "status": "PASS",
    "proof_commit": mapping["proof_commit"],
    "gcp_run": mapping["gcp_run"],
    "current_and_cited_commit_match_accepted_capture": capture["source"],
    "accepted_source_count": len(capture["source"]),
    "checkout_crlf_to_lf_comparisons": checkout_eol,
    "mapped_audited_exports": len(names),
    "total_accepted_export_reports": len(axioms),
    "root_build_jobs": 3027,
    "allowed_axioms": ["propext", "Classical.choice", "Quot.sound"],
    "preservation_baseline": mapping["preservation_baseline"],
    "protected_baseline_file_count": len(protected),
    "protected_baseline_files_unchanged": True,
    "raw_evidence_sha256": {
        p.relative_to(root).as_posix(): sha(p.read_bytes())
        for p in [evidence / "capture-manifest.json", evidence / "receipt.json",
                  evidence / "logs/audit.stdout.txt", evidence / "logs/build.stdout.txt"]
    },
    "new_lean_invocations": 0,
    "semantic_map_review": "Manual source/type/prose inspection recorded separately; not inferred from names alone",
}
(folder / "source-verification.json").write_text(
    json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n"
)
print(f"PASS: 135 accepted identities, {len(names)} mapped exports, 446 audit reports; "
      f"{len(protected)} baseline files protected; no Lean invoked")
