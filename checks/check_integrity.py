"""Audit proof source and actual Lean dependency reports; exit nonzero on failure."""
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
sources = [ROOT / "QuantyraNullCone.lean", *sorted((ROOT / "QuantyraNullCone").glob("*.lean")), ROOT / "checks/Audit.lean"]
for path in sources:
    source = path.read_text(encoding="utf-8")
    if re.search(r"\b(?:sorry|admit)\b|^\s*axiom\s", source, re.MULTILINE):
        sys.exit(f"Forbidden proof token or axiom declaration: {path.relative_to(ROOT)}")

result = subprocess.run(["lake", "env", "lean", "checks/Audit.lean"], cwd=ROOT,
                        text=True, encoding="utf-8", capture_output=True)
print(result.stdout, end="")
if result.stderr:
    print(result.stderr, file=sys.stderr, end="")
if result.returncode:
    sys.exit(result.returncode)
reports = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", result.stdout)
if not reports:
    sys.exit("No Lean dependency reports found")
for report in reports:
    names = {name.strip() for name in report.split(",") if name.strip()}
    if not names <= ALLOWED:
        sys.exit(f"Unexpected theorem dependencies: {sorted(names - ALLOWED)}")
for name in ("finite_realizer_rank_rigidity", "finite_realizer_rank_rigidity_specified",
             "finite_realizer_coordinate_rigidity", "finite_realizer_cumulative_error",
             "sampledOrder_measurable", "InDensityClass.densityMeasure_univ",
             "InDensityClass.orderLaw_isProbabilityMeasure"):
    if not re.search(rf"'QuantyraNullCone\.{re.escape(name)}' depends on axioms:", result.stdout):
        sys.exit(f"Missing final theorem dependency report: {name}")
print("PASS: proof sources and final Lean dependency reports")
