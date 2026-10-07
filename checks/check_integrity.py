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
             "InDensityClass.orderLaw_isProbabilityMeasure", "InDensityClass.uMarginal_mass",
             "InDensityClass.vMarginal_mass", "InDensityClass.populationCDF_thresholdStability",
             "InDensityClass.populationCDF_u_one", "InDensityClass.populationCDF_one_v",
             "grid_marginal_accuracy_uniform", "boundary_card_le_of_grid_marginals",
             "grid_vertices_empiricalCDF", "finite_realizer_cumulative_error_of_grid_vertices",
             "InDensityClass.sample_ae_mem_diamond", "InDensityClass.sample_ae_no_grid_lines",
             "InDensityClass.gridCell_mass_lower", "InDensityClass.sample_misses_le_exp",
             "InDensityClass.grid_occupancy_failure", "InDensityClass.fst_map_uniform",
             "InDensityClass.snd_map_uniform", "InDensityClass.sample_coordinates_injective",
             "InDensityClass.indicator_concentration", "InDensityClass.empiricalCDF_concentration",
             "InDensityClass.grid_vertices_failure", "InDensityClass.sample_good_probability",
             "InDensityClass.reconstruction_probability_grid", "grid_failure_bound",
             "fourth_root_grid_data", "InDensityClass.reconstruction_probability"):
    if not re.search(rf"'QuantyraNullCone\.{re.escape(name)}' depends on axioms:", result.stdout):
        sys.exit(f"Missing final theorem dependency report: {name}")
print("PASS: proof sources and final Lean dependency reports")
