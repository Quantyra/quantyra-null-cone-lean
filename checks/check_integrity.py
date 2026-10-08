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
             "fourth_root_grid_data", "InDensityClass.reconstruction_probability",
             "InDensityClass.rectangle_mass_cdf", "InDensityClass.coefficientDeviation_attained",
             "InDensityClass.coefficient_interpolation", "chronological_realizer_exists",
             "selectedCDF_measurable", "InDensityClass.orderCDFGood_probability",
             "finite_probability_event_bound", "InDensityClass.orderLawTV_event_bound",
             "InDensityClass.orderCDFGood_intersects",
             "InDensityClass.populationCDF_orbit_of_orderLawTV", "InDensityClass.transpose",
             "diamondVolume_transpose_preserving", "densityMeasure_transpose_apply",
             "populationCDF_transpose", "coefficientDeviation_transpose_both",
             "InDensityClass.coefficientDeviation_bounds", "InDensityClass.conformalDistance_bounds",
             "orderLawTV_le_finiteLawDiscrepancy", "InDensityClass.conformalDistance_of_small_TV",
             "InDensityClass.full_inverse", "InDensityClass.coefficientDeviation_zero_iff",
             "InDensityClass.conformalDistance_zero_iff", "InDensityClass.all_law_identifiability",
             "sampledOrder_strict_partial_order",
             "InDensityClass.sample_relabel_preserving",
             "InDensityClass.orderLaw_exchangeable",
             "InDensityClass.orderLaw_singleton_relabel",
             "abs_sum_of_constant",
             "finite_map_L1_of_fiber_constant",
             "forgetOrderLabels_eq_iff",
             "InDensityClass.unlabeledOrderLaw_isProbabilityMeasure",
             "InDensityClass.orderLaw_fiber_constant",
             "InDensityClass.unlabeledOrderLawTV_eq",
             "InDensityClass.unlabeledFiniteLawDiscrepancy_eq",
             "InDensityClass.full_inverse_unlabeled",
             "InDensityClass.all_unlabeled_law_identifiability",
             "log_large_bounds", "logarithmic_grid_data", "logarithmic_grid_failure",
             "logarithmic_grid_reciprocal", "InDensityClass.logarithmic_reconstruction_probability",
             "InDensityClass.logarithmic_orderCDFGood_probability",
             "InDensityClass.logarithmic_populationCDF_orbit_of_orderLawTV",
             "logarithmic_small_sample_lower", "InDensityClass.full_inverse_logarithmic",
             "InDensityClass.full_inverse_logarithmic_unlabeled",
             "sqrt_coefficient_lipschitz",
             "FutureCurve.integral_derivU",
             "FutureCurve.integral_derivV",
             "FutureCurve.integral_weight_cauchy_schwarz",
             "FutureCurve.integrable_length",
             "FutureCurve.length_difference",
             "timeSeparation_empty",
             "InDensityClass.timeSeparation_difference",
             "InDensityClass.timeSeparation_transpose",
             "InDensityClass.proper_time_conformalDistance",
             "InDensityClass.proper_time_inverse_unlabeled",
             "InDensityClass.proper_time_logarithmic_unlabeled",
             "residual_box_bound",
             "finite_lp_weak_duality",
             "rationalDual_checker_sound",
             "Realizer.originalForceStep_sound",
             "Realizer.checkForcingTrace_sound",
             "Realizer.forcing_trace_global_alignment",
             "Realizer.checked_forcing_rank_bounds",
             "negative_exp_upper_512",
             "negative_exp_upper_rational",
             "roundFailureQ_upper",
             "roundFailureQ_le_budget",
             "rounded_split_failure_budget",
             "finite_grid_CDF",
             "normalized_rank_coordinate_error_general",
             "checked_trimmed_CDF",
             "rank_position_eq",
             "checkedPositionRealizer_ranks",
             "dkw_log_ratio_lower",
             "dkw_log_ratio_upper",
             "dkw_stationarity_root",
             "dkw_bernoulli_pinsker",
             "dkw_likelihood_hasDerivAt",
             "dkw_likelihood_derivative_hasDerivAt",
             "dkw_likelihood_stationary_value_lower",
             "dkw_sharp_likelihood_barrier",
             "finite_bin_atom_card",
             "finite_bin_atom_likelihood_identity",
             "finite_bin_terminal_sum",
             "finite_bin_reveal_count",
             "finite_bin_invariant_terminal_sum",
             "finite_bin_likelihood_maximal",
             "finite_bin_deviation_likelihood",
             "finite_bin_upper_DKW",
             "finite_bin_reflect_CDF",
             "finite_bin_two_sided_DKW"):
    if not re.search(rf"'QuantyraNullCone\.{re.escape(name)}' "
                     rf"(?:depends on axioms:|does not depend on any axioms)", result.stdout):
        sys.exit(f"Missing final theorem dependency report: {name}")
print("PASS: proof sources and final Lean dependency reports")
