import QuantyraNullCone.DensityReportCoverage
import QuantyraNullCone.CDFReportFixtures

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace QuantyraNullCone

def densityFixtureCDF : CDFReport 3 := {cdfFixtureReport with radius := 1 / 10}

def densityFixtureA : List (List ℚ) :=
  [[0,0,0,0], [0,0,0,0], [0,0,0,0], [0,0,0,0], [0,0,0,0], [0,0,0,0],
   [0,0,0,0], [0,0,0,0], [1,0,0,0], [-1,0,0,0], [1,1,0,0], [-1,-1,0,0],
   [0,0,0,0], [0,0,0,0], [1,0,1,0], [-1,0,-1,0], [1,1,1,1], [-1,-1,-1,-1],
   [1,0,-1,0], [-1,0,1,0], [1,-1,0,0], [-1,1,0,0],
   [0,1,0,-1], [0,-1,0,1], [0,0,1,-1], [0,0,-1,1]]

def densityFixtureE : List (List ℚ) := [[1,1,0,0], [0,0,1,1], [1,0,1,0], [0,1,0,1]]

def densityFixtureB : List ℚ :=
  [2/5,2/5,2/5,2/5,2/5,2/5,2/5,2/5,26/15,-14/15,26/15,-14/15,
   2/5,2/5,26/15,-14/15,22/5,-18/5,1,1,1,1,1,1,1,1]

theorem density_fixture_matrix :
    List.ofFn (fun i => List.ofFn (densityLP_A 2 i)) = densityFixtureA := by
  norm_num [densityFixtureA, densityLP_A, densityLP_E, densityLP_b, densityLP_d, densityEqualityRows,
    densityInequalityRows, densityEqualityCoefficient, densityInequalityCoefficient,
    densityInequalityRight, densityPrefixCoefficient, densityRowCoefficient, densityColumnCoefficient,
    densityDifferenceCoefficient, densityCellObjective, densityCellPair, densityNeighborStart,
    densityNeighborEnd, List.finRange, List.ofFn_succ, Fin.sum_univ_succ, Finset.filter_insert,
    Finset.range_add_one, Finset.filter_singleton]
  all_goals norm_num [Fin.ext_iff, density_cell_flat_value]

theorem density_fixture_equalities :
    List.ofFn (fun i => List.ofFn (densityLP_E 2 i)) = densityFixtureE := by decide

theorem density_fixture_right : List.ofFn (densityLP_b densityFixtureCDF 2) = densityFixtureB := by
  norm_num [densityFixtureB, densityLP_A, densityLP_E, densityLP_b, densityLP_d, densityEqualityRows,
    densityInequalityRows, densityEqualityCoefficient, densityInequalityCoefficient,
    densityInequalityRight, densityPrefixCoefficient, densityRowCoefficient, densityColumnCoefficient,
    densityDifferenceCoefficient, densityCellObjective, densityCellPair, densityNeighborStart,
    densityNeighborEnd, List.finRange, List.ofFn_succ, Fin.sum_univ_succ, Finset.filter_insert,
    Finset.range_add_one, Finset.filter_singleton, reportLPCounts, reportCornerCount, reportCornerIndices,
    densityFixtureCDF, cdfFixtureReport, Fin.univ_succ, Finset.filter_insert]
  all_goals norm_num [Fin.ext_iff, density_cell_flat_value]

theorem density_fixture_dimensions :
    (densityInequalityRows 2).length = 26 ∧ (densityEqualityRows 2).length = 4 := by decide

def densityFixtureY : Fin (densityInequalityRows 2).length → ℚ := fun i => if i.val = 8 then -1 else 0
def densityFixtureZ : Fin (densityEqualityRows 2).length → ℚ :=
  fun i => if i.val = 0 then 1/3 else if i.val = 3 then -1/5 else 0

theorem density_fixture_residual :
    List.ofFn (rationalResidual (densityLP_A 2) (densityLP_E 2)
      (densityCellObjective (0 : Fin (2 * 2))) densityFixtureY densityFixtureZ) = [5/3,-2/15,0,1/5] := by
  unfold rationalResidual
  simp_rw [← Fin.sum_ofFn]
  norm_num [densityFixtureY, densityFixtureZ, densityLP_A, densityLP_E, densityLP_b, densityLP_d,
    densityEqualityRows, densityInequalityRows, densityEqualityCoefficient, densityInequalityCoefficient,
    densityInequalityRight, densityPrefixCoefficient, densityRowCoefficient, densityColumnCoefficient,
    densityDifferenceCoefficient, densityCellObjective, densityCellPair, densityNeighborStart,
    densityNeighborEnd, List.finRange, List.ofFn_succ, Fin.sum_univ_succ, Finset.filter_insert,
    Finset.range_add_one, Finset.filter_singleton]
  all_goals norm_num [Fin.ext_iff, density_cell_flat_value]

theorem density_fixture_dual_bound :
    densityLPDualLower densityFixtureCDF 2 (densityCellObjective (0 : Fin (2 * 2)))
      densityFixtureY densityFixtureZ = -11/15 := by
  unfold densityLPDualLower rationalDualLower rationalResidual
  simp_rw [← Fin.sum_ofFn]
  norm_num [densityFixtureY, densityFixtureZ, densityLP_A, densityLP_E, densityLP_b, densityLP_d,
    densityEqualityRows, densityInequalityRows, densityEqualityCoefficient, densityInequalityCoefficient,
    densityInequalityRight, densityPrefixCoefficient, densityRowCoefficient, densityColumnCoefficient,
    densityDifferenceCoefficient, densityCellObjective, densityCellPair, densityNeighborStart,
    densityNeighborEnd, List.finRange, List.ofFn_succ, Fin.sum_univ_succ, Finset.filter_insert,
    Finset.range_add_one, Finset.filter_singleton, reportLPCounts, reportCornerCount, reportCornerIndices,
    densityFixtureCDF, cdfFixtureReport, Fin.univ_succ, Finset.filter_insert]
  all_goals norm_num [Fin.ext_iff, density_cell_flat_value]

example : rationalDualValid densityFixtureY = true := by decide
example : rationalDualValid (fun i : Fin (densityInequalityRows 2).length =>
    if i.val = 8 then (1 : ℚ) else 0) = false := by decide
example : checkDensityLPModel densityFixtureCDF 2 (fun i j =>
    if i.val = 9 ∧ j.val = 0 then 1 else densityLP_A 2 i j)
    (densityLP_E 2) (densityLP_b densityFixtureCDF 2) (densityLP_d 2) = false := by decide
example : checkDensityLPModel densityFixtureCDF 2 (densityLP_A 2) (densityLP_E 2)
    (fun i => if i.val = 18 then 0 else densityLP_b densityFixtureCDF 2 i) (densityLP_d 2) = false := by
  simp only [checkDensityLPModel, decide_eq_false_iff_not]
  intro hc
  have hBad := hc.2.2.1 (⟨18, by decide⟩)
  norm_num [densityLP_A, densityLP_E, densityLP_b, densityLP_d, densityEqualityRows, densityInequalityRows,
    densityEqualityCoefficient, densityInequalityCoefficient, densityInequalityRight,
    densityPrefixCoefficient, densityRowCoefficient, densityColumnCoefficient,
    densityDifferenceCoefficient, densityCellObjective, densityCellPair, densityNeighborStart,
    densityNeighborEnd, List.finRange, List.ofFn_succ, Fin.sum_univ_succ, Finset.filter_insert,
    Finset.range_add_one, Finset.filter_singleton, reportLPCounts, reportCornerCount, reportCornerIndices,
    densityFixtureCDF, cdfFixtureReport, Fin.univ_succ, Finset.filter_insert] at hBad

def densityFixtureDual : DensityDualPair 2 := ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩

def densityFixtureBands : DensityBands 2 where
  dual := fun _ => densityFixtureDual
  cellLower := fun _ => 1/2
  cellUpper := fun _ => 3/2
  pointLower := fun _ => 1/2
  pointUpper := fun _ => 3/2
  histogram := fun _ => 1
  cornerExcess := 1/15
  histogramError := 1
  fallback := false

theorem density_fixture_counts (r : ℚ) : ∀ p q : Fin 3,
    reportLPCounts {cdfFixtureReport with radius := r} 2 p q =
      (![![0,0,0], ![0,1,1], ![0,1,3]] : Fin 3 → Fin 3 → ℕ) p q := by
  change ∀ p q : Fin 3, reportLPCounts cdfFixtureReport 2 p q = _
  decide

theorem density_fixture_histogram : ∀ p q : Fin 3,
    densityHistogramCornerQ (fun _ : Fin (2 * 2) => (1 : ℚ)) p.val q.val = (p.val : ℚ) * q.val / 4 := by
  intro p q
  fin_cases p <;> fin_cases q <;>
    norm_num [densityHistogramCornerQ, densityHistogramQ, Finset.sum_range_succ, Finset.filter_insert, Finset.range_add_one, Finset.filter_singleton]

theorem density_fixture_excess (r v : ℚ) (hv : 0 ≤ v)
    (hUpper : ∀ p q : Fin 3,
      |(p.val : ℚ) * q.val / 4 -
        ((![![0,0,0], ![0,1,1], ![0,1,3]] : Fin 3 → Fin 3 → ℕ) p q : ℚ) / 3| - r ≤ v)
    (hAttained : v = 0 ∨ ∃ p q : Fin 3,
      |(p.val : ℚ) * q.val / 4 -
        ((![![0,0,0], ![0,1,1], ![0,1,3]] : Fin 3 → Fin 3 → ℕ) p q : ℚ) / 3| - r = v) :
    densityHistogramViolationQ {cdfFixtureReport with radius := r}
      (fun _ : Fin (2 * 2) => (1 : ℚ)) = v := by
  unfold densityHistogramViolationQ
  rw [Finset.max'_eq_iff]
  constructor
  · rcases hAttained with hZero | ⟨p, q, hValue⟩
    · rw [hZero]; exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      apply Finset.mem_image.mpr
      refine ⟨(p, q), Finset.mem_univ _, ?_⟩
      simpa only [density_fixture_histogram, density_fixture_counts] using hValue
  · intro b hb
    rcases Finset.mem_insert.mp hb with hZero | hImage
    · simpa only [hZero] using hv
    · obtain ⟨⟨p, q⟩, _hpq, rfl⟩ := Finset.mem_image.mp hImage
      simpa only [density_fixture_histogram, density_fixture_counts] using hUpper p q

theorem density_fixture_corner_excess : densityHistogramViolationQ densityFixtureCDF
    (fun _ : Fin (2 * 2) => (1 : ℚ)) = 1 / 15 := by
  apply density_fixture_excess (1/10) (1/15) (by norm_num)
  · intro p q; fin_cases p <;> fin_cases q <;> norm_num
  · right; refine ⟨1, 2, ?_⟩
    change |(1 : ℚ) * 2 / 4 - 1 / 3| - 1 / 10 = 1 / 15
    norm_num

theorem density_fixture_checked : checkDensityBands densityFixtureCDF densityFixtureBands = true := by
  simp only [checkDensityBands, decide_eq_true_eq]
  refine ⟨by decide, ?_, density_fixture_corner_excess.symm, Or.inr ⟨rfl, ?_⟩⟩
  · intro cell; norm_num [densityFixtureBands]
  · unfold DensityBandsCertifiedFields
    constructor
    · intro cell
      fin_cases cell <;>
        norm_num [DensityBandsCertifiedFields, densityFixtureBands, checkDensityDualPair,
          rationalDualValid, densityCellLowerQ, densityCellUpperQ, densityPointLowerQ, densityPointUpperQ,
          densityLPDualLower, rationalDualLower, rationalResidual, densityFixtureDual,
          densityCellObjective, Fin.sum_univ_succ] <;>
        norm_num [Fin.ext_iff]
    · norm_num [densityFixtureBands, densityHistogramErrorQ, densityFixtureCDF]

def densityFixtureFallbackCDF : CDFReport 3 := {cdfFixtureReport with radius := 1}
def densityFixtureFallbackBands : DensityBands 2 :=
  {densityFixtureBands with cornerExcess := 0, fallback := true}
def densityFixtureFallbackReport : DensityReport 3 :=
  ⟨densityFixtureFallbackCDF, 2, densityFixtureFallbackBands⟩

theorem density_fixture_fallback_checked :
    checkDensityReport cdfFixtureChain densityFixtureFallbackReport 1 0 0 = true := by
  have hEta : densityHistogramViolationQ densityFixtureFallbackCDF
      (fun _ : Fin (2 * 2) => (1 : ℚ)) = 0 := by
    apply density_fixture_excess 1 0 (by norm_num)
    · intro p q; fin_cases p <;> fin_cases q <;> norm_num
    · exact Or.inl rfl
  have hCDF : checkCDFReport cdfFixtureChain densityFixtureFallbackCDF 1 0 0 = true := by
    simp only [checkCDFReport, decide_eq_true_eq]
    refine ⟨by decide, by decide, by decide, by decide, by decide, ?_⟩
    rw [report_radius_fallback _ _ (by norm_num [splitRadiusQ])]
    exact le_rfl
  simp only [checkDensityReport, decide_eq_true_eq]
  change checkCDFReport cdfFixtureChain densityFixtureFallbackCDF 1 0 0 = true ∧
    checkDensityBands densityFixtureFallbackCDF densityFixtureFallbackBands = true
  refine ⟨hCDF, ?_⟩
  norm_num [checkDensityBands, densityFixtureFallbackBands, densityFixtureBands, hEta, DensityBandsFallbackFields]

example : checkDensityBands densityFixtureFallbackCDF
    {densityFixtureFallbackBands with cellLower := fun _ => 3/4} = false := by
  norm_num [checkDensityBands, densityFixtureFallbackBands, densityFixtureBands, DensityBandsFallbackFields]
example : checkDensityBands densityFixtureFallbackCDF
    {densityFixtureFallbackBands with histogram := fun _ => 2} = false := by
  norm_num [checkDensityBands, densityFixtureFallbackBands, densityFixtureBands]
example : checkDensityBands densityFixtureFallbackCDF
    {densityFixtureFallbackBands with cornerExcess := 1/10} = false := by
  have hEta : densityHistogramViolationQ densityFixtureFallbackCDF
      (fun _ : Fin (2 * 2) => (1 : ℚ)) = 0 := by
    apply density_fixture_excess 1 0 (by norm_num)
    · intro p q; fin_cases p <;> fin_cases q <;> norm_num
    · exact Or.inl rfl
  norm_num [checkDensityBands, densityFixtureFallbackBands, densityFixtureBands, hEta]
example : checkDensityBands densityFixtureFallbackCDF
    {densityFixtureFallbackBands with histogramError := 0} = false := by
  norm_num [checkDensityBands, densityFixtureFallbackBands, densityFixtureBands, DensityBandsFallbackFields]

#print axioms density_fixture_matrix
#print axioms density_fixture_equalities
#print axioms density_fixture_right
#print axioms density_fixture_dimensions
#print axioms density_fixture_residual
#print axioms density_fixture_dual_bound
#print axioms density_fixture_checked
#print axioms density_fixture_fallback_checked

end QuantyraNullCone
