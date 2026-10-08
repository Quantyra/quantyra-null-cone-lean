import QuantyraNullCone.DensityCellGrid

namespace QuantyraNullCone

theorem InDensityClass.grid_cell_row {rho : DiamondPoint → ℝ} (h : InDensityClass rho)
    {k i : ℕ} (hk : 0 < k) (hi : i < k) :
    (∑ j ∈ Finset.range k, densityGridCellMean rho k i j) = (k : ℝ) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hI : (i : ℝ) / k ≤ 1 := by
    have hLocation := grid_cell_location hk hi
    linarith [one_div_pos.mpr hkR]
  have hI' : ((i + 1 : ℕ) : ℝ) / k ≤ 1 :=
    (div_le_one hkR).mpr (by exact_mod_cast Nat.succ_le_of_lt hi)
  have hSucc : (∑ j ∈ Finset.range k, densityGridCellMean rho k i j) =
      (∑ u ∈ Finset.range (i + 1), ∑ j ∈ Finset.range k, densityGridCellMean rho k u j) -
        (∑ u ∈ Finset.range i, ∑ j ∈ Finset.range k, densityGridCellMean rho k u j) := by
    rw [Finset.sum_range_succ]
    ring
  rw [hSucc, h.grid_cell_prefix hk (Nat.succ_le_of_lt hi) le_rfl,
    h.grid_cell_prefix hk hi.le le_rfl, div_self hkR.ne',
    h.populationCDF_u_one (by positivity) hI', h.populationCDF_u_one (by positivity) hI]
  push_cast
  field_simp [hkR.ne']
  ring

theorem InDensityClass.grid_cell_transpose {rho : DiamondPoint → ℝ} (h : InDensityClass rho)
    {k : ℕ} (hk : 0 < k) (i j : ℕ) :
    densityGridCellMean (transposeDensity rho) k i j = densityGridCellMean rho k j i :=
  h.cell_mean_transpose (by positivity)

theorem InDensityClass.grid_cell_column {rho : DiamondPoint → ℝ} (h : InDensityClass rho)
    {k j : ℕ} (hk : 0 < k) (hj : j < k) :
    (∑ i ∈ Finset.range k, densityGridCellMean rho k i j) = (k : ℝ) := by
  have hRow := h.transpose.grid_cell_row hk hj
  simp_rw [h.grid_cell_transpose hk] at hRow
  exact hRow

theorem InDensityClass.grid_cell_row_fin {rho : DiamondPoint → ℝ} (h : InDensityClass rho)
    {k : ℕ} (hk : 0 < k) (i : Fin k) :
    (∑ j : Fin k, densityGridCellMean rho k i.val j.val) = (k : ℝ) := by
  rw [Fin.sum_univ_eq_sum_range]
  exact h.grid_cell_row hk i.isLt

theorem InDensityClass.grid_cell_column_fin {rho : DiamondPoint → ℝ} (h : InDensityClass rho)
    {k : ℕ} (hk : 0 < k) (j : Fin k) :
    (∑ i : Fin k, densityGridCellMean rho k i.val j.val) = (k : ℝ) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => densityGridCellMean rho k i j.val) k]
  exact h.grid_cell_column hk j.isLt

theorem InDensityClass.grid_cell_horizontal {rho : DiamondPoint → ℝ} (h : InDensityClass rho)
    {k i j : ℕ} (hk : 0 < k) (hi : i + 1 < k) (hj : j < k) :
    |densityGridCellMean rho k (i + 1) j - densityGridCellMean rho k i j| ≤ 2 / (k : ℝ) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hI := grid_cell_location hk (Nat.lt_of_succ_lt hi)
  have hJ := grid_cell_location hk hj
  have hINat : i + 2 ≤ k := Nat.succ_le_of_lt hi
  have hIReal : (i : ℝ) + 2 ≤ k := by exact_mod_cast hINat
  have hI2 : (i : ℝ) / k + 1 / k + 1 / k ≤ 1 := by
    rw [← add_div, ← add_div]
    apply (div_le_one hkR).mpr
    linarith
  have hBound := h.cell_mean_horizontal (one_div_pos.mpr hkR) hI.1 hJ.1 hI2 hJ.2
  simpa [densityGridCellMean, Nat.cast_add, add_div, mul_one_div] using hBound

theorem InDensityClass.grid_cell_vertical {rho : DiamondPoint → ℝ} (h : InDensityClass rho)
    {k i j : ℕ} (hk : 0 < k) (hi : i < k) (hj : j + 1 < k) :
    |densityGridCellMean rho k i (j + 1) - densityGridCellMean rho k i j| ≤ 2 / (k : ℝ) := by
  have hBound := h.transpose.grid_cell_horizontal hk hj hi
  simp_rw [h.grid_cell_transpose hk] at hBound
  exact hBound

theorem InDensityClass.grid_cell_point_bias {rho : DiamondPoint → ℝ} (h : InDensityClass rho)
    {k i j : ℕ} (hk : 0 < k) (hi : i < k) (hj : j < k)
    {p : DiamondPoint} (hp : p ∈ closedSquareCell ((i : ℝ) / k) ((j : ℝ) / k) (1 / k)) :
    |densityGridCellMean rho k i j - rho p| ≤ 2 / (k : ℝ) := by
  have hI := grid_cell_location hk hi
  have hJ := grid_cell_location hk hj
  have hBound := h.cell_mean_point_bias (by positivity : (0 : ℝ) < 1 / k) hI.1 hJ.1 hI.2 hJ.2 hp
  simpa only [densityGridCellMean, mul_one_div] using hBound

/-- The CDF-quality event implies both exact LP prefix inequalities for actual means. -/
theorem InDensityClass.grid_cell_prefix_restriction {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) {k p q : ℕ} (hk : 0 < k) (hp : p ≤ k) (hq : q ≤ k)
    (F : ℝ → ℝ → ℝ) {radius : ℝ}
    (hAccuracy : |F ((p : ℝ) / k) ((q : ℝ) / k) -
      populationCDF rho ((p : ℝ) / k) ((q : ℝ) / k)| ≤ radius) :
    (k : ℝ) ^ 2 * (F ((p : ℝ) / k) ((q : ℝ) / k) - radius) ≤
      (∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q, densityGridCellMean rho k i j) ∧
    (∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q, densityGridCellMean rho k i j) ≤
      (k : ℝ) ^ 2 * (F ((p : ℝ) / k) ((q : ℝ) / k) + radius) := by
  rw [h.grid_cell_prefix hk hp hq]
  have hBounds := abs_le.mp hAccuracy
  constructor
  · apply mul_le_mul_of_nonneg_left _ (sq_nonneg (k : ℝ))
    linarith
  · apply mul_le_mul_of_nonneg_left _ (sq_nonneg (k : ℝ))
    linarith

#print axioms InDensityClass.grid_cell_row_fin
#print axioms InDensityClass.grid_cell_column_fin
#print axioms InDensityClass.grid_cell_horizontal
#print axioms InDensityClass.grid_cell_vertical
#print axioms InDensityClass.grid_cell_point_bias
#print axioms InDensityClass.grid_cell_prefix_restriction

end QuantyraNullCone
