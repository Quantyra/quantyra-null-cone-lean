import QuantyraNullCone.DensityCellRestrictions

namespace QuantyraNullCone

/-- Actual prefix CDF of the supplied histogram coefficients; margins are not assumed. -/
noncomputable def histogramGridCDF (coefficient : ℕ → ℕ → ℝ) (k p q : ℕ) : ℝ :=
  (∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q, coefficient i j) / (k : ℝ) ^ 2

theorem histogram_cell_corner {k : ℕ} (hk : 0 < k)
    (coefficient : ℕ → ℕ → ℝ) (i j : ℕ) :
    coefficient i j = (k : ℝ) ^ 2 *
      (histogramGridCDF coefficient k (i + 1) (j + 1) - histogramGridCDF coefficient k i (j + 1) -
        histogramGridCDF coefficient k (i + 1) j + histogramGridCDF coefficient k i j) := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  unfold histogramGridCDF
  simp only [Finset.sum_range_succ, Finset.sum_add_distrib]
  field_simp [hkR]
  ring

theorem four_corner_difference_bound {A11 A01 A10 A00 B11 B01 B10 B00 E : ℝ}
    (h11 : |A11 - B11| ≤ E) (h01 : |A01 - B01| ≤ E)
    (h10 : |A10 - B10| ≤ E) (h00 : |A00 - B00| ≤ E) :
    |(A11 - A01 - A10 + A00) - (B11 - B01 - B10 + B00)| ≤ 4 * E := by
  obtain ⟨h11L, h11U⟩ := abs_le.mp h11
  obtain ⟨h01L, h01U⟩ := abs_le.mp h01
  obtain ⟨h10L, h10U⟩ := abs_le.mp h10
  obtain ⟨h00L, h00U⟩ := abs_le.mp h00
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem InDensityClass.histogram_cell_error {rho : DiamondPoint → ℝ} (h : InDensityClass rho)
    {k i j : ℕ} (hk : 0 < k) (hi : i < k) (hj : j < k)
    (coefficient : ℕ → ℕ → ℝ) (F : ℝ → ℝ → ℝ) {a eta : ℝ}
    (hAccuracy : ∀ s t : ℝ, |F s t - populationCDF rho s t| ≤ a)
    (hCorners : ∀ p q : ℕ, p ≤ k → q ≤ k →
      |histogramGridCDF coefficient k p q - F ((p : ℝ) / k) ((q : ℝ) / k)| ≤ a + eta) :
    |coefficient i j - densityGridCellMean rho k i j| ≤ 4 * (k : ℝ) ^ 2 * (2 * a + eta) := by
  have hEach : ∀ p q : ℕ, p ≤ k → q ≤ k →
      |histogramGridCDF coefficient k p q - populationCDF rho ((p : ℝ) / k) ((q : ℝ) / k)| ≤
        2 * a + eta := by
    intro p q hp hq
    have hError := (abs_sub_le (histogramGridCDF coefficient k p q) (F ((p : ℝ) / k) ((q : ℝ) / k))
      (populationCDF rho ((p : ℝ) / k) ((q : ℝ) / k))).trans
        (add_le_add (hCorners p q hp hq) (hAccuracy ((p : ℝ) / k) ((q : ℝ) / k)))
    exact hError.trans_eq (by ring)
  have h11 := hEach (i + 1) (j + 1) (Nat.succ_le_of_lt hi) (Nat.succ_le_of_lt hj)
  have h01 := hEach i (j + 1) hi.le (Nat.succ_le_of_lt hj)
  have h10 := hEach (i + 1) j (Nat.succ_le_of_lt hi) hj.le
  have h00 := hEach i j hi.le hj.le
  have hFour := four_corner_difference_bound h11 h01 h10 h00
  rw [histogram_cell_corner hk coefficient i j, h.grid_cell_CDF hk i j, ← mul_sub,
    abs_mul, abs_of_nonneg (sq_nonneg (k : ℝ))]
  push_cast at hFour
  exact (mul_le_mul_of_nonneg_left hFour (sq_nonneg (k : ℝ))).trans_eq (by ring)

/-- All-point histogram error for arbitrary rounded coefficients in the density box.
    No histogram marginal or LP feasibility assumption is used. -/
theorem InDensityClass.histogram_point_error {rho : DiamondPoint → ℝ} (h : InDensityClass rho)
    {k i j : ℕ} (hk : 0 < k) (hi : i < k) (hj : j < k)
    (coefficient : ℕ → ℕ → ℝ) (F : ℝ → ℝ → ℝ) {a eta : ℝ}
    (hBox : ∀ u v : ℕ, u < k → v < k → (1 / 2 : ℝ) ≤ coefficient u v ∧ coefficient u v ≤ 3 / 2)
    (hAccuracy : ∀ s t : ℝ, |F s t - populationCDF rho s t| ≤ a)
    (hCorners : ∀ u v : ℕ, u ≤ k → v ≤ k →
      |histogramGridCDF coefficient k u v - F ((u : ℝ) / k) ((v : ℝ) / k)| ≤ a + eta)
    {p : DiamondPoint} (hp : p ∈ closedSquareCell ((i : ℝ) / k) ((j : ℝ) / k) (1 / k)) :
    |coefficient i j - rho p| ≤ min 1 (8 * a * (k : ℝ) ^ 2 + 4 * eta * (k : ℝ) ^ 2 + 2 / (k : ℝ)) := by
  have hCell := h.histogram_cell_error hk hi hj coefficient F hAccuracy hCorners
  have hBias := h.grid_cell_point_bias hk hi hj hp
  have hTotal := (abs_sub_le (coefficient i j) (densityGridCellMean rho k i j) (rho p)).trans
    (add_le_add hCell hBias)
  have hTotal' : |coefficient i j - rho p| ≤
      8 * a * (k : ℝ) ^ 2 + 4 * eta * (k : ℝ) ^ 2 + 2 / (k : ℝ) := hTotal.trans_eq (by ring)
  have hI := grid_cell_location hk hi
  have hJ := grid_cell_location hk hj
  have hpD := closed_square_cell_subset hI.1 hJ.1 hI.2 hJ.2 hp
  obtain ⟨hRhoL, hRhoU⟩ := h.bounds p hpD
  obtain ⟨hCoeffL, hCoeffU⟩ := hBox i j hi hj
  have hOne : |coefficient i j - rho p| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  exact le_min hOne hTotal'

#print axioms histogram_cell_corner
#print axioms InDensityClass.histogram_cell_error
#print axioms InDensityClass.histogram_point_error

end QuantyraNullCone
