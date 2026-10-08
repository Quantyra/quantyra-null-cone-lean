import QuantyraNullCone.DensityCellBias
import QuantyraNullCone.DensityCellTranslations

namespace QuantyraNullCone

open MeasureTheory

noncomputable def densityGridCellMean (rho : DiamondPoint → ℝ) (k i j : ℕ) : ℝ :=
  densityCellMean rho ((i : ℝ) / k) ((j : ℝ) / k) (1 / k)

theorem grid_cell_location {k i : ℕ} (hk : 0 < k) (hi : i < k) :
    0 ≤ (i : ℝ) / k ∧ (i : ℝ) / k + 1 / k ≤ 1 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  refine ⟨by positivity, ?_⟩
  rw [← add_div]
  apply (div_le_one hkR).mpr
  exact_mod_cast Nat.succ_le_of_lt hi

theorem InDensityClass.grid_cell_bounds {rho : DiamondPoint → ℝ} (h : InDensityClass rho)
    {k i j : ℕ} (hk : 0 < k) (hi : i < k) (hj : j < k) :
    (1 / 2 : ℝ) ≤ densityGridCellMean rho k i j ∧ densityGridCellMean rho k i j ≤ 3 / 2 := by
  have hI := grid_cell_location hk hi
  have hJ := grid_cell_location hk hj
  exact h.cell_mean_bounds (by positivity) hI.1 hJ.1 hI.2 hJ.2

theorem InDensityClass.grid_cell_CDF {rho : DiamondPoint → ℝ} (h : InDensityClass rho)
    {k : ℕ} (hk : 0 < k) (i j : ℕ) :
    densityGridCellMean rho k i j = (k : ℝ) ^ 2 *
      (populationCDF rho (((i : ℝ) + 1) / k) (((j : ℝ) + 1) / k) -
        populationCDF rho ((i : ℝ) / k) (((j : ℝ) + 1) / k) -
        populationCDF rho (((i : ℝ) + 1) / k) ((j : ℝ) / k) +
        populationCDF rho ((i : ℝ) / k) ((j : ℝ) / k)) := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  unfold densityGridCellMean
  rw [h.cell_mean_CDF (by positivity : (0 : ℝ) ≤ 1 / k)]
  rw [← add_div, ← add_div]
  field_simp [hkR]

theorem sum_rectangle_differences (F : ℕ → ℕ → ℝ) (p q : ℕ) :
    (∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q,
      (F (i + 1) (j + 1) - F i (j + 1) - F (i + 1) j + F i j)) =
      F p q - F 0 q - F p 0 + F 0 0 := by
  have hInner : ∀ i, (∑ j ∈ Finset.range q,
      (F (i + 1) (j + 1) - F i (j + 1) - F (i + 1) j + F i j)) =
      (F (i + 1) q - F i q) - (F (i + 1) 0 - F i 0) := by
    intro i
    calc
      _ = ∑ j ∈ Finset.range q,
          ((F (i + 1) (j + 1) - F i (j + 1)) - (F (i + 1) j - F i j)) := by
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := Finset.sum_range_sub (fun j => F (i + 1) j - F i j) q
  simp_rw [hInner]
  calc
    _ = ∑ i ∈ Finset.range p, ((F (i + 1) q - F (i + 1) 0) - (F i q - F i 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (F p q - F p 0) - (F 0 q - F 0 0) := Finset.sum_range_sub (fun i => F i q - F i 0) p
    _ = _ := by ring

theorem InDensityClass.population_CDF_zero_first {rho : DiamondPoint → ℝ} (h : InDensityClass rho)
    {t : ℝ} (ht : t ≤ 1) : populationCDF rho 0 t = 0 := by
  letI : IsProbabilityMeasure (densityMeasure rho) := h.isProbabilityMeasure
  have hSub : cdfRegion 0 t ⊆ cdfRegion 0 1 := fun _ hp => ⟨hp.1, hp.2.trans ht⟩
  have hLe : populationCDF rho 0 t ≤ populationCDF rho 0 1 := measureReal_mono hSub
  have hZero : populationCDF rho 0 1 = 0 := h.populationCDF_u_one (by norm_num) (by norm_num)
  rw [hZero] at hLe
  exact le_antisymm hLe measureReal_nonneg

theorem InDensityClass.population_CDF_zero_second {rho : DiamondPoint → ℝ} (h : InDensityClass rho)
    {s : ℝ} (hs : s ≤ 1) : populationCDF rho s 0 = 0 := by
  rw [← populationCDF_transpose rho 0 s]
  exact h.transpose.population_CDF_zero_first hs

/-- Actual prefix masses equal the population CDF, with no feasible-vector premise. -/
theorem InDensityClass.grid_cell_prefix {rho : DiamondPoint → ℝ} (h : InDensityClass rho)
    {k p q : ℕ} (hk : 0 < k) (hp : p ≤ k) (hq : q ≤ k) :
    (∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q, densityGridCellMean rho k i j) =
      (k : ℝ) ^ 2 * populationCDF rho ((p : ℝ) / k) ((q : ℝ) / k) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hpR : (p : ℝ) / k ≤ 1 := (div_le_one hkR).mpr (by exact_mod_cast hp)
  have hqR : (q : ℝ) / k ≤ 1 := (div_le_one hkR).mpr (by exact_mod_cast hq)
  simp_rw [h.grid_cell_CDF hk, ← Finset.mul_sum]
  have hTel := sum_rectangle_differences (fun i j => populationCDF rho ((i : ℝ) / k) ((j : ℝ) / k)) p q
  simp only [Nat.cast_add, Nat.cast_one] at hTel
  rw [hTel]
  simp [h.population_CDF_zero_first hqR, h.population_CDF_zero_second hpR,
    h.population_CDF_zero_first (by norm_num : (0 : ℝ) ≤ 1)]

#print axioms InDensityClass.grid_cell_bounds
#print axioms sum_rectangle_differences
#print axioms InDensityClass.grid_cell_prefix

end QuantyraNullCone
