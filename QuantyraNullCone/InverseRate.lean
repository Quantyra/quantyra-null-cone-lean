import QuantyraNullCone.Transpose
import QuantyraNullCone.FiniteTV

namespace QuantyraNullCone

theorem InDensityClass.coefficientDeviation_bounds {rho sigma : DiamondPoint → ℝ}
    (hR : InDensityClass rho) (hS : InDensityClass sigma) :
    0 ≤ coefficientDeviation rho sigma ∧ coefficientDeviation rho sigma ≤ 1 := by
  obtain ⟨p, hp, hValue⟩ := hR.coefficientDeviation_attained hS
  rw [hValue]
  refine ⟨abs_nonneg _, abs_le.mpr ?_⟩
  have hRp := hR.bounds p hp
  have hSp := hS.bounds p hp
  constructor <;> linarith

theorem InDensityClass.conformalDistance_bounds {rho sigma : DiamondPoint → ℝ}
    (hR : InDensityClass rho) (hS : InDensityClass sigma) :
    0 ≤ conformalDistance rho sigma ∧ conformalDistance rho sigma ≤ 1 := by
  have hD := hR.coefficientDeviation_bounds hS
  have hT := hR.coefficientDeviation_bounds hS.transpose
  exact ⟨le_min hD.1 hT.1, (min_le_left _ _).trans hD.2⟩

theorem orderLawTV_nonneg (rho sigma : DiamondPoint → ℝ) (n : ℕ) :
    0 ≤ orderLawTV rho sigma n := by
  unfold orderLawTV
  positivity

theorem finiteLawDiscrepancy_set (rho sigma : DiamondPoint → ℝ) (N : ℕ) :
    {d : ℝ | ∃ k : ℕ, 2 ≤ k ∧ k ≤ N ∧ d = orderLawTV rho sigma k} =
      (orderLawTV rho sigma) '' Set.Icc 2 N := by
  ext d
  constructor
  · rintro ⟨k, hk, hN, rfl⟩
    exact ⟨k, ⟨hk, hN⟩, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk.1, hk.2, rfl⟩

theorem orderLawTV_le_finiteLawDiscrepancy (rho sigma : DiamondPoint → ℝ)
    {k N : ℕ} (hk : 2 ≤ k) (hN : k ≤ N) :
    orderLawTV rho sigma k ≤ finiteLawDiscrepancy rho sigma N := by
  unfold finiteLawDiscrepancy
  rw [finiteLawDiscrepancy_set]
  exact le_csSup ((Set.finite_Icc 2 N).image (orderLawTV rho sigma)).bddAbove
    ⟨k, ⟨hk, hN⟩, rfl⟩

theorem finiteLawDiscrepancy_nonneg (rho sigma : DiamondPoint → ℝ)
    {N : ℕ} (hN : 2 ≤ N) : 0 ≤ finiteLawDiscrepancy rho sigma N :=
  (orderLawTV_nonneg rho sigma N).trans
    (orderLawTV_le_finiteLawDiscrepancy rho sigma hN le_rfl)

theorem coefficient_rate_cube (n : ℕ) :
    (100 * (n : ℝ) ^ (-1 / 12 : ℝ)) ^ 3 =
      1000000 * (n : ℝ) ^ (-1 / 4 : ℝ) := by
  rw [mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ (-1 / 12 : ℝ)) 3,
    ← Real.rpow_mul (Nat.cast_nonneg n)]
  norm_num

theorem InDensityClass.coefficient_rate_of_cdf {rho sigma : DiamondPoint → ℝ}
    (hR : InDensityClass rho) (hS : InDensityClass sigma) (n : ℕ)
    (hCDF : ∀ s t : ℝ, |populationCDF rho s t - populationCDF sigma s t| ≤
      348 * (n : ℝ) ^ (-1 / 4 : ℝ)) :
    coefficientDeviation rho sigma ≤ 100 * (n : ℝ) ^ (-1 / 12 : ℝ) := by
  have hCube := hR.coefficient_interpolation hS hCDF
  have hNonneg : 0 ≤ (n : ℝ) ^ (-1 / 4 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hBound : coefficientDeviation rho sigma ^ 3 ≤
      (100 * (n : ℝ) ^ (-1 / 12 : ℝ)) ^ 3 := by
    rw [coefficient_rate_cube]
    nlinarith only [hCube, hNonneg]
  exact le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) (by positivity) hBound

theorem InDensityClass.conformalDistance_of_small_TV {rho sigma : DiamondPoint → ℝ}
    (hR : InDensityClass rho) (hS : InDensityClass sigma) {n : ℕ} (hn : 65536 ≤ n)
    (hTV : orderLawTV rho sigma n < (4 / 5 : ℝ)) :
    conformalDistance rho sigma ≤ 100 * (n : ℝ) ^ (-1 / 12 : ℝ) := by
  rcases hR.populationCDF_orbit_of_orderLawTV hS hn hTV with hDirect | hSwap
  · exact (min_le_left _ _).trans (hR.coefficient_rate_of_cdf hS n hDirect)
  · have hCDF : ∀ s t : ℝ,
        |populationCDF rho s t - populationCDF (transposeDensity sigma) s t| ≤
          348 * (n : ℝ) ^ (-1 / 4 : ℝ) := by
      intro s t
      rw [populationCDF_transpose]
      exact hSwap s t
    exact (min_le_right _ _).trans (hR.coefficient_rate_of_cdf hS.transpose n hCDF)

theorem small_sample_rate_lower {n : ℕ} (hn : 0 < n) (hSmall : n < 65536) :
    1 ≤ 100 * (n : ℝ) ^ (-1 / 12 : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hN : (n : ℝ) ≤ (100 : ℝ) ^ 12 := by
    have h := (show (n : ℝ) < 65536 by exact_mod_cast hSmall)
    norm_num at ⊢
    linarith
  have hAnti := Real.rpow_le_rpow_of_nonpos hnR hN (by norm_num : (-1 / 12 : ℝ) ≤ 0)
  have hPow : ((100 : ℝ) ^ 12) ^ (-1 / 12 : ℝ) = (100 : ℝ)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 100)]
    norm_num
  rw [hPow] at hAnti
  linarith

/-- The original all-N coefficient inverse estimate for the actual density class and
actual iid directed-order laws. All analytic and probability bridges are proved. -/
theorem InDensityClass.full_inverse {rho sigma : DiamondPoint → ℝ}
    (hR : InDensityClass rho) (hS : InDensityClass sigma) {N : ℕ} (hN : 2 ≤ N) :
    conformalDistance rho sigma ≤
      100 * ((N : ℝ) ^ (-1 / 12 : ℝ) + finiteLawDiscrepancy rho sigma N) := by
  have hBounds := hR.conformalDistance_bounds hS
  have hDelta := finiteLawDiscrepancy_nonneg rho sigma hN
  have hRate : 0 ≤ (N : ℝ) ^ (-1 / 12 : ℝ) := by positivity
  by_cases hLarge : 65536 ≤ N
  · by_cases hTV : orderLawTV rho sigma N < (4 / 5 : ℝ)
    · have h := hR.conformalDistance_of_small_TV hS hLarge hTV
      linarith
    · have hD := orderLawTV_le_finiteLawDiscrepancy rho sigma hN le_rfl
      have hTV' : (4 / 5 : ℝ) ≤ orderLawTV rho sigma N := le_of_not_gt hTV
      linarith
  · have hSmall := small_sample_rate_lower (by omega : 0 < N) (by omega : N < 65536)
    linarith

#print axioms InDensityClass.coefficientDeviation_bounds
#print axioms InDensityClass.conformalDistance_bounds
#print axioms orderLawTV_le_finiteLawDiscrepancy
#print axioms InDensityClass.conformalDistance_of_small_TV
#print axioms InDensityClass.full_inverse

end QuantyraNullCone
