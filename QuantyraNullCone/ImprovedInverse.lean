import QuantyraNullCone.LogGridRate
import QuantyraNullCone.Unlabeled

namespace QuantyraNullCone

open MeasureTheory

theorem InDensityClass.logarithmic_orderCDFGood_intersects {rho sigma : DiamondPoint → ℝ}
    (hR : InDensityClass rho) (hS : InDensityClass sigma) {n : ℕ} (hn : 65536 ≤ n)
    (hTV : orderLawTV rho sigma n < (4 / 5 : ℝ)) :
    ∃ code : OrderCode n,
      OrderCDFGood rho (174 * Real.sqrt 8 * Real.sqrt (Real.log (n : ℝ) / n)) code ∧
      OrderCDFGood sigma (174 * Real.sqrt 8 * Real.sqrt (Real.log (n : ℝ) / n)) code := by
  classical
  letI := hR.orderLaw_isProbabilityMeasure n
  letI := hS.orderLaw_isProbabilityMeasure n
  let A : Set (OrderCode n) := {code | OrderCDFGood rho (174 * Real.sqrt 8 * Real.sqrt (Real.log (n : ℝ) / n)) code}
  let B : Set (OrderCode n) := {code | OrderCDFGood sigma (174 * Real.sqrt 8 * Real.sqrt (Real.log (n : ℝ) / n)) code}
  by_contra hEmpty
  have hDisjoint : Disjoint A B := by
    rw [Set.disjoint_left]
    exact fun code hA hB => hEmpty ⟨code, hA, hB⟩
  have hSum : (orderLaw sigma n).real A + (orderLaw sigma n).real B ≤ 1 := by
    rw [← measureReal_union (μ := orderLaw sigma n) hDisjoint (orderCDFGood_measurable _ _)]
    exact (measureReal_mono (Set.subset_univ _)).trans_eq probReal_univ
  have hA := hR.logarithmic_orderCDFGood_probability hn
  have hB := hS.logarithmic_orderCDFGood_probability hn
  have hEvent := hR.orderLawTV_event_bound hS n A
  change (9 / 10 : ℝ) ≤ (orderLaw rho n).real A at hA
  change (9 / 10 : ℝ) ≤ (orderLaw sigma n).real B at hB
  linarith

theorem InDensityClass.logarithmic_populationCDF_orbit_of_orderLawTV {rho sigma : DiamondPoint → ℝ}
    (hR : InDensityClass rho) (hS : InDensityClass sigma) {n : ℕ} (hn : 65536 ≤ n)
    (hTV : orderLawTV rho sigma n < (4 / 5 : ℝ)) :
    (∀ s t : ℝ, |populationCDF rho s t - populationCDF sigma s t| ≤
      348 * Real.sqrt 8 * Real.sqrt (Real.log (n : ℝ) / n)) ∨
    (∀ s t : ℝ, |populationCDF rho s t - populationCDF sigma t s| ≤
      348 * Real.sqrt 8 * Real.sqrt (Real.log (n : ℝ) / n)) := by
  obtain ⟨code, hA, hB⟩ := hR.logarithmic_orderCDFGood_intersects hS hn hTV
  have h := orderCDFGood_common_orbit hA hB
  simpa only [show 2 * (174 * Real.sqrt 8 * Real.sqrt (Real.log (n : ℝ) / n)) =
    348 * Real.sqrt 8 * Real.sqrt (Real.log (n : ℝ) / n) by ring] using h


theorem logarithmic_coefficient_constant : 712704 * Real.sqrt (8 : ℝ) ≤ 2197000 := by
  have hSq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)
  nlinarith [Real.sqrt_nonneg (8 : ℝ)]

theorem logarithmic_rate_cube {n : ℕ} (hn : 2 ≤ n) :
    (130 * (Real.log (n : ℝ) / n) ^ (1 / 6 : ℝ)) ^ 3 =
      2197000 * Real.sqrt (Real.log (n : ℝ) / n) := by
  rw [Real.sqrt_eq_rpow, mul_pow, ← Real.rpow_natCast ((Real.log (n : ℝ) / n) ^ (1 / 6 : ℝ)) 3,
    ← Real.rpow_mul (log_ratio_positive hn).le]
  norm_num

theorem InDensityClass.logarithmic_coefficient_rate_of_cdf
    {rho sigma : DiamondPoint → ℝ} (hR : InDensityClass rho) (hS : InDensityClass sigma)
    {n : ℕ} (hn : 2 ≤ n)
    (hCDF : ∀ s t : ℝ, |populationCDF rho s t - populationCDF sigma s t| ≤
      348 * Real.sqrt 8 * Real.sqrt (Real.log (n : ℝ) / n)) :
    coefficientDeviation rho sigma ≤ 130 * (Real.log (n : ℝ) / n) ^ (1 / 6 : ℝ) := by
  have hCube := hR.coefficient_interpolation hS hCDF
  have hConst := mul_le_mul_of_nonneg_right logarithmic_coefficient_constant
    (Real.sqrt_nonneg (Real.log (n : ℝ) / n))
  have hBound : coefficientDeviation rho sigma ^ 3 ≤
      (130 * (Real.log (n : ℝ) / n) ^ (1 / 6 : ℝ)) ^ 3 := by
    rw [logarithmic_rate_cube hn]
    nlinarith only [hCube, hConst]
  exact le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0)
    (mul_nonneg (by norm_num) (Real.rpow_nonneg (log_ratio_positive hn).le _)) hBound

theorem InDensityClass.logarithmic_conformalDistance_of_small_TV
    {rho sigma : DiamondPoint → ℝ} (hR : InDensityClass rho) (hS : InDensityClass sigma)
    {n : ℕ} (hn : 65536 ≤ n) (hTV : orderLawTV rho sigma n < (4 / 5 : ℝ)) :
    conformalDistance rho sigma ≤ 130 * (Real.log (n : ℝ) / n) ^ (1 / 6 : ℝ) := by
  have hnTwo : 2 ≤ n := by omega
  rcases hR.logarithmic_populationCDF_orbit_of_orderLawTV hS hn hTV with hDirect | hSwap
  · exact (min_le_left _ _).trans (hR.logarithmic_coefficient_rate_of_cdf hS hnTwo hDirect)
  · have hCDF : ∀ s t : ℝ,
        |populationCDF rho s t - populationCDF (transposeDensity sigma) s t| ≤
          348 * Real.sqrt 8 * Real.sqrt (Real.log (n : ℝ) / n) := by
      intro s t
      rw [populationCDF_transpose]
      exact hSwap s t
    exact (min_le_right _ _).trans
      (hR.logarithmic_coefficient_rate_of_cdf hS.transpose hnTwo hCDF)

theorem logarithmic_small_sample_lower {n : ℕ} (hn : 2 ≤ n) (hSmall : n < 65536) :
    1 ≤ 130 * (Real.log (n : ℝ) / n) ^ (1 / 6 : ℝ) := by
  have hnPos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnTwo : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnSmall : (n : ℝ) < 65536 := by exact_mod_cast hSmall
  have hLog : (1 / 2 : ℝ) ≤ Real.log n :=
    log_two_lower.trans (Real.log_le_log (by norm_num) hnTwo)
  have hRatio : (1 / 8 : ℝ) ^ 6 ≤ Real.log (n : ℝ) / n := by
    apply (le_div_iff₀ hnPos).mpr
    norm_num
    linarith
  have hPow := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ (1 / 8 : ℝ) ^ 6) hRatio
    (by norm_num : (0 : ℝ) ≤ 1 / 6)
  have hIdentity : ((1 / 8 : ℝ) ^ 6) ^ (1 / 6 : ℝ) = (1 / 8 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 8)]
    norm_num
  rw [hIdentity] at hPow
  linarith

theorem InDensityClass.full_inverse_logarithmic {rho sigma : DiamondPoint → ℝ}
    (hR : InDensityClass rho) (hS : InDensityClass sigma) {N : ℕ} (hN : 2 ≤ N) :
    conformalDistance rho sigma ≤
      130 * ((Real.log (N : ℝ) / N) ^ (1 / 6 : ℝ) + finiteLawDiscrepancy rho sigma N) := by
  have hBounds := hR.conformalDistance_bounds hS
  have hDelta := finiteLawDiscrepancy_nonneg rho sigma hN
  have hRate : 0 ≤ (Real.log (N : ℝ) / N) ^ (1 / 6 : ℝ) :=
    Real.rpow_nonneg (log_ratio_positive hN).le _
  by_cases hLarge : 65536 ≤ N
  · by_cases hTV : orderLawTV rho sigma N < (4 / 5 : ℝ)
    · have h := hR.logarithmic_conformalDistance_of_small_TV hS hLarge hTV
      linarith
    · have hD := orderLawTV_le_finiteLawDiscrepancy rho sigma hN le_rfl
      have hTV' : (4 / 5 : ℝ) ≤ orderLawTV rho sigma N := le_of_not_gt hTV
      linarith
  · have hSmall := logarithmic_small_sample_lower hN (by omega : N < 65536)
    linarith

theorem InDensityClass.full_inverse_logarithmic_unlabeled {rho sigma : DiamondPoint → ℝ}
    (hR : InDensityClass rho) (hS : InDensityClass sigma) {N : ℕ} (hN : 2 ≤ N) :
    conformalDistance rho sigma ≤
      130 * ((Real.log (N : ℝ) / N) ^ (1 / 6 : ℝ) +
        unlabeledFiniteLawDiscrepancy rho sigma N) := by
  rw [hR.unlabeledFiniteLawDiscrepancy_eq hS]
  exact hR.full_inverse_logarithmic hS hN

#print axioms InDensityClass.logarithmic_populationCDF_orbit_of_orderLawTV
#print axioms InDensityClass.full_inverse_logarithmic
#print axioms InDensityClass.full_inverse_logarithmic_unlabeled

end QuantyraNullCone
