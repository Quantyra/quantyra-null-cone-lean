import QuantyraNullCone.VolumeRateLikelihood

namespace QuantyraNullCone

open MeasureTheory

noncomputable def volumeSamplingEpsilon (n : ℕ) : ℝ := volumeSamplingScale n/2

theorem volume_sampling_epsilon_positive {n : ℕ} (hn : 0 < n) : 0 < volumeSamplingEpsilon n :=
  div_pos (volume_sampling_scale_positive hn) (by norm_num)

theorem volume_sampling_epsilon_small {n : ℕ} (hn : 0 < n) : volumeSamplingEpsilon n ≤ 1/2 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : 1 ≤ Real.sqrt (n : ℝ) := Real.one_le_sqrt.mpr hn1
  unfold volumeSamplingEpsilon volumeSamplingScale
  have hi : 1 / Real.sqrt (n : ℝ) ≤ 1 := (div_le_one (by positivity)).mpr hs
  linarith

theorem volume_sampling_epsilon_square {n : ℕ} (hn : 0 < n) :
    volumeSamplingEpsilon n^2/9 = 1/(36*(n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply (eq_div_iff (by positivity : 36*(n : ℝ) ≠ 0)).mpr
  unfold volumeSamplingEpsilon
  have h := volume_sampling_budget hn
  nlinarith

/-- A finite Bernoulli argument, with no limiting exponential approximation. -/
theorem volume_sampling_power_bound {n : ℕ} (hn : 0 < n) :
    (1+1/(36*(n : ℝ)))^n ≤ (36/35 : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  let x : ℝ := 1/(36*(n : ℝ))
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hx1 : x ≤ 1 := by
    dsimp [x]
    apply (div_le_one (by positivity)).mpr
    linarith
  have hnx : (n : ℝ)*x = 1/36 := by dsimp [x]; field_simp
  have hBern := one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ -x) n
  have hlo : (35/36 : ℝ) ≤ (1-x)^n := by
    simp only [mul_neg, ← sub_eq_add_neg] at hBern
    linarith
  have hprod : (1+x)^n*(1-x)^n ≤ 1 := by
    rw [← mul_pow]
    apply pow_le_one₀ (mul_nonneg (by linarith) (by linarith))
    nlinarith [sq_nonneg x]
  have hmul := mul_le_mul_of_nonneg_left hlo (pow_nonneg (by linarith : 0 ≤ 1+x) n)
  change (1+x)^n ≤ (36/35 : ℝ)
  linarith

theorem volume_sampling_divergence_bound {n : ℕ} (hn : 0 < n) :
    (∫ x, (calibrationLikelihood (volumeSamplingEpsilon n) x-1)^2 ∂lowerBaseSample n) ≤ (1/35 : ℝ) := by
  rw [calibration_product_divergence (volume_sampling_epsilon_positive hn).le
    (volume_sampling_epsilon_small hn), volume_sampling_epsilon_square hn]
  linarith [volume_sampling_power_bound hn]

end QuantyraNullCone
