import QuantyraNullCone.LogLowerProfile

namespace QuantyraNullCone

open MeasureTheory

theorem log_lower_raw_square_integrable {h : ℝ} (hh : h ≠ 0) (c : ℝ) :
    Integrable (fun x : ℝ => logLowerRaw h c x ^ 2) :=
  (odd_gaussian_square_integrable.comp_div hh).comp_sub_right c

theorem log_lower_raw_total_moment {h : ℝ} (hh : 0 < h) (c : ℝ) :
    (∫ x : ℝ, logLowerRaw h c x ^ 2) = h * (∫ t : ℝ, oddGaussian t ^ 2) := by
  change (∫ x : ℝ, oddGaussian ((x-c)/h)^2) = _
  rw [integral_sub_right_eq_self (fun x : ℝ => oddGaussian (x/h)^2) c,
    Measure.integral_comp_div (fun t : ℝ => oddGaussian t^2) h, abs_of_pos hh, smul_eq_mul]

theorem log_lower_gaussian_moment_le_one : (∫ t : ℝ, oddGaussian t^2) ≤ 1 := by
  have hNonneg : 0 ≤ ∫ t : ℝ, oddGaussian t^2 := integral_nonneg (fun _ => sq_nonneg _)
  have hSq := odd_gaussian_second_moment_sq
  have hPi := Real.pi_lt_four
  nlinarith

theorem log_lower_raw_interval_moment {h : ℝ} (hh : 0 < h) (c : ℝ) :
    (∫ x in (0 : ℝ)..1, logLowerRaw h c x ^ 2) ≤ h := by
  have hSub : (∫ x in (0 : ℝ)..1, logLowerRaw h c x ^ 2) ≤
      ∫ x : ℝ, logLowerRaw h c x ^ 2 := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact setIntegral_le_integral (log_lower_raw_square_integrable hh.ne' c)
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
  rw [log_lower_raw_total_moment hh c] at hSub
  exact hSub.trans (by nlinarith [mul_le_mul_of_nonneg_left log_lower_gaussian_moment_le_one hh.le])

theorem log_lower_profile_variance (h c : ℝ) :
    (∫ x in (0 : ℝ)..1, logLowerProfile h c x ^ 2) =
      (∫ x in (0 : ℝ)..1, logLowerRaw h c x ^ 2) - logLowerMean h c ^ 2 := by
  have hc := (log_lower_raw_smooth h c).continuous
  have hEq : (fun x => logLowerProfile h c x ^ 2) =
      (fun x => logLowerRaw h c x ^ 2 - (2 * logLowerMean h c) * logLowerRaw h c x +
        logLowerMean h c ^ 2) := by
    funext x
    unfold logLowerProfile
    ring
  rw [hEq, intervalIntegral.integral_add
    ((hc.pow 2).intervalIntegrable 0 1 |>.sub ((hc.const_mul _).intervalIntegrable 0 1))
    intervalIntegrable_const,
    intervalIntegral.integral_sub ((hc.pow 2).intervalIntegrable 0 1)
      ((hc.const_mul _).intervalIntegrable 0 1),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
  change (∫ x in (0 : ℝ)..1, logLowerRaw h c x ^ 2) -
    2 * logLowerMean h c * logLowerMean h c + (1-0) • logLowerMean h c ^ 2 = _
  simp only [sub_zero, one_smul]
  ring

theorem log_lower_profile_moment {h : ℝ} (hh : 0 < h) (c : ℝ) :
    0 ≤ (∫ x in (0 : ℝ)..1, logLowerProfile h c x ^ 2) ∧
      (∫ x in (0 : ℝ)..1, logLowerProfile h c x ^ 2) ≤ h := by
  constructor
  · rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact integral_nonneg (fun _ => sq_nonneg _)
  · rw [log_lower_profile_variance]
    nlinarith [log_lower_raw_interval_moment hh c, sq_nonneg (logLowerMean h c)]

#print axioms log_lower_raw_square_integrable
#print axioms log_lower_raw_total_moment
#print axioms log_lower_gaussian_moment_le_one
#print axioms log_lower_raw_interval_moment
#print axioms log_lower_profile_variance
#print axioms log_lower_profile_moment

end QuantyraNullCone
