import QuantyraNullCone.ConfoundingTargets
import QuantyraNullCone.ProperTime

namespace QuantyraNullCone

open MeasureTheory Set

def calibrationDiagonal : FutureCurve (0,0) (1,1) where
  u := id
  v := id
  uAC := LipschitzWith.id.lipschitzOnWith.absolutelyContinuousOnInterval
  vAC := LipschitzWith.id.lipschitzOnWith.absolutelyContinuousOnInterval
  startU := rfl
  startV := rfl
  endU := rfl
  endV := rfl
  inDiamond := fun _ ht => ⟨ht, ht⟩
  futureU := ae_of_all _ (fun _ => by simp)
  futureV := ae_of_all _ (fun _ => by simp)

theorem calibration_diagonal_flat_length : calibrationDiagonal.length lowerFlat = Real.sqrt 2 := by
  simp [FutureCurve.length, calibrationDiagonal, lowerFlat, curveMeasure]

theorem calibration_flat_curve_length {p q : DiamondPoint} (c : FutureCurve p q) :
    c.length lowerFlat ≤ Real.sqrt 2 := by
  rw [c.length_eq_factored lower_flat_in_class]
  simp only [lowerFlat, mul_one, integral_const_mul]
  simpa using mul_le_mul_of_nonneg_left c.integral_weight_le_one (Real.sqrt_nonneg 2)

theorem calibration_flat_time : timeSeparation lowerFlat (0,0) (1,1) = Real.sqrt 2 := by
  apply le_antisymm
  · apply csSup_le (by simp : (insert 0 (Set.range
      (fun c : FutureCurve (0,0) (1,1) => c.length lowerFlat))).Nonempty)
    rintro x (hx | ⟨c, rfl⟩)
    · subst x
      exact Real.sqrt_nonneg (2 : ℝ)
    · exact calibration_flat_curve_length c
  · rw [← calibration_diagonal_flat_length]
    exact lower_flat_in_class.length_le_timeSeparation calibrationDiagonal

theorem calibration_sqrt_lower {x : ℝ} (hx : 0 ≤ x) (hxSmall : x ≤ 1/2) :
    1 + 4*x/9 ≤ Real.sqrt (1+x) := by
  apply Real.le_sqrt_of_sq_le
  nlinarith [mul_nonneg hx (show 0 ≤ 1/2-x by linarith)]

theorem calibration_profile_square_integral :
    (∫ t in (0 : ℝ)..1, (calibrationProfile t)^2) = 1/3 := by
  have h (t : ℝ) : (calibrationProfile t)^2 = (4*t^2 - 4*t) + 1 := by
    unfold calibrationProfile
    ring
  simp_rw [h]
  rw [intervalIntegral.integral_add
    ((show Continuous (fun t : ℝ => 4*t^2 - 4*t) by fun_prop).intervalIntegrable 0 1)
    (continuous_const.intervalIntegrable 0 1),
    intervalIntegral.integral_sub
      ((show Continuous (fun t : ℝ => 4*t^2) by fun_prop).intervalIntegrable 0 1)
      ((show Continuous (fun t : ℝ => 4*t) by fun_prop).intervalIntegrable 0 1),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  norm_num [integral_pow, integral_id]

theorem calibration_diagonal_length_lower {epsilon : ℝ} (he : 0 ≤ epsilon)
    (heSmall : epsilon ≤ 1/2) :
    Real.sqrt 2 * (1 + 4*epsilon/27) ≤ calibrationDiagonal.length (calibrationDensity epsilon) := by
  have hK := calibration_density_in_class he heSmall
  have hInt : Integrable (fun t => Real.sqrt 2 * (1 + 4*(epsilon*(calibrationProfile t)^2)/9))
      curveMeasure :=
    (show Continuous (fun t : ℝ => Real.sqrt 2 * (1 + 4*(epsilon*(calibrationProfile t)^2)/9)) by
      unfold calibrationProfile
      fun_prop).continuousOn.integrableOn_compact isCompact_Icc
  have hl : (∫ t, Real.sqrt 2 * (1+4*(epsilon*(calibrationProfile t)^2)/9) ∂curveMeasure) ≤
      calibrationDiagonal.length (calibrationDensity epsilon) := by
    apply integral_mono_ae hInt (calibrationDiagonal.integrable_length hK)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hsq : (calibrationProfile t)^2 ≤ 1 := by
      have h := calibration_profile_abs ht
      nlinarith [sq_abs (calibrationProfile t), abs_nonneg (calibrationProfile t)]
    have h0 : 0 ≤ epsilon*(calibrationProfile t)^2 := by positivity
    have hu : epsilon*(calibrationProfile t)^2 ≤ 1/2 := by nlinarith
    have hb := mul_le_mul_of_nonneg_left (calibration_sqrt_lower h0 hu) (Real.sqrt_nonneg 2)
    have hid : 2 * calibrationDensity epsilon (calibrationDiagonal.point t) *
        deriv calibrationDiagonal.u t * deriv calibrationDiagonal.v t =
        2 * (1 + epsilon*(calibrationProfile t)^2) := by
      simp [calibrationDiagonal, FutureCurve.point, calibrationDensity]
      ring
    rw [hid, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact hb
  have hi : (∫ t, Real.sqrt 2 * (1+4*(epsilon*(calibrationProfile t)^2)/9) ∂curveMeasure) =
      Real.sqrt 2 * (1+4*epsilon/27) := by
    rw [integral_const_mul]
    change Real.sqrt 2 * (∫ t in Icc (0 : ℝ) 1, 1+4*(epsilon*(calibrationProfile t)^2)/9) = _
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
    have hf : (fun t : ℝ => 1+4*(epsilon*(calibrationProfile t)^2)/9) =
        (fun t => 1+(4*epsilon/9)*(calibrationProfile t)^2) := by funext t; ring
    rw [hf, intervalIntegral.integral_add (continuous_const.intervalIntegrable 0 1)
      (((calibration_profile_smooth.continuous.pow 2).const_mul _).intervalIntegrable 0 1),
      intervalIntegral.integral_const_mul, calibration_profile_square_integral]
    simp
    ring
  rwa [hi] at hl

/-- Separation of the existing supremum over actual absolutely continuous future curves. -/
theorem calibration_time_separation :
    Real.sqrt 2 / 30 < timeSeparation (calibrationDensity (1/4)) (0,0) (1,1) -
      timeSeparation lowerFlat (0,0) (1,1) := by
  have hl := calibration_diagonal_length_lower (epsilon := 1/4) (by norm_num) (by norm_num)
  have ht := (calibration_density_in_class (epsilon := 1/4) (by norm_num) (by norm_num)).length_le_timeSeparation
    calibrationDiagonal
  rw [calibration_flat_time]
  have hs : 0 < Real.sqrt 2 := by positivity
  linarith

end QuantyraNullCone
