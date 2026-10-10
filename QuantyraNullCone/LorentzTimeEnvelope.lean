import QuantyraNullCone.LorentzCurveMap

namespace QuantyraNullCone
open MeasureTheory Set
noncomputable section
set_option maxHeartbeats 800000

/-- A rational, continuous majorant avoids an irrational splitting point in the AC estimate. -/
def timeShapeEnvelope3 (t : ℝ) : ℝ :=
  t^2 - 1/10 + 2 * max 0 (1/10 - (9/10)*t^2)

theorem continuous_time_shape_envelope3 : Continuous timeShapeEnvelope3 := by
  unfold timeShapeEnvelope3
  fun_prop

theorem abs_time_shape_le_envelope3 (t : ℝ) : |t^2-1/10| ≤ timeShapeEnvelope3 t := by
  have h0 := le_max_left (0 : ℝ) (1/10-(9/10)*t^2)
  have h1 := le_max_right (0 : ℝ) (1/10-(9/10)*t^2)
  apply abs_le.mpr
  unfold timeShapeEnvelope3
  constructor <;> nlinarith [sq_nonneg t]

theorem time_shape_envelope_nonneg3 (t : ℝ) : 0 ≤ timeShapeEnvelope3 t :=
  (abs_nonneg _).trans (abs_time_shape_le_envelope3 t)

theorem time_shape_envelope_small3 {t : ℝ} (ht : |t| ≤ 1/3) :
    timeShapeEnvelope3 t = -(4/5)*t^2 + 1/10 := by
  have hsq : t^2 ≤ 1/9 := by nlinarith [sq_abs t, abs_nonneg t]
  unfold timeShapeEnvelope3
  rw [max_eq_right (by nlinarith : (0 : ℝ) ≤ 1/10-(9/10)*t^2)]
  ring

theorem time_shape_envelope_large3 {t : ℝ} (ht : 1/3 ≤ |t|) :
    timeShapeEnvelope3 t = t^2 + (-1/10) := by
  have hsq : 1/9 ≤ t^2 := by nlinarith [sq_abs t]
  unfold timeShapeEnvelope3
  rw [max_eq_left (by nlinarith : 1/10-(9/10)*t^2 ≤ (0 : ℝ))]
  ring

theorem time_shape_envelope_le_one3 {t : ℝ} (ht : |t| ≤ 1) :
    timeShapeEnvelope3 t ≤ 1 := by
  have hsq : t^2 ≤ 1 := by nlinarith [sq_abs t, abs_nonneg t]
  unfold timeShapeEnvelope3
  rcases le_total 0 (1/10-(9/10)*t^2) with h | h
  · rw [max_eq_right h]; nlinarith [sq_nonneg t]
  · rw [max_eq_left h]; linarith

theorem integral_quadratic_time3 (A B a b : ℝ) :
    (∫ t in a..b, A*t^2+B) = A*((b^3-a^3)/3)+B*(b-a) := by
  rw [intervalIntegral.integral_add
    ((show Continuous (fun t : ℝ => A*t^2) by fun_prop).intervalIntegrable (μ := volume) a b)
    (continuous_const.intervalIntegrable (μ := volume) a b), intervalIntegral.integral_const_mul,
    integral_pow, intervalIntegral.integral_const]
  norm_num
  ring

theorem integral_time_shape_envelope3 :
    (∫ t in (-1 : ℝ)..1, timeShapeEnvelope3 t) = 5/9 := by
  have hl : (∫ t in (-1 : ℝ)..(-1/3), timeShapeEnvelope3 t) =
      ∫ t in (-1 : ℝ)..(-1/3), t^2 + (-1/10) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (-1 : ℝ) (-1/3) := by
      rw [uIcc_of_le (by norm_num)] at ht
      exact ht
    exact time_shape_envelope_large3 (by linarith [neg_le_abs t, ht'.2])
  have hm : (∫ t in (-1/3 : ℝ)..(1/3), timeShapeEnvelope3 t) =
      ∫ t in (-1/3 : ℝ)..(1/3), -(4/5)*t^2+1/10 := by
    apply intervalIntegral.integral_congr
    intro t ht
    apply time_shape_envelope_small3
    apply abs_le.mpr
    rw [uIcc_of_le (by norm_num)] at ht
    constructor <;> linarith [ht.1,ht.2]
  have hr : (∫ t in (1/3 : ℝ)..1, timeShapeEnvelope3 t) =
      ∫ t in (1/3 : ℝ)..1, t^2+(-1/10) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (1/3 : ℝ) 1 := by
      rw [uIcc_of_le (by norm_num)] at ht
      exact ht
    exact time_shape_envelope_large3 (ht'.1.trans (le_abs_self t))
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (continuous_time_shape_envelope3.intervalIntegrable (μ := volume) (-1) (-1/3))
    (continuous_time_shape_envelope3.intervalIntegrable (μ := volume) (-1/3) 1),
    ← intervalIntegral.integral_add_adjacent_intervals
      (continuous_time_shape_envelope3.intervalIntegrable (μ := volume) (-1/3) (1/3))
      (continuous_time_shape_envelope3.intervalIntegrable (μ := volume) (1/3) 1), hl, hm, hr]
  simp_rw [show (fun t : ℝ => t^2+(-1/10)) = (fun t => 1*t^2+(-1/10)) by
    funext t; ring]
  rw [integral_quadratic_time3, integral_quadratic_time3, integral_quadratic_time3]
  norm_num

def timeShapePrimitive3 (t : ℝ) : ℝ := ∫ u in (-1 : ℝ)..t, timeShapeEnvelope3 u

theorem time_shape_primitive_hasDeriv3 (t : ℝ) :
    HasDerivAt timeShapePrimitive3 (timeShapeEnvelope3 t) t :=
  intervalIntegral.integral_hasDerivAt_right
    (continuous_time_shape_envelope3.intervalIntegrable (μ := volume) (-1) t)
    continuous_time_shape_envelope3.aestronglyMeasurable.stronglyMeasurableAtFilter
    continuous_time_shape_envelope3.continuousAt

theorem time_shape_primitive_lipschitz3 :
    LipschitzOnWith 1 timeShapePrimitive3 (Icc (-1 : ℝ) 1) := by
  apply (convex_Icc (-1 : ℝ) 1).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun t _ => (time_shape_primitive_hasDeriv3 t).hasDerivWithinAt)
  intro t ht
  change ‖timeShapeEnvelope3 t‖ ≤ (1 : ℝ)
  rw [Real.norm_eq_abs, abs_of_nonneg (time_shape_envelope_nonneg3 t)]
  exact time_shape_envelope_le_one3 (abs_le.mpr ht)

theorem FutureCurve3.time_primitive_AC {p q : LorentzPoint3} (c : FutureCurve3 p q) :
    AbsolutelyContinuousOnInterval (timeShapePrimitive3 ∘ c.coord 0) 0 1 := by
  apply ac_comp_lipschitz3 (c.coordAC 0) time_shape_primitive_lipschitz3
  intro t ht
  have hm : t ∈ Icc (0 : ℝ) 1 := by
    simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
  exact abs_le.mp (closed_lorentz_diamond_bounds3 (c.inDiamond t hm)).1

theorem FutureCurve3.time_primitive_deriv {p q : LorentzPoint3} (c : FutureCurve3 p q) :
    deriv (timeShapePrimitive3 ∘ c.coord 0) =ᵐ[curveMeasure]
      (fun t => timeShapeEnvelope3 (c.coord 0 t) * deriv (c.coord 0) t) := by
  filter_upwards [c.coord_hasDerivAt 0] with t ht
  exact ((time_shape_primitive_hasDeriv3 (c.coord 0 t)).comp t ht).deriv

theorem FutureCurve3.integrable_time_envelope {p q : LorentzPoint3} (c : FutureCurve3 p q) :
    Integrable (fun t => timeShapeEnvelope3 (c.coord 0 t) * deriv (c.coord 0) t)
      curveMeasure := by
  have h : Integrable (deriv (timeShapePrimitive3 ∘ c.coord 0)) curveMeasure :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
      c.time_primitive_AC.intervalIntegrable_deriv
  exact h.congr c.time_primitive_deriv

/-- Actual AC substitution along the time coordinate, without reparametrizing the curve. -/
theorem FutureCurve3.integral_time_envelope {p q : LorentzPoint3} (c : FutureCurve3 p q) :
    (∫ t, timeShapeEnvelope3 (c.coord 0 t) * deriv (c.coord 0) t ∂curveMeasure) =
      ∫ t in p 0..q 0, timeShapeEnvelope3 t := by
  rw [← integral_congr_ae c.time_primitive_deriv]
  change (∫ t in Icc (0 : ℝ) 1, deriv (timeShapePrimitive3 ∘ c.coord 0) t) = _
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num),
    c.time_primitive_AC.integral_deriv_eq_sub]
  simp only [Function.comp_apply, c.finish, c.start, timeShapePrimitive3]
  have h := intervalIntegral.integral_add_adjacent_intervals
    (continuous_time_shape_envelope3.intervalIntegrable (μ := volume) (-1) (p 0))
    (continuous_time_shape_envelope3.intervalIntegrable (μ := volume) (p 0) (q 0))
  linarith

theorem FutureCurve3.integral_time_envelope_le {p q : LorentzPoint3} (c : FutureCurve3 p q) :
    (∫ t, timeShapeEnvelope3 (c.coord 0 t) * deriv (c.coord 0) t ∂curveMeasure) ≤ 5/9 := by
  have hp := (closed_lorentz_diamond_bounds3 (c.inDiamond 0 (by norm_num))).1
  have hq := (closed_lorentz_diamond_bounds3 (c.inDiamond 1 (by norm_num))).1
  change |c.coord 0 0| ≤ 1 at hp
  change |c.coord 0 1| ≤ 1 at hq
  rw [c.start] at hp
  rw [c.finish] at hq
  rw [c.integral_time_envelope, ← integral_time_shape_envelope3]
  exact intervalIntegral.integral_mono_interval (abs_le.mp hp).1
    (by linarith [c.endpoint_time_nonneg]) (abs_le.mp hq).2
    (Filter.Eventually.of_forall time_shape_envelope_nonneg3)
    (continuous_time_shape_envelope3.intervalIntegrable (μ := volume) (-1) 1)

#print axioms abs_time_shape_le_envelope3
#print axioms integral_time_shape_envelope3
#print axioms FutureCurve3.time_primitive_AC
#print axioms FutureCurve3.integral_time_envelope
#print axioms FutureCurve3.integral_time_envelope_le
end
end QuantyraNullCone
