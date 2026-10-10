import QuantyraNullCone.LorentzConcatenation

namespace QuantyraNullCone

open MeasureTheory Set

noncomputable section

def acPoint3 (f : Fin 3 → ℝ → ℝ) (t : ℝ) : LorentzPoint3 :=
  WithLp.toLp 2 (fun i => f i t)

def acVelocity3 (f : Fin 3 → ℝ → ℝ) (t : ℝ) : LorentzPoint3 :=
  WithLp.toLp 2 (fun i => deriv (f i) t)

def spatialLift3 (v : LorentzPoint3) : LorentzPoint3 := lorentzPoint3 0 (v 1) (v 2)

theorem spatial_lift_norm3 (v : LorentzPoint3) : ‖spatialLift3 v‖ = spatialRadius3 v := by
  have h := lorentz_norm_sq3 (spatialLift3 v)
  change ‖spatialLift3 v‖ ^ 2 = 0 ^ 2 + spatialSquared3 v at h
  nlinarith [norm_nonneg (spatialLift3 v), spatial_radius_nonneg3 v, spatial_radius_sq3 v]

theorem spatial_radius_add_le3 (u v : LorentzPoint3) :
    spatialRadius3 (u + v) ≤ spatialRadius3 u + spatialRadius3 v := by
  simpa using spatial_radius_triangle3 0 v (u + v)

theorem future_cone_add3 {u v : LorentzPoint3}
    (hu : spatialRadius3 u ≤ u 0) (hv : spatialRadius3 v ≤ v 0) :
    spatialRadius3 (u + v) ≤ (u + v) 0 :=
  (spatial_radius_add_le3 u v).trans (add_le_add hu hv)

theorem future_cone_smul3 {u : LorentzPoint3} (hu : spatialRadius3 u ≤ u 0)
    {s : ℝ} (hs : 0 ≤ s) : spatialRadius3 (s • u) ≤ (s • u) 0 := by
  rw [spatial_radius_smul3, abs_of_nonneg hs]
  exact mul_le_mul_of_nonneg_left hu hs

/-- Future-cone superadditivity follows from the Euclidean norm of the proper-speed lift. -/
theorem flat_proper_speed_add_ge3 {u v : LorentzPoint3}
    (hu : spatialRadius3 u ≤ u 0) (hv : spatialRadius3 v ≤ v 0) :
    flatProperSpeed3 u + flatProperSpeed3 v ≤ flatProperSpeed3 (u + v) := by
  let a := lorentzPoint3 (flatProperSpeed3 u) (u 1) (u 2)
  let b := lorentzPoint3 (flatProperSpeed3 v) (v 1) (v 2)
  have hn : ‖a + b‖ ≤ u 0 + v 0 := by
    calc
      ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le _ _
      _ = u 0 + v 0 := by rw [proper_speed_lift_norm3 hu, proper_speed_lift_norm3 hv]
  have ht : 0 ≤ u 0 + v 0 :=
    add_nonneg ((spatial_radius_nonneg3 u).trans hu) ((spatial_radius_nonneg3 v).trans hv)
  have hs := (sq_le_sq₀ (norm_nonneg (a + b)) ht).mpr hn
  have he := lorentz_norm_sq3 (a + b)
  change ‖a + b‖ ^ 2 = (flatProperSpeed3 u + flatProperSpeed3 v) ^ 2 +
    spatialSquared3 (u + v) at he
  apply Real.le_sqrt_of_sq_le
  change (flatProperSpeed3 u + flatProperSpeed3 v) ^ 2 ≤
    (u 0 + v 0) ^ 2 - spatialSquared3 (u + v)
  linarith

theorem ac_subinterval_subset3 {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (hb : b ∈ Icc (0 : ℝ) 1) (hab : a ≤ b) : uIcc a b ⊆ uIcc (0 : ℝ) 1 := by
  rw [uIcc_of_le hab, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact Icc_subset_Icc ha.1 hb.2

theorem ac_deriv_integrable_subinterval3 {f : Fin 3 → ℝ → ℝ}
    (hf : ∀ i, AbsolutelyContinuousOnInterval (f i) 0 1)
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) (hab : a ≤ b)
    (i : Fin 3) : Integrable (deriv (f i)) (volume.restrict (Icc a b)) :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp
    ((hf i).mono (ac_subinterval_subset3 ha hb hab)).intervalIntegrable_deriv

theorem ac_integral_deriv_subinterval3 {f : Fin 3 → ℝ → ℝ}
    (hf : ∀ i, AbsolutelyContinuousOnInterval (f i) 0 1)
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) (hab : a ≤ b)
    (i : Fin 3) : (∫ t in Icc a b, deriv (f i) t) = f i b - f i a := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  exact ((hf i).mono (ac_subinterval_subset3 ha hb hab)).integral_deriv_eq_sub

/-- An AC derivative in the future cone gives causal increments on every subinterval.
No containment or endpoint-causality hypothesis is used. -/
theorem ac_causal_increment3 {f : Fin 3 → ℝ → ℝ}
    (hf : ∀ i, AbsolutelyContinuousOnInterval (f i) 0 1)
    (hv : ∀ᵐ t ∂curveMeasure, spatialRadius3 (acVelocity3 f t) ≤ deriv (f 0) t)
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) (hab : a ≤ b) :
    causal3 (acPoint3 f a) (acPoint3 f b) := by
  have hi := ac_deriv_integrable_subinterval3 hf ha hb hab
  have hvec : Integrable (fun t => spatialLift3 (acVelocity3 f t))
      (volume.restrict (Icc a b)) := by
    apply Integrable.of_eval_piLp
    intro i
    fin_cases i
    · exact integrable_const 0
    · exact hi 1
    · exact hi 2
  have hint : (∫ t in Icc a b, spatialLift3 (acVelocity3 f t)) =
      spatialLift3 (acPoint3 f b - acPoint3 f a) := by
    ext i
    rw [eval_integral_piLp (fun j => hvec.eval_piLp j)]
    fin_cases i
    · simp [spatialLift3, lorentzPoint3]
    · exact ac_integral_deriv_subinterval3 hf ha hb hab 1
    · exact ac_integral_deriv_subinterval3 hf ha hb hab 2
  have hv' := ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc ha.1 hb.2) hv
  have hnorm : ∀ᵐ t ∂volume.restrict (Icc a b),
      ‖spatialLift3 (acVelocity3 f t)‖ ≤ deriv (f 0) t := by
    filter_upwards [hv'] with t ht
    rwa [spatial_lift_norm3]
  have h := norm_integral_le_of_norm_le (hi 0) hnorm
  rw [hint, spatial_lift_norm3, ac_integral_deriv_subinterval3 hf ha hb hab 0] at h
  exact h

theorem FutureCurve3.causal_mono {p q : LorentzPoint3} (c : FutureCurve3 p q)
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) (hab : a ≤ b) :
    causal3 (c.point a) (c.point b) := ac_causal_increment3 c.coordAC c.future ha hb hab

theorem FutureCurve3.time_position_bounds {p q : LorentzPoint3} (c : FutureCurve3 p q)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : p 0 ≤ c.coord 0 t ∧ c.coord 0 t ≤ q 0 := by
  have hl := c.causal_mono (by constructor <;> norm_num) ht ht.1
  have hr := c.causal_mono ht (by constructor <;> norm_num) ht.2
  have hln := (spatial_radius_nonneg3 _).trans hl
  have hrn := (spatial_radius_nonneg3 _).trans hr
  change 0 ≤ c.coord 0 t - c.coord 0 0 at hln
  change 0 ≤ c.coord 0 1 - c.coord 0 t at hrn
  rw [c.start] at hln
  rw [c.finish] at hrn
  constructor <;> linarith

def FutureCurve3.timeFraction {p q : LorentzPoint3} (c : FutureCurve3 p q) (t : ℝ) : ℝ :=
  (c.coord 0 t - p 0) / (q 0 - p 0)

theorem FutureCurve3.timeFraction_mem {p q : LorentzPoint3} (c : FutureCurve3 p q)
    (hpq : chronological3 p q) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    c.timeFraction t ∈ Icc (0 : ℝ) 1 := by
  have hT : 0 < q 0 - p 0 := (spatial_radius_nonneg3 _).trans_lt hpq
  have h := c.time_position_bounds ht
  constructor
  · exact div_nonneg (sub_nonneg.mpr h.1) hT.le
  · exact (div_le_one hT).mpr (sub_le_sub_right h.2 _)

theorem closed_diamond_norm_le_one3 {p : LorentzPoint3} (hp : p ∈ closedLorentzDiamond3) :
    ‖p‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using
      closed_lorentz_diamond_subset_ball3 hp

theorem closed_diamond_dist_le_two3 {p q : LorentzPoint3}
    (hp : p ∈ closedLorentzDiamond3) (hq : q ∈ closedLorentzDiamond3) : ‖p - q‖ ≤ 2 := by
  have h := norm_sub_le p q
  linarith [closed_diamond_norm_le_one3 hp, closed_diamond_norm_le_one3 hq]

theorem FutureCurve3.point_zero {p q : LorentzPoint3} (c : FutureCurve3 p q) :
    c.point 0 = p := by ext i; exact c.start i

theorem FutureCurve3.point_one {p q : LorentzPoint3} (c : FutureCurve3 p q) :
    c.point 1 = q := by ext i; exact c.finish i

#print axioms spatial_lift_norm3
#print axioms spatial_radius_add_le3
#print axioms future_cone_add3
#print axioms future_cone_smul3
#print axioms flat_proper_speed_add_ge3
#print axioms ac_subinterval_subset3
#print axioms ac_deriv_integrable_subinterval3
#print axioms ac_integral_deriv_subinterval3
#print axioms ac_causal_increment3
#print axioms FutureCurve3.causal_mono
#print axioms FutureCurve3.time_position_bounds
#print axioms FutureCurve3.timeFraction_mem
#print axioms closed_diamond_norm_le_one3
#print axioms closed_diamond_dist_le_two3
#print axioms FutureCurve3.point_zero
#print axioms FutureCurve3.point_one

end
end QuantyraNullCone
