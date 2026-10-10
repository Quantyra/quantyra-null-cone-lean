import QuantyraNullCone.LorentzCurveControl

namespace QuantyraNullCone

open MeasureTheory Set

noncomputable section

def endpointResidual3 (p q p' q' : LorentzPoint3) (k : ℝ) : LorentzPoint3 :=
  (q' - p') - k • (q - p)

def FutureCurve3.adjustCoord {p q : LorentzPoint3} (c : FutureCurve3 p q)
    (p' q' : LorentzPoint3) (k : ℝ) (i : Fin 3) (t : ℝ) : ℝ :=
  p' i + k * (c.coord i t - p i) + c.timeFraction t * endpointResidual3 p q p' q' k i

theorem ac_const3 (a : ℝ) : AbsolutelyContinuousOnInterval (fun _ : ℝ => a) 0 1 := by
  apply ContDiffOn.absolutelyContinuousOnInterval
  fun_prop

theorem FutureCurve3.coord_hasDerivAt {p q : LorentzPoint3} (c : FutureCurve3 p q)
    (i : Fin 3) : ∀ᵐ t ∂curveMeasure, HasDerivAt (c.coord i) (deriv (c.coord i) t) t := by
  have h := ae_restrict_of_ae (c.coordAC i).ae_differentiableAt (s := Icc (0 : ℝ) 1)
  filter_upwards [h, self_mem_ae_restrict measurableSet_Icc] with t ht hmem
  exact (ht (by simpa using hmem)).hasDerivAt

theorem FutureCurve3.timeFraction_AC {p q : LorentzPoint3} (c : FutureCurve3 p q) :
    AbsolutelyContinuousOnInterval c.timeFraction 0 1 := by
  change AbsolutelyContinuousOnInterval (fun t => (c.coord 0 t - p 0) / (q 0 - p 0)) 0 1
  simpa only [div_eq_mul_inv, Pi.sub_apply, mul_comm] using
    ((c.coordAC 0).sub (ac_const3 (p 0))).const_mul (q 0 - p 0)⁻¹

theorem FutureCurve3.adjustCoord_AC {p q : LorentzPoint3} (c : FutureCurve3 p q)
    (p' q' : LorentzPoint3) (k : ℝ) (i : Fin 3) :
    AbsolutelyContinuousOnInterval (c.adjustCoord p' q' k i) 0 1 := by
  simpa only [FutureCurve3.adjustCoord, Pi.add_apply, Pi.sub_apply, mul_comm] using
    ((ac_const3 (p' i)).add (((c.coordAC i).sub (ac_const3 (p i))).const_mul k)).add
      (c.timeFraction_AC.const_mul (endpointResidual3 p q p' q' k i))

theorem FutureCurve3.adjustCoord_deriv {p q : LorentzPoint3} (c : FutureCurve3 p q)
    (p' q' : LorentzPoint3) (k : ℝ) (i : Fin 3) :
    ∀ᵐ t ∂curveMeasure, deriv (c.adjustCoord p' q' k i) t =
      k * deriv (c.coord i) t + (deriv (c.coord 0) t / (q 0 - p 0)) *
        endpointResidual3 p q p' q' k i := by
  filter_upwards [c.coord_hasDerivAt i, c.coord_hasDerivAt 0] with t hi h0
  exact (((hi.sub_const (p i)).const_mul k).const_add (p' i) |>.add
    (((h0.sub_const (p 0)).div_const (q 0 - p 0)).mul_const
      (endpointResidual3 p q p' q' k i))).deriv

theorem FutureCurve3.adjust_start {p q : LorentzPoint3} (c : FutureCurve3 p q)
    (p' q' : LorentzPoint3) (k : ℝ) (i : Fin 3) : c.adjustCoord p' q' k i 0 = p' i := by
  simp [FutureCurve3.adjustCoord, FutureCurve3.timeFraction, c.start]

theorem FutureCurve3.adjust_finish {p q : LorentzPoint3} (c : FutureCurve3 p q)
    (hpq : chronological3 p q) (p' q' : LorentzPoint3) (k : ℝ) (i : Fin 3) :
    c.adjustCoord p' q' k i 1 = q' i := by
  have hT : q 0 - p 0 ≠ 0 := ne_of_gt ((spatial_radius_nonneg3 _).trans_lt hpq)
  simp only [FutureCurve3.adjustCoord, FutureCurve3.timeFraction, c.finish, div_self hT,
    one_mul, endpointResidual3, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  ring

theorem FutureCurve3.adjust_velocity {p q : LorentzPoint3} (c : FutureCurve3 p q)
    (p' q' : LorentzPoint3) (k : ℝ) :
    ∀ᵐ t ∂curveMeasure, acVelocity3 (c.adjustCoord p' q' k) t = k • c.velocity t +
      (deriv (c.coord 0) t / (q 0 - p 0)) • endpointResidual3 p q p' q' k := by
  have h : ∀ᵐ t ∂curveMeasure, ∀ i, deriv (c.adjustCoord p' q' k i) t =
      k * deriv (c.coord i) t + (deriv (c.coord 0) t / (q 0 - p 0)) *
        endpointResidual3 p q p' q' k i := ae_all_iff.mpr (c.adjustCoord_deriv p' q' k)
  filter_upwards [h] with t ht
  ext i
  exact ht i

theorem FutureCurve3.adjust_future {p q : LorentzPoint3} (c : FutureCurve3 p q)
    (hpq : chronological3 p q) (p' q' : LorentzPoint3) {k : ℝ} (hk : 0 ≤ k)
    (he : spatialRadius3 (endpointResidual3 p q p' q' k) ≤ endpointResidual3 p q p' q' k 0) :
    ∀ᵐ t ∂curveMeasure, spatialRadius3 (acVelocity3 (c.adjustCoord p' q' k) t) ≤
      deriv (c.adjustCoord p' q' k 0) t := by
  have hT : 0 ≤ q 0 - p 0 := ((spatial_radius_nonneg3 _).trans_lt hpq).le
  filter_upwards [c.adjust_velocity p' q' k, c.future] with t hv ht
  change spatialRadius3 (acVelocity3 (c.adjustCoord p' q' k) t) ≤
    acVelocity3 (c.adjustCoord p' q' k) t 0
  rw [hv]
  exact future_cone_add3 (future_cone_smul3 ht hk)
    (future_cone_smul3 he (div_nonneg ((spatial_radius_nonneg3 _).trans ht) hT))

/-- Direct endpoint adjustment in the original AC class, with a causal residual. -/
def FutureCurve3.adjust {p q : LorentzPoint3} (c : FutureCurve3 p q)
    (hpq : chronological3 p q) {p' q' : LorentzPoint3}
    (hp' : p' ∈ closedLorentzDiamond3) (hq' : q' ∈ closedLorentzDiamond3)
    {k : ℝ} (hk : 0 ≤ k)
    (he : spatialRadius3 (endpointResidual3 p q p' q' k) ≤ endpointResidual3 p q p' q' k 0) :
    FutureCurve3 p' q' where
  coord := c.adjustCoord p' q' k
  coordAC := c.adjustCoord_AC p' q' k
  start := c.adjust_start p' q' k
  finish := c.adjust_finish hpq p' q' k
  future := c.adjust_future hpq p' q' hk he
  inDiamond t ht := by
    have h0 : acPoint3 (c.adjustCoord p' q' k) 0 = p' := by
      ext i
      exact c.adjust_start p' q' k i
    have h1 : acPoint3 (c.adjustCoord p' q' k) 1 = q' := by
      ext i
      exact c.adjust_finish hpq p' q' k i
    apply causal_diamond_subset_closed3 hp' hq'
    constructor
    · have h := ac_causal_increment3 (c.adjustCoord_AC p' q' k)
        (c.adjust_future hpq p' q' hk he) (by constructor <;> norm_num) ht ht.1
      rw [h0] at h
      exact h
    · have h := ac_causal_increment3 (c.adjustCoord_AC p' q' k)
        (c.adjust_future hpq p' q' hk he) ht (by constructor <;> norm_num) ht.2
      rw [h1] at h
      exact h

theorem FutureCurve3.adjust_point {p q : LorentzPoint3} (c : FutureCurve3 p q)
    (hpq : chronological3 p q) {p' q' : LorentzPoint3}
    (hp' : p' ∈ closedLorentzDiamond3) (hq' : q' ∈ closedLorentzDiamond3)
    {k : ℝ} (hk : 0 ≤ k)
    (he : spatialRadius3 (endpointResidual3 p q p' q' k) ≤ endpointResidual3 p q p' q' k 0)
    (t : ℝ) : (c.adjust hpq hp' hq' hk he).point t =
      p' + k • (c.point t - p) + c.timeFraction t • endpointResidual3 p q p' q' k := by
  ext i
  rfl

theorem FutureCurve3.adjust_speed_lower {p q : LorentzPoint3} (c : FutureCurve3 p q)
    (hpq : chronological3 p q) {p' q' : LorentzPoint3}
    (hp' : p' ∈ closedLorentzDiamond3) (hq' : q' ∈ closedLorentzDiamond3)
    {k : ℝ} (hk : 0 ≤ k)
    (he : spatialRadius3 (endpointResidual3 p q p' q' k) ≤ endpointResidual3 p q p' q' k 0) :
    ∀ᵐ t ∂curveMeasure, k * c.flatSpeed t ≤ (c.adjust hpq hp' hq' hk he).flatSpeed t := by
  have hT : 0 ≤ q 0 - p 0 := ((spatial_radius_nonneg3 _).trans_lt hpq).le
  filter_upwards [c.adjust_velocity p' q' k, c.future] with t hv ht
  change k * flatProperSpeed3 (c.velocity t) ≤
    flatProperSpeed3 (acVelocity3 (c.adjustCoord p' q' k) t)
  rw [hv]
  have h := flat_proper_speed_add_ge3 (future_cone_smul3 ht hk)
    (future_cone_smul3 he (div_nonneg ((spatial_radius_nonneg3 _).trans ht) hT))
  rw [flat_proper_speed_smul3 k, abs_of_nonneg hk] at h
  exact (le_add_of_nonneg_right (flat_proper_speed_nonneg3 _)).trans h

theorem endpoint_residual_norm3 {p q p' q' : LorentzPoint3} {k : ℝ}
    (hp : p ∈ closedLorentzDiamond3) (hq : q ∈ closedLorentzDiamond3) (hk : k ≤ 1) :
    ‖endpointResidual3 p q p' q' k‖ ≤ ‖(q' - p') - (q - p)‖ + 2 * (1 - k) := by
  have he : endpointResidual3 p q p' q' k =
      ((q' - p') - (q - p)) + (1 - k) • (q - p) := by
    ext i
    change (q' i - p' i) - k * (q i - p i) =
      ((q' i - p' i) - (q i - p i)) + (1 - k) * (q i - p i)
    ring
  rw [he]
  calc
    _ ≤ ‖(q' - p') - (q - p)‖ + ‖(1 - k) • (q - p)‖ := norm_add_le _ _
    _ = ‖(q' - p') - (q - p)‖ + (1 - k) * ‖q - p‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hk)]
    _ ≤ _ := by nlinarith [closed_diamond_dist_le_two3 hq hp]

theorem FutureCurve3.adjust_point_distance {p q : LorentzPoint3} (c : FutureCurve3 p q)
    (hpq : chronological3 p q) {p' q' : LorentzPoint3}
    (hp' : p' ∈ closedLorentzDiamond3) (hq' : q' ∈ closedLorentzDiamond3)
    {k : ℝ} (hk : 0 ≤ k) (hk' : k ≤ 1)
    (he : spatialRadius3 (endpointResidual3 p q p' q' k) ≤ endpointResidual3 p q p' q' k 0)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖(c.adjust hpq hp' hq' hk he).point t - c.point t‖ ≤
      ‖p' - p‖ + ‖(q' - p') - (q - p)‖ + 4 * (1 - k) := by
  have hp : p ∈ closedLorentzDiamond3 := by
    rw [← c.point_zero]
    exact c.inDiamond 0 (by constructor <;> norm_num)
  have hq : q ∈ closedLorentzDiamond3 := by
    rw [← c.point_one]
    exact c.inDiamond 1 (by constructor <;> norm_num)
  have htheta := c.timeFraction_mem hpq ht
  have hd := closed_diamond_dist_le_two3 (c.inDiamond t ht) hp
  change ‖c.point t - p‖ ≤ 2 at hd
  have hres := endpoint_residual_norm3 (p' := p') (q' := q') hp hq hk'
  rw [c.adjust_point hpq hp' hq' hk he]
  have hsub : p' + k • (c.point t - p) + c.timeFraction t • endpointResidual3 p q p' q' k - c.point t =
      (p' - p) - (1 - k) • (c.point t - p) + c.timeFraction t • endpointResidual3 p q p' q' k := by
    ext i
    change p' i + k * (c.point t i - p i) + c.timeFraction t * endpointResidual3 p q p' q' k i - c.point t i =
      (p' i - p i) - (1 - k) * (c.point t i - p i) + c.timeFraction t * endpointResidual3 p q p' q' k i
    ring
  rw [hsub]
  calc
    _ ≤ ‖(p' - p) - (1 - k) • (c.point t - p)‖ +
        ‖c.timeFraction t • endpointResidual3 p q p' q' k‖ := norm_add_le _ _
    _ ≤ (‖p' - p‖ + ‖(1 - k) • (c.point t - p)‖) +
        ‖c.timeFraction t • endpointResidual3 p q p' q' k‖ :=
      add_le_add (norm_sub_le _ _) le_rfl
    _ = (‖p' - p‖ + (1 - k) * ‖c.point t - p‖) +
        c.timeFraction t * ‖endpointResidual3 p q p' q' k‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr hk'), abs_of_nonneg htheta.1]
    _ ≤ _ := by
      have h1 := mul_le_mul_of_nonneg_left hd (sub_nonneg.mpr hk')
      have h2 := mul_le_mul_of_nonneg_right htheta.2 (norm_nonneg (endpointResidual3 p q p' q' k))
      nlinarith

theorem FutureCurve3.adjust_weightedLength_lower {p q : LorentzPoint3} (c : FutureCurve3 p q)
    (hpq : chronological3 p q) {p' q' : LorentzPoint3}
    (hp' : p' ∈ closedLorentzDiamond3) (hq' : q' ∈ closedLorentzDiamond3)
    {k : ℝ} (hk : 0 ≤ k) (hk' : k ≤ 1)
    (he : spatialRadius3 (endpointResidual3 p q p' q' k) ≤ endpointResidual3 p q p' q' k 0)
    {w : LorentzPoint3 → ℝ} {lo hi delta : ℝ} (hw : InTimeWeightClass3 w lo hi)
    (hdelta : 0 ≤ delta)
    (hclose : ∀ t ∈ Icc (0 : ℝ) 1,
      |w ((c.adjust hpq hp' hq' hk he).point t) - w (c.point t)| ≤ delta) :
    k * c.weightedLength w - 2 * delta ≤ (c.adjust hpq hp' hq' hk he).weightedLength w := by
  let d := c.adjust hpq hp' hq' hk he
  have hpoint : ∀ᵐ t ∂curveMeasure,
      k * (w (c.point t) * c.flatSpeed t) - delta * c.flatSpeed t ≤ w (d.point t) * d.flatSpeed t := by
    filter_upwards [c.adjust_speed_lower hpq hp' hq' hk he,
      self_mem_ae_restrict measurableSet_Icc] with t hv ht
    have hc := (abs_le.mp (hclose t ht)).1
    have hw0 : 0 ≤ w (d.point t) := hw.lower_pos.le.trans (hw.bounds _ (d.inDiamond t ht)).1
    have hs : 0 ≤ c.flatSpeed t := flat_proper_speed_nonneg3 (c.velocity t)
    change k * c.flatSpeed t ≤ d.flatSpeed t at hv
    have h1 := mul_le_mul_of_nonneg_left hv hw0
    have h2 := mul_le_mul_of_nonneg_left (show w (c.point t) - delta ≤ w (d.point t) by linarith) hk
    have h3 := mul_le_mul_of_nonneg_right h2 hs
    have h4 := mul_le_mul_of_nonneg_right hk' hdelta
    have h5 := mul_le_mul_of_nonneg_right h4 hs
    nlinarith
  have hint := integral_mono_ae
    (((c.integrable_weightedSpeed hw).const_mul k).sub (c.integrable_flatSpeed.const_mul delta))
    (d.integrable_weightedSpeed hw) hpoint
  simp only [Pi.sub_apply] at hint
  rw [integral_sub ((c.integrable_weightedSpeed hw).const_mul k)
    (c.integrable_flatSpeed.const_mul delta), integral_const_mul, integral_const_mul] at hint
  change k * c.weightedLength w - delta * c.flatLength ≤ d.weightedLength w at hint
  have hbound := mul_le_mul_of_nonneg_left c.flatLength_le_two hdelta
  linarith

#print axioms ac_const3
#print axioms FutureCurve3.coord_hasDerivAt
#print axioms FutureCurve3.timeFraction_AC
#print axioms FutureCurve3.adjustCoord_AC
#print axioms FutureCurve3.adjustCoord_deriv
#print axioms FutureCurve3.adjust_start
#print axioms FutureCurve3.adjust_finish
#print axioms FutureCurve3.adjust_velocity
#print axioms FutureCurve3.adjust_future
#print axioms FutureCurve3.adjust_point
#print axioms FutureCurve3.adjust_speed_lower
#print axioms endpoint_residual_norm3
#print axioms FutureCurve3.adjust_point_distance
#print axioms FutureCurve3.adjust_weightedLength_lower

end
end QuantyraNullCone
