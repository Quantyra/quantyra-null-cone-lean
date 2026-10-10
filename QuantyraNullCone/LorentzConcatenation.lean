import QuantyraNullCone.LorentzWeightedTime
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

namespace QuantyraNullCone

open MeasureTheory Set

noncomputable section

/-- Run two scalar velocities on the two half intervals, at twice their original speed. -/
def joinScalar3 (f g : ℝ → ℝ) (t : ℝ) : ℝ :=
  if t ≤ 1 / 2 then 2 * f (2 * t) else 2 * g (2 * t - 1)

theorem join_integrable_left3 {f g : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 1) :
    IntervalIntegrable (joinScalar3 f g) volume 0 (1 / 2) := by
  have h : IntervalIntegrable (fun t => 2 * f (2 * t)) volume 0 (1 / 2) := by
    simpa using (hf.comp_mul_left (c := 2)).const_mul 2
  apply h.congr
  intro t ht
  have ht' : t ∈ Ioc (0 : ℝ) (1 / 2) := by
    rwa [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at ht
  simp only [joinScalar3, if_pos ht'.2]

theorem join_integrable_right3 {f g : ℝ → ℝ} (hg : IntervalIntegrable g volume 0 1) :
    IntervalIntegrable (joinScalar3 f g) volume (1 / 2) 1 := by
  have h : IntervalIntegrable (fun t => 2 * g (2 * t - 1)) volume (1 / 2) 1 := by
    simpa using ((hg.comp_sub_right 1).comp_mul_left (c := 2)).const_mul 2
  apply h.congr
  intro t ht
  have ht' : t ∈ Ioc (1 / 2 : ℝ) 1 := by
    rwa [uIoc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at ht
  simp only [joinScalar3, if_neg (not_le.mpr ht'.1)]

theorem join_integrable3 {f g : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 1)
    (hg : IntervalIntegrable g volume 0 1) : IntervalIntegrable (joinScalar3 f g) volume 0 1 :=
  (join_integrable_left3 hf).trans (join_integrable_right3 hg)

theorem join_integral_left3 (f g : ℝ → ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / 2)) :
    (∫ s in 0..t, joinScalar3 f g s) = ∫ s in 0..(2 * t), f s := by
  have heq : (∫ s in 0..t, joinScalar3 f g s) = ∫ s in 0..t, 2 * f (2 * s) := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) t := by simpa [uIcc_of_le ht.1] using hs
    simp only [joinScalar3, if_pos (hs'.2.trans ht.2)]
  rw [heq, intervalIntegral.integral_const_mul]
  simpa only [smul_eq_mul, mul_zero] using
    intervalIntegral.smul_integral_comp_mul_left f 2 (a := 0) (b := t)

theorem join_integral_right3 (f g : ℝ → ℝ) {t : ℝ} (ht : t ∈ Icc (1 / 2 : ℝ) 1) :
    (∫ s in (1 / 2)..t, joinScalar3 f g s) = ∫ s in 0..(2 * t - 1), g s := by
  have heq : (∫ s in (1 / 2)..t, joinScalar3 f g s) =
      ∫ s in (1 / 2)..t, 2 * g (2 * s - 1) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with s hs
    have hs' : s ∈ Ioc (1 / 2 : ℝ) t := by rwa [uIoc_of_le ht.1] at hs
    simp only [joinScalar3, if_neg (not_le.mpr hs'.1)]
  rw [heq, intervalIntegral.integral_const_mul]
  have h := intervalIntegral.smul_integral_comp_mul_sub g 2 1 (a := (1 / 2)) (b := t)
  simp only [smul_eq_mul, show (2 : ℝ) * (1 / 2) - 1 = 0 by norm_num] at h
  exact h

theorem join_integral3 {f g : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 1)
    (hg : IntervalIntegrable g volume 0 1) :
    (∫ s in (0 : ℝ)..1, joinScalar3 f g s) = (∫ s in (0 : ℝ)..1, f s) + ∫ s in (0 : ℝ)..1, g s := by
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (join_integrable_left3 hf) (join_integrable_right3 hg)]
  rw [join_integral_left3 f g (by constructor <;> norm_num),
    join_integral_right3 f g (by constructor <;> norm_num)]
  norm_num

theorem join_primitive_left3 {f g : ℝ → ℝ} (hf : AbsolutelyContinuousOnInterval f 0 1)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / 2)) :
    f 0 + (∫ s in 0..t, joinScalar3 (deriv f) (deriv g) s) = f (2 * t) := by
  rw [join_integral_left3 _ _ ht]
  have hsub : uIcc (0 : ℝ) (2 * t) ⊆ uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le (by linarith [ht.1] : (0 : ℝ) ≤ 2 * t), uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl (by linarith [ht.2])
  rw [(hf.mono hsub).integral_deriv_eq_sub]
  ring

theorem join_primitive_right3 {f g : ℝ → ℝ} (hf : AbsolutelyContinuousOnInterval f 0 1)
    (hg : AbsolutelyContinuousOnInterval g 0 1) (hfg : f 1 = g 0)
    {t : ℝ} (ht : t ∈ Icc (1 / 2 : ℝ) 1) :
    f 0 + (∫ s in 0..t, joinScalar3 (deriv f) (deriv g) s) = g (2 * t - 1) := by
  have hsub : uIcc (1 / 2 : ℝ) t ⊆ uIcc (1 / 2 : ℝ) 1 := by
    rw [uIcc_of_le ht.1, uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl ht.2
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (join_integrable_left3 hf.intervalIntegrable_deriv)
    ((join_integrable_right3 hg.intervalIntegrable_deriv).mono_set hsub)]
  rw [join_integral_left3 _ _ (by constructor <;> norm_num), join_integral_right3 _ _ ht]
  norm_num
  rw [hf.integral_deriv_eq_sub]
  have hsub' : uIcc (0 : ℝ) (2 * t - 1) ⊆ uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le (by linarith [ht.1] : (0 : ℝ) ≤ 2 * t - 1), uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl (by linarith [ht.2])
  rw [(hg.mono hsub').integral_deriv_eq_sub, hfg]
  ring

def joinedCoord3 {p q r : LorentzPoint3} (c : FutureCurve3 p q) (d : FutureCurve3 q r)
    (i : Fin 3) (t : ℝ) : ℝ :=
  p i + ∫ s in 0..t, joinScalar3 (deriv (c.coord i)) (deriv (d.coord i)) s

theorem joined_coord_AC3 {p q r : LorentzPoint3} (c : FutureCurve3 p q) (d : FutureCurve3 q r)
    (i : Fin 3) : AbsolutelyContinuousOnInterval (joinedCoord3 c d i) 0 1 := by
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => p i) 0 1 := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    fun_prop
  exact hc.add ((join_integrable3 (c.coordAC i).intervalIntegrable_deriv
    (d.coordAC i).intervalIntegrable_deriv).absolutelyContinuousOnInterval_intervalIntegral (by simp))

theorem joined_coord_left3 {p q r : LorentzPoint3} (c : FutureCurve3 p q) (d : FutureCurve3 q r)
    (i : Fin 3) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / 2)) :
    joinedCoord3 c d i t = c.coord i (2 * t) := by
  unfold joinedCoord3
  rw [← c.start i]
  exact join_primitive_left3 (c.coordAC i) ht

theorem joined_coord_right3 {p q r : LorentzPoint3} (c : FutureCurve3 p q) (d : FutureCurve3 q r)
    (i : Fin 3) {t : ℝ} (ht : t ∈ Icc (1 / 2 : ℝ) 1) :
    joinedCoord3 c d i t = d.coord i (2 * t - 1) := by
  unfold joinedCoord3
  rw [← c.start i]
  exact join_primitive_right3 (c.coordAC i) (d.coordAC i) (by rw [c.finish, d.start]) ht

theorem joined_coord_deriv3 {p q r : LorentzPoint3} (c : FutureCurve3 p q) (d : FutureCurve3 q r)
    (i : Fin 3) : ∀ᵐ t ∂curveMeasure, deriv (joinedCoord3 c d i) t =
      joinScalar3 (deriv (c.coord i)) (deriv (d.coord i)) t := by
  have h := (join_integrable3 (c.coordAC i).intervalIntegrable_deriv
    (d.coordAC i).intervalIntegrable_deriv).ae_hasDerivAt_integral
  have h' := ae_restrict_of_ae h (s := Icc (0 : ℝ) 1)
  filter_upwards [h', self_mem_ae_restrict measurableSet_Icc] with t ht hmem
  have hmem' : t ∈ uIcc (0 : ℝ) 1 := by simpa using hmem
  exact ((ht hmem' 0 (by simp)).const_add (p i)).deriv

theorem ae_left_half3 {P : ℝ → Prop} (h : ∀ᵐ t ∂curveMeasure, P t) :
    ∀ᵐ t ∂curveMeasure, t ≤ 1 / 2 → P (2 * t) := by
  have hglobal : ∀ᵐ t ∂volume, t ∈ Icc (0 : ℝ) 1 → P t :=
    (ae_restrict_iff' measurableSet_Icc).mp h
  have hq : Measure.QuasiMeasurePreserving (fun t : ℝ => 2 * t) volume volume := by
    simpa only [smul_eq_mul] using
      Measure.quasiMeasurePreserving_smul (volume : Measure ℝ) (by norm_num : (2 : ℝ) ≠ 0)
  have hc := ae_restrict_of_ae (hq.ae hglobal) (s := Icc (0 : ℝ) 1)
  filter_upwards [hc, self_mem_ae_restrict measurableSet_Icc] with t ht hmem hhalf
  exact ht ⟨by linarith [hmem.1], by linarith⟩

theorem ae_right_half3 {P : ℝ → Prop} (h : ∀ᵐ t ∂curveMeasure, P t) :
    ∀ᵐ t ∂curveMeasure, 1 / 2 < t → P (2 * t - 1) := by
  have hglobal : ∀ᵐ t ∂volume, t ∈ Icc (0 : ℝ) 1 → P t :=
    (ae_restrict_iff' measurableSet_Icc).mp h
  have hq : Measure.QuasiMeasurePreserving (fun t : ℝ => 2 * t - 1) volume volume := by
    simpa only [Function.comp_def, smul_eq_mul, sub_eq_add_neg] using
      (measurePreserving_add_right (volume : Measure ℝ) (-1)).quasiMeasurePreserving.comp
        (Measure.quasiMeasurePreserving_smul (volume : Measure ℝ) (by norm_num : (2 : ℝ) ≠ 0))
  have hc := ae_restrict_of_ae (hq.ae hglobal) (s := Icc (0 : ℝ) 1)
  filter_upwards [hc, self_mem_ae_restrict measurableSet_Icc] with t ht hmem hhalf
  exact ht ⟨by linarith, by linarith [hmem.2]⟩

theorem joined_velocity3 {p q r : LorentzPoint3} (c : FutureCurve3 p q) (d : FutureCurve3 q r) :
    ∀ᵐ t ∂curveMeasure, WithLp.toLp 2 (fun i => deriv (joinedCoord3 c d i) t) =
      if t ≤ 1 / 2 then (2 : ℝ) • c.velocity (2 * t) else (2 : ℝ) • d.velocity (2 * t - 1) := by
  have h : ∀ᵐ t ∂curveMeasure, ∀ i, deriv (joinedCoord3 c d i) t =
      joinScalar3 (deriv (c.coord i)) (deriv (d.coord i)) t :=
    ae_all_iff.mpr (joined_coord_deriv3 c d)
  filter_upwards [h] with t ht
  ext i
  by_cases hh : t ≤ 1 / 2
  · rw [if_pos hh]
    change deriv (joinedCoord3 c d i) t = 2 * deriv (c.coord i) (2 * t)
    rw [ht i, joinScalar3, if_pos hh]
  · rw [if_neg hh]
    change deriv (joinedCoord3 c d i) t = 2 * deriv (d.coord i) (2 * t - 1)
    rw [ht i, joinScalar3, if_neg hh]

theorem joined_future3 {p q r : LorentzPoint3} (c : FutureCurve3 p q) (d : FutureCurve3 q r) :
    ∀ᵐ t ∂curveMeasure,
      spatialRadius3 (WithLp.toLp 2 (fun i => deriv (joinedCoord3 c d i) t)) ≤
        deriv (joinedCoord3 c d 0) t := by
  filter_upwards [joined_velocity3 c d, joined_coord_deriv3 c d 0,
    ae_left_half3 c.future, ae_right_half3 d.future] with t hv h0 hc hd
  rw [hv, h0]
  by_cases hh : t ≤ 1 / 2
  · simp only [if_pos hh, joinScalar3, spatial_radius_smul3]
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left (hc hh) (by norm_num)
  · simp only [if_neg hh, joinScalar3, spatial_radius_smul3]
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left (hd (lt_of_not_ge hh)) (by norm_num)

/-- Concatenation constructed from an integrable piecewise velocity, in the original AC class. -/
def FutureCurve3.concat {p q r : LorentzPoint3} (c : FutureCurve3 p q) (d : FutureCurve3 q r) :
    FutureCurve3 p r where
  coord := joinedCoord3 c d
  coordAC := joined_coord_AC3 c d
  start i := by simp [joinedCoord3]
  finish i := by
    rw [joined_coord_right3 c d i (by constructor <;> norm_num)]
    norm_num
    exact d.finish i
  inDiamond t ht := by
    by_cases hh : t ≤ 1 / 2
    · have hp : WithLp.toLp 2 (fun i => joinedCoord3 c d i t) = c.point (2 * t) := by
        ext i
        exact joined_coord_left3 c d i ⟨ht.1, hh⟩
      rw [hp]
      exact c.inDiamond _ ⟨by linarith [ht.1], by linarith⟩
    · have hp : WithLp.toLp 2 (fun i => joinedCoord3 c d i t) = d.point (2 * t - 1) := by
        ext i
        exact joined_coord_right3 c d i ⟨(lt_of_not_ge hh).le, ht.2⟩
      rw [hp]
      exact d.inDiamond _ ⟨by linarith [lt_of_not_ge hh], by linarith [ht.2]⟩
  future := joined_future3 c d

theorem FutureCurve3.concat_point_left {p q r : LorentzPoint3} (c : FutureCurve3 p q)
    (d : FutureCurve3 q r) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / 2)) :
    (c.concat d).point t = c.point (2 * t) := by
  ext i
  exact joined_coord_left3 c d i ht

theorem FutureCurve3.concat_point_right {p q r : LorentzPoint3} (c : FutureCurve3 p q)
    (d : FutureCurve3 q r) {t : ℝ} (ht : t ∈ Icc (1 / 2 : ℝ) 1) :
    (c.concat d).point t = d.point (2 * t - 1) := by
  ext i
  exact joined_coord_right3 c d i ht

theorem FutureCurve3.concat_velocity {p q r : LorentzPoint3} (c : FutureCurve3 p q)
    (d : FutureCurve3 q r) : ∀ᵐ t ∂curveMeasure, (c.concat d).velocity t =
      if t ≤ 1 / 2 then (2 : ℝ) • c.velocity (2 * t) else (2 : ℝ) • d.velocity (2 * t - 1) :=
  joined_velocity3 c d

theorem flat_proper_speed_smul3 (s : ℝ) (v : LorentzPoint3) :
    flatProperSpeed3 (s • v) = |s| * flatProperSpeed3 v := by
  change Real.sqrt ((s * v 0) ^ 2 - ((s * v 1) ^ 2 + (s * v 2) ^ 2)) = _
  rw [show (s * v 0) ^ 2 - ((s * v 1) ^ 2 + (s * v 2) ^ 2) =
    s ^ 2 * (v 0 ^ 2 - spatialSquared3 v) by unfold spatialSquared3; ring]
  rw [Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq_eq_abs]
  rfl

theorem FutureCurve3.concat_weighted_integrand {p q r : LorentzPoint3} (c : FutureCurve3 p q)
    (d : FutureCurve3 q r) (w : LorentzPoint3 → ℝ) :
    (fun t => w ((c.concat d).point t) * (c.concat d).flatSpeed t) =ᵐ[curveMeasure]
      joinScalar3 (fun t => w (c.point t) * c.flatSpeed t)
        (fun t => w (d.point t) * d.flatSpeed t) := by
  filter_upwards [c.concat_velocity d, self_mem_ae_restrict measurableSet_Icc] with t hv ht
  change w ((c.concat d).point t) * flatProperSpeed3 ((c.concat d).velocity t) = _
  by_cases hh : t ≤ 1 / 2
  · rw [c.concat_point_left d ⟨ht.1, hh⟩, hv, if_pos hh, flat_proper_speed_smul3]
    simp only [joinScalar3, if_pos hh]
    norm_num
    change w (c.point (2 * t)) * (2 * c.flatSpeed (2 * t)) = 2 * (w (c.point (2 * t)) * c.flatSpeed (2 * t))
    ring
  · rw [c.concat_point_right d ⟨(lt_of_not_ge hh).le, ht.2⟩, hv, if_neg hh, flat_proper_speed_smul3]
    simp only [joinScalar3, if_neg hh]
    norm_num
    change w (d.point (2 * t - 1)) * (2 * d.flatSpeed (2 * t - 1)) =
      2 * (w (d.point (2 * t - 1)) * d.flatSpeed (2 * t - 1))
    ring

theorem curve_integral_eq_interval3 (f : ℝ → ℝ) :
    (∫ t, f t ∂curveMeasure) = ∫ t in (0 : ℝ)..1, f t := by
  change (∫ t in Icc (0 : ℝ) 1, f t) = _
  rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by norm_num)]

theorem FutureCurve3.concat_weightedLength {p q r : LorentzPoint3} (c : FutureCurve3 p q)
    (d : FutureCurve3 q r) {w : LorentzPoint3 → ℝ} {lo hi : ℝ}
    (hw : InTimeWeightClass3 w lo hi) :
    (c.concat d).weightedLength w = c.weightedLength w + d.weightedLength w := by
  have hc := (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
    (c.integrable_weightedSpeed hw)
  have hd := (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
    (d.integrable_weightedSpeed hw)
  unfold weightedLength
  rw [integral_congr_ae (c.concat_weighted_integrand d w)]
  simp only [curve_integral_eq_interval3]
  exact join_integral3 hc hd

theorem FutureCurve3.weightedLength_nonneg {p q : LorentzPoint3} (c : FutureCurve3 p q)
    {w : LorentzPoint3 → ℝ} {lo hi : ℝ} (hw : InTimeWeightClass3 w lo hi) :
    0 ≤ c.weightedLength w :=
  (mul_nonneg hw.lower_pos.le c.flatLength_nonneg).trans (c.weightedLength_bounds hw).1

/-- Causal reverse triangle, including null/zero-time pieces, for the actual curve supremum. -/
theorem weighted_time_reverse_triangle3 {w : LorentzPoint3 → ℝ} {lo hi : ℝ}
    (hw : InTimeWeightClass3 w lo hi) {p q r : LorentzPoint3}
    (hp : p ∈ closedLorentzDiamond3) (hq : q ∈ closedLorentzDiamond3)
    (hr : r ∈ closedLorentzDiamond3) (hpq : causal3 p q) (hqr : causal3 q r) :
    weightedTimeSeparation3 w p q + weightedTimeSeparation3 w q r ≤
      weightedTimeSeparation3 w p r := by
  have hjoin (c : FutureCurve3 p q) (d : FutureCurve3 q r) :
      c.weightedLength w + d.weightedLength w ≤ weightedTimeSeparation3 w p r := by
    rw [← c.concat_weightedLength d hw]
    exact (c.concat d).weightedLength_le_timeSeparation hw
  have hright (c : FutureCurve3 p q) :
      c.weightedLength w + weightedTimeSeparation3 w q r ≤ weightedTimeSeparation3 w p r := by
    have hb : weightedTimeSeparation3 w q r ≤ weightedTimeSeparation3 w p r - c.weightedLength w := by
      apply csSup_le (by simp : (insert 0 (Set.range
        (fun d : FutureCurve3 q r => d.weightedLength w))).Nonempty)
      rintro x (hx | ⟨d, rfl⟩)
      · subst x
        have h := hjoin c (straightCurve3 hq hr hqr)
        linarith [(straightCurve3 hq hr hqr).weightedLength_nonneg hw]
      · linarith [hjoin c d]
    linarith
  have hb : weightedTimeSeparation3 w p q ≤ weightedTimeSeparation3 w p r - weightedTimeSeparation3 w q r := by
    apply csSup_le (by simp : (insert 0 (Set.range
      (fun c : FutureCurve3 p q => c.weightedLength w))).Nonempty)
    rintro x (hx | ⟨c, rfl⟩)
    · subst x
      have h := hright (straightCurve3 hp hq hpq)
      linarith [(straightCurve3 hp hq hpq).weightedLength_nonneg hw]
    · linarith [hright c]
  linarith

theorem InDensityClass3.time_reverse_triangle3 {rho : LorentzPoint3 → ℝ}
    (hR : InDensityClass3 rho) {p q r : LorentzPoint3}
    (hp : p ∈ closedLorentzDiamond3) (hq : q ∈ closedLorentzDiamond3)
    (hr : r ∈ closedLorentzDiamond3) (hpq : causal3 p q) (hqr : causal3 q r) :
    weightedTimeSeparation3 (densityTimeWeight3 rho) p q +
      weightedTimeSeparation3 (densityTimeWeight3 rho) q r ≤
        weightedTimeSeparation3 (densityTimeWeight3 rho) p r :=
  weighted_time_reverse_triangle3 hR.timeWeight hp hq hr hpq hqr

#print axioms join_integrable_left3
#print axioms join_integrable_right3
#print axioms join_integrable3
#print axioms join_integral_left3
#print axioms join_integral_right3
#print axioms join_integral3
#print axioms join_primitive_left3
#print axioms join_primitive_right3
#print axioms joined_coord_AC3
#print axioms joined_coord_left3
#print axioms joined_coord_right3
#print axioms joined_coord_deriv3
#print axioms ae_left_half3
#print axioms ae_right_half3
#print axioms joined_velocity3
#print axioms joined_future3
#print axioms FutureCurve3.concat_point_left
#print axioms FutureCurve3.concat_point_right
#print axioms FutureCurve3.concat_velocity
#print axioms flat_proper_speed_smul3
#print axioms FutureCurve3.concat_weighted_integrand
#print axioms curve_integral_eq_interval3
#print axioms FutureCurve3.concat_weightedLength
#print axioms FutureCurve3.weightedLength_nonneg
#print axioms weighted_time_reverse_triangle3
#print axioms InDensityClass3.time_reverse_triangle3

end
end QuantyraNullCone
