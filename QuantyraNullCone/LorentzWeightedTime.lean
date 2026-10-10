import QuantyraNullCone.LorentzProperTime

namespace QuantyraNullCone

open MeasureTheory Set

noncomputable section

/-- Positive continuous weights, with explicit bounds on the original closed diamond. -/
structure InTimeWeightClass3 (w : LorentzPoint3 → ℝ) (lo hi : ℝ) : Prop where
  lower_pos : 0 < lo
  lower_le_upper : lo ≤ hi
  continuousOn : ContinuousOn w closedLorentzDiamond3
  bounds : ∀ p ∈ closedLorentzDiamond3, lo ≤ w p ∧ w p ≤ hi

def FutureCurve3.weightedLength {p q : LorentzPoint3} (c : FutureCurve3 p q)
    (w : LorentzPoint3 → ℝ) : ℝ := ∫ t, w (c.point t) * c.flatSpeed t ∂curveMeasure

/-- Supremum of actual weighted AC-curve lengths; the empty curve class gives zero. -/
def weightedTimeSeparation3 (w : LorentzPoint3 → ℝ) (p q : LorentzPoint3) : ℝ :=
  sSup (insert 0 (Set.range (fun c : FutureCurve3 p q => c.weightedLength w)))

theorem FutureCurve3.continuousOn_point {p q : LorentzPoint3} (c : FutureCurve3 p q) :
    ContinuousOn c.point (Icc (0 : ℝ) 1) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp_continuousOn
  apply continuousOn_pi.mpr
  intro i
  simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using (c.coordAC i).continuousOn

theorem FutureCurve3.integrable_weightedSpeed {p q : LorentzPoint3} (c : FutureCurve3 p q)
    {w : LorentzPoint3 → ℝ} {lo hi : ℝ} (hw : InTimeWeightClass3 w lo hi) :
    Integrable (fun t => w (c.point t) * c.flatSpeed t) curveMeasure := by
  have hm : AEStronglyMeasurable (fun t => w (c.point t)) curveMeasure :=
    (hw.continuousOn.comp c.continuousOn_point c.inDiamond).aestronglyMeasurable measurableSet_Icc
  apply (c.integrable_flatSpeed.const_mul hi).mono' (hm.mul c.integrable_flatSpeed.aestronglyMeasurable)
  filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
  have hb := hw.bounds _ (c.inDiamond t ht)
  have hn : 0 ≤ w (c.point t) := hw.lower_pos.le.trans hb.1
  change ‖w (c.point t) * c.flatSpeed t‖ ≤ hi * c.flatSpeed t
  rw [Real.norm_eq_abs, abs_of_nonneg
    (show 0 ≤ w (c.point t) * c.flatSpeed t from mul_nonneg hn (flat_proper_speed_nonneg3 _))]
  exact mul_le_mul_of_nonneg_right hb.2 (flat_proper_speed_nonneg3 _)

theorem FutureCurve3.weightedLength_bounds {p q : LorentzPoint3} (c : FutureCurve3 p q)
    {w : LorentzPoint3 → ℝ} {lo hi : ℝ} (hw : InTimeWeightClass3 w lo hi) :
    lo * c.flatLength ≤ c.weightedLength w ∧ c.weightedLength w ≤ hi * c.flatLength := by
  constructor
  · rw [FutureCurve3.flatLength, ← integral_const_mul]
    apply integral_mono_ae (c.integrable_flatSpeed.const_mul lo) (c.integrable_weightedSpeed hw)
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
    exact mul_le_mul_of_nonneg_right (hw.bounds _ (c.inDiamond t ht)).1
      (flat_proper_speed_nonneg3 _)
  · rw [FutureCurve3.flatLength, ← integral_const_mul]
    apply integral_mono_ae (c.integrable_weightedSpeed hw) (c.integrable_flatSpeed.const_mul hi)
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
    exact mul_le_mul_of_nonneg_right (hw.bounds _ (c.inDiamond t ht)).2
      (flat_proper_speed_nonneg3 _)

theorem weighted_lengths_bddAbove3 {w : LorentzPoint3 → ℝ} {lo hi : ℝ}
    (hw : InTimeWeightClass3 w lo hi) (p q : LorentzPoint3) :
    BddAbove (insert 0 (Set.range (fun c : FutureCurve3 p q => c.weightedLength w))) := by
  refine ⟨hi * 2, ?_⟩
  have hh : 0 ≤ hi := hw.lower_pos.le.trans hw.lower_le_upper
  rintro x (hx | ⟨c, rfl⟩)
  · subst x; positivity
  · exact (c.weightedLength_bounds hw).2.trans (mul_le_mul_of_nonneg_left c.flatLength_le_two hh)

theorem weighted_time_separation_nonneg3 {w : LorentzPoint3 → ℝ} {lo hi : ℝ}
    (hw : InTimeWeightClass3 w lo hi) (p q : LorentzPoint3) :
    0 ≤ weightedTimeSeparation3 w p q := le_csSup (weighted_lengths_bddAbove3 hw p q) (by simp)

theorem FutureCurve3.weightedLength_le_timeSeparation {p q : LorentzPoint3}
    (c : FutureCurve3 p q) {w : LorentzPoint3 → ℝ} {lo hi : ℝ}
    (hw : InTimeWeightClass3 w lo hi) : c.weightedLength w ≤ weightedTimeSeparation3 w p q :=
  le_csSup (weighted_lengths_bddAbove3 hw p q) (by simp)

theorem weighted_time_separation_of_not_causal3 {p q : LorentzPoint3}
    (hpq : ¬causal3 p q) (w : LorentzPoint3 → ℝ) : weightedTimeSeparation3 w p q = 0 := by
  have hr : Set.range (fun c : FutureCurve3 p q => c.weightedLength w) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro x ⟨c, rfl⟩
    exact hpq c.endpoint_causal
  simp [weightedTimeSeparation3, hr]

/-- Uniform two-sided comparison for the actual curve supremum. -/
theorem weighted_time_separation_bounds3 {w : LorentzPoint3 → ℝ} {lo hi : ℝ}
    (hw : InTimeWeightClass3 w lo hi) {p q : LorentzPoint3}
    (hp : p ∈ closedLorentzDiamond3) (hq : q ∈ closedLorentzDiamond3) :
    lo * flatTimeSeparation3 p q ≤ weightedTimeSeparation3 w p q ∧
      weightedTimeSeparation3 w p q ≤ hi * flatTimeSeparation3 p q := by
  have hh : 0 ≤ hi := hw.lower_pos.le.trans hw.lower_le_upper
  constructor
  · by_cases hc : causal3 p q
    · rw [flat_time_separation_eq3 hp hq hc, ← straight_curve_flatLength3 hp hq hc]
      exact ((straightCurve3 hp hq hc).weightedLength_bounds hw).1.trans
        ((straightCurve3 hp hq hc).weightedLength_le_timeSeparation hw)
    · rw [flat_time_separation_of_not_causal3 hc, mul_zero]
      exact weighted_time_separation_nonneg3 hw p q
  · apply csSup_le (by simp : (insert 0 (Set.range
      (fun c : FutureCurve3 p q => c.weightedLength w))).Nonempty)
    rintro x (hx | ⟨c, rfl⟩)
    · subst x; exact mul_nonneg hh (flat_time_separation_nonneg3 p q)
    · apply (c.weightedLength_bounds hw).2.trans
      apply mul_le_mul_of_nonneg_left _ hh
      exact le_csSup (flat_lengths_bddAbove3 p q) (by simp)

theorem weighted_time_separation_pos_iff3 {w : LorentzPoint3 → ℝ} {lo hi : ℝ}
    (hw : InTimeWeightClass3 w lo hi) {p q : LorentzPoint3}
    (hp : p ∈ closedLorentzDiamond3) (hq : q ∈ closedLorentzDiamond3) :
    0 < weightedTimeSeparation3 w p q ↔ chronological3 p q := by
  have hb := weighted_time_separation_bounds3 hw hp hq
  rw [← flat_time_separation_pos_iff3 hp hq]
  constructor
  · intro h
    by_contra hn
    have hz : flatTimeSeparation3 p q = 0 :=
      le_antisymm (le_of_not_gt hn) (flat_time_separation_nonneg3 p q)
    rw [hz, mul_zero] at hb
    linarith [hb.2]
  · intro h
    exact (mul_pos hw.lower_pos h).trans_le hb.1

theorem weighted_time_separation_zero_iff3 {w : LorentzPoint3 → ℝ} {lo hi : ℝ}
    (hw : InTimeWeightClass3 w lo hi) {p q : LorentzPoint3}
    (hp : p ∈ closedLorentzDiamond3) (hq : q ∈ closedLorentzDiamond3) :
    weightedTimeSeparation3 w p q = 0 ↔ ¬chronological3 p q := by
  rw [← weighted_time_separation_pos_iff3 hw hp hq]
  constructor
  · intro h; rw [h]; exact lt_irrefl 0
  · intro h
    exact le_antisymm (le_of_not_gt h) (weighted_time_separation_nonneg3 hw p q)

def SameTimeProfile3 (w : LorentzPoint3 → ℝ) (p q : LorentzPoint3) : Prop :=
  (∀ z ∈ closedLorentzDiamond3, weightedTimeSeparation3 w z p = weightedTimeSeparation3 w z q) ∧
    (∀ z ∈ closedLorentzDiamond3, weightedTimeSeparation3 w p z = weightedTimeSeparation3 w q z)

/-- Equal numerical time profiles against the whole closed diamond collapse exactly the waist. -/
theorem weighted_time_profile_eq_iff3 {w : LorentzPoint3 → ℝ} {lo hi : ℝ}
    (hw : InTimeWeightClass3 w lo hi) {p q : LorentzPoint3}
    (hp : p ∈ closedLorentzDiamond3) (hq : q ∈ closedLorentzDiamond3) :
    SameTimeProfile3 w p q ↔ p = q ∨ (p ∈ lorentzWaist3 ∧ q ∈ lorentzWaist3) := by
  constructor
  · intro h
    apply (chronological_profile_eq_iff3 hp hq).mp
    constructor
    · intro z hz
      have hzC := lorentz_diamond_subset_closed3 hz
      rw [← weighted_time_separation_pos_iff3 hw hzC hp,
        ← weighted_time_separation_pos_iff3 hw hzC hq, h.1 z hzC]
    · intro z hz
      have hzC := lorentz_diamond_subset_closed3 hz
      rw [← weighted_time_separation_pos_iff3 hw hp hzC,
        ← weighted_time_separation_pos_iff3 hw hq hzC, h.2 z hzC]
  · rintro (rfl | ⟨hP, hQ⟩)
    · exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
    · constructor
      · intro z hz
        have hpN := lorentz_waist_no_closed_neighbors3 hP hz
        have hqN := lorentz_waist_no_closed_neighbors3 hQ hz
        rw [(weighted_time_separation_zero_iff3 hw hz hp).mpr hpN.2,
          (weighted_time_separation_zero_iff3 hw hz hq).mpr hqN.2]
      · intro z hz
        have hpN := lorentz_waist_no_closed_neighbors3 hP hz
        have hqN := lorentz_waist_no_closed_neighbors3 hQ hz
        rw [(weighted_time_separation_zero_iff3 hw hp hz).mpr hpN.1,
          (weighted_time_separation_zero_iff3 hw hq hz).mpr hqN.1]

def densityTimeWeight3 (rho : LorentzPoint3 → ℝ) (p : LorentzPoint3) : ℝ :=
  Real.rpow (rho p / lorentzVolume3) (1 / 3)

def densityTimeLower3 : ℝ := Real.rpow ((1 / 2) / lorentzVolume3) (1 / 3)
def densityTimeUpper3 : ℝ := Real.rpow ((3 / 2) / lorentzVolume3) (1 / 3)

theorem InDensityClass3.timeWeight {rho : LorentzPoint3 → ℝ} (hr : InDensityClass3 rho) :
    InTimeWeightClass3 (densityTimeWeight3 rho) densityTimeLower3 densityTimeUpper3 := by
  have hv := lorentz_volume_pos3
  constructor
  · exact Real.rpow_pos_of_pos (div_pos (by norm_num) hv) _
  · apply Real.rpow_le_rpow (by positivity)
      (div_le_div_of_nonneg_right (by norm_num : (1 / 2 : ℝ) ≤ 3 / 2) hv.le)
      (by norm_num)
  · exact (hr.continuousOn.div_const _).rpow_const (fun _ _ => Or.inr (by norm_num))
  · intro p hp
    have hb := hr.bounds p hp
    have hr0 : 0 ≤ rho p := (by norm_num : (0 : ℝ) ≤ 1 / 2).trans hb.1
    constructor
    · exact Real.rpow_le_rpow (by positivity)
        (div_le_div_of_nonneg_right hb.1 hv.le) (by norm_num)
    · exact Real.rpow_le_rpow (by positivity)
        (div_le_div_of_nonneg_right hb.2 hv.le) (by norm_num)

theorem InDensityClass3.time_separation_pos_iff3 {rho : LorentzPoint3 → ℝ}
    (hr : InDensityClass3 rho) {p q : LorentzPoint3}
    (hp : p ∈ closedLorentzDiamond3) (hq : q ∈ closedLorentzDiamond3) :
    0 < weightedTimeSeparation3 (densityTimeWeight3 rho) p q ↔ chronological3 p q :=
  weighted_time_separation_pos_iff3 hr.timeWeight hp hq

theorem InDensityClass3.time_profile_eq_iff3 {rho : LorentzPoint3 → ℝ}
    (hr : InDensityClass3 rho) {p q : LorentzPoint3}
    (hp : p ∈ closedLorentzDiamond3) (hq : q ∈ closedLorentzDiamond3) :
    SameTimeProfile3 (densityTimeWeight3 rho) p q ↔
      p = q ∨ (p ∈ lorentzWaist3 ∧ q ∈ lorentzWaist3) :=
  weighted_time_profile_eq_iff3 hr.timeWeight hp hq

theorem density_time_weight_sq3 {rho : LorentzPoint3 → ℝ} {p : LorentzPoint3}
    (hr : 0 ≤ rho p) : densityTimeWeight3 rho p ^ 2 =
      Real.rpow lorentzVolume3 (-2 / 3) * Real.rpow (rho p) (2 / 3) := by
  have hv := lorentz_volume_pos3.le
  unfold densityTimeWeight3
  simp only [Real.rpow_eq_pow]
  rw [← Real.rpow_two, ← Real.rpow_mul (div_nonneg hr hv)]
  norm_num
  rw [Real.div_rpow hr hv, Real.rpow_neg hv]
  ring

/-- The normalized cube-root weight is exactly the proper-speed coefficient of the metric. -/
theorem density_metric_proper_speed3 {rho : LorentzPoint3 → ℝ} {p v : LorentzPoint3}
    (hr : 0 ≤ rho p) (hv : spatialRadius3 v ≤ v 0) :
    Real.sqrt (-densityMetric3 rho p v v) = densityTimeWeight3 rho p * flatProperSpeed3 v := by
  have hw : 0 ≤ densityTimeWeight3 rho p := Real.rpow_nonneg (div_nonneg hr lorentz_volume_pos3.le) _
  have heq : -densityMetric3 rho p v v =
      (densityTimeWeight3 rho p * flatProperSpeed3 v) ^ 2 := by
    rw [mul_pow, density_time_weight_sq3 hr, flat_proper_speed_sq3 hv]
    unfold densityMetric3 lorentzBilinear3 spatialSquared3
    ring
  rw [heq, Real.sqrt_sq_eq_abs, abs_of_nonneg (mul_nonneg hw (flat_proper_speed_nonneg3 v))]

theorem FutureCurve3.weightedLength_eq_metric {p q : LorentzPoint3} (c : FutureCurve3 p q)
    {rho : LorentzPoint3 → ℝ} (hr : InDensityClass3 rho) :
    c.weightedLength (densityTimeWeight3 rho) =
      ∫ t, Real.sqrt (-densityMetric3 rho (c.point t) (c.velocity t) (c.velocity t)) ∂curveMeasure := by
  apply integral_congr_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Icc, c.future] with t ht hv
  have hp : 0 ≤ rho (c.point t) := (by norm_num : (0 : ℝ) ≤ 1 / 2).trans
    (hr.bounds _ (c.inDiamond t ht)).1
  exact (density_metric_proper_speed3 hp hv).symm

theorem FutureCurve3.weightedLength_difference {p q : LorentzPoint3} (c : FutureCurve3 p q)
    {w v : LorentzPoint3 → ℝ} {lo hi lo' hi' delta : ℝ}
    (hw : InTimeWeightClass3 w lo hi) (hv : InTimeWeightClass3 v lo' hi')
    (hd : 0 ≤ delta) (hclose : ∀ z ∈ closedLorentzDiamond3, |w z - v z| ≤ delta) :
    |c.weightedLength w - c.weightedLength v| ≤ 2 * delta := by
  unfold weightedLength
  rw [← integral_sub (c.integrable_weightedSpeed hw) (c.integrable_weightedSpeed hv)]
  have hle : (∫ t, |w (c.point t) * c.flatSpeed t - v (c.point t) * c.flatSpeed t| ∂curveMeasure) ≤
      ∫ t, delta * c.flatSpeed t ∂curveMeasure := by
    apply integral_mono_ae ((c.integrable_weightedSpeed hw).sub (c.integrable_weightedSpeed hv)).abs
      (c.integrable_flatSpeed.const_mul delta)
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
    change |w (c.point t) * c.flatSpeed t - v (c.point t) * c.flatSpeed t| ≤ delta * c.flatSpeed t
    rw [← sub_mul, abs_mul, abs_of_nonneg
      (show 0 ≤ c.flatSpeed t from flat_proper_speed_nonneg3 _)]
    exact mul_le_mul_of_nonneg_right (hclose _ (c.inDiamond t ht)) (flat_proper_speed_nonneg3 _)
  rw [integral_const_mul] at hle
  have hlast := mul_le_mul_of_nonneg_left c.flatLength_le_two hd
  exact abs_integral_le_integral_abs.trans (hle.trans (by simpa [flatLength, mul_comm] using hlast))

theorem weighted_time_separation_le_add3 {w v : LorentzPoint3 → ℝ}
    {lo hi lo' hi' delta : ℝ} (hw : InTimeWeightClass3 w lo hi)
    (hv : InTimeWeightClass3 v lo' hi') (hd : 0 ≤ delta)
    (hclose : ∀ z ∈ closedLorentzDiamond3, |w z - v z| ≤ delta) (p q : LorentzPoint3) :
    weightedTimeSeparation3 w p q ≤ weightedTimeSeparation3 v p q + 2 * delta := by
  apply csSup_le (by simp : (insert 0 (Set.range
    (fun c : FutureCurve3 p q => c.weightedLength w))).Nonempty)
  rintro x (hx | ⟨c, rfl⟩)
  · subst x
    linarith [weighted_time_separation_nonneg3 hv p q]
  · have h := (abs_le.mp (c.weightedLength_difference hw hv hd hclose)).2
    linarith [c.weightedLength_le_timeSeparation hv]

/-- Uniform dependence on weights, with no assumed continuity of the curve supremum. -/
theorem weighted_time_separation_difference3 {w v : LorentzPoint3 → ℝ}
    {lo hi lo' hi' delta : ℝ} (hw : InTimeWeightClass3 w lo hi)
    (hv : InTimeWeightClass3 v lo' hi') (hd : 0 ≤ delta)
    (hclose : ∀ z ∈ closedLorentzDiamond3, |w z - v z| ≤ delta) (p q : LorentzPoint3) :
    |weightedTimeSeparation3 w p q - weightedTimeSeparation3 v p q| ≤ 2 * delta := by
  have h1 := weighted_time_separation_le_add3 hw hv hd hclose p q
  have h2 := weighted_time_separation_le_add3 hv hw hd
    (fun z hz => by simpa [abs_sub_comm] using hclose z hz) p q
  exact abs_le.mpr ⟨by linarith, by linarith⟩

#print axioms FutureCurve3.continuousOn_point
#print axioms FutureCurve3.integrable_weightedSpeed
#print axioms FutureCurve3.weightedLength_bounds
#print axioms weighted_lengths_bddAbove3
#print axioms weighted_time_separation_nonneg3
#print axioms FutureCurve3.weightedLength_le_timeSeparation
#print axioms weighted_time_separation_of_not_causal3
#print axioms weighted_time_separation_bounds3
#print axioms weighted_time_separation_pos_iff3
#print axioms weighted_time_separation_zero_iff3
#print axioms weighted_time_profile_eq_iff3
#print axioms InDensityClass3.timeWeight
#print axioms InDensityClass3.time_separation_pos_iff3
#print axioms InDensityClass3.time_profile_eq_iff3
#print axioms density_time_weight_sq3
#print axioms density_metric_proper_speed3
#print axioms FutureCurve3.weightedLength_eq_metric
#print axioms FutureCurve3.weightedLength_difference
#print axioms weighted_time_separation_le_add3
#print axioms weighted_time_separation_difference3

end
end QuantyraNullCone
