import QuantyraNullCone.LorentzEndpointBounds
import Mathlib.Topology.UniformSpace.HeineCantor

namespace QuantyraNullCone

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

def flatEndpoint3 (p q : LorentzPoint3) : ℝ :=
  Real.sqrt (max (q 0 - p 0 - spatialRadius3 (q - p)) 0 *
    max (q 0 - p 0 + spatialRadius3 (q - p)) 0)

theorem flat_time_max_formula3 {p q : LorentzPoint3}
    (hp : p ∈ closedLorentzDiamond3) (hq : q ∈ closedLorentzDiamond3) :
    flatTimeSeparation3 p q = flatEndpoint3 p q := by
  by_cases hc : causal3 p q
  · rw [flat_time_separation_eq3 hp hq hc]
    have hminus : 0 ≤ q 0 - p 0 - spatialRadius3 (q - p) := sub_nonneg.mpr hc
    have hplus : 0 ≤ q 0 - p 0 + spatialRadius3 (q - p) := by
      linarith [spatial_radius_nonneg3 (q - p)]
    unfold flatProperSpeed3 flatEndpoint3
    rw [max_eq_left hminus, max_eq_left hplus]
    congr 1
    change (q 0 - p 0) ^ 2 - spatialSquared3 (q - p) = _
    nlinarith [spatial_radius_sq3 (q - p)]
  · rw [flat_time_separation_of_not_causal3 hc]
    have hminus : q 0 - p 0 - spatialRadius3 (q - p) ≤ 0 := by
      have h : q 0 - p 0 < spatialRadius3 (q - p) := lt_of_not_ge hc
      linarith
    simp only [flatEndpoint3, max_eq_right hminus, zero_mul, Real.sqrt_zero]

theorem continuous_flatEndpoint3 : Continuous (fun z : LorentzPoint3 × LorentzPoint3 => flatEndpoint3 z.1 z.2) := by
  have ht : Continuous (fun z : LorentzPoint3 × LorentzPoint3 => z.2 0 - z.1 0) := by fun_prop
  have hr : Continuous (fun z : LorentzPoint3 × LorentzPoint3 => spatialRadius3 (z.2 - z.1)) :=
    continuous_spatial_radius3.comp (continuous_snd.sub continuous_fst)
  exact Real.continuous_sqrt.comp (((ht.sub hr).max continuous_const).mul
    ((ht.add hr).max continuous_const))

theorem flat_endpoint_zero_of_not_chronological3 {p q : LorentzPoint3}
    (h : ¬chronological3 p q) : flatEndpoint3 p q = 0 := by
  have hm : q 0 - p 0 - spatialRadius3 (q - p) ≤ 0 := by
    have ht : q 0 - p 0 ≤ spatialRadius3 (q - p) := not_lt.mp h
    linarith
  simp only [flatEndpoint3, max_eq_right hm, zero_mul, Real.sqrt_zero]

theorem weighted_time_continuousWithinAt_timelike3 {w : LorentzPoint3 → ℝ} {lo hi : ℝ}
    (hw : InTimeWeightClass3 w lo hi) {p q : LorentzPoint3}
    (hp : p ∈ closedLorentzDiamond3) (hq : q ∈ closedLorentzDiamond3)
    (hpq : chronological3 p q) :
    ContinuousWithinAt (fun z : LorentzPoint3 × LorentzPoint3 => weightedTimeSeparation3 w z.1 z.2)
      (closedLorentzDiamond3 ×ˢ closedLorentzDiamond3) (p, q) := by
  apply Metric.continuousWithinAt_iff.mpr
  intro eps heps
  have hhi : 0 < hi := hw.lower_pos.trans_le hw.lower_le_upper
  let a := timeMargin3 p q / 2
  have ha : 0 < a := half_pos ((time_margin_pos_iff3 p q).mpr hpq)
  have hma : timeMargin3 p q = 2 * a := by dsimp [a]; ring
  obtain ⟨d, hd, hweight⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_closedLorentzDiamond3.uniformContinuousOn_of_continuous hw.continuousOn)
    (eps / 8) (by positivity)
  let eta := min (1 / 2 : ℝ) (min (d / 16) (eps / (8 * hi)))
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hetahalf : eta ≤ 1 / 2 := min_le_left _ _
  have hetad : eta ≤ d / 16 := (min_le_right _ _).trans (min_le_left _ _)
  have hetaeps : eta ≤ eps / (8 * hi) := (min_le_right _ _).trans (min_le_right _ _)
  have hscale : eta * (8 * hi) ≤ eps := (le_div_iff₀ (by positivity : 0 < 8 * hi)).mp hetaeps
  let e := min (eta * a / 8) (d / 12)
  have he : 0 < e := by dsimp [e]; positivity
  have hea : e ≤ eta * a / 8 := min_le_left _ _
  have hed : e ≤ d / 12 := min_le_right _ _
  refine ⟨e, he, ?_⟩
  intro z hz hdist
  rw [Prod.dist_eq] at hdist
  have hpc : ‖z.1 - p‖ ≤ e := by
    simpa only [dist_eq_norm] using (max_lt_iff.mp hdist).1.le
  have hqc : ‖z.2 - q‖ ≤ e := by
    simpa only [dist_eq_norm] using (max_lt_iff.mp hdist).2.le
  have hinc := endpoint_increment_difference3 hpc hqc
  have hmargin := (abs_le.mp (time_margin_difference3 p q z.1 z.2)).1
  have hm' : a ≤ timeMargin3 z.1 z.2 := by
    have hprod := mul_le_mul_of_nonneg_right hetahalf ha.le
    nlinarith
  have hnoise : 2 * ‖(z.2 - z.1) - (q - p)‖ ≤ eta * a := by nlinarith
  have hbound := weighted_time_endpoint_bound3 hw hp hq hz.1 hz.2 ha
    (by linarith : a ≤ timeMargin3 p q) hm' heta.le (by linarith : eta ≤ 1)
    (by positivity : 0 ≤ eps / 8) hnoise (by
      intro x hx y hy hxy
      have hnear : dist x y < d := by
        rw [dist_eq_norm]
        nlinarith
      have h := hweight x hx y hy hnear
      exact (by simpa only [Real.dist_eq] using h.le))
  rw [Real.dist_eq]
  exact hbound.trans_lt (by nlinarith)

theorem weighted_time_continuousWithinAt_nontimelike3 {w : LorentzPoint3 → ℝ} {lo hi : ℝ}
    (hw : InTimeWeightClass3 w lo hi) {p q : LorentzPoint3}
    (hp : p ∈ closedLorentzDiamond3) (hq : q ∈ closedLorentzDiamond3)
    (hpq : ¬chronological3 p q) :
    ContinuousWithinAt (fun z : LorentzPoint3 × LorentzPoint3 => weightedTimeSeparation3 w z.1 z.2)
      (closedLorentzDiamond3 ×ˢ closedLorentzDiamond3) (p, q) := by
  have hz : weightedTimeSeparation3 w p q = 0 :=
    (weighted_time_separation_zero_iff3 hw hp hq).mpr hpq
  change Tendsto _ _ (𝓝 (weightedTimeSeparation3 w p q))
  rw [hz]
  have hg : ContinuousWithinAt (fun z : LorentzPoint3 × LorentzPoint3 => hi * flatEndpoint3 z.1 z.2)
      (closedLorentzDiamond3 ×ˢ closedLorentzDiamond3) (p, q) :=
    (continuous_const.mul continuous_flatEndpoint3).continuousWithinAt
  change Tendsto _ _ (𝓝 (hi * flatEndpoint3 p q)) at hg
  have hg0 : Tendsto (fun z : LorentzPoint3 × LorentzPoint3 => hi * flatEndpoint3 z.1 z.2)
      (𝓝[closedLorentzDiamond3 ×ˢ closedLorentzDiamond3] (p, q)) (𝓝 0) := by
    simpa only [flat_endpoint_zero_of_not_chronological3 hpq, mul_zero] using hg
  apply squeeze_zero' (Eventually.of_forall fun z => weighted_time_separation_nonneg3 hw z.1 z.2) _ hg0
  filter_upwards [self_mem_nhdsWithin] with z hz'
  have h := (weighted_time_separation_bounds3 hw hz'.1 hz'.2).2
  rwa [flat_time_max_formula3 hz'.1 hz'.2] at h

/-- Joint endpoint continuity on the full closed diamond for the original AC-curve supremum. -/
theorem weighted_time_continuousOn3 {w : LorentzPoint3 → ℝ} {lo hi : ℝ}
    (hw : InTimeWeightClass3 w lo hi) :
    ContinuousOn (fun z : LorentzPoint3 × LorentzPoint3 => weightedTimeSeparation3 w z.1 z.2)
      (closedLorentzDiamond3 ×ˢ closedLorentzDiamond3) := by
  rintro ⟨p, q⟩ ⟨hp, hq⟩
  by_cases h : chronological3 p q
  · exact weighted_time_continuousWithinAt_timelike3 hw hp hq h
  · exact weighted_time_continuousWithinAt_nontimelike3 hw hp hq h

theorem weighted_time_uniformContinuousOn3 {w : LorentzPoint3 → ℝ} {lo hi : ℝ}
    (hw : InTimeWeightClass3 w lo hi) :
    UniformContinuousOn (fun z : LorentzPoint3 × LorentzPoint3 => weightedTimeSeparation3 w z.1 z.2)
      (closedLorentzDiamond3 ×ˢ closedLorentzDiamond3) :=
  (isCompact_closedLorentzDiamond3.prod isCompact_closedLorentzDiamond3).uniformContinuousOn_of_continuous
    (weighted_time_continuousOn3 hw)

theorem InDensityClass3.time_continuousOn {rho : LorentzPoint3 → ℝ} (hR : InDensityClass3 rho) :
    ContinuousOn (fun z : LorentzPoint3 × LorentzPoint3 => weightedTimeSeparation3 (densityTimeWeight3 rho) z.1 z.2)
      (closedLorentzDiamond3 ×ˢ closedLorentzDiamond3) := weighted_time_continuousOn3 hR.timeWeight

#print axioms flat_time_max_formula3
#print axioms continuous_flatEndpoint3
#print axioms flat_endpoint_zero_of_not_chronological3
#print axioms weighted_time_continuousWithinAt_timelike3
#print axioms weighted_time_continuousWithinAt_nontimelike3
#print axioms weighted_time_continuousOn3
#print axioms weighted_time_uniformContinuousOn3
#print axioms InDensityClass3.time_continuousOn

end
end QuantyraNullCone
