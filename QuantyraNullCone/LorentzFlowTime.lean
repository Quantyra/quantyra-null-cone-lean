import QuantyraNullCone.LorentzFlowCone
import QuantyraNullCone.LorentzCurveMap

namespace QuantyraNullCone

open Set
noncomputable section

theorem convex_closedLorentzDiamond3 : Convex ℝ closedLorentzDiamond3 := by
  intro x hx y hy a b ha hb hab
  change |(a • x + b • y) 0| + spatialRadius3 (a • x + b • y) ≤ 1
  have ht : |(a • x + b • y) 0| ≤ a * |x 0| + b * |y 0| := by
    simpa only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, abs_mul,
      abs_of_nonneg ha, abs_of_nonneg hb] using abs_add_le (a * x 0) (b * y 0)
  have hs := spatial_radius_add_le3 (a • x) (b • y)
  rw [spatial_radius_smul3, spatial_radius_smul3, abs_of_nonneg ha, abs_of_nonneg hb] at hs
  have h := add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
  change a * (|x 0| + spatialRadius3 x) + b * (|y 0| + spatialRadius3 y) ≤ a * 1 + b * 1 at h
  nlinarith

theorem lorentz_flow_lipschitz3 {a : ℝ} (ha : |a| < 1) :
    ∃ K, LipschitzOnWith K (lorentzFlow3 a) closedLorentzDiamond3 :=
  ((lorentz_flow_smooth3 a).mono (flow_smooth_domain_contains3 ha)).exists_lipschitzOnWith
    (by simp) convex_closedLorentzDiamond3 isCompact_closedLorentzDiamond3

theorem lorentz_flow_isCausalMap3 {a : ℝ} (ha : |a| < 1) :
    IsCausalMap3 (lorentzFlow3 a) (lorentzFlowDerivative3 a) where
  lipschitz := lorentz_flow_lipschitz3 ha
  hasFDerivAt p hp := hasFDerivAt_lorentz_flow3 a p (flow_denominator_pos3 ha hp).ne'
  mapsTo := fun _ hp => lorentz_flow_preserves_closed3 ha hp
  future := fun _ hp _ hv => lorentz_flow_derivative_future3 ha hp hv

/-- The actual AC supremum transports under the conformal weight action. -/
theorem weighted_time_flow_eq3 {a : ℝ} (ha : |a| < 1)
    {w z : LorentzPoint3 → ℝ} {lo hi lo' hi' : ℝ}
    (hw : InTimeWeightClass3 w lo hi) (hz : InTimeWeightClass3 z lo' hi')
    (hweight : ∀ p ∈ closedLorentzDiamond3, z (lorentzFlow3 a p) * flowFactor3 a p = w p)
    {p q : LorentzPoint3} (hp : p ∈ closedLorentzDiamond3) (hq : q ∈ closedLorentzDiamond3) :
    weightedTimeSeparation3 z (lorentzFlow3 a p) (lorentzFlow3 a q) =
      weightedTimeSeparation3 w p q := by
  have hneg : |-a| < 1 := by simpa using ha
  have hfactor : ∀ r ∈ closedLorentzDiamond3,
      w (lorentzFlow3 (-a) r) * flowFactor3 (-a) r = z r := by
    intro r hr
    rw [← hweight _ (lorentz_flow_preserves_closed3 hneg hr)]
    have he : lorentzFlow3 a (lorentzFlow3 (-a) r) = r := by
      simpa only [neg_neg] using lorentz_flow_inverse_closed3 hneg hr
    rw [he,mul_assoc]
    have hf := flow_inverse_factor3 (-a) r (flow_denominator_pos3 hneg hr).ne'
      (sub_pos.mpr ((sq_lt_one_iff_abs_lt_one (-a)).mpr hneg)).ne'
    have hf' : flowFactor3 a (lorentzFlow3 (-a) r) * flowFactor3 (-a) r = 1 := by
      simpa only [neg_neg] using hf
    rw [hf',mul_one]
  apply le_antisymm
  · have h := weighted_time_le_of_causal_map3 (lorentz_flow_isCausalMap3 hneg) hw
      (fun r hr v hv => by rw [lorentz_flow_flat_proper_speed3 hneg hr hv,
        ← mul_assoc,hfactor r hr]) (lorentzFlow3 a p) (lorentzFlow3 a q)
    simpa only [lorentz_flow_inverse_closed3 ha hp,lorentz_flow_inverse_closed3 ha hq] using h
  · exact weighted_time_le_of_causal_map3 (lorentz_flow_isCausalMap3 ha) hz
      (fun r hr v hv => by rw [lorentz_flow_flat_proper_speed3 ha hr hv,
        ← mul_assoc,hweight r hr]) p q

theorem gauge_time_weight3 {p : LorentzPoint3} (hp : p ∈ closedLorentzDiamond3) :
    densityTimeWeight3 gaugeDensity3 p =
      densityTimeWeight3 flatDensity3 (lorentzFlow3 (-gaugeParameter3) p) *
        flowFactor3 (-gaugeParameter3) p := by
  have hf := flow_factor_pos3 gauge_parameter_abs3 hp
  have hv := lorentz_volume_pos3
  have he : Real.rpow (flowFactor3 (-gaugeParameter3) p ^ 3) (1 / 3) =
      flowFactor3 (-gaugeParameter3) p := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_natCast_mul hf.le 3 (1 / 3)]
    norm_num
  unfold densityTimeWeight3 gaugeDensity3 flatDensity3
  simp only [Real.rpow_eq_pow] at he ⊢
  rw [Real.div_rpow (pow_nonneg hf.le 3) hv.le, he,
    Real.div_rpow (by norm_num : (0 : ℝ) ≤ 1) hv.le, Real.one_rpow]
  ring

theorem gauge_inverse_time_separation3 {p q : LorentzPoint3}
    (hp : p ∈ closedLorentzDiamond3) (hq : q ∈ closedLorentzDiamond3) :
    weightedTimeSeparation3 (densityTimeWeight3 flatDensity3)
      (lorentzFlow3 (-gaugeParameter3) p) (lorentzFlow3 (-gaugeParameter3) q) =
      weightedTimeSeparation3 (densityTimeWeight3 gaugeDensity3) p q :=
  weighted_time_flow_eq3 gauge_parameter_abs3 gauge_density_class3.timeWeight
    flat_density_class3.timeWeight (fun _ hr => (gauge_time_weight3 hr).symm) hp hq

theorem gauge_forward_time_separation3 {p q : LorentzPoint3}
    (hp : p ∈ closedLorentzDiamond3) (hq : q ∈ closedLorentzDiamond3) :
    weightedTimeSeparation3 (densityTimeWeight3 gaugeDensity3)
      (lorentzFlow3 gaugeParameter3 p) (lorentzFlow3 gaugeParameter3 q) =
      weightedTimeSeparation3 (densityTimeWeight3 flatDensity3) p q := by
  have ha : |gaugeParameter3| < 1 := by norm_num [gaugeParameter3]
  have h := gauge_inverse_time_separation3
    (lorentz_flow_preserves_closed3 ha hp) (lorentz_flow_preserves_closed3 ha hq)
  simpa only [lorentz_flow_inverse_closed3 ha hp,lorentz_flow_inverse_closed3 ha hq] using h.symm

#print axioms convex_closedLorentzDiamond3
#print axioms lorentz_flow_lipschitz3
#print axioms lorentz_flow_isCausalMap3
#print axioms weighted_time_flow_eq3
#print axioms gauge_time_weight3
#print axioms gauge_inverse_time_separation3
#print axioms gauge_forward_time_separation3

end
end QuantyraNullCone
