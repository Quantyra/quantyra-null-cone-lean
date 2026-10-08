import QuantyraNullCone.LorentzInverse

namespace QuantyraNullCone

noncomputable section

def nullMap3 (a z : ℝ) : ℝ := (z + a) / (1 + a * z)

theorem null_factor_pos3 {a z : ℝ} (ha : |a| < 1) (hz : |z| ≤ 1) : 0 < 1 + a * z :=
  (sub_pos.mpr ha).trans_le (null_factor_lower3 hz)

theorem null_map_bounds3 {a z : ℝ} (ha : |a| < 1) (hz : |z| ≤ 1) : |nullMap3 a z| ≤ 1 := by
  have hA := abs_lt.mp ha
  have hZ := abs_le.mp hz
  have hD := null_factor_pos3 ha hz
  unfold nullMap3
  apply abs_le.mpr
  constructor
  · apply (le_div_iff₀ hD).mpr
    have hProduct := mul_nonneg (by linarith : 0 ≤ 1 + a) (by linarith : 0 ≤ 1 + z)
    nlinarith
  · apply (div_le_iff₀ hD).mpr
    have hProduct := mul_nonneg (by linarith : 0 ≤ 1 - a) (by linarith : 0 ≤ 1 - z)
    nlinarith

theorem null_map_strict_bounds3 {a z : ℝ} (ha : |a| < 1) (hz : |z| < 1) : |nullMap3 a z| < 1 := by
  have hA := abs_lt.mp ha
  have hZ := abs_lt.mp hz
  have hD := null_factor_pos3 ha hz.le
  unfold nullMap3
  apply abs_lt.mpr
  constructor
  · apply (lt_div_iff₀ hD).mpr
    have hProduct := mul_pos (by linarith : 0 < 1 + a) (by linarith : 0 < 1 + z)
    nlinarith
  · apply (div_lt_iff₀ hD).mpr
    have hProduct := mul_pos (by linarith : 0 < 1 - a) (by linarith : 0 < 1 - z)
    nlinarith

theorem lorentz_null_plus3 {a : ℝ} (ha : |a| < 1) {p : LorentzPoint3}
    (hp : p ∈ closedLorentzDiamond3) :
    lorentzFlow3 a p 0 + spatialRadius3 (lorentzFlow3 a p) = nullMap3 a (p 0 + spatialRadius3 p) := by
  have hD := (flow_denominator_pos3 ha hp).ne'
  have hZ := (null_factor_pos3 ha (closed_lorentz_null_bounds3 hp).1).ne'
  rw [lorentz_flow_time3, spatial_radius_flow3, abs_of_pos (flow_factor_pos3 ha hp)]
  unfold nullMap3 flowFactor3
  field_simp [hD, hZ]
  unfold flowTimeNumerator3 flowDenominator3
  rw [← spatial_radius_sq3 p]
  ring

theorem lorentz_null_minus3 {a : ℝ} (ha : |a| < 1) {p : LorentzPoint3}
    (hp : p ∈ closedLorentzDiamond3) :
    lorentzFlow3 a p 0 - spatialRadius3 (lorentzFlow3 a p) = nullMap3 a (p 0 - spatialRadius3 p) := by
  have hD := (flow_denominator_pos3 ha hp).ne'
  have hZ := (null_factor_pos3 ha (closed_lorentz_null_bounds3 hp).2).ne'
  rw [lorentz_flow_time3, spatial_radius_flow3, abs_of_pos (flow_factor_pos3 ha hp)]
  unfold nullMap3 flowFactor3
  field_simp [hD, hZ]
  unfold flowTimeNumerator3 flowDenominator3
  rw [← spatial_radius_sq3 p]
  ring

theorem closed_lorentz_null_iff3 (p : LorentzPoint3) : p ∈ closedLorentzDiamond3 ↔
    |p 0 + spatialRadius3 p| ≤ 1 ∧ |p 0 - spatialRadius3 p| ≤ 1 := by
  constructor
  · exact closed_lorentz_null_bounds3
  · intro h
    have hu := (abs_le.mp h.1).2
    have hv := (abs_le.mp h.2).1
    have ht : |p 0| ≤ 1 - spatialRadius3 p := abs_le.mpr ⟨by linarith, by linarith⟩
    change |p 0| + spatialRadius3 p ≤ 1
    linarith

theorem open_lorentz_null_iff3 (p : LorentzPoint3) : p ∈ lorentzDiamond3 ↔
    |p 0 + spatialRadius3 p| < 1 ∧ |p 0 - spatialRadius3 p| < 1 := by
  constructor
  · intro hp
    change |p 0| + spatialRadius3 p < 1 at hp
    have htLower := neg_abs_le (p 0)
    have htUpper := le_abs_self (p 0)
    have hr := spatial_radius_nonneg3 p
    constructor <;> apply abs_lt.mpr <;> constructor <;> linarith
  · intro h
    have hu := (abs_lt.mp h.1).2
    have hv := (abs_lt.mp h.2).1
    have ht : |p 0| < 1 - spatialRadius3 p := abs_lt.mpr ⟨by linarith, by linarith⟩
    change |p 0| + spatialRadius3 p < 1
    linarith

theorem lorentz_flow_preserves_closed3 {a : ℝ} (ha : |a| < 1) {p : LorentzPoint3}
    (hp : p ∈ closedLorentzDiamond3) : lorentzFlow3 a p ∈ closedLorentzDiamond3 := by
  apply (closed_lorentz_null_iff3 _).mpr
  rw [lorentz_null_plus3 ha hp, lorentz_null_minus3 ha hp]
  obtain ⟨hu, hv⟩ := closed_lorentz_null_bounds3 hp
  exact ⟨null_map_bounds3 ha hu, null_map_bounds3 ha hv⟩

theorem lorentz_flow_preserves_open3 {a : ℝ} (ha : |a| < 1) {p : LorentzPoint3}
    (hp : p ∈ lorentzDiamond3) : lorentzFlow3 a p ∈ lorentzDiamond3 := by
  have hc := lorentz_diamond_subset_closed3 hp
  apply (open_lorentz_null_iff3 _).mpr
  rw [lorentz_null_plus3 ha hc, lorentz_null_minus3 ha hc]
  obtain ⟨hu, hv⟩ := (open_lorentz_null_iff3 p).mp hp
  exact ⟨null_map_strict_bounds3 ha hu, null_map_strict_bounds3 ha hv⟩

theorem lorentz_flow_image3 {a : ℝ} (ha : |a| < 1) : lorentzFlow3 a '' lorentzDiamond3 = lorentzDiamond3 := by
  apply Set.Subset.antisymm
  · rintro _ ⟨p, hp, rfl⟩
    exact lorentz_flow_preserves_open3 ha hp
  · intro q hq
    have hNeg : |-a| < 1 := by simpa using ha
    refine ⟨lorentzFlow3 (-a) q, lorentz_flow_preserves_open3 hNeg hq, ?_⟩
    simpa only [neg_neg] using lorentz_flow_inverse_closed3 hNeg (lorentz_diamond_subset_closed3 hq)

theorem lorentz_flow_injectiveOn3 {a : ℝ} (ha : |a| < 1) : Set.InjOn (lorentzFlow3 a) lorentzDiamond3 := by
  intro p hp q hq hEq
  have h := congrArg (lorentzFlow3 (-a)) hEq
  rw [lorentz_flow_inverse_closed3 ha (lorentz_diamond_subset_closed3 hp),
    lorentz_flow_inverse_closed3 ha (lorentz_diamond_subset_closed3 hq)] at h
  exact h

#print axioms null_map_bounds3
#print axioms null_map_strict_bounds3
#print axioms lorentz_null_plus3
#print axioms lorentz_null_minus3
#print axioms lorentz_flow_preserves_closed3
#print axioms lorentz_flow_preserves_open3
#print axioms lorentz_flow_image3
#print axioms lorentz_flow_injectiveOn3

end

end QuantyraNullCone
