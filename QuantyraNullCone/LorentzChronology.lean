import QuantyraNullCone.LorentzPreservation
import Mathlib.Topology.Order.IntermediateValue

namespace QuantyraNullCone

noncomputable section

theorem chronological_iff_square3 (p q : LorentzPoint3) : chronological3 p q ↔
    lorentzSquare3 (q - p) < 0 ∧ 0 < q 0 - p 0 := by
  have hr := spatial_radius_nonneg3 (q - p)
  have hs := spatial_radius_sq3 (q - p)
  change spatialRadius3 (q - p) < q 0 - p 0 ↔ _
  simp only [lorentzSquare3, PiLp.sub_apply]
  constructor
  · intro h
    constructor
    · nlinarith
    · linarith
  · rintro ⟨h, ht⟩
    nlinarith

/-- Actual Lorentzian separation, with no radial coordinate singularities. -/
theorem lorentz_flow_separation3 (a : ℝ) (p q : LorentzPoint3)
    (hp : flowDenominator3 a p ≠ 0) (hq : flowDenominator3 a q ≠ 0) :
    lorentzSquare3 (lorentzFlow3 a q - lorentzFlow3 a p) =
      flowFactor3 a p * flowFactor3 a q * lorentzSquare3 (q - p) := by
  simp only [lorentzSquare3, spatialSquared3, PiLp.sub_apply,
    lorentz_flow_time3, lorentz_flow_x3, lorentz_flow_y3, flowFactor3]
  field_simp [hp, hq]
  unfold flowTimeNumerator3 flowDenominator3 spatialSquared3
  ring

theorem parameter_segment_bounds3 {a s : ℝ} (ha : |a| < 1) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    |a * s| < 1 := by
  rw [abs_mul, abs_of_nonneg hs.1]
  have h := mul_le_mul_of_nonneg_left hs.2 (abs_nonneg a)
  nlinarith [abs_nonneg a]

theorem continuousOn_flow_time_parameter3 {a : ℝ} (ha : |a| < 1) {p : LorentzPoint3}
    (hp : p ∈ closedLorentzDiamond3) :
    ContinuousOn (fun s : ℝ => lorentzFlow3 (a * s) p 0) (Set.Icc 0 1) := by
  simp only [lorentz_flow_time3]
  apply ContinuousOn.div
  · unfold flowTimeNumerator3
    fun_prop
  · unfold flowDenominator3
    fun_prop
  · intro s hs
    exact (flow_denominator_pos3 (parameter_segment_bounds3 ha hs) hp).ne'

theorem lorentz_flow_chronological_forward3 {a : ℝ} (ha : |a| < 1)
    {p q : LorentzPoint3} (hp : p ∈ closedLorentzDiamond3)
    (hq : q ∈ closedLorentzDiamond3) (hChron : chronological3 p q) :
    chronological3 (lorentzFlow3 a p) (lorentzFlow3 a q) := by
  obtain ⟨hSquare, hTime⟩ := (chronological_iff_square3 p q).mp hChron
  have hNegative : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      lorentzSquare3 (lorentzFlow3 (a * s) q - lorentzFlow3 (a * s) p) < 0 := by
    intro s hs
    have hParam := parameter_segment_bounds3 ha hs
    rw [lorentz_flow_separation3 _ _ _ (flow_denominator_pos3 hParam hp).ne'
      (flow_denominator_pos3 hParam hq).ne']
    exact mul_neg_of_pos_of_neg
      (mul_pos (flow_factor_pos3 hParam hp) (flow_factor_pos3 hParam hq)) hSquare
  let f : ℝ → ℝ := fun s => lorentzFlow3 (a * s) q 0 - lorentzFlow3 (a * s) p 0
  have hContinuous : ContinuousOn f (Set.Icc 0 1) :=
    (continuousOn_flow_time_parameter3 ha hq).sub (continuousOn_flow_time_parameter3 ha hp)
  have hZero : 0 < f 0 := by simpa [f, lorentz_flow_zero3] using hTime
  have hOne : 0 < f 1 := by
    by_contra h
    have hAtOne : f 1 ≤ 0 := le_of_not_gt h
    obtain ⟨s, hs, hFs⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1)
      hContinuous ⟨hAtOne, hZero.le⟩
    have hNeg := hNegative s hs
    have hNonneg := spatial_squared_nonneg3 (lorentzFlow3 (a * s) q - lorentzFlow3 (a * s) p)
    change lorentzFlow3 (a * s) q 0 - lorentzFlow3 (a * s) p 0 = 0 at hFs
    unfold lorentzSquare3 at hNeg
    simp only [PiLp.sub_apply, hFs] at hNeg
    linarith
  apply (chronological_iff_square3 _ _).mpr
  constructor
  · simpa using hNegative 1 (by norm_num)
  · simpa [f] using hOne

theorem lorentz_flow_chronological_iff3 {a : ℝ} (ha : |a| < 1)
    {p q : LorentzPoint3} (hp : p ∈ closedLorentzDiamond3)
    (hq : q ∈ closedLorentzDiamond3) :
    chronological3 (lorentzFlow3 a p) (lorentzFlow3 a q) ↔ chronological3 p q := by
  constructor
  · intro h
    have hNeg : |-a| < 1 := by simpa using ha
    have hBack := lorentz_flow_chronological_forward3 hNeg
      (lorentz_flow_preserves_closed3 ha hp) (lorentz_flow_preserves_closed3 ha hq) h
    simpa only [lorentz_flow_inverse_closed3 ha hp, lorentz_flow_inverse_closed3 ha hq] using hBack
  · exact lorentz_flow_chronological_forward3 ha hp hq

#print axioms chronological_iff_square3
#print axioms lorentz_flow_separation3
#print axioms continuousOn_flow_time_parameter3
#print axioms lorentz_flow_chronological_forward3
#print axioms lorentz_flow_chronological_iff3

end

end QuantyraNullCone
