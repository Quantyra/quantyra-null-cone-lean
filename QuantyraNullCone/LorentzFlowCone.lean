import QuantyraNullCone.LorentzIsometry
import QuantyraNullCone.LorentzCurveControl
import Mathlib.Analysis.SpecificLimits.Basic

namespace QuantyraNullCone

open Set Filter
open scoped Topology

noncomputable section

set_option maxHeartbeats 800000

theorem lorentz_flow_derivative_zero3 (p v : LorentzPoint3) :
    lorentzFlowDerivative3 0 p v = v := by
  ext i
  fin_cases i <;>
    simp [lorentzFlowDerivative3, flowDerivativeCoordinates3, scalarQuotientDerivative3,
      flowNumeratorDerivative3, flowDenominatorDerivative3, lorentzCoordinateCLM3,
      flowTimeNumerator3, flowDenominator3]

theorem lorentz_flow_derivative_square3 (a : ℝ) (p v : LorentzPoint3)
    (hd : flowDenominator3 a p ≠ 0) :
    lorentzSquare3 (lorentzFlowDerivative3 a p v) = flowFactor3 a p ^ 2 * lorentzSquare3 v := by
  simpa only [lorentzSquare3, spatialSquared3, lorentzBilinear3, pow_two, add_assoc]
    using lorentz_flow_derivative_bilinear3 a p v v hd

theorem continuousOn_flow_derivative_time_parameter3 {a : ℝ} (ha : |a| < 1)
    {p : LorentzPoint3} (hp : p ∈ closedLorentzDiamond3) (v : LorentzPoint3) :
    ContinuousOn (fun s : ℝ => lorentzFlowDerivative3 (a * s) p v 0) (Icc 0 1) := by
  have hd : ContinuousOn (fun s : ℝ => flowDenominator3 (a * s) p) (Icc 0 1) := by
    unfold flowDenominator3; fun_prop
  have hn : ∀ s ∈ Icc (0 : ℝ) 1, flowDenominator3 (a * s) p ≠ 0 :=
    fun s hs => (flow_denominator_pos3 (parameter_segment_bounds3 ha hs) hp).ne'
  have hi := hd.inv₀ hn
  have hi2 := (hd.pow 2).inv₀ (fun s hs => pow_ne_zero 2 (hn s hs))
  change ContinuousOn (fun s : ℝ => (flowDenominator3 (a * s) p)⁻¹ *
    ((1 + (a * s) ^ 2 + 2 * (a * s) * p 0) * v 0 -
      (2 * (a * s) * p 1) * v 1 - (2 * (a * s) * p 2) * v 2) -
    (flowTimeNumerator3 (a * s) p / (flowDenominator3 (a * s) p) ^ 2) *
    ((2 * (a * s) * (1 + (a * s) * p 0)) * v 0 -
      (2 * (a * s) ^ 2 * p 1) * v 1 - (2 * (a * s) ^ 2 * p 2) * v 2)) (Icc 0 1)
  simp only [div_eq_mul_inv]
  unfold flowTimeNumerator3
  fun_prop

/-- The actual derivative preserves the timelike future cone, including at boundary points. -/
theorem lorentz_flow_derivative_timelike3 {a : ℝ} (ha : |a| < 1)
    {p v : LorentzPoint3} (hp : p ∈ closedLorentzDiamond3)
    (hv : spatialRadius3 v < v 0) :
    spatialRadius3 (lorentzFlowDerivative3 a p v) < lorentzFlowDerivative3 a p v 0 := by
  have hv0 : 0 < v 0 := (spatial_radius_nonneg3 v).trans_lt hv
  have hvn : lorentzSquare3 v < 0 := by
    have hs := spatial_radius_sq3 v
    unfold lorentzSquare3
    nlinarith [spatial_radius_nonneg3 v]
  have hneg : ∀ s ∈ Icc (0 : ℝ) 1,
      lorentzSquare3 (lorentzFlowDerivative3 (a * s) p v) < 0 := by
    intro s hs
    rw [lorentz_flow_derivative_square3 _ _ _
      (flow_denominator_pos3 (parameter_segment_bounds3 ha hs) hp).ne']
    exact mul_neg_of_pos_of_neg
      (sq_pos_of_pos (flow_factor_pos3 (parameter_segment_bounds3 ha hs) hp)) hvn
  let f : ℝ → ℝ := fun s => lorentzFlowDerivative3 (a * s) p v 0
  have hcont : ContinuousOn f (Icc 0 1) := continuousOn_flow_derivative_time_parameter3 ha hp v
  have hz : 0 < f 0 := by simpa [f, lorentz_flow_derivative_zero3] using hv0
  have hone : 0 < f 1 := by
    by_contra h
    obtain ⟨s, hs, he⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1)
      hcont ⟨le_of_not_gt h, hz.le⟩
    have hn := hneg s hs
    change lorentzFlowDerivative3 (a * s) p v 0 = 0 at he
    unfold lorentzSquare3 at hn
    rw [he] at hn
    linarith [spatial_squared_nonneg3 (lorentzFlowDerivative3 (a * s) p v)]
  have hn := hneg 1 (by norm_num)
  simp only [mul_one] at hn
  have ht : 0 < lorentzFlowDerivative3 a p v 0 := by simpa [f] using hone
  have hs := spatial_radius_sq3 (lorentzFlowDerivative3 a p v)
  unfold lorentzSquare3 at hn
  nlinarith [spatial_radius_nonneg3 (lorentzFlowDerivative3 a p v)]

/-- Null and zero velocities follow by continuity from strictly future timelike velocities. -/
theorem lorentz_flow_derivative_future3 {a : ℝ} (ha : |a| < 1)
    {p v : LorentzPoint3} (hp : p ∈ closedLorentzDiamond3)
    (hv : spatialRadius3 v ≤ v 0) :
    spatialRadius3 (lorentzFlowDerivative3 a p v) ≤ lorentzFlowDerivative3 a p v 0 := by
  let u : ℕ → LorentzPoint3 := fun n => v + (1 / ((n : ℝ) + 1)) • lorentzPoint3 1 0 0
  have hu : Tendsto u atTop (𝓝 v) := by
    have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [zero_smul,add_zero] using
      (tendsto_const_nhds (x := v)).add (ht.smul_const (lorentzPoint3 1 0 0))
  have hL := (lorentzFlowDerivative3 a p).continuous.tendsto v |>.comp hu
  apply le_of_tendsto_of_tendsto' (continuous_spatial_radius3.tendsto _ |>.comp hL)
    ((lorentzCoordinateCLM3 0).continuous.tendsto _ |>.comp hL)
  intro n
  apply (lorentz_flow_derivative_timelike3 ha hp ?_).le
  have he : spatialRadius3 (u n) = spatialRadius3 v := by
    simp [u, spatialRadius3, spatialSquared3, lorentzPoint3]
  rw [he]
  change spatialRadius3 v < v 0 + 1 / ((n : ℝ) + 1) * 1
  have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
  linarith

theorem lorentz_flow_flat_proper_speed3 {a : ℝ} (ha : |a| < 1)
    {p v : LorentzPoint3} (hp : p ∈ closedLorentzDiamond3)
    (hv : spatialRadius3 v ≤ v 0) :
    flatProperSpeed3 (lorentzFlowDerivative3 a p v) = flowFactor3 a p * flatProperSpeed3 v := by
  have hl := flat_proper_speed_sq3 (lorentz_flow_derivative_future3 ha hp hv)
  have hr := flat_proper_speed_sq3 hv
  have he := lorentz_flow_derivative_square3 a p v (flow_denominator_pos3 ha hp).ne'
  unfold lorentzSquare3 at he
  have hf := (flow_factor_pos3 ha hp).le
  have hsp := flat_proper_speed_nonneg3 v
  nlinarith [flat_proper_speed_nonneg3 (lorentzFlowDerivative3 a p v), mul_nonneg hf hsp]

#print axioms lorentz_flow_derivative_zero3
#print axioms lorentz_flow_derivative_square3
#print axioms continuousOn_flow_derivative_time_parameter3
#print axioms lorentz_flow_derivative_timelike3
#print axioms lorentz_flow_derivative_future3
#print axioms lorentz_flow_flat_proper_speed3

end
end QuantyraNullCone
