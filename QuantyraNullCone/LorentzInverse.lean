import QuantyraNullCone.LorentzFlow
import QuantyraNullCone.LorentzMeasures

namespace QuantyraNullCone

noncomputable section

theorem flow_inverse_denominator_identity3 (a : ℝ) (p : LorentzPoint3)
    (hD : flowDenominator3 a p ≠ 0) :
    flowDenominator3 (-a) (lorentzFlow3 a p) * flowDenominator3 a p = (1 - a ^ 2) ^ 2 := by
  have hD' : (1 + a * p 0) ^ 2 - a ^ 2 * spatialSquared3 p ≠ 0 := hD
  rw [flowDenominator3, lorentz_flow_time3, spatial_squared_flow3]
  dsimp [flowTimeNumerator3, flowFactor3, flowDenominator3]
  field_simp [hD']
  ring

theorem flow_inverse_denominator3 (a : ℝ) (p : LorentzPoint3)
    (hD : flowDenominator3 a p ≠ 0) :
    flowDenominator3 (-a) (lorentzFlow3 a p) = (1 - a ^ 2) ^ 2 / flowDenominator3 a p :=
  (eq_div_iff hD).mpr (flow_inverse_denominator_identity3 a p hD)

theorem flow_inverse_factor3 (a : ℝ) (p : LorentzPoint3)
    (hD : flowDenominator3 a p ≠ 0) (hA : 1 - a ^ 2 ≠ 0) :
    flowFactor3 (-a) (lorentzFlow3 a p) * flowFactor3 a p = 1 := by
  unfold flowFactor3
  rw [flow_inverse_denominator3 a p hD]
  field_simp [hD, hA]

/-- Cartesian inverse identity includes the spatial axis; it never divides by a radius. -/
theorem lorentz_flow_inverse3 (a : ℝ) (p : LorentzPoint3)
    (hD : flowDenominator3 a p ≠ 0) (hA : 1 - a ^ 2 ≠ 0) :
    lorentzFlow3 (-a) (lorentzFlow3 a p) = p := by
  ext i
  fin_cases i
  · change lorentzFlow3 (-a) (lorentzFlow3 a p) 0 = p 0
    rw [lorentz_flow_time3, flow_inverse_denominator3 a p hD]
    unfold flowTimeNumerator3
    rw [lorentz_flow_time3, spatial_squared_flow3]
    unfold flowFactor3
    field_simp [hD, hA]
    unfold flowTimeNumerator3 flowDenominator3
    ring
  · change lorentzFlow3 (-a) (lorentzFlow3 a p) 1 = p 1
    rw [lorentz_flow_x3, lorentz_flow_x3, ← mul_assoc, flow_inverse_factor3 a p hD hA, one_mul]
  · change lorentzFlow3 (-a) (lorentzFlow3 a p) 2 = p 2
    rw [lorentz_flow_y3, lorentz_flow_y3, ← mul_assoc, flow_inverse_factor3 a p hD hA, one_mul]

theorem lorentz_flow_inverse_closed3 {a : ℝ} (ha : |a| < 1) {p : LorentzPoint3}
    (hp : p ∈ closedLorentzDiamond3) : lorentzFlow3 (-a) (lorentzFlow3 a p) = p := by
  have hA : 1 - a ^ 2 ≠ 0 := (sub_pos.mpr ((sq_lt_one_iff_abs_lt_one a).mpr ha)).ne'
  exact lorentz_flow_inverse3 a p (flow_denominator_pos3 ha hp).ne' hA

#print axioms flow_inverse_denominator_identity3
#print axioms flow_inverse_denominator3
#print axioms flow_inverse_factor3
#print axioms lorentz_flow_inverse3
#print axioms lorentz_flow_inverse_closed3

end

end QuantyraNullCone
