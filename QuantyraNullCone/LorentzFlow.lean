import QuantyraNullCone.LorentzDiamond
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace QuantyraNullCone

noncomputable section

def flowDenominator3 (a : ℝ) (p : LorentzPoint3) : ℝ :=
  (1 + a * p 0) ^ 2 - a ^ 2 * spatialSquared3 p
def flowTimeNumerator3 (a : ℝ) (p : LorentzPoint3) : ℝ :=
  (p 0 + a) * (1 + a * p 0) - a * spatialSquared3 p
def flowFactor3 (a : ℝ) (p : LorentzPoint3) : ℝ := (1 - a ^ 2) / flowDenominator3 a p
def lorentzFlow3 (a : ℝ) (p : LorentzPoint3) : LorentzPoint3 :=
  lorentzPoint3 (flowTimeNumerator3 a p / flowDenominator3 a p)
    (flowFactor3 a p * p 1) (flowFactor3 a p * p 2)

def gaugeParameter3 : ℝ := 1 / 100
def gaugeDensity3 (p : LorentzPoint3) : ℝ := flowFactor3 (-gaugeParameter3) p ^ 3

theorem lorentz_flow_time3 (a : ℝ) (p : LorentzPoint3) :
    lorentzFlow3 a p 0 = flowTimeNumerator3 a p / flowDenominator3 a p := rfl
theorem lorentz_flow_x3 (a : ℝ) (p : LorentzPoint3) :
    lorentzFlow3 a p 1 = flowFactor3 a p * p 1 := rfl
theorem lorentz_flow_y3 (a : ℝ) (p : LorentzPoint3) :
    lorentzFlow3 a p 2 = flowFactor3 a p * p 2 := rfl

theorem lorentz_flow_zero3 (p : LorentzPoint3) : lorentzFlow3 0 p = p := by
  ext i
  fin_cases i <;>
    simp [lorentzFlow3, lorentzPoint3, flowTimeNumerator3, flowDenominator3, flowFactor3]

theorem spatial_squared_flow3 (a : ℝ) (p : LorentzPoint3) :
    spatialSquared3 (lorentzFlow3 a p) = flowFactor3 a p ^ 2 * spatialSquared3 p := by
  unfold spatialSquared3
  rw [lorentz_flow_x3, lorentz_flow_y3]
  ring

theorem spatial_radius_flow3 (a : ℝ) (p : LorentzPoint3) :
    spatialRadius3 (lorentzFlow3 a p) = |flowFactor3 a p| * spatialRadius3 p := by
  unfold spatialRadius3
  rw [spatial_squared_flow3, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

theorem flow_denominator_null_factors3 (a : ℝ) (p : LorentzPoint3) :
    flowDenominator3 a p =
      (1 + a * (p 0 + spatialRadius3 p)) * (1 + a * (p 0 - spatialRadius3 p)) := by
  unfold flowDenominator3
  rw [← spatial_radius_sq3 p]
  ring

theorem closed_lorentz_null_bounds3 {p : LorentzPoint3} (hp : p ∈ closedLorentzDiamond3) :
    |p 0 + spatialRadius3 p| ≤ 1 ∧ |p 0 - spatialRadius3 p| ≤ 1 := by
  change |p 0| + spatialRadius3 p ≤ 1 at hp
  have htLower := neg_abs_le (p 0)
  have htUpper := le_abs_self (p 0)
  have hr := spatial_radius_nonneg3 p
  constructor <;> apply abs_le.mpr <;> constructor <;> linarith

theorem null_factor_lower3 {a z : ℝ} (hz : |z| ≤ 1) : 1 - |a| ≤ 1 + a * z := by
  have hAbs : |a * z| ≤ |a| := by
    rw [abs_mul]
    simpa using mul_le_mul_of_nonneg_left hz (abs_nonneg a)
  have hLower := neg_abs_le (a * z)
  linarith

theorem flow_denominator_lower3 {a : ℝ} (ha : |a| < 1) {p : LorentzPoint3}
    (hp : p ∈ closedLorentzDiamond3) : (1 - |a|) ^ 2 ≤ flowDenominator3 a p := by
  obtain ⟨hu, hv⟩ := closed_lorentz_null_bounds3 hp
  have hU := null_factor_lower3 (a := a) hu
  have hV := null_factor_lower3 (a := a) hv
  have hNonneg : 0 ≤ 1 - |a| := sub_nonneg.mpr ha.le
  rw [flow_denominator_null_factors3, pow_two]
  exact mul_le_mul hU hV hNonneg (hNonneg.trans hU)

theorem flow_denominator_pos3 {a : ℝ} (ha : |a| < 1) {p : LorentzPoint3}
    (hp : p ∈ closedLorentzDiamond3) : 0 < flowDenominator3 a p :=
  (sq_pos_of_pos (sub_pos.mpr ha)).trans_le (flow_denominator_lower3 ha hp)

theorem flow_factor_pos3 {a : ℝ} (ha : |a| < 1) {p : LorentzPoint3}
    (hp : p ∈ closedLorentzDiamond3) : 0 < flowFactor3 a p := by
  have hSquare : a ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one a).mpr ha
  exact div_pos (sub_pos.mpr hSquare) (flow_denominator_pos3 ha hp)

#print axioms lorentz_flow_zero3
#print axioms spatial_radius_flow3
#print axioms flow_denominator_null_factors3
#print axioms closed_lorentz_null_bounds3
#print axioms flow_denominator_lower3
#print axioms flow_denominator_pos3
#print axioms flow_factor_pos3

end

end QuantyraNullCone
