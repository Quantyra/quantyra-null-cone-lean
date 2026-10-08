import QuantyraNullCone.LorentzInverse
import Mathlib.Analysis.Calculus.ContDiff.Operations

namespace QuantyraNullCone

noncomputable section

@[fun_prop] theorem contDiff_lorentz_coordinate3 (i : Fin 3) :
    ContDiff ℝ ⊤ (fun p : LorentzPoint3 => p i) :=
  (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 3 => ℝ) i).contDiff

theorem null_factor_upper3 {a z : ℝ} (hz : |z| ≤ 1) : 1 + a * z ≤ 1 + |a| := by
  have hAbs : |a * z| ≤ |a| := by
    rw [abs_mul]
    simpa using mul_le_mul_of_nonneg_left hz (abs_nonneg a)
  linarith [le_abs_self (a * z)]

theorem flow_denominator_upper3 {a : ℝ} (ha : |a| < 1) {p : LorentzPoint3}
    (hp : p ∈ closedLorentzDiamond3) : flowDenominator3 a p ≤ (1 + |a|) ^ 2 := by
  obtain ⟨hu, hv⟩ := closed_lorentz_null_bounds3 hp
  rw [flow_denominator_null_factors3, pow_two]
  exact mul_le_mul (null_factor_upper3 hu) (null_factor_upper3 hv)
    (le_of_lt ((sub_pos.mpr ha).trans_le (null_factor_lower3 hv)))
    (by positivity)

theorem gauge_parameter_abs3 : |-gaugeParameter3| < 1 := by norm_num [gaugeParameter3]

theorem gauge_denominator_bounds3 {p : LorentzPoint3} (hp : p ∈ closedLorentzDiamond3) :
    (99 / 100 : ℝ) ^ 2 ≤ flowDenominator3 (-gaugeParameter3) p ∧
      flowDenominator3 (-gaugeParameter3) p ≤ (101 / 100 : ℝ) ^ 2 := by
  constructor
  · have h := flow_denominator_lower3 gauge_parameter_abs3 hp
    norm_num [gaugeParameter3] at h ⊢
    exact h
  · have h := flow_denominator_upper3 gauge_parameter_abs3 hp
    norm_num [gaugeParameter3] at h ⊢
    exact h

theorem gauge_factor_bounds3 {p : LorentzPoint3} (hp : p ∈ closedLorentzDiamond3) :
    (9 / 10 : ℝ) ≤ flowFactor3 (-gaugeParameter3) p ∧
      flowFactor3 (-gaugeParameter3) p ≤ (11 / 10 : ℝ) := by
  obtain ⟨hLower, hUpper⟩ := gauge_denominator_bounds3 hp
  have hPos := flow_denominator_pos3 gauge_parameter_abs3 hp
  unfold flowFactor3
  constructor
  · apply (le_div_iff₀ hPos).mpr
    norm_num [gaugeParameter3] at *
    linarith
  · apply (div_le_iff₀ hPos).mpr
    norm_num [gaugeParameter3] at *
    linarith

theorem gauge_density_bounds3 {p : LorentzPoint3} (hp : p ∈ closedLorentzDiamond3) :
    (1 / 2 : ℝ) ≤ gaugeDensity3 p ∧ gaugeDensity3 p ≤ 3 / 2 := by
  obtain ⟨hLower, hUpper⟩ := gauge_factor_bounds3 hp
  have hLo := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 9 / 10) hLower 3
  have hHi := pow_le_pow_left₀ (by linarith : 0 ≤ flowFactor3 (-gaugeParameter3) p) hUpper 3
  change (1 / 2 : ℝ) ≤ flowFactor3 (-gaugeParameter3) p ^ 3 ∧
    flowFactor3 (-gaugeParameter3) p ^ 3 ≤ 3 / 2
  constructor <;> nlinarith

def gaugeSmoothDomain3 : Set LorentzPoint3 := {p | 0 < flowDenominator3 (-gaugeParameter3) p}

theorem gauge_smooth_domain_open3 : IsOpen gaugeSmoothDomain3 := by
  unfold gaugeSmoothDomain3
  apply isOpen_lt continuous_const
  unfold flowDenominator3 spatialSquared3
  fun_prop

theorem gauge_smooth_domain_contains3 : closedLorentzDiamond3 ⊆ gaugeSmoothDomain3 :=
  fun _ hp => flow_denominator_pos3 gauge_parameter_abs3 hp

theorem gauge_density_smooth3 : ContDiffOn ℝ ⊤ gaugeDensity3 gaugeSmoothDomain3 := by
  unfold gaugeDensity3 flowFactor3
  apply ContDiffOn.pow
  apply ContDiffOn.div contDiffOn_const
  · have h : ContDiff ℝ ⊤ (flowDenominator3 (-gaugeParameter3)) := by
      unfold flowDenominator3 spatialSquared3
      fun_prop
    exact h.contDiffOn
  · intro p hp
    exact (show 0 < flowDenominator3 (-gaugeParameter3) p from hp).ne'

#print axioms flow_denominator_upper3
#print axioms gauge_density_bounds3
#print axioms gauge_density_smooth3

end

end QuantyraNullCone
