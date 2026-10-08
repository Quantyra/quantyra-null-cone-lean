import QuantyraNullCone.LorentzDerivative
import QuantyraNullCone.LorentzPreservation
import QuantyraNullCone.LorentzChronology
import Mathlib.Analysis.Calculus.ContDiff.WithLp

namespace QuantyraNullCone

noncomputable section

def flowSmoothDomain3 (a : ℝ) : Set LorentzPoint3 := {p | 0 < flowDenominator3 a p}

theorem flow_smooth_domain_open3 (a : ℝ) : IsOpen (flowSmoothDomain3 a) := by
  unfold flowSmoothDomain3
  apply isOpen_lt continuous_const
  unfold flowDenominator3 spatialSquared3
  fun_prop

theorem flow_smooth_domain_contains3 {a : ℝ} (ha : |a| < 1) :
    closedLorentzDiamond3 ⊆ flowSmoothDomain3 a := fun _ hp => flow_denominator_pos3 ha hp

theorem lorentz_flow_smooth3 (a : ℝ) : ContDiffOn ℝ ⊤ (lorentzFlow3 a) (flowSmoothDomain3 a) := by
  have hD : ContDiff ℝ ⊤ (flowDenominator3 a) := by
    unfold flowDenominator3 spatialSquared3
    fun_prop
  have hN : ContDiff ℝ ⊤ (flowTimeNumerator3 a) := by
    unfold flowTimeNumerator3 spatialSquared3
    fun_prop
  have hNonzero : ∀ p ∈ flowSmoothDomain3 a, flowDenominator3 a p ≠ 0 :=
    fun p hp => (show 0 < flowDenominator3 a p from hp).ne'
  have hFactor : ContDiffOn ℝ ⊤ (flowFactor3 a) (flowSmoothDomain3 a) :=
    contDiffOn_const.fun_div hD.contDiffOn hNonzero
  apply (contDiffOn_piLp 2).mpr
  intro i
  fin_cases i
  · change ContDiffOn ℝ ⊤ (fun p => flowTimeNumerator3 a p / flowDenominator3 a p) _
    exact hN.contDiffOn.fun_div hD.contDiffOn hNonzero
  · change ContDiffOn ℝ ⊤ (fun p => flowFactor3 a p * p 1) _
    exact hFactor.mul (contDiff_lorentz_coordinate3 1).contDiffOn
  · change ContDiffOn ℝ ⊤ (fun p => flowFactor3 a p * p 2) _
    exact hFactor.mul (contDiff_lorentz_coordinate3 2).contDiffOn

theorem lorentz_flow_closed_bijective3 {a : ℝ} (ha : |a| < 1) :
    Set.BijOn (lorentzFlow3 a) closedLorentzDiamond3 closedLorentzDiamond3 := by
  refine ⟨fun _ hp => lorentz_flow_preserves_closed3 ha hp, ?_, ?_⟩
  · intro p hp q hq hEq
    have h := congrArg (lorentzFlow3 (-a)) hEq
    rw [lorentz_flow_inverse_closed3 ha hp, lorentz_flow_inverse_closed3 ha hq] at h
    exact h
  · intro q hq
    have hNeg : |-a| < 1 := by simpa using ha
    refine ⟨lorentzFlow3 (-a) q, lorentz_flow_preserves_closed3 hNeg hq, ?_⟩
    simpa only [neg_neg] using lorentz_flow_inverse_closed3 hNeg hq

theorem lorentz_flow_smooth_automorphism3 {a : ℝ} (ha : |a| < 1) :
    Set.BijOn (lorentzFlow3 a) closedLorentzDiamond3 closedLorentzDiamond3 ∧
    (∃ U : Set LorentzPoint3, IsOpen U ∧ closedLorentzDiamond3 ⊆ U ∧
      ContDiffOn ℝ ⊤ (lorentzFlow3 a) U) ∧
    (∀ p ∈ closedLorentzDiamond3, lorentzFlow3 (-a) (lorentzFlow3 a p) = p) ∧
    (∀ p ∈ closedLorentzDiamond3, ∀ q ∈ closedLorentzDiamond3,
      chronological3 (lorentzFlow3 a p) (lorentzFlow3 a q) ↔ chronological3 p q) :=
  ⟨lorentz_flow_closed_bijective3 ha,
    ⟨flowSmoothDomain3 a, flow_smooth_domain_open3 a, flow_smooth_domain_contains3 ha,
      lorentz_flow_smooth3 a⟩,
    fun _ hp => lorentz_flow_inverse_closed3 ha hp,
    fun _ hp _ hq => lorentz_flow_chronological_iff3 ha hp hq⟩

#print axioms lorentz_flow_smooth3
#print axioms lorentz_flow_smooth_automorphism3

end

end QuantyraNullCone
