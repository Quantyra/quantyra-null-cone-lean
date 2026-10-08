import QuantyraNullCone.LorentzGaugeBounds
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Normed.Lp.Matrix

namespace QuantyraNullCone

noncomputable section

def lorentzCoordinateCLM3 (i : Fin 3) : LorentzPoint3 →L[ℝ] ℝ :=
  PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 3 => ℝ) i

def flowDenominatorDerivative3 (a : ℝ) (p : LorentzPoint3) : LorentzPoint3 →L[ℝ] ℝ :=
  (2 * a * (1 + a * p 0)) • lorentzCoordinateCLM3 0 -
    (2 * a ^ 2 * p 1) • lorentzCoordinateCLM3 1 -
    (2 * a ^ 2 * p 2) • lorentzCoordinateCLM3 2

def flowNumeratorDerivative3 (a : ℝ) (p : LorentzPoint3) : LorentzPoint3 →L[ℝ] ℝ :=
  (1 + a ^ 2 + 2 * a * p 0) • lorentzCoordinateCLM3 0 -
    (2 * a * p 1) • lorentzCoordinateCLM3 1 -
    (2 * a * p 2) • lorentzCoordinateCLM3 2

theorem hasFDerivAt_flow_denominator3 (a : ℝ) (p : LorentzPoint3) :
    HasFDerivAt (flowDenominator3 a) (flowDenominatorDerivative3 a p) p := by
  have h0 := (lorentzCoordinateCLM3 0).hasFDerivAt (x := p)
  have h1 := (lorentzCoordinateCLM3 1).hasFDerivAt (x := p)
  have h2 := (lorentzCoordinateCLM3 2).hasFDerivAt (x := p)
  convert (((hasFDerivAt_const (1 : ℝ) p).add (h0.const_mul a)).pow 2).sub
    (((h1.pow 2).add (h2.pow 2)).const_mul (a ^ 2)) using 1
  ext v
  simp [flowDenominatorDerivative3, lorentzCoordinateCLM3]
  ring

theorem hasFDerivAt_flow_numerator3 (a : ℝ) (p : LorentzPoint3) :
    HasFDerivAt (flowTimeNumerator3 a) (flowNumeratorDerivative3 a p) p := by
  have h0 := (lorentzCoordinateCLM3 0).hasFDerivAt (x := p)
  have h1 := (lorentzCoordinateCLM3 1).hasFDerivAt (x := p)
  have h2 := (lorentzCoordinateCLM3 2).hasFDerivAt (x := p)
  convert ((h0.add_const a).mul ((hasFDerivAt_const (1 : ℝ) p).add (h0.const_mul a))).sub
    (((h1.pow 2).add (h2.pow 2)).const_mul a) using 1
  ext v
  simp [flowNumeratorDerivative3, lorentzCoordinateCLM3]
  ring

def scalarQuotientDerivative3 (f d : ℝ) (f' d' : LorentzPoint3 →L[ℝ] ℝ) :
    LorentzPoint3 →L[ℝ] ℝ := d⁻¹ • f' - (f / d ^ 2) • d'

theorem hasFDerivAt_scalar_quotient3 {f d : LorentzPoint3 → ℝ}
    {f' d' : LorentzPoint3 →L[ℝ] ℝ} {p : LorentzPoint3}
    (hf : HasFDerivAt f f' p) (hd : HasFDerivAt d d' p) (hNonzero : d p ≠ 0) :
    HasFDerivAt (fun q => f q / d q) (scalarQuotientDerivative3 (f p) (d p) f' d') p := by
  have hInv := (hasDerivAt_inv hNonzero).comp_hasFDerivAt p hd
  change HasFDerivAt (fun q => f q * (d q)⁻¹) _ p
  apply (hf.fun_mul hInv).congr_fderiv
  ext v
  simp [scalarQuotientDerivative3, div_eq_mul_inv, smul_eq_mul]
  ring

def flowDerivativeCoordinates3 (a : ℝ) (p : LorentzPoint3) : Fin 3 → (LorentzPoint3 →L[ℝ] ℝ) :=
  ![scalarQuotientDerivative3 (flowTimeNumerator3 a p) (flowDenominator3 a p)
      (flowNumeratorDerivative3 a p) (flowDenominatorDerivative3 a p),
    scalarQuotientDerivative3 ((1 - a ^ 2) * p 1) (flowDenominator3 a p)
      ((1 - a ^ 2) • lorentzCoordinateCLM3 1) (flowDenominatorDerivative3 a p),
    scalarQuotientDerivative3 ((1 - a ^ 2) * p 2) (flowDenominator3 a p)
      ((1 - a ^ 2) • lorentzCoordinateCLM3 2) (flowDenominatorDerivative3 a p)]

def lorentzFlowDerivative3 (a : ℝ) (p : LorentzPoint3) : LorentzPoint3 →L[ℝ] LorentzPoint3 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (flowDerivativeCoordinates3 a p))

theorem hasFDerivAt_lorentz_flow3 (a : ℝ) (p : LorentzPoint3)
    (hD : flowDenominator3 a p ≠ 0) : HasFDerivAt (lorentzFlow3 a) (lorentzFlowDerivative3 a p) p := by
  let phi : Fin 3 → LorentzPoint3 → ℝ := fun i q =>
    ![flowTimeNumerator3 a q / flowDenominator3 a q,
      (1 - a ^ 2) * q 1 / flowDenominator3 a q,
      (1 - a ^ 2) * q 2 / flowDenominator3 a q] i
  have hCoordinates : ∀ i, HasFDerivAt (phi i) (flowDerivativeCoordinates3 a p i) p := by
    intro i
    fin_cases i
    · exact hasFDerivAt_scalar_quotient3 (hasFDerivAt_flow_numerator3 a p)
        (hasFDerivAt_flow_denominator3 a p) hD
    · exact hasFDerivAt_scalar_quotient3 ((lorentzCoordinateCLM3 1).hasFDerivAt.const_mul (1 - a ^ 2))
        (hasFDerivAt_flow_denominator3 a p) hD
    · exact hasFDerivAt_scalar_quotient3 ((lorentzCoordinateCLM3 2).hasFDerivAt.const_mul (1 - a ^ 2))
        (hasFDerivAt_flow_denominator3 a p) hD
  have hPi := hasFDerivAt_pi.mpr hCoordinates
  have hCompose := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap.hasFDerivAt.comp p hPi
  convert hCompose using 1
  · funext q
    ext i
    fin_cases i <;> simp [phi, lorentzFlow3, lorentzPoint3, flowFactor3, div_eq_mul_inv,
      mul_assoc, mul_comm, mul_left_comm]

#print axioms hasFDerivAt_flow_denominator3
#print axioms hasFDerivAt_flow_numerator3
#print axioms hasFDerivAt_lorentz_flow3

end

end QuantyraNullCone
