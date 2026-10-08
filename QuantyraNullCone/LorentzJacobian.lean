import QuantyraNullCone.LorentzDerivative
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace QuantyraNullCone

noncomputable section

def flowDenominatorGradient3 (a : ℝ) (p : LorentzPoint3) : Fin 3 → ℝ :=
  ![2 * a * (1 + a * p 0), -2 * a ^ 2 * p 1, -2 * a ^ 2 * p 2]

def flowNumeratorGradient3 (a : ℝ) (p : LorentzPoint3) : Fin 3 → ℝ :=
  ![1 + a ^ 2 + 2 * a * p 0, -2 * a * p 1, -2 * a * p 2]

def lorentzFlowMatrix3 (a : ℝ) (p : LorentzPoint3) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => ![
    (flowNumeratorGradient3 a p j * flowDenominator3 a p -
      flowTimeNumerator3 a p * flowDenominatorGradient3 a p j) / flowDenominator3 a p ^ 2,
    (1 - a ^ 2) * ((if j = 1 then flowDenominator3 a p else 0) -
      p 1 * flowDenominatorGradient3 a p j) / flowDenominator3 a p ^ 2,
    (1 - a ^ 2) * ((if j = 2 then flowDenominator3 a p else 0) -
      p 2 * flowDenominatorGradient3 a p j) / flowDenominator3 a p ^ 2] i

theorem lorentz_flow_derivative_matrix3 (a : ℝ) (p : LorentzPoint3)
    (hD : flowDenominator3 a p ≠ 0) :
    (lorentzFlowDerivative3 a p).toLinearMap = (lorentzFlowMatrix3 a p).toLpLin 2 2 := by
  ext v i
  fin_cases i <;>
    simp [lorentzFlowDerivative3, flowDerivativeCoordinates3, scalarQuotientDerivative3,
      flowNumeratorDerivative3, flowDenominatorDerivative3, lorentzCoordinateCLM3,
      lorentzFlowMatrix3, flowNumeratorGradient3, flowDenominatorGradient3,
      Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, smul_eq_mul] <;>
    field_simp [hD] <;> ring

theorem lorentz_flow_matrix_det3 (a : ℝ) (p : LorentzPoint3)
    (hD : flowDenominator3 a p ≠ 0) : (lorentzFlowMatrix3 a p).det = flowFactor3 a p ^ 3 := by
  rw [Matrix.det_fin_three]
  dsimp [lorentzFlowMatrix3, flowNumeratorGradient3, flowDenominatorGradient3, flowFactor3]
  field_simp [hD]
  unfold flowTimeNumerator3 flowDenominator3 spatialSquared3
  ring

/-- Determinant of the actual Cartesian Frechet derivative. -/
theorem lorentz_flow_derivative_det3 (a : ℝ) (p : LorentzPoint3)
    (hD : flowDenominator3 a p ≠ 0) : (lorentzFlowDerivative3 a p).det = flowFactor3 a p ^ 3 := by
  change (lorentzFlowDerivative3 a p).toLinearMap.det = _
  rw [lorentz_flow_derivative_matrix3 a p hD, LinearMap.det_toLpLin]
  exact lorentz_flow_matrix_det3 a p hD

theorem lorentz_flow_derivative_bilinear3 (a : ℝ) (p u v : LorentzPoint3)
    (hD : flowDenominator3 a p ≠ 0) :
    lorentzBilinear3 (lorentzFlowDerivative3 a p u) (lorentzFlowDerivative3 a p v) =
      flowFactor3 a p ^ 2 * lorentzBilinear3 u v := by
  simp only [lorentzBilinear3]
  simp [lorentzFlowDerivative3, flowDerivativeCoordinates3, scalarQuotientDerivative3,
    flowNumeratorDerivative3, flowDenominatorDerivative3, lorentzCoordinateCLM3,
    smul_eq_mul, flowFactor3]
  field_simp [hD]
  unfold flowTimeNumerator3 flowDenominator3 spatialSquared3
  ring

#print axioms lorentz_flow_derivative_matrix3
#print axioms lorentz_flow_derivative_det3
#print axioms lorentz_flow_derivative_bilinear3

end

end QuantyraNullCone
