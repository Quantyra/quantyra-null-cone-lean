import QuantyraNullCone.LorentzDensityWeight
import QuantyraNullCone.LorentzJacobian

namespace QuantyraNullCone
open Matrix
noncomputable section
set_option maxHeartbeats 1200000

def lorentzGramMatrix3 : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![-1,1,1]

theorem lorentz_gram_det3 : lorentzGramMatrix3.det = -1 := by
  norm_num [lorentzGramMatrix3,Matrix.det_fin_three,Fin.prod_univ_succ]

/-- The determinant is forced by the metric pullback, without an assumed volume law. -/
theorem lorentz_metric_linear_det3 (L : LorentzPoint3 →L[ℝ] LorentzPoint3)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ u v, a ^ 2 * lorentzBilinear3 u v = b ^ 2 * lorentzBilinear3 (L u) (L v)) :
    b ^ 3 * |L.det| = a ^ 3 := by
  let M : Matrix (Fin 3) (Fin 3) ℝ := (Matrix.toLpLin 2 2).symm L.toLinearMap
  have hm : M.toLpLin 2 2 = L.toLinearMap := (Matrix.toLpLin 2 2).apply_symm_apply _
  have hcol (i j : Fin 3) : L (PiLp.single 2 j 1) i = M i j := by
    have he := congrArg (fun f : LorentzPoint3 →ₗ[ℝ] LorentzPoint3 => f (PiLp.single 2 j 1) i) hm
    fin_cases i <;> fin_cases j <;>
      simpa [Matrix.toLpLin_apply,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using he.symm
  have heq : b ^ 2 • (M.transpose * lorentzGramMatrix3 * M) = a ^ 2 • lorentzGramMatrix3 := by
    ext i j
    have he := (h (PiLp.single 2 i 1) (PiLp.single 2 j 1)).symm
    simp only [lorentzBilinear3,hcol] at he
    fin_cases i <;> fin_cases j <;>
      simpa [lorentzGramMatrix3,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.transpose_apply,
        Matrix.smul_apply,smul_eq_mul,add_assoc] using he
  have hd := congrArg Matrix.det heq
  simp only [Matrix.det_smul,Fintype.card_fin,Matrix.det_mul,Matrix.det_transpose,lorentz_gram_det3] at hd
  have hdet : M.det = L.det := by
    rw [← LinearMap.det_toLpLin 2 M,hm]
  rw [hdet] at hd
  apply (sq_eq_sq₀ (mul_nonneg (pow_nonneg hb _) (abs_nonneg _)) (pow_nonneg ha _)).mp
  rw [mul_pow,sq_abs]
  nlinarith only [hd]

theorem density_metric_jacobian3 {rho sigma : LorentzPoint3 → ℝ}
    {p q : LorentzPoint3} (hr : 0 ≤ rho p) (hs : 0 ≤ sigma q)
    (L : LorentzPoint3 →L[ℝ] LorentzPoint3)
    (hm : ∀ u v, densityMetric3 rho p u v = densityMetric3 sigma q (L u) (L v)) :
    sigma q * |L.det| = rho p := by
  have ha : 0 ≤ densityTimeWeight3 rho p := Real.rpow_nonneg (div_nonneg hr lorentz_volume_pos3.le) _
  have hb : 0 ≤ densityTimeWeight3 sigma q := Real.rpow_nonneg (div_nonneg hs lorentz_volume_pos3.le) _
  have h := lorentz_metric_linear_det3 L ha hb (fun u v => by
    rw [density_time_weight_sq3 hr,density_time_weight_sq3 hs]
    exact hm u v)
  rw [density_time_weight_cube3 hs,density_time_weight_cube3 hr] at h
  apply (div_left_inj' lorentz_volume_pos3.ne').mp
  simpa only [div_mul_eq_mul_div] using h

#print axioms lorentz_gram_det3
#print axioms lorentz_metric_linear_det3
#print axioms density_metric_jacobian3

end
end QuantyraNullCone
