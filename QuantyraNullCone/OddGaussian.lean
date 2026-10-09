import QuantyraNullCone.DegreeLaw
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace QuantyraNullCone

open MeasureTheory

noncomputable def oddGaussian (t : ℝ) : ℝ := t * Real.exp (-(t ^ 2))

noncomputable def lowerProfile (h x : ℝ) : ℝ := oddGaussian ((x - 1 / 2) / h)

theorem odd_gaussian_smooth : ContDiff ℝ ⊤ oddGaussian := by
  unfold oddGaussian
  fun_prop

theorem odd_gaussian_odd (t : ℝ) : oddGaussian (-t) = -oddGaussian t := by
  simp [oddGaussian]

theorem odd_gaussian_abs_le (t : ℝ) : |oddGaussian t| ≤ 1 / 2 := by
  have hExp := Real.add_one_le_exp (t ^ 2)
  have hAbs : 2 * |t| ≤ Real.exp (t ^ 2) := by
    nlinarith [sq_nonneg (|t| - 1), sq_abs t]
  have hMul := mul_le_mul_of_nonneg_right hAbs (Real.exp_pos (-(t ^ 2))).le
  have hInv : Real.exp (t ^ 2) * Real.exp (-(t ^ 2)) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [hInv] at hMul
  simp only [oddGaussian, abs_mul, abs_of_pos (Real.exp_pos _)]
  linarith

theorem odd_gaussian_hasDerivAt (t : ℝ) :
    HasDerivAt oddGaussian ((1 - 2 * t ^ 2) * Real.exp (-(t ^ 2))) t := by
  have h := (hasDerivAt_id t).mul (((hasDerivAt_id t).pow 2).neg.exp)
  convert h using 1
  dsimp
  ring

theorem odd_gaussian_deriv_bound (t : ℝ) :
    |(1 - 2 * t ^ 2) * Real.exp (-(t ^ 2))| ≤ 1 := by
  have hPos := Real.exp_pos (-(t ^ 2))
  have hSmall : Real.exp (-(t ^ 2)) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (neg_nonpos.mpr (sq_nonneg t))
  have hHalf := Real.add_one_le_exp (t ^ 2 / 2)
  have hHalfSq := pow_le_pow_left₀ (by positivity : 0 ≤ t ^ 2 / 2 + 1) hHalf 2
  have hExpSq : Real.exp (t ^ 2 / 2) ^ 2 = Real.exp (t ^ 2) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hExpSq] at hHalfSq
  have hLarge : 2 * t ^ 2 - 1 ≤ Real.exp (t ^ 2) := by
    nlinarith [sq_nonneg (t ^ 2 - 2)]
  have hLower := mul_le_mul_of_nonneg_right hLarge hPos.le
  have hInv : Real.exp (t ^ 2) * Real.exp (-(t ^ 2)) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [hInv] at hLower
  have hUpper := mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg t] : 1 - 2 * t ^ 2 ≤ 1) hPos.le
  exact abs_le.mpr (by constructor <;> nlinarith only [hLower, hUpper, hSmall])

theorem odd_gaussian_lipschitz (x y : ℝ) : |oddGaussian x - oddGaussian y| ≤ |x - y| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t (_ : t ∈ (Set.univ : Set ℝ)) => (odd_gaussian_hasDerivAt t).hasDerivWithinAt)
    (fun t (_ : t ∈ (Set.univ : Set ℝ)) => by
      simpa only [Real.norm_eq_abs] using odd_gaussian_deriv_bound t)
    convex_univ (Set.mem_univ y) (Set.mem_univ x)
  simpa only [Real.norm_eq_abs, one_mul] using h

theorem lower_profile_smooth (h : ℝ) : ContDiff ℝ ⊤ (lowerProfile h) := by
  unfold lowerProfile oddGaussian
  fun_prop

theorem lower_profile_abs_le (h x : ℝ) : |lowerProfile h x| ≤ 1 / 2 :=
  odd_gaussian_abs_le _

theorem lower_profile_lipschitz {h : ℝ} (hh : 0 < h) (x y : ℝ) :
    |lowerProfile h x - lowerProfile h y| ≤ |x - y| / h := by
  calc
    _ ≤ |(x - 1 / 2) / h - (y - 1 / 2) / h| := odd_gaussian_lipschitz _ _
    _ = _ := by
      rw [← sub_div, show x - 1 / 2 - (y - 1 / 2) = x - y by ring, abs_div, abs_of_pos hh]

theorem lower_profile_primitive {h : ℝ} (hh : h ≠ 0) (x : ℝ) :
    HasDerivAt (fun t : ℝ => -(h / 2) * Real.exp (-(((t - 1 / 2) / h) ^ 2)))
      (lowerProfile h x) x := by
  have hD := (((((hasDerivAt_id x).sub_const (1 / 2)).div_const h).pow 2).neg.exp).const_mul (-(h / 2))
  convert hD using 1
  dsimp [lowerProfile, oddGaussian]
  field_simp [hh]

theorem lower_profile_integral_zero {h : ℝ} (hh : h ≠ 0) :
    (∫ x in (0 : ℝ)..1, lowerProfile h x) = 0 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => lower_profile_primitive hh x) ((lower_profile_smooth h).continuous.intervalIntegrable 0 1)]
  have hSq : ((1 - (1 / 2 : ℝ)) / h) ^ 2 = ((0 - (1 / 2 : ℝ)) / h) ^ 2 := by ring
  rw [hSq]
  ring

#print axioms odd_gaussian_smooth
#print axioms odd_gaussian_odd
#print axioms odd_gaussian_abs_le
#print axioms odd_gaussian_hasDerivAt
#print axioms odd_gaussian_deriv_bound
#print axioms odd_gaussian_lipschitz
#print axioms lower_profile_smooth
#print axioms lower_profile_abs_le
#print axioms lower_profile_lipschitz
#print axioms lower_profile_primitive
#print axioms lower_profile_integral_zero

end QuantyraNullCone
