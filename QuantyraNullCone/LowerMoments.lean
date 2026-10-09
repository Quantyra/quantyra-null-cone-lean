import QuantyraNullCone.LowerSeparation
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace QuantyraNullCone

open MeasureTheory

theorem gaussian_second_integrable : Integrable (fun t : ℝ => t ^ 2 * Real.exp (-2 * t ^ 2)) := by
  simpa only [Real.rpow_two] using
    (integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 2) (by norm_num : (-1 : ℝ) < 2))

theorem odd_gaussian_square_integrable : Integrable (fun t : ℝ => oddGaussian t ^ 2) := by
  simpa only [odd_gaussian_square, neg_mul] using gaussian_second_integrable

/-- Gaussian second moment by integration by parts, with all three product
integrability conditions proved. -/
theorem odd_gaussian_second_moment :
    (∫ t : ℝ, oddGaussian t ^ 2) = Real.sqrt (Real.pi / 2) / 4 := by
  let g : ℝ → ℝ := fun t => Real.exp (-2 * t ^ 2)
  let g' : ℝ → ℝ := fun t => -4 * t * Real.exp (-2 * t ^ 2)
  have hDeriv (t : ℝ) : HasDerivAt g (g' t) t := by
    have h := (((hasDerivAt_id t).pow 2).const_mul (-2)).exp
    convert h using 1
    dsimp [g']
    ring
  have hEq : (fun t : ℝ => t * g' t) = (fun t => -4 * (t ^ 2 * Real.exp (-2 * t ^ 2))) := by
    funext t
    dsimp [g']
    ring
  have hUv : Integrable ((fun t : ℝ => t) * g') := by
    change Integrable (fun t : ℝ => t * g' t)
    rw [hEq]
    exact gaussian_second_integrable.const_mul (-4)
  have hG : Integrable ((fun _ : ℝ => (1 : ℝ)) * g) := by
    change Integrable (fun t : ℝ => 1 * Real.exp (-2 * t ^ 2))
    simpa only [one_mul] using integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 2)
  have hTG : Integrable ((fun t : ℝ => t) * g) :=
    integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 2)
  have hParts := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun t : ℝ => t) (v := g) (u' := fun _ => (1 : ℝ)) (v' := g')
    (fun t _ => hasDerivAt_id t) (fun t _ => hDeriv t) hUv hG hTG
  rw [hEq, integral_const_mul] at hParts
  simp only [one_mul, g] at hParts
  rw [integral_gaussian 2] at hParts
  have hSquare : (fun t : ℝ => oddGaussian t ^ 2) =
      (fun t => t ^ 2 * Real.exp (-2 * t ^ 2)) := by
    funext t
    rw [odd_gaussian_square, neg_mul]
  rw [hSquare]
  linarith only [hParts]

theorem odd_gaussian_second_moment_sq : (∫ t : ℝ, oddGaussian t ^ 2) ^ 2 = Real.pi / 32 := by
  rw [odd_gaussian_second_moment, div_pow, Real.sq_sqrt (by positivity)]
  ring

theorem lower_profile_square_integrable {h : ℝ} (hh : h ≠ 0) :
    Integrable (fun x : ℝ => lowerProfile h x ^ 2) :=
  (odd_gaussian_square_integrable.comp_div hh).comp_sub_right (1 / 2)

theorem lower_profile_total_second_moment {h : ℝ} (hh : 0 < h) :
    (∫ x : ℝ, lowerProfile h x ^ 2) = h * (∫ t : ℝ, oddGaussian t ^ 2) := by
  change (∫ x : ℝ, oddGaussian ((x - 1 / 2) / h) ^ 2) = _
  rw [integral_sub_right_eq_self (fun x : ℝ => oddGaussian (x / h) ^ 2) (1 / 2),
    Measure.integral_comp_div (fun t : ℝ => oddGaussian t ^ 2) h, abs_of_pos hh, smul_eq_mul]

theorem lower_profile_truncated_second_moment {h : ℝ} (hh : 0 < h) :
    0 ≤ (∫ x in (0 : ℝ)..1, lowerProfile h x ^ 2) ∧
      (∫ x in (0 : ℝ)..1, lowerProfile h x ^ 2) ≤ h * (∫ t : ℝ, oddGaussian t ^ 2) := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  constructor
  · exact integral_nonneg (fun _ => sq_nonneg _)
  · rw [← lower_profile_total_second_moment hh]
    exact setIntegral_le_integral (lower_profile_square_integrable hh.ne')
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _))

theorem lower_single_point_divergence_identity (h : ℝ) :
    (∫ p, (lowerAlternative h p - 1) ^ 2 ∂diamondVolume) =
      4 * h ^ 2 * (∫ x in (0 : ℝ)..1, lowerProfile h x ^ 2) ^ 2 := by
  have hEq : (fun p : DiamondPoint => (lowerAlternative h p - 1) ^ 2) =
      (fun p => (4 * h ^ 2) * (lowerProfile h p.1 ^ 2 * lowerProfile h p.2 ^ 2)) := by
    funext p
    unfold lowerAlternative
    ring
  rw [hEq, integral_const_mul]
  have hMeasure : diamondVolume =
      ((volume : Measure ℝ).restrict (Set.Icc 0 1)).prod (volume.restrict (Set.Icc 0 1)) := by
    rw [Measure.prod_restrict]
    rfl
  rw [hMeasure, integral_prod_mul (fun x : ℝ => lowerProfile h x ^ 2)
    (fun x : ℝ => lowerProfile h x ^ 2)]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  ring

/-- The chi-square numerator against the uniform one-point law has the exact
Gaussian constant selected by the ordinary lower construction. -/
theorem lower_single_point_divergence_bound {h : ℝ} (hh : 0 < h) :
    (∫ p, (lowerAlternative h p - 1) ^ 2 ∂diamondVolume) ≤ (Real.pi / 8) * h ^ 4 := by
  obtain ⟨hNonneg, hBound⟩ := lower_profile_truncated_second_moment hh
  have hSq := pow_le_pow_left₀ hNonneg hBound 2
  rw [mul_pow, odd_gaussian_second_moment_sq] at hSq
  rw [lower_single_point_divergence_identity]
  have h := mul_le_mul_of_nonneg_left hSq (by positivity : 0 ≤ 4 * h ^ 2)
  nlinarith only [h]

#print axioms gaussian_second_integrable
#print axioms odd_gaussian_square_integrable
#print axioms odd_gaussian_second_moment
#print axioms odd_gaussian_second_moment_sq
#print axioms lower_profile_square_integrable
#print axioms lower_profile_total_second_moment
#print axioms lower_profile_truncated_second_moment
#print axioms lower_single_point_divergence_identity
#print axioms lower_single_point_divergence_bound

end QuantyraNullCone
