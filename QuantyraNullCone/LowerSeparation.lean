import QuantyraNullCone.LowerAlternatives
import Mathlib.Analysis.Complex.ExponentialBounds

namespace QuantyraNullCone

theorem odd_gaussian_square (t : ℝ) :
    oddGaussian t ^ 2 = t ^ 2 * Real.exp (-(2 * t ^ 2)) := by
  have hExp : Real.exp (-(t ^ 2)) ^ 2 = Real.exp (-(2 * t ^ 2)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  simp only [oddGaussian, mul_pow, hExp]

theorem odd_gaussian_square_sharp (t : ℝ) :
    2 * Real.exp 1 * oddGaussian t ^ 2 ≤ 1 := by
  have hExp : 2 * t ^ 2 ≤ Real.exp (2 * t ^ 2 - 1) := by
    have h := Real.add_one_le_exp (2 * t ^ 2 - 1)
    linarith only [h]
  have hMul := mul_le_mul_of_nonneg_right hExp (Real.exp_pos (1 - 2 * t ^ 2)).le
  have hInv : Real.exp (2 * t ^ 2 - 1) * Real.exp (1 - 2 * t ^ 2) = 1 := by
    rw [← Real.exp_add, show 2 * t ^ 2 - 1 + (1 - 2 * t ^ 2) = 0 by ring, Real.exp_zero]
  rw [hInv] at hMul
  calc
    _ = 2 * t ^ 2 * (Real.exp 1 * Real.exp (-(2 * t ^ 2))) := by rw [odd_gaussian_square]; ring
    _ = 2 * t ^ 2 * Real.exp (1 - 2 * t ^ 2) := by rw [← Real.exp_add]; rfl
    _ ≤ 1 := hMul

theorem odd_gaussian_product_sharp (x y : ℝ) :
    2 * Real.exp 1 * |oddGaussian x * oddGaussian y| ≤ 1 := by
  have hAM : 2 * |oddGaussian x * oddGaussian y| ≤ oddGaussian x ^ 2 + oddGaussian y ^ 2 := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|oddGaussian x| - |oddGaussian y|), sq_abs (oddGaussian x), sq_abs (oddGaussian y)]
  have hMul := mul_le_mul_of_nonneg_left hAM (Real.exp_pos 1).le
  nlinarith only [hMul, odd_gaussian_square_sharp x, odd_gaussian_square_sharp y]

theorem lower_alternative_deviation_sharp {h : ℝ} (hh : 0 ≤ h) (p : DiamondPoint) :
    |lowerAlternative h p - 1| ≤ h / Real.exp 1 := by
  apply (le_div_iff₀ (Real.exp_pos 1)).mpr
  have hBound := odd_gaussian_product_sharp ((p.1 - 1 / 2) / h) ((p.2 - 1 / 2) / h)
  have hMul := mul_le_mul_of_nonneg_left hBound hh
  simp only [lowerAlternative, add_sub_cancel_left, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hh]
  simp only [abs_mul, lowerProfile] at hMul ⊢
  nlinarith only [hMul]

noncomputable def lowerWitness (h : ℝ) : DiamondPoint :=
  (1 / 2 + h / Real.sqrt 2, 1 / 2 + h / Real.sqrt 2)

theorem lower_witness_mem {h : ℝ} (hh : 0 < h) (hSmall : h ≤ 1 / 2) : lowerWitness h ∈ diamond := by
  have hSqrt : (1 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
  have hDiv : h / Real.sqrt 2 ≤ h := div_le_self hh.le hSqrt
  have hDiv0 : 0 ≤ h / Real.sqrt 2 := by positivity
  constructor <;> constructor <;> dsimp [lowerWitness] <;> linarith

theorem odd_gaussian_witness_square :
    oddGaussian (1 / Real.sqrt 2) ^ 2 = 1 / (2 * Real.exp 1) := by
  have hT : (1 / Real.sqrt 2 : ℝ) ^ 2 = 1 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  rw [odd_gaussian_square, hT]
  norm_num
  rw [Real.exp_neg]
  ring

theorem lower_witness_value {h : ℝ} (hh : h ≠ 0) :
    lowerAlternative h (lowerWitness h) - 1 = h / Real.exp 1 := by
  have hArg : ((1 / 2 + h / Real.sqrt 2) - (1 / 2 : ℝ)) / h = 1 / Real.sqrt 2 := by
    field_simp [hh]
    ring
  have hProfile : lowerProfile h (1 / 2 + h / Real.sqrt 2) = oddGaussian (1 / Real.sqrt 2) :=
    congrArg oddGaussian hArg
  simp only [lowerAlternative, lowerWitness, hProfile, add_sub_cancel_left]
  calc
    _ = 2 * h * oddGaussian (1 / Real.sqrt 2) ^ 2 := by ring
    _ = h / Real.exp 1 := by rw [odd_gaussian_witness_square]; ring

theorem lower_coefficient_separation {h : ℝ} (hh : 0 < h) (hSmall : h ≤ 1 / 2) :
    coefficientDeviation lowerFlat (lowerAlternative h) = h / Real.exp 1 := by
  have hK := lower_alternative_in_class hh hSmall
  have hBdd : BddAbove ((fun p => |lowerFlat p - lowerAlternative h p|) '' diamond) := by
    refine ⟨h / Real.exp 1, ?_⟩
    rintro _ ⟨p, _, rfl⟩
    simpa only [lowerFlat, abs_sub_comm] using lower_alternative_deviation_sharp hh.le p
  have hLo := le_csSup hBdd ⟨lowerWitness h, lower_witness_mem hh hSmall, rfl⟩
  have hValue : |lowerFlat (lowerWitness h) - lowerAlternative h (lowerWitness h)| = h / Real.exp 1 := by
    rw [lowerFlat, abs_sub_comm, lower_witness_value hh.ne', abs_of_pos (div_pos hh (Real.exp_pos 1))]
  change |lowerFlat (lowerWitness h) - lowerAlternative h (lowerWitness h)| ≤
    coefficientDeviation lowerFlat (lowerAlternative h) at hLo
  rw [hValue] at hLo
  obtain ⟨p, _, hAtt⟩ := lower_flat_in_class.coefficientDeviation_attained hK
  apply le_antisymm _ hLo
  rw [hAtt]
  simpa only [lowerFlat, abs_sub_comm] using lower_alternative_deviation_sharp hh.le p

theorem lower_quotient_separation {h : ℝ} (hh : 0 < h) (hSmall : h ≤ 1 / 2) :
    conformalDistance lowerFlat (lowerAlternative h) = h / Real.exp 1 := by
  have hTranspose : transposeDensity (lowerAlternative h) = lowerAlternative h := by
    funext p
    exact lower_alternative_transpose h p
  simp only [conformalDistance, hTranspose, min_self, lower_coefficient_separation hh hSmall]

theorem lower_separation_strict {h : ℝ} (hh : 0 < h) : h / 3 < h / Real.exp 1 :=
  div_lt_div_of_pos_left hh (Real.exp_pos 1) Real.exp_one_lt_three

theorem lower_success_disjoint {h : ℝ} (hh : 0 < h) (hSmall : h ≤ 1 / 2)
    (f : DiamondPoint → ℝ) :
    ¬ (DensityEstimateGood lowerFlat (h / 6) f ∧ DensityEstimateGood (lowerAlternative h) (h / 6) f) := by
  rintro ⟨hFlat, hAlt⟩
  have hp := lower_witness_mem hh hSmall
  have hValue : |lowerFlat (lowerWitness h) - lowerAlternative h (lowerWitness h)| = h / Real.exp 1 := by
    rw [lowerFlat, abs_sub_comm, lower_witness_value hh.ne', abs_of_pos (div_pos hh (Real.exp_pos 1))]
  rcases density_estimate_common_orbit hFlat hAlt with hDirect | hSwap
  · have h := hDirect (lowerWitness h) hp
    rw [hValue] at h
    linarith [lower_separation_strict hh]
  · have hb := hSwap (lowerWitness h) hp
    change |lowerFlat (lowerWitness h) - lowerAlternative h (transposePoint (lowerWitness h))| ≤ _ at hb
    rw [lower_alternative_transpose, hValue] at hb
    linarith [lower_separation_strict hh]

#print axioms odd_gaussian_square
#print axioms odd_gaussian_square_sharp
#print axioms odd_gaussian_product_sharp
#print axioms lower_alternative_deviation_sharp
#print axioms lower_witness_mem
#print axioms odd_gaussian_witness_square
#print axioms lower_witness_value
#print axioms lower_coefficient_separation
#print axioms lower_quotient_separation
#print axioms lower_separation_strict
#print axioms lower_success_disjoint

end QuantyraNullCone
