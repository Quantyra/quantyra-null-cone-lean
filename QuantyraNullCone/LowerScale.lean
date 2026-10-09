import QuantyraNullCone.LowerTesting
import Mathlib.Analysis.Real.Pi.Bounds

namespace QuantyraNullCone

noncomputable def lowerBandwidth (n : ℕ) : ℝ := min (1 / 2 : ℝ) ((n : ℝ) ^ (-1 / 4 : ℝ))

noncomputable def lowerTVBound (n : ℕ) (h : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.sqrt (Real.exp ((n : ℝ) * Real.pi * h ^ 4 / 8) - 1)

theorem lower_bandwidth_bounds {n : ℕ} (hn : 1 ≤ n) :
    0 < lowerBandwidth n ∧ lowerBandwidth n ≤ 1 / 2 := by
  have hnPos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  exact ⟨lt_min (by norm_num) (Real.rpow_pos_of_pos hnPos _), min_le_left _ _⟩

theorem lower_bandwidth_budget {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) * lowerBandwidth n ^ 4 ≤ 1 := by
  have hnPos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hPow : ((n : ℝ) ^ (-1 / 4 : ℝ)) ^ 4 = 1 / (n : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnPos.le]
    norm_num [Real.rpow_neg_one]
  have hLe := pow_le_pow_left₀ (lower_bandwidth_bounds hn).1.le
    (min_le_right (1 / 2 : ℝ) ((n : ℝ) ^ (-1 / 4 : ℝ))) 4
  rw [hPow] at hLe
  have h := mul_le_mul_of_nonneg_left hLe hnPos.le
  simpa only [mul_one_div_cancel hnPos.ne'] using h

theorem lower_bandwidth_large {n : ℕ} (hn : 16 ≤ n) :
    lowerBandwidth n = (n : ℝ) ^ (-1 / 4 : ℝ) := by
  apply min_eq_right
  have hnR : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have h := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 16) hnR
    (by norm_num : (-1 / 4 : ℝ) ≤ 0)
  have hId : (16 : ℝ) ^ (-1 / 4 : ℝ) = 1 / 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  exact h.trans_eq hId

theorem lower_TV_budget_strict {n : ℕ} {h : ℝ} (hBudget : (n : ℝ) * h ^ 4 ≤ 1) :
    lowerTVBound n h < 1 / 2 := by
  have hNonneg : 0 ≤ (n : ℝ) * Real.pi * h ^ 4 / 8 := by positivity
  have hPi := mul_le_mul_of_nonneg_left hBudget Real.pi_pos.le
  have hExponent : (n : ℝ) * Real.pi * h ^ 4 / 8 < 1 / 2 := by
    nlinarith only [hPi, Real.pi_lt_four]
  have hHalfSq : Real.exp (1 / 2 : ℝ) ^ 2 = Real.exp 1 := by
    rw [pow_two, ← Real.exp_add]
    norm_num
  have hHalf : Real.exp (1 / 2 : ℝ) < 2 := by
    nlinarith [Real.exp_one_lt_three, Real.exp_pos (1 / 2 : ℝ)]
  have hExp := (Real.exp_lt_exp.mpr hExponent).trans hHalf
  have hRad : 0 ≤ Real.exp ((n : ℝ) * Real.pi * h ^ 4 / 8) - 1 := by
    have h := Real.one_le_exp_iff.mpr hNonneg
    linarith
  have hSqrt : Real.sqrt (Real.exp ((n : ℝ) * Real.pi * h ^ 4 / 8) - 1) < 1 :=
    (Real.sqrt_lt hRad (by norm_num : (0 : ℝ) ≤ 1)).mpr (by nlinarith only [hExp])
  unfold lowerTVBound
  linarith only [hSqrt]

theorem lower_probability_strict {n : ℕ} (hn : 1 ≤ n) :
    (1 / 4 : ℝ) < (1 - lowerTVBound n (lowerBandwidth n)) / 2 := by
  have h := lower_TV_budget_strict (lower_bandwidth_budget hn)
  linarith

#print axioms lower_bandwidth_bounds
#print axioms lower_bandwidth_budget
#print axioms lower_bandwidth_large
#print axioms lower_TV_budget_strict
#print axioms lower_probability_strict

end QuantyraNullCone
