import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace QuantyraNullCone

/-- The exact rational upper function used by the 512-subdivision calibration. -/
def negativeExpUpperQ (t : ℚ) : ℚ := 1 / (1 + t / 512) ^ 512

theorem negative_exp_upper_512 {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-t) ≤ 1 / (1 + t / 512) ^ 512 := by
  have hBase : 0 < 1 + t / 512 := by positivity
  have hLe : 1 + t / 512 ≤ Real.exp (t / 512) := by
    simpa [add_comm] using Real.add_one_le_exp (t / 512)
  have hPow : (1 + t / 512) ^ 512 ≤ Real.exp t := by
    calc
      (1 + t / 512) ^ 512 ≤ (Real.exp (t / 512)) ^ 512 :=
        pow_le_pow_left₀ hBase.le hLe 512
      _ = Real.exp ((512 : ℕ) * (t / 512)) := (Real.exp_nat_mul (t / 512) 512).symm
      _ = Real.exp t := by congr 1; ring
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (pow_pos hBase _) hPow

theorem negative_exp_upper_rational {t : ℚ} (ht : 0 ≤ t) :
    Real.exp (-(t : ℝ)) ≤ (negativeExpUpperQ t : ℝ) := by
  have htReal : (0 : ℝ) ≤ t := by exact_mod_cast ht
  simpa [negativeExpUpperQ] using negative_exp_upper_512 htReal

/-- Outward rounding to the exact grid; no floating-point arithmetic is used. -/
def roundFailureQ (denominator : ℕ) (raw : ℚ) : ℚ :=
  (Int.ceil (raw * denominator) : ℚ) / denominator

theorem roundFailureQ_upper {D : ℕ} (hD : 0 < D) (raw : ℚ) :
    raw ≤ roundFailureQ D raw := by
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD
  apply (le_div_iff₀ hDq).mpr
  exact Int.le_ceil (raw * D)

theorem roundFailureQ_le_grid_budget {D : ℕ} (hD : 0 < D) {raw budget : ℚ}
    (hRaw : raw ≤ budget) (hGrid : ∃ z : ℤ, (z : ℚ) = budget * D) :
    roundFailureQ D raw ≤ budget := by
  obtain ⟨z, hz⟩ := hGrid
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD
  apply (div_le_iff₀ hDq).mpr
  rw [← hz]
  have hCeil : Int.ceil (raw * D) ≤ z := Int.ceil_le.mpr (by
    rw [hz]
    exact mul_le_mul_of_nonneg_right hRaw hDq.le)
  exact_mod_cast hCeil

theorem failure_budget_grid (budget : ℚ) :
    ∃ z : ℤ, (z : ℚ) = budget * (10 ^ 12 * budget.den : ℕ) := by
  refine ⟨budget.num * (10 ^ 12), ?_⟩
  have hDen : (budget.den : ℚ) ≠ 0 := by exact_mod_cast budget.den_ne_zero
  have hNumDen := congrArg (fun x : ℚ => x * (budget.den : ℚ)) (Rat.num_div_den budget)
  change (budget.num : ℚ) / (budget.den : ℚ) * (budget.den : ℚ) =
    budget * (budget.den : ℚ) at hNumDen
  rw [div_mul_cancel₀ _ hDen] at hNumDen
  push_cast
  rw [hNumDen]
  ring

theorem roundFailureQ_le_budget {raw budget : ℚ} (hRaw : raw ≤ budget) :
    roundFailureQ (10 ^ 12 * budget.den) raw ≤ budget := by
  apply roundFailureQ_le_grid_budget
  · exact Nat.mul_pos (by norm_num) budget.den_pos
  · exact hRaw
  · exact failure_budget_grid budget

theorem rounded_split_failure_budget {rawM rawJ budgetM budgetJ delta : ℚ}
    (hM : rawM ≤ budgetM) (hJ : rawJ ≤ budgetJ) (hSplit : budgetM + budgetJ = delta) :
    roundFailureQ (10 ^ 12 * budgetM.den) rawM +
      roundFailureQ (10 ^ 12 * budgetJ.den) rawJ ≤ delta := by
  have hm := roundFailureQ_le_budget hM
  have hj := roundFailureQ_le_budget hJ
  linarith

#print axioms negative_exp_upper_512
#print axioms negative_exp_upper_rational
#print axioms roundFailureQ_upper
#print axioms roundFailureQ_le_budget
#print axioms rounded_split_failure_budget

end QuantyraNullCone
