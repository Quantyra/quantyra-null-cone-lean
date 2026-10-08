import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace QuantyraNullCone

open Finset

/-- Exact box correction; a residual need not vanish. -/
theorem residual_box_bound {r x L U : ℝ} (hL : L ≤ x) (hU : x ≤ U) :
    min (r * L) (r * U) ≤ r * x := by
  by_cases hr : 0 ≤ r
  · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left hL hr)
  · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left hU (le_of_not_ge hr))

/-- The residual correction used by the executable LP certificate verifier.
Only primal feasibility, the known box, and multiplier signs are assumptions. -/
theorem finite_lp_weak_duality {n m k : ℕ}
    (A : Fin m → Fin n → ℝ) (E : Fin k → Fin n → ℝ)
    (b : Fin m → ℝ) (d : Fin k → ℝ) (c x L U : Fin n → ℝ)
    (y : Fin m → ℝ) (z : Fin k → ℝ)
    (hA : ∀ i, (∑ j, A i j * x j) ≤ b i)
    (hE : ∀ i, (∑ j, E i j * x j) = d i)
    (hY : ∀ i, y i ≤ 0) (hL : ∀ j, L j ≤ x j) (hU : ∀ j, x j ≤ U j) :
    (∑ i, b i * y i) + (∑ i, d i * z i) +
      (∑ j, min ((c j - (∑ i, A i j * y i) - (∑ i, E i j * z i)) * L j)
        ((c j - (∑ i, A i j * y i) - (∑ i, E i j * z i)) * U j)) ≤
      ∑ j, c j * x j := by
  let r : Fin n → ℝ := fun j => c j - (∑ i, A i j * y i) - (∑ i, E i j * z i)
  have hAI : (∑ j, (∑ i, A i j * y i) * x j) =
      ∑ i, y i * (∑ j, A i j * x j) := by
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hEI : (∑ j, (∑ i, E i j * z i) * x j) =
      ∑ i, z i * (∑ j, E i j * x j) := by
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hIdentity : (∑ j, c j * x j) = (∑ j, r j * x j) +
      (∑ i, y i * (∑ j, A i j * x j)) + (∑ i, z i * d i) := by
    calc
      (∑ j, c j * x j) = ∑ j, (r j * x j +
        (∑ i, A i j * y i) * x j + (∑ i, E i j * z i) * x j) := by
          apply Finset.sum_congr rfl
          intro j _
          dsimp [r]
          ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hAI, hEI]
        simp_rw [hE]
  have hIneq : (∑ i, b i * y i) ≤ ∑ i, y i * (∑ j, A i j * x j) := by
    apply Finset.sum_le_sum
    intro i _
    rw [mul_comm (b i)]
    exact mul_le_mul_of_nonpos_left (hA i) (hY i)
  have hBox : (∑ j, min (r j * L j) (r j * U j)) ≤ ∑ j, r j * x j := by
    apply Finset.sum_le_sum
    intro j _
    exact residual_box_bound (hL j) (hU j)
  have hEq : (∑ i, d i * z i) = ∑ i, z i * d i := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  change (∑ i, b i * y i) + (∑ i, d i * z i) +
    (∑ j, min (r j * L j) (r j * U j)) ≤ _
  linarith

def rationalResidual {n m k : ℕ} (A : Fin m → Fin n → ℚ) (E : Fin k → Fin n → ℚ)
    (c : Fin n → ℚ) (y : Fin m → ℚ) (z : Fin k → ℚ) (j : Fin n) : ℚ :=
  c j - (∑ i, A i j * y i) - (∑ i, E i j * z i)

def rationalDualLower {n m k : ℕ} (A : Fin m → Fin n → ℚ) (E : Fin k → Fin n → ℚ)
    (b : Fin m → ℚ) (d : Fin k → ℚ) (c L U : Fin n → ℚ)
    (y : Fin m → ℚ) (z : Fin k → ℚ) : ℚ :=
  (∑ i, b i * y i) + (∑ i, d i * z i) +
    (∑ j, min (rationalResidual A E c y z j * L j)
      (rationalResidual A E c y z j * U j))

/-- Executable exact arithmetic sign gate; dimensions are enforced by the types. -/
def rationalDualValid {m : ℕ} (y : Fin m → ℚ) : Bool := decide (∀ i, y i ≤ 0)

/-- Accepted rational dual data provide a lower bound for every feasible REAL primal point. -/
theorem rationalDual_checker_sound {n m k : ℕ}
    (A : Fin m → Fin n → ℚ) (E : Fin k → Fin n → ℚ)
    (b : Fin m → ℚ) (d : Fin k → ℚ) (c L U : Fin n → ℚ)
    (y : Fin m → ℚ) (z : Fin k → ℚ) (x : Fin n → ℝ)
    (hValid : rationalDualValid y = true)
    (hA : ∀ i, (∑ j, (A i j : ℝ) * x j) ≤ (b i : ℝ))
    (hE : ∀ i, (∑ j, (E i j : ℝ) * x j) = (d i : ℝ))
    (hL : ∀ j, (L j : ℝ) ≤ x j) (hU : ∀ j, x j ≤ (U j : ℝ)) :
    (rationalDualLower A E b d c L U y z : ℝ) ≤ ∑ j, (c j : ℝ) * x j := by
  have hY : ∀ i, y i ≤ 0 := by simpa [rationalDualValid] using hValid
  have hYReal : ∀ i, (y i : ℝ) ≤ 0 := fun i => by exact_mod_cast hY i
  have h := finite_lp_weak_duality (fun i j => (A i j : ℝ))
    (fun i j => (E i j : ℝ)) (fun i => (b i : ℝ)) (fun i => (d i : ℝ))
    (fun j => (c j : ℝ)) x (fun j => (L j : ℝ)) (fun j => (U j : ℝ))
    (fun i => (y i : ℝ)) (fun i => (z i : ℝ)) hA hE hYReal hL hU
  simpa [rationalDualLower, rationalResidual] using h

#print axioms residual_box_bound
#print axioms finite_lp_weak_duality
#print axioms rationalDual_checker_sound

end QuantyraNullCone
