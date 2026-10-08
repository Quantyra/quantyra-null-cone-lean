import QuantyraNullCone.FiniteFoundation

namespace QuantyraNullCone

/-- Shared fixture: the only order relation is 1 < 2, with anchor 0 -> 1. -/
def fixtureRows (i j : Fin 3) : Bool := decide (i = 1 ∧ j = 2)

def fixtureSecond (i : Fin 3) : Fin 3 := if i = 0 then 2 else if i = 1 then 0 else 1

def fixtureTrace : List (ForcingEntry 3) :=
  [((0, 1), none), ((0, 2), some (0, 1))]

example : checkPositionRealizer fixtureRows id fixtureSecond = true := by decide
example : checkPositionRealizer fixtureRows (fun _ => 0) fixtureSecond = false := by decide
example : checkForcingTrace fixtureRows (0, 1) fixtureTrace = true := by decide
example : checkForcingTrace fixtureRows (0, 1)
    [((0, 1), none), ((0, 2), some (1, 0))] = false := by decide

example : rationalDualValid (fun _ : Fin 1 => (-1 : ℚ)) = true := by decide
example : rationalDualValid (fun _ : Fin 1 => (1 : ℚ)) = false := by decide
example : rationalDualLower (fun _ _ : Fin 1 => (1 : ℚ))
    (fun i : Fin 0 => Fin.elim0 i) (fun _ => (3 / 2 : ℚ))
    (fun i : Fin 0 => Fin.elim0 i) (fun _ => (1 : ℚ)) (fun _ => (1 / 2 : ℚ))
    (fun _ => (3 / 2 : ℚ)) (fun _ => (-1 : ℚ)) (fun i : Fin 0 => Fin.elim0 i) =
      (-1 / 2 : ℚ) := by
  norm_num [rationalDualLower, rationalResidual]

example : roundFailureQ (10 ^ 12 * 2) (1 / 3) = (666666666667 / 2000000000000 : ℚ) := by
  have hCeil : Int.ceil ((1 / 3 : ℚ) * (10 ^ 12 * 2 : ℕ)) = (666666666667 : ℤ) := by
    apply Int.ceil_eq_iff.mpr
    constructor <;> norm_num
  unfold roundFailureQ
  rw [hCeil]
  norm_num

end QuantyraNullCone
