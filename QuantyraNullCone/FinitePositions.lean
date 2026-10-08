import QuantyraNullCone.FiniteForcing
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Fintype.Card

namespace QuantyraNullCone

/-- Exact finite checks on the decoded zero-based position arrays.
Injectivity makes each array a permutation of Fin n. -/
def checkPositionRealizer {n : ℕ} (rows : Fin n → Fin n → Bool)
    (x y : Fin n → Fin n) : Bool :=
  decide (Function.Injective x ∧ Function.Injective y ∧
    ∀ i j, rows i j = decide (x i < x j ∧ y i < y j))

def checkedPositionRealizer {n : ℕ} (rows : Fin n → Fin n → Bool)
    (x y : Fin n → Fin n) (hAccept : checkPositionRealizer rows x y = true) :
    Realizer (rowRelation rows) where
  first := fun i j => x i < x j
  second := fun i j => y i < y j
  firstTotal := by
    have h := of_decide_eq_true hAccept
    exact ⟨fun i => lt_irrefl (x i), fun h₁ h₂ => lt_trans h₁ h₂,
      fun hij => lt_or_gt_of_ne (h.1.ne hij)⟩
  secondTotal := by
    have h := of_decide_eq_true hAccept
    exact ⟨fun i => lt_irrefl (y i), fun h₁ h₂ => lt_trans h₁ h₂,
      fun hij => lt_or_gt_of_ne (h.2.1.ne hij)⟩
  intersection := by
    have h := of_decide_eq_true hAccept
    intro i j
    change rows i j = true ↔ x i < x j ∧ y i < y j
    rw [h.2.2 i j]
    simp

/-- The formal predecessor rank agrees exactly with the Python one-based position. -/
theorem rank_position_eq {n : ℕ} (positions : Fin n → Fin n)
    (hInjective : Function.Injective positions) (i : Fin n) :
    rank (fun j k => positions j < positions k) i = (positions i).val + 1 := by
  classical
  have hSurjective := Finite.surjective_of_injective hInjective
  have hCard : (predecessors (fun j k => positions j < positions k) i).card =
      (Finset.Iio (positions i)).card := by
    apply Finset.card_bij (fun j _ => positions j)
    · intro j hj
      apply Finset.mem_Iio.mpr
      simpa [predecessors] using hj
    · intro j _ k _ hjk
      exact hInjective hjk
    · intro b hb
      obtain ⟨a, rfl⟩ := hSurjective b
      refine ⟨a, ?_, rfl⟩
      simpa [predecessors] using Finset.mem_Iio.mp hb
  simp only [rank, hCard, Fin.card_Iio, Nat.add_comm]

theorem checkedPositionRealizer_ranks {n : ℕ} (rows : Fin n → Fin n → Bool)
    (x y : Fin n → Fin n) (hAccept : checkPositionRealizer rows x y = true) (i : Fin n) :
    rank (checkedPositionRealizer rows x y hAccept).first i = (x i).val + 1 ∧
      rank (checkedPositionRealizer rows x y hAccept).second i = (y i).val + 1 := by
  have h := of_decide_eq_true hAccept
  exact ⟨rank_position_eq x h.1 i, rank_position_eq y h.2.1 i⟩

#print axioms rank_position_eq
#print axioms checkedPositionRealizer_ranks

end QuantyraNullCone
