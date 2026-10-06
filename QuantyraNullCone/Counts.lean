import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace QuantyraNullCone

noncomputable def predecessors {α : Type} [Fintype α]
    (R : α → α → Prop) (i : α) : Finset α := by
  classical
  exact Finset.univ.filter (fun j => R j i)

noncomputable def rank {α : Type} [Fintype α]
    (R : α → α → Prop) (i : α) : ℕ := 1 + (predecessors R i).card

noncomputable def disagreements {α : Type} [Fintype α]
    (R T : α → α → Prop) (i : α) : Finset α := by
  classical
  exact Finset.univ.filter (fun j => ¬ (R j i ↔ T j i))

/-- Rank error is bounded by the number of pairwise comparison disagreements.
No totality, geometry, or already-assumed rank bound is required. -/
theorem abs_rank_sub_le_disagreements {α : Type} [Fintype α]
    (R T : α → α → Prop) (i : α) :
    |(rank R i : ℝ) - (rank T i : ℝ)| ≤ (disagreements R T i).card := by
  classical
  have subRT : predecessors R i \ predecessors T i ⊆ disagreements R T i := by
    intro j hj
    rcases Finset.mem_sdiff.mp hj with ⟨hjR, hjT⟩
    have hR : R j i := by simpa [predecessors] using hjR
    have hnT : ¬ T j i := by simpa [predecessors] using hjT
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ j, fun h => hnT (h.mp hR)⟩
  have subTR : predecessors T i \ predecessors R i ⊆ disagreements R T i := by
    intro j hj
    rcases Finset.mem_sdiff.mp hj with ⟨hjT, hjR⟩
    have hT : T j i := by simpa [predecessors] using hjT
    have hnR : ¬ R j i := by simpa [predecessors] using hjR
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ j, fun h => hnR (h.mpr hT)⟩
  have hRT := Finset.card_le_card_sdiff_add_card
    (s := predecessors R i) (t := predecessors T i)
  have hTR := Finset.card_le_card_sdiff_add_card
    (s := predecessors T i) (t := predecessors R i)
  have hRT' : ((predecessors R i).card : ℝ) ≤
      ((predecessors R i \ predecessors T i).card : ℝ) +
      ((predecessors T i).card : ℝ) := by exact_mod_cast hRT
  have hTR' : ((predecessors T i).card : ℝ) ≤
      ((predecessors T i \ predecessors R i).card : ℝ) +
      ((predecessors R i).card : ℝ) := by exact_mod_cast hTR
  have hsubRT : ((predecessors R i \ predecessors T i).card : ℝ) ≤
      ((disagreements R T i).card : ℝ) := by
    exact_mod_cast Finset.card_le_card subRT
  have hsubTR : ((predecessors T i \ predecessors R i).card : ℝ) ≤
      ((disagreements R T i).card : ℝ) := by
    exact_mod_cast Finset.card_le_card subTR
  apply abs_le.mpr
  simp only [rank, Nat.cast_add, Nat.cast_one]
  constructor <;> linarith only [hRT', hTR', hsubRT, hsubTR]

end QuantyraNullCone

#print axioms QuantyraNullCone.abs_rank_sub_le_disagreements
