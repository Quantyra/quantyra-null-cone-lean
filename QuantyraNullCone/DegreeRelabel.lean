import QuantyraNullCone.DegreeRateNumbers
import QuantyraNullCone.Unlabeled

namespace QuantyraNullCone

theorem predecessors_reindex_card {n : ℕ} (π : Equiv.Perm (Fin n))
    (R : Fin n → Fin n → Prop) (i : Fin n) :
    (predecessors (fun a b => R (π a) (π b)) i).card = (predecessors R (π i)).card := by
  classical
  exact Finset.card_equiv π (fun a => by simp [predecessors])

theorem rank_reindex {n : ℕ} (π : Equiv.Perm (Fin n)) (R : Fin n → Fin n → Prop) (i : Fin n) :
    rank (fun a b => R (π a) (π b)) i = rank R (π i) := by
  simp only [rank, predecessors_reindex_card]

theorem degree_retained_reindex {n : ℕ} (π : Equiv.Perm (Fin n))
    (R : Fin n → Fin n → Prop) (r : ℝ) (i : Fin n) :
    DegreeRetained (fun a b => R (π a) (π b)) r i ↔ DegreeRetained R r (π i) := by
  have hSucc := predecessors_reindex_card π (fun a b => R b a) i
  simp only [DegreeRetained, predecessors_reindex_card, hSucc]

def Realizer.reindex {n : ℕ} {R : Fin n → Fin n → Prop}
    (L : Realizer R) (π : Equiv.Perm (Fin n)) : Realizer (fun a b => R (π a) (π b)) where
  first := fun a b => L.first (π a) (π b)
  second := fun a b => L.second (π a) (π b)
  firstTotal := ⟨fun _ => L.firstTotal.irrefl _, fun hab hbc => L.firstTotal.trans hab hbc,
    fun hne => L.firstTotal.total (π.injective.ne hne)⟩
  secondTotal := ⟨fun _ => L.secondTotal.irrefl _, fun hab hbc => L.secondTotal.trans hab hbc,
    fun hne => L.secondTotal.total (π.injective.ne hne)⟩
  intersection := fun _ _ => L.intersection _ _

theorem Realizer.rankPoint_reindex {n : ℕ} {R : Fin n → Fin n → Prop}
    (L : Realizer R) (π : Equiv.Perm (Fin n)) (i : Fin n) :
    (L.reindex π).rankPoint i = L.rankPoint (π i) := by
  simp only [Realizer.rankPoint, Realizer.reindex, rank_reindex]

theorem Realizer.aligned_reindex {n : ℕ} {R : Fin n → Fin n → Prop}
    (L : Realizer R) (π : Equiv.Perm (Fin n)) (b : Bool) :
    (L.reindex π).aligned b = (L.aligned b).reindex π := by cases b <;> rfl

theorem Realizer.degreeCellValue_reindex {n : ℕ} {R : Fin n → Fin n → Prop}
    (L : Realizer R) (π : Equiv.Perm (Fin n)) (r H w : ℝ) (i j : ℕ) :
    (L.reindex π).degreeCellValue r H w i j = L.degreeCellValue r H w i j := by
  have hCard : (retainedPointsIn (DegreeRetained (fun a b => R (π a) (π b)) r)
      (L.reindex π).rankPoint (innerCell H w i j)).card =
      (retainedPointsIn (DegreeRetained R r) L.rankPoint (innerCell H w i j)).card := by
    classical
    apply Finset.card_equiv π
    intro a
    simp only [retainedPointsIn, Finset.mem_filter, Finset.mem_univ, true_and,
      degree_retained_reindex, Realizer.rankPoint_reindex]
  simp only [Realizer.degreeCellValue, hCard]

theorem Realizer.degreeHistogram_reindex {n : ℕ} {R : Fin n → Fin n → Prop}
    (L : Realizer R) (π : Equiv.Perm (Fin n)) (r : ℝ) (k : ℕ) (H w : ℝ) (p : DiamondPoint) :
    (L.reindex π).degreeHistogram r k H w p = L.degreeHistogram r k H w p :=
  L.degreeCellValue_reindex π r H w _ _

def CodeDegreeReconstructed {n : ℕ} (rho : DiamondPoint → ℝ) (r : ℝ) (k : ℕ)
    (H w E : ℝ) (code : OrderCode n) : Prop :=
  ∀ L : Realizer (CodeRelation code), ∃ b : Bool, ∀ p ∈ diamond,
    |(L.aligned b).degreeHistogram r k H w p - rho p| ≤ E

theorem code_degree_reconstructed_sample {n : ℕ} {rho : DiamondPoint → ℝ}
    {r H w E : ℝ} {k : ℕ} {sample : Fin n → DiamondPoint}
    (h : SampleDegreeReconstructed rho r k H w E sample) :
    CodeDegreeReconstructed rho r k H w E (sampledOrder sample) := by
  unfold CodeDegreeReconstructed
  rw [sampledOrder_relation]
  exact h

theorem code_realizer_relabel {n : ℕ} {code : OrderCode n}
    (h : Nonempty (Realizer (CodeRelation code))) (π : Equiv.Perm (Fin n)) :
    Nonempty (Realizer (CodeRelation (relabelOrder π code))) := by
  obtain ⟨L⟩ := h
  exact ⟨L.reindex π⟩

/-- Relabeling changes neither strict degrees nor the multiset of reconstructed
rank points. Thus canonical quotient representatives need no latent input. -/
theorem CodeDegreeReconstructed.relabel {n : ℕ} {rho : DiamondPoint → ℝ}
    {r H w E : ℝ} {k : ℕ} {code : OrderCode n}
    (h : CodeDegreeReconstructed rho r k H w E code) (π : Equiv.Perm (Fin n)) :
    CodeDegreeReconstructed rho r k H w E (relabelOrder π code) := by
  intro L
  have hEq : (fun a b => CodeRelation (relabelOrder π code) (π.symm a) (π.symm b)) =
      CodeRelation code := by
    funext a b
    simp only [CodeRelation, relabelOrder, Equiv.apply_symm_apply]
  have hOriginal : ∀ M : Realizer
      (fun a b => CodeRelation (relabelOrder π code) (π.symm a) (π.symm b)),
      ∃ b : Bool, ∀ p ∈ diamond, |(M.aligned b).degreeHistogram r k H w p - rho p| ≤ E := by
    rw [hEq]
    exact h
  obtain ⟨b, hBound⟩ := hOriginal (L.reindex π.symm)
  refine ⟨b, ?_⟩
  simpa only [Realizer.aligned_reindex, Realizer.degreeHistogram_reindex] using hBound

#print axioms predecessors_reindex_card
#print axioms rank_reindex
#print axioms degree_retained_reindex
#print axioms Realizer.rankPoint_reindex
#print axioms Realizer.aligned_reindex
#print axioms Realizer.degreeCellValue_reindex
#print axioms Realizer.degreeHistogram_reindex
#print axioms code_degree_reconstructed_sample
#print axioms code_realizer_relabel
#print axioms CodeDegreeReconstructed.relabel

end QuantyraNullCone
