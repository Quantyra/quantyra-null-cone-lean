import QuantyraNullCone.Bridges

namespace QuantyraNullCone

abbrev FiniteArc (n : ℕ) := Fin n × Fin n

def rowRelation {n : ℕ} (rows : Fin n → Fin n → Bool) (u v : Fin n) : Prop :=
  rows u v = true

instance {n : ℕ} (rows : Fin n → Fin n → Bool) (u v : Fin n) :
    Decidable (Incomparable (rowRelation rows) u v) :=
  inferInstanceAs (Decidable (u ≠ v ∧ ¬ rows u v = true ∧ ¬ rows v u = true))

instance {n : ℕ} (rows : Fin n → Fin n → Bool) (u v : Fin n) :
    Decidable (Comparable (rowRelation rows) u v) :=
  inferInstanceAs (Decidable (rows u v = true ∨ rows v u = true))

/-- This step always checks the original order table, never a deleted graph. -/
def originalForceStep {n : ℕ} (rows : Fin n → Fin n → Bool)
    (parent arc : FiniteArc n) : Bool :=
  decide ((parent.1 = arc.1 ∧ Incomparable (rowRelation rows) parent.1 parent.2 ∧
      Incomparable (rowRelation rows) arc.1 arc.2 ∧ Comparable (rowRelation rows) parent.2 arc.2) ∨
    (parent.2 = arc.2 ∧ Incomparable (rowRelation rows) parent.1 parent.2 ∧
      Incomparable (rowRelation rows) arc.1 arc.2 ∧ Comparable (rowRelation rows) parent.1 arc.1))

theorem Realizer.originalForceStep_sound {n : ℕ} {rows : Fin n → Fin n → Bool}
    (L : Realizer (rowRelation rows)) (parent arc : FiniteArc n)
    (h : originalForceStep rows parent arc = true) :
    L.opposite parent.1 parent.2 ↔ L.opposite arc.1 arc.2 := by
  rcases parent with ⟨a, b⟩
  rcases arc with ⟨u, v⟩
  have hStep := of_decide_eq_true h
  rcases hStep with ⟨rfl, hab, huv, hbv⟩ | ⟨rfl, hab, huv, hau⟩
  · exact L.forcing_at_left hab huv hbv
  · exact L.forcing_at_right hab huv hau

abbrev ForcingEntry (n : ℕ) := FiniteArc n × Option (FiniteArc n)

def forcingEntryValid {n : ℕ} (rows : Fin n → Fin n → Bool) (anchor : FiniteArc n)
    (seen : List (FiniteArc n)) (entry : ForcingEntry n) : Prop :=
  Incomparable (rowRelation rows) entry.1.1 entry.1.2 ∧ entry.1 ∉ seen ∧
    (entry.1.2, entry.1.1) ∉ seen ∧
    match entry.2 with
    | none => seen = [] ∧ entry.1 = anchor
    | some parent => parent ∈ seen ∧ originalForceStep rows parent entry.1 = true

instance {n : ℕ} (rows : Fin n → Fin n → Bool) (anchor : FiniteArc n)
    (seen : List (FiniteArc n)) (entry : ForcingEntry n) :
    Decidable (forcingEntryValid rows anchor seen entry) := by
  unfold forcingEntryValid
  split <;> infer_instance

/-- The computational witness-tree core of the finite-data verifier. -/
def checkForcingTraceFrom {n : ℕ} (rows : Fin n → Fin n → Bool) (anchor : FiniteArc n)
    (seen : List (FiniteArc n)) : List (ForcingEntry n) → Bool
  | [] => true
  | entry :: rest =>
    if forcingEntryValid rows anchor seen entry then
      checkForcingTraceFrom rows anchor (entry.1 :: seen) rest
    else false

def checkForcingTrace {n : ℕ} (rows : Fin n → Fin n → Bool) (anchor : FiniteArc n)
    (trace : List (ForcingEntry n)) : Bool := checkForcingTraceFrom rows anchor [] trace

theorem Realizer.checkForcingTraceFrom_sound {n : ℕ} {rows : Fin n → Fin n → Bool}
    (L : Realizer (rowRelation rows)) (anchor : FiniteArc n) (trace : List (ForcingEntry n)) :
    ∀ seen : List (FiniteArc n),
      (∀ arc ∈ seen, L.opposite arc.1 arc.2 ↔ L.opposite anchor.1 anchor.2) →
      checkForcingTraceFrom rows anchor seen trace = true →
      ∀ arc ∈ seen ++ trace.map Prod.fst,
        L.opposite arc.1 arc.2 ↔ L.opposite anchor.1 anchor.2 := by
  induction trace with
  | nil =>
    intro seen hSeen _ arc hArc
    exact hSeen arc (by simpa using hArc)
  | cons entry rest ih =>
    intro seen hSeen hAccept
    simp only [checkForcingTraceFrom] at hAccept
    split at hAccept
    next hValid =>
      have hLink : L.opposite entry.1.1 entry.1.2 ↔ L.opposite anchor.1 anchor.2 := by
        rcases hValid with ⟨_, _, _, hParent⟩
        cases hEntry : entry.2 with
        | none =>
          simp only [hEntry] at hParent
          rw [hParent.2]
        | some parent =>
          simp only [hEntry] at hParent
          exact (L.originalForceStep_sound parent entry.1 hParent.2).symm.trans
            (hSeen parent hParent.1)
      have hNew : ∀ arc ∈ entry.1 :: seen,
          L.opposite arc.1 arc.2 ↔ L.opposite anchor.1 anchor.2 := by
        intro arc hArc
        rcases List.mem_cons.mp hArc with rfl | hArc
        · exact hLink
        · exact hSeen arc hArc
      have hRest := ih (entry.1 :: seen) hNew hAccept
      intro arc hArc
      apply hRest arc
      simpa only [List.map_cons, List.mem_append, List.mem_cons, or_assoc, or_comm,
        or_left_comm] using hArc
    next => simp_all

theorem Realizer.checkForcingTrace_sound {n : ℕ} {rows : Fin n → Fin n → Bool}
    (L : Realizer (rowRelation rows)) (anchor : FiniteArc n) (trace : List (ForcingEntry n))
    (hAccept : checkForcingTrace rows anchor trace = true) :
    ∀ arc ∈ trace.map Prod.fst, L.opposite arc.1 arc.2 ↔ L.opposite anchor.1 anchor.2 := by
  have h := L.checkForcingTraceFrom_sound anchor trace [] (by simp) hAccept
  simpa using h

#print axioms Realizer.originalForceStep_sound
#print axioms Realizer.checkForcingTrace_sound

theorem StrictTotal.reverse_iff_not {α : Type} {R : α → α → Prop}
    (h : StrictTotal R) {x y : α} (hxy : x ≠ y) : R y x ↔ ¬ R x y := by
  constructor
  · intro hyx
    exact h.asymm hyx
  · intro hNot
    exact (h.total hxy).resolve_left hNot

theorem Realizer.opposite_iff_first {α : Type} {P : α → α → Prop}
    (L : Realizer P) {x y : α} (hInc : Incomparable P x y) :
    L.opposite x y ↔ L.first x y := by
  constructor
  · exact And.left
  · intro hFirst
    rcases L.orient_incomparable hInc with hOpp | hOpp
    · exact hOpp
    · exact False.elim (L.firstTotal.asymm hFirst hOpp.1)

theorem Realizer.second_iff_not_first {α : Type} {P : α → α → Prop}
    (L : Realizer P) {x y : α} (hInc : Incomparable P x y) :
    L.second x y ↔ ¬ L.first x y := by
  constructor
  · intro hSecond hFirst
    exact hInc.2.1 ((L.intersection x y).mpr ⟨hFirst, hSecond⟩)
  · intro hNot
    rcases L.orient_incomparable hInc with hOpp | hOpp
    · exact False.elim (hNot hOpp.1)
    · exact hOpp.2

theorem Realizer.align_at_anchor {α : Type} {P : α → α → Prop}
    (L R : Realizer P) {a b : α} (hInc : Incomparable P a b) :
    ∃ swap : Bool, (L.aligned swap).opposite a b ↔ R.opposite a b := by
  classical
  by_cases hR : R.opposite a b
  · by_cases hL : L.opposite a b
    · refine ⟨false, ?_⟩
      constructor <;> intro _
      · exact hR
      · exact hL
    · have hReverse := (L.orient_incomparable hInc).resolve_left hL
      refine ⟨true, ?_⟩
      constructor <;> intro _
      · exact hR
      · exact ⟨hReverse.2, hReverse.1⟩
  · by_cases hL : L.opposite a b
    · refine ⟨true, ?_⟩
      constructor
      · intro hSwap
        exact False.elim (L.opposite_asymm hL ⟨hSwap.2, hSwap.1⟩)
      · intro hOpp
        exact False.elim (hR hOpp)
    · refine ⟨false, ?_⟩
      constructor
      · intro hOpp
        exact False.elim (hL hOpp)
      · intro hOpp
        exact False.elim (hR hOpp)

theorem forcing_trace_anchor_incomparable {n : ℕ} {rows : Fin n → Fin n → Bool}
    (anchor : FiniteArc n) (trace : List (ForcingEntry n)) (hTrace : trace ≠ [])
    (hAccept : checkForcingTrace rows anchor trace = true) :
    Incomparable (rowRelation rows) anchor.1 anchor.2 := by
  cases trace with
  | nil => exact False.elim (hTrace rfl)
  | cons entry rest =>
    have hValid : forcingEntryValid rows anchor [] entry := by
      by_contra hNot
      simp [checkForcingTrace, checkForcingTraceFrom, hNot] at hAccept
    rcases hValid with ⟨hInc, _, _, hParent⟩
    cases hEntry : entry.2 with
    | none =>
      simp only [hEntry] at hParent
      simpa only [hParent.2] using hInc
    | some parent =>
      simp only [hEntry] at hParent
      simp at hParent

theorem Realizer.forcing_trace_global_alignment {n : ℕ} {rows : Fin n → Fin n → Bool}
    (L R : Realizer (rowRelation rows)) (anchor : FiniteArc n) (trace : List (ForcingEntry n))
    (hAccept : checkForcingTrace rows anchor trace = true) :
    ∃ swap : Bool, ∀ arc ∈ trace.map Prod.fst,
      (L.aligned swap).opposite arc.1 arc.2 ↔ R.opposite arc.1 arc.2 := by
  by_cases hEmpty : trace = []
  · refine ⟨false, ?_⟩
    simp [hEmpty]
  · have hInc := forcing_trace_anchor_incomparable anchor trace hEmpty hAccept
    obtain ⟨swap, hAnchor⟩ := L.align_at_anchor R hInc
    refine ⟨swap, ?_⟩
    intro arc hArc
    exact ((L.aligned swap).checkForcingTrace_sound anchor trace hAccept arc hArc).trans
      (hAnchor.trans (R.checkForcingTrace_sound anchor trace hAccept arc hArc).symm)

#print axioms Realizer.forcing_trace_global_alignment

theorem Realizer.comparisons_agree_of_not_incomparable {α : Type} {P : α → α → Prop}
    (L R : Realizer P) {x y : α} (hNot : ¬ Incomparable P x y) :
    (L.first x y ↔ R.first x y) ∧ (L.second x y ↔ R.second x y) := by
  classical
  by_cases hxy : x = y
  · subst y
    constructor <;> constructor <;> intro h
    · exact False.elim (L.firstTotal.irrefl x h)
    · exact False.elim (R.firstTotal.irrefl x h)
    · exact False.elim (L.secondTotal.irrefl x h)
    · exact False.elim (R.secondTotal.irrefl x h)
  · have hComp : Comparable P x y := by
      by_contra hnComp
      apply hNot
      exact ⟨hxy, fun h => hnComp (Or.inl h), fun h => hnComp (Or.inr h)⟩
    rcases hComp with hP | hP
    · have hL := (L.intersection x y).mp hP
      have hR := (R.intersection x y).mp hP
      constructor <;> constructor <;> intro _
      · exact hR.1
      · exact hL.1
      · exact hR.2
      · exact hL.2
    · have hL := (L.intersection y x).mp hP
      have hR := (R.intersection y x).mp hP
      constructor <;> constructor <;> intro h
      · exact False.elim (L.firstTotal.asymm hL.1 h)
      · exact False.elim (R.firstTotal.asymm hR.1 h)
      · exact False.elim (L.secondTotal.asymm hL.2 h)
      · exact False.elim (R.secondTotal.asymm hR.2 h)

theorem Realizer.covered_comparisons_agree {n : ℕ} {rows : Fin n → Fin n → Bool}
    (L R : Realizer (rowRelation rows)) (covered : List (FiniteArc n))
    (hOpp : ∀ arc ∈ covered, L.opposite arc.1 arc.2 ↔ R.opposite arc.1 arc.2)
    {x y : Fin n} (hInc : Incomparable (rowRelation rows) x y)
    (hCovered : (x, y) ∈ covered ∨ (y, x) ∈ covered) :
    (L.first x y ↔ R.first x y) ∧ (L.second x y ↔ R.second x y) := by
  have hFirst : L.first x y ↔ R.first x y := by
    rcases hCovered with hForward | hReverse
    · exact (L.opposite_iff_first hInc).symm.trans
        ((hOpp (x, y) hForward).trans (R.opposite_iff_first hInc))
    · have hIncRev : Incomparable (rowRelation rows) y x :=
        ⟨hInc.1.symm, hInc.2.2, hInc.2.1⟩
      have hRev : L.first y x ↔ R.first y x :=
        (L.opposite_iff_first hIncRev).symm.trans
          ((hOpp (y, x) hReverse).trans (R.opposite_iff_first hIncRev))
      exact (L.firstTotal.reverse_iff_not hInc.1.symm).trans
        ((not_congr hRev).trans (R.firstTotal.reverse_iff_not hInc.1.symm).symm)
  exact ⟨hFirst, (L.second_iff_not_first hInc).trans
    ((not_congr hFirst).trans (R.second_iff_not_first hInc).symm)⟩

/-- Exactly the unresolved incomparability neighbors outside the undirected trace class. -/
def unresolvedNeighbors {n : ℕ} (rows : Fin n → Fin n → Bool)
    (trace : List (ForcingEntry n)) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => Incomparable (rowRelation rows) j i ∧
    (j, i) ∉ trace.map Prod.fst ∧ (i, j) ∉ trace.map Prod.fst)

def unresolvedDegree {n : ℕ} (rows : Fin n → Fin n → Bool)
    (trace : List (ForcingEntry n)) (i : Fin n) : ℕ := (unresolvedNeighbors rows trace i).card

/-- Every realizer has one alignment controlling BOTH ranks at EVERY vertex.
The budgets are computed from the original graph and the checked witness tree. -/
theorem Realizer.checked_forcing_rank_bounds {n : ℕ} {rows : Fin n → Fin n → Bool}
    (L R : Realizer (rowRelation rows)) (anchor : FiniteArc n) (trace : List (ForcingEntry n))
    (hAccept : checkForcingTrace rows anchor trace = true) :
    ∃ swap : Bool, ∀ i : Fin n,
      |(rank (L.aligned swap).first i : ℝ) - (rank R.first i : ℝ)| ≤
        unresolvedDegree rows trace i ∧
      |(rank (L.aligned swap).second i : ℝ) - (rank R.second i : ℝ)| ≤
        unresolvedDegree rows trace i := by
  classical
  obtain ⟨swap, hOpp⟩ := L.forcing_trace_global_alignment R anchor trace hAccept
  refine ⟨swap, ?_⟩
  intro i
  have hFirstSub : disagreements (L.aligned swap).first R.first i ⊆
      unresolvedNeighbors rows trace i := by
    intro j hj
    have hDis : ¬ ((L.aligned swap).first j i ↔ R.first j i) := by
      simpa [disagreements] using hj
    have hInc : Incomparable (rowRelation rows) j i := by
      by_contra hNot
      exact hDis ((L.aligned swap).comparisons_agree_of_not_incomparable R hNot).1
    have hCoveredNot : (j, i) ∉ trace.map Prod.fst ∧ (i, j) ∉ trace.map Prod.fst := by
      constructor
      · intro hIn
        exact hDis ((L.aligned swap).covered_comparisons_agree R _ hOpp hInc
          (Or.inl hIn)).1
      · intro hIn
        exact hDis ((L.aligned swap).covered_comparisons_agree R _ hOpp hInc
          (Or.inr hIn)).1
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hInc, hCoveredNot⟩
  have hSecondSub : disagreements (L.aligned swap).second R.second i ⊆
      unresolvedNeighbors rows trace i := by
    intro j hj
    have hDis : ¬ ((L.aligned swap).second j i ↔ R.second j i) := by
      simpa [disagreements] using hj
    have hInc : Incomparable (rowRelation rows) j i := by
      by_contra hNot
      exact hDis ((L.aligned swap).comparisons_agree_of_not_incomparable R hNot).2
    have hCoveredNot : (j, i) ∉ trace.map Prod.fst ∧ (i, j) ∉ trace.map Prod.fst := by
      constructor
      · intro hIn
        exact hDis ((L.aligned swap).covered_comparisons_agree R _ hOpp hInc
          (Or.inl hIn)).2
      · intro hIn
        exact hDis ((L.aligned swap).covered_comparisons_agree R _ hOpp hInc
          (Or.inr hIn)).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hInc, hCoveredNot⟩
  have hFirstCard : ((disagreements (L.aligned swap).first R.first i).card : ℝ) ≤
      unresolvedDegree rows trace i := by exact_mod_cast Finset.card_le_card hFirstSub
  have hSecondCard : ((disagreements (L.aligned swap).second R.second i).card : ℝ) ≤
      unresolvedDegree rows trace i := by exact_mod_cast Finset.card_le_card hSecondSub
  exact ⟨(abs_rank_sub_le_disagreements (L.aligned swap).first R.first i).trans hFirstCard,
    (abs_rank_sub_le_disagreements (L.aligned swap).second R.second i).trans hSecondCard⟩

#print axioms Realizer.checked_forcing_rank_bounds

end QuantyraNullCone
