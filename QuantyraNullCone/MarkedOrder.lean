import QuantyraNullCone.BinomialGeometry

namespace QuantyraNullCone

open MeasureTheory

abbrev MarkedOrderIndex (n m : ℕ) := Fin n ⊕ Fin m
abbrev MarkedOrderCode (n m : ℕ) := MarkedOrderIndex n m → MarkedOrderIndex n m → Bool

def markedLocation {n m : ℕ} (anchors : Fin m → DiamondPoint)
    (sample : Fin n → DiamondPoint) : MarkedOrderIndex n m → DiamondPoint :=
  Sum.elim sample anchors

/-- Every directed chronological relation, including sample-anchor and anchor-anchor entries. -/
noncomputable def sampledMarkedOrder {n m : ℕ} (anchors : Fin m → DiamondPoint)
    (sample : Fin n → DiamondPoint) : MarkedOrderCode n m := by
  classical
  exact fun i j => decide (nullChronology (markedLocation anchors sample i)
    (markedLocation anchors sample j))

theorem marked_location_measurable {n m : ℕ} (anchors : Fin m → DiamondPoint)
    (i : MarkedOrderIndex n m) : Measurable (fun sample => markedLocation anchors sample i) := by
  cases i with
  | inl i => exact measurable_pi_apply i
  | inr i => exact measurable_const

theorem sampled_marked_order_measurable {n m : ℕ} (anchors : Fin m → DiamondPoint) :
    Measurable (sampledMarkedOrder (n := n) anchors) := by
  classical
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_pi_iff.mpr
  intro j
  apply measurable_to_bool
  have hU := measurableSet_lt (measurable_fst.comp (marked_location_measurable anchors i))
    (measurable_fst.comp (marked_location_measurable anchors j))
  have hV := measurableSet_lt (measurable_snd.comp (marked_location_measurable anchors i))
    (measurable_snd.comp (marked_location_measurable anchors j))
  have hset : (fun sample : Fin n → DiamondPoint => sampledMarkedOrder anchors sample i j) ⁻¹' {true} =
      {sample | (markedLocation anchors sample i).1 < (markedLocation anchors sample j).1} ∩
      {sample | (markedLocation anchors sample i).2 < (markedLocation anchors sample j).2} := by
    ext sample
    simp [sampledMarkedOrder, nullChronology]
  rw [hset]
  exact hU.inter hV

def markedRelabelIndex {n m : ℕ} (pi : Equiv.Perm (Fin n)) :
    MarkedOrderIndex n m → MarkedOrderIndex n m := Sum.map pi id

def relabelMarkedOrder {n m : ℕ} (pi : Equiv.Perm (Fin n))
    (code : MarkedOrderCode n m) : MarkedOrderCode n m :=
  fun i j => code (markedRelabelIndex pi i) (markedRelabelIndex pi j)

theorem marked_relabel_inverse {n m : ℕ} (pi : Equiv.Perm (Fin n))
    (i : MarkedOrderIndex n m) : markedRelabelIndex pi (markedRelabelIndex pi.symm i) = i := by
  cases i <;> simp [markedRelabelIndex]

theorem marked_relabel_comp {n m : ℕ} (pi tau : Equiv.Perm (Fin n))
    (i : MarkedOrderIndex n m) :
    markedRelabelIndex (tau.trans pi) i = markedRelabelIndex pi (markedRelabelIndex tau i) := by
  cases i <;> rfl

def markedOrderSetoid (n m : ℕ) : Setoid (MarkedOrderCode n m) where
  r code other := ∃ pi : Equiv.Perm (Fin n), relabelMarkedOrder pi code = other
  iseqv := {
    refl := by
      intro code
      refine ⟨Equiv.refl _, ?_⟩
      funext i j
      cases i <;> cases j <;> rfl
    symm := by
      rintro code other ⟨pi, rfl⟩
      refine ⟨pi.symm, ?_⟩
      funext i j
      simp only [relabelMarkedOrder, marked_relabel_inverse]
    trans := by
      rintro a b c ⟨pi, rfl⟩ ⟨tau, rfl⟩
      refine ⟨tau.trans pi, ?_⟩
      funext i j
      simp only [relabelMarkedOrder, marked_relabel_comp]
  }

abbrev UnlabeledMarkedOrderCode (n m : ℕ) := Quotient (markedOrderSetoid n m)

noncomputable instance (n m : ℕ) : Fintype (UnlabeledMarkedOrderCode n m) := Fintype.ofFinite _
instance (n m : ℕ) : MeasurableSpace (UnlabeledMarkedOrderCode n m) := ⊤

def forgetMarkedSampleLabels {n m : ℕ} (code : MarkedOrderCode n m) :
    UnlabeledMarkedOrderCode n m := Quotient.mk _ code

theorem forget_marked_labels_eq_iff {n m : ℕ} (code other : MarkedOrderCode n m) :
    forgetMarkedSampleLabels code = forgetMarkedSampleLabels other ↔
      ∃ pi : Equiv.Perm (Fin n), relabelMarkedOrder pi code = other := by
  constructor
  · exact Quotient.exact
  · intro h
    apply Quotient.sound
    exact h

noncomputable def sampledUnlabeledMarkedOrder {n m : ℕ} (anchors : Fin m → DiamondPoint)
    (sample : Fin n → DiamondPoint) : UnlabeledMarkedOrderCode n m :=
  forgetMarkedSampleLabels (sampledMarkedOrder anchors sample)

theorem sampled_unlabeled_marked_order_measurable {n m : ℕ} (anchors : Fin m → DiamondPoint) :
    Measurable (sampledUnlabeledMarkedOrder (n := n) anchors) :=
  (measurable_of_countable forgetMarkedSampleLabels).comp (sampled_marked_order_measurable anchors)

theorem sampled_marked_order_relabel {n m : ℕ} (anchors : Fin m → DiamondPoint)
    (sample : Fin n → DiamondPoint) (pi : Equiv.Perm (Fin n)) :
    sampledMarkedOrder anchors (sample ∘ pi) = relabelMarkedOrder pi (sampledMarkedOrder anchors sample) := by
  funext i j
  cases i <;> cases j <;> rfl

theorem sampled_unlabeled_marked_order_relabel {n m : ℕ} (anchors : Fin m → DiamondPoint)
    (sample : Fin n → DiamondPoint) (pi : Equiv.Perm (Fin n)) :
    sampledUnlabeledMarkedOrder anchors (sample ∘ pi) = sampledUnlabeledMarkedOrder anchors sample := by
  apply Eq.symm
  apply Quotient.sound
  exact ⟨pi, (sampled_marked_order_relabel anchors sample pi).symm⟩

end QuantyraNullCone
