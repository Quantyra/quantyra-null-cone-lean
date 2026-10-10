import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Pi

namespace QuantyraNullCone
open MeasureTheory ProbabilityTheory
noncomputable section

/-- An injectively selected subtuple of iid coordinates has the corresponding product law. -/
theorem iid_subtuple_preserving {Ω ι κ : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Fintype κ] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (e : κ → ι) (he : Function.Injective e) :
    MeasurePreserving (fun x : ι → Ω => fun k => x (e k))
      (Measure.pi (fun _ : ι => μ)) (Measure.pi (fun _ : κ => μ)) := by
  have hi : iIndepFun (fun i (x : ι → Ω) => x i) (Measure.pi (fun _ : ι => μ)) :=
    iIndepFun_pi (X := fun _ : ι => id) (fun _ => measurable_id.aemeasurable)
  refine ⟨measurable_pi_lambda _ (fun k => measurable_pi_apply (e k)), ?_⟩
  rw [iIndepFun.map_fun_eq_pi_map
    (fun k => (measurable_pi_apply (e k)).aemeasurable) (hi.precomp he)]
  congr 1
  funext k
  exact (measurePreserving_eval (fun _ : ι => μ) (e k)).map_eq

/-- Joint product law of all disjoint pairs, not merely pairwise independence. -/
theorem iid_disjoint_pairs_preserving {Ω ι κ : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Fintype κ] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (e : κ ⊕ κ → ι) (he : Function.Injective e) :
    MeasurePreserving (fun x : ι → Ω => fun k => (x (e (.inl k)),x (e (.inr k))))
      (Measure.pi (fun _ : ι => μ)) (Measure.pi (fun _ : κ => μ.prod μ)) := by
  have h1 := iid_subtuple_preserving μ e he
  have h2 := measurePreserving_sumPiEquivProdPi (fun _ : κ ⊕ κ => μ)
  have h3 := (measurePreserving_arrowProdEquivProdArrow Ω Ω κ (fun _ => μ) (fun _ => μ)).symm
  exact h3.comp (h2.comp h1)

def disjointPairLeft (n : ℕ) (k : Fin (n/2)) : Fin n :=
  ⟨2*k.val, by have := k.isLt; omega⟩

def disjointPairRight (n : ℕ) (k : Fin (n/2)) : Fin n :=
  ⟨2*k.val+1, by have := k.isLt; omega⟩

def disjointPairIndex (n : ℕ) : Fin (n/2) ⊕ Fin (n/2) → Fin n :=
  Sum.elim (disjointPairLeft n) (disjointPairRight n)

theorem disjointPairIndex_injective (n : ℕ) : Function.Injective (disjointPairIndex n) := by
  intro i j hij
  have hv := congrArg Fin.val hij
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      congr 1
      apply Fin.ext
      change 2*i.val = 2*j.val at hv
      omega
    | inr j =>
      change 2*i.val = 2*j.val+1 at hv
      omega
  | inr i =>
    cases j with
    | inl j =>
      change 2*i.val+1 = 2*j.val at hv
      omega
    | inr j =>
      congr 1
      apply Fin.ext
      change 2*i.val+1 = 2*j.val+1 at hv
      omega

theorem disjointPair_ne (n : ℕ) (k : Fin (n/2)) :
    disjointPairLeft n k ≠ disjointPairRight n k := by
  intro h
  have := congrArg Fin.val h
  change 2*k.val = 2*k.val+1 at this
  omega

theorem permuted_disjoint_pairs_preserving {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (e : Equiv.Perm (Fin n)) :
    MeasurePreserving (fun x : Fin n → Ω => fun k : Fin (n/2) =>
      (x (e (disjointPairLeft n k)),x (e (disjointPairRight n k))))
      (Measure.pi (fun _ : Fin n => μ)) (Measure.pi (fun _ : Fin (n/2) => μ.prod μ)) :=
  iid_disjoint_pairs_preserving μ (e ∘ disjointPairIndex n)
    (e.injective.comp (disjointPairIndex_injective n))

#print axioms iid_subtuple_preserving
#print axioms iid_disjoint_pairs_preserving
#print axioms disjointPairIndex_injective
#print axioms permuted_disjoint_pairs_preserving
end
end QuantyraNullCone
