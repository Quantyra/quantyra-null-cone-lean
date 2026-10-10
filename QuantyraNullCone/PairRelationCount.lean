import QuantyraNullCone.LorentzPairStatistic

namespace QuantyraNullCone
open scoped BigOperators
noncomputable section

def swapDistinctPair {ι : Type*} : DistinctPair ι ≃ DistinctPair ι where
  toFun p := ⟨(p.val.2,p.val.1),p.property.symm⟩
  invFun p := ⟨(p.val.2,p.val.1),p.property.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_distinctPair (n : ℕ) : Fintype.card (DistinctPair (Fin n)) = n*(n-1) := by
  let e : {p : Fin n × Fin n // p.1 = p.2} ≃ Fin n := {
    toFun := fun p => p.val.1
    invFun := fun i => ⟨(i,i),rfl⟩
    left_inv := by intro p; apply Subtype.ext; exact Prod.ext rfl p.property
    right_inv := fun _ => rfl }
  have he := Fintype.card_congr e
  change Fintype.card {p : Fin n × Fin n // ¬p.1 = p.2} = _
  rw [Fintype.card_subtype_compl,Fintype.card_prod,he,Fintype.card_fin,Nat.mul_sub_left_distrib]
  simp

/-- Counts every strict relation on distinct indices, including transitive relations. -/
def strictRelationCount {n : ℕ} (code : OrderCode n) : ℕ :=
  (Finset.univ.filter (fun p : DistinctPair (Fin n) => code p.val.1 p.val.2 = true)).card

theorem orderPairMean_eq_relation_count {n : ℕ} (code : OrderCode n)
    (ha : ∀ i j, code i j = true → code j i ≠ true) :
    orderPairMean code = 2*(strictRelationCount code : ℝ)/(n*(n-1) : ℕ) := by
  classical
  have he (p : DistinctPair (Fin n)) :
      (if code p.val.1 p.val.2 = true ∨ code p.val.2 p.val.1 = true then (1 : ℝ) else 0) =
      (if code p.val.1 p.val.2 = true then 1 else 0)+(if code p.val.2 p.val.1 = true then 1 else 0) := by
    by_cases h1 : code p.val.1 p.val.2 = true
    · simp [h1,ha _ _ h1]
    · by_cases h2 : code p.val.2 p.val.1 = true <;> simp [h1,h2]
  have hs : (∑ p : DistinctPair (Fin n), if code p.val.2 p.val.1 = true then (1 : ℝ) else 0) =
      ∑ p : DistinctPair (Fin n), if code p.val.1 p.val.2 = true then (1 : ℝ) else 0 :=
    Fintype.sum_equiv swapDistinctPair _ _ (fun _ => rfl)
  unfold orderPairMean pairMean
  rw [Fintype.expect_eq_sum_div_card]
  simp_rw [he]
  rw [Finset.sum_add_distrib,hs,card_distinctPair]
  simp only [Finset.sum_boole,strictRelationCount]
  ring

theorem sampled_order_relation_count3 {n : ℕ} (x : Fin n → LorentzPoint3) :
    orderPairMean (sampledOrder3 x) = 2*(strictRelationCount (sampledOrder3 x) : ℝ)/(n*(n-1) : ℕ) := by
  apply orderPairMean_eq_relation_count
  intro i j hij hji
  have h1 : chronological3 (x i) (x j) := by simpa [sampledOrder3] using hij
  have h2 : chronological3 (x j) (x i) := by simpa [sampledOrder3] using hji
  exact chronological3_irreflexive _ (chronological3_transitive h1 h2)

#print axioms card_distinctPair
#print axioms orderPairMean_eq_relation_count
#print axioms sampled_order_relation_count3
end
end QuantyraNullCone
