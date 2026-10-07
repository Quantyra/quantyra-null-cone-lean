import QuantyraNullCone.Identifiability

namespace QuantyraNullCone

open MeasureTheory

def relabelOrder {n : ℕ} (π : Equiv.Perm (Fin n)) (code : OrderCode n) : OrderCode n :=
  fun i j => code (π i) (π j)

theorem sampledOrder_strict_partial_order {n : ℕ} (sample : Fin n → DiamondPoint) :
    (∀ i, ¬ CodeRelation (sampledOrder sample) i i) ∧
    (∀ i j k, CodeRelation (sampledOrder sample) i j →
      CodeRelation (sampledOrder sample) j k → CodeRelation (sampledOrder sample) i k) := by
  rw [sampledOrder_relation]
  constructor
  · intro i h
    exact lt_irrefl _ h.1
  · intro i j k hij hjk
    exact ⟨lt_trans hij.1 hjk.1, lt_trans hij.2 hjk.2⟩

def relabelSample {n : ℕ} (π : Equiv.Perm (Fin n)) :
    (Fin n → DiamondPoint) ≃ᵐ (Fin n → DiamondPoint) :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin n => DiamondPoint) π.symm

theorem relabelSample_apply {n : ℕ} (π : Equiv.Perm (Fin n))
    (sample : Fin n → DiamondPoint) (i : Fin n) : relabelSample π sample i = sample (π i) := by
  simpa only [Equiv.symm_apply_apply] using
    MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin n => DiamondPoint) π.symm sample (π i)

def relabelOrderEquiv {n : ℕ} (π : Equiv.Perm (Fin n)) : OrderCode n ≃ᵐ OrderCode n where
  toFun := relabelOrder π
  invFun := relabelOrder π.symm
  left_inv := by intro code; funext i j; simp [relabelOrder]
  right_inv := by intro code; funext i j; simp [relabelOrder]
  measurable_toFun := measurable_of_countable _
  measurable_invFun := measurable_of_countable _

theorem sampledOrder_relabel {n : ℕ} (π : Equiv.Perm (Fin n)) :
    relabelOrder π ∘ sampledOrder = sampledOrder ∘ relabelSample π := by
  funext sample i j
  simp only [Function.comp_apply, relabelOrder, sampledOrder, relabelSample_apply]

theorem InDensityClass.sample_relabel_preserving {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) {n : ℕ} (π : Equiv.Perm (Fin n)) :
    MeasurePreserving (relabelSample π) (sampleMeasure rho n) (sampleMeasure rho n) := by
  letI := h.isProbabilityMeasure
  exact measurePreserving_piCongrLeft (fun _ : Fin n => densityMeasure rho) π.symm

theorem InDensityClass.orderLaw_exchangeable {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) {n : ℕ} (π : Equiv.Perm (Fin n)) :
    (orderLaw rho n).map (relabelOrder π) = orderLaw rho n := by
  unfold orderLaw
  rw [Measure.map_map (measurable_of_countable _) (sampledOrder_measurable n),
    sampledOrder_relabel, ← Measure.map_map (sampledOrder_measurable n) (relabelSample π).measurable,
    (h.sample_relabel_preserving π).map_eq]

theorem InDensityClass.orderLaw_singleton_relabel {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) {n : ℕ} (π : Equiv.Perm (Fin n)) (code : OrderCode n) :
    orderLaw rho n {relabelOrder π code} = orderLaw rho n {code} := by
  let e := relabelOrderEquiv π
  have hPre : e ⁻¹' {e code} = {code} := by
    ext c
    simp only [Set.mem_preimage, Set.mem_singleton_iff, e.injective.eq_iff]
  have hMap : (orderLaw rho n).map e = orderLaw rho n := h.orderLaw_exchangeable π
  calc
    _ = (orderLaw rho n).map e {e code} := by rw [hMap]; rfl
    _ = orderLaw rho n (e ⁻¹' {e code}) := Measure.map_apply e.measurable (measurableSet_singleton _)
    _ = orderLaw rho n {code} := by rw [hPre]

#print axioms InDensityClass.sample_relabel_preserving
#print axioms sampledOrder_strict_partial_order
#print axioms InDensityClass.orderLaw_exchangeable
#print axioms InDensityClass.orderLaw_singleton_relabel

end QuantyraNullCone
