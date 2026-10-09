import QuantyraNullCone.LowerMoments

namespace QuantyraNullCone

open MeasureTheory

theorem finite_probability_weight_bound {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (a : α → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) :
    (∑ i, μ.real {i} * a i) - (∑ i, ν.real {i} * a i) ≤
      (1 / 2 : ℝ) * ∑ i, |μ.real {i} - ν.real {i}| := by
  classical
  let d := fun i => μ.real {i} - ν.real {i}
  have hTotal : ∑ i, d i = 0 := by
    simp only [d, Finset.sum_sub_distrib, sum_measureReal_singleton, Finset.coe_univ, probReal_univ, sub_self]
  have hPoint (i : α) : d i * a i ≤ (d i + |d i|) / 2 := by
    by_cases hd : 0 ≤ d i
    · rw [abs_of_nonneg hd]
      have h := mul_le_mul_of_nonneg_left (ha i).2 hd
      linarith only [h]
    · rw [abs_of_neg (lt_of_not_ge hd)]
      have h := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hd) (ha i).1
      linarith only [h]
  have hSum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hPoint i)
  rw [← Finset.sum_div, Finset.sum_add_distrib, hTotal, zero_add] at hSum
  simp only [d, sub_mul, Finset.sum_sub_distrib] at hSum
  linarith only [hSum]

/-- Exact decomposition over finite observations; the independent random seed
can have any measurable probability space. -/
theorem finite_seed_event_decomposition {α Ω : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace Ω] (μ : Measure α) (ξ : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ξ] {S : Set (α × Ω)} (hS : MeasurableSet S) :
    (μ.prod ξ).real S = ∑ i : α, μ.real {i} * ξ.real {ω | (i, ω) ∈ S} := by
  classical
  let slices (i : α) : Set (α × Ω) := ({i} : Set α) ×ˢ {ω | (i, ω) ∈ S}
  have hSlices (i : α) : MeasurableSet (slices i) :=
    (measurableSet_singleton i).prod (hS.preimage (measurable_const.prodMk measurable_id))
  have hDisjoint : Pairwise (fun i j => Disjoint (slices i) (slices j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    rintro ⟨k, ω⟩ hi hj
    exact hij (hi.1.symm.trans hj.1)
  have hUnion : (⋃ i, slices i) = S := by
    ext p
    simp only [Set.mem_iUnion, slices, Set.mem_prod, Set.mem_singleton_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨i, hi, h⟩
      simpa only [← hi] using h
    · intro hp
      exact ⟨p.1, rfl, hp⟩
  calc
    _ = (μ.prod ξ).real (⋃ i, slices i) := congrArg (μ.prod ξ).real hUnion.symm
    _ = ∑ i, (μ.prod ξ).real (slices i) := measureReal_iUnion_fintype hDisjoint hSlices
    _ = _ := by simp only [slices, measureReal_prod_prod]

theorem finite_seed_event_bound {α Ω : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace Ω] (μ ν : Measure α) (ξ : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ξ]
    {S : Set (α × Ω)} (hS : MeasurableSet S) :
    (μ.prod ξ).real S - (ν.prod ξ).real S ≤
      (1 / 2 : ℝ) * ∑ i, |μ.real {i} - ν.real {i}| := by
  rw [finite_seed_event_decomposition μ ξ hS, finite_seed_event_decomposition ν ξ hS]
  exact finite_probability_weight_bound μ ν _ (fun _ => ⟨measureReal_nonneg, measureReal_le_one⟩)

theorem finite_seed_two_point_lower_bound {α Ω : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace Ω] (μ ν : Measure α) (ξ : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ξ]
    {A B : Set (α × Ω)} (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : Disjoint A B) :
    (1 - (1 / 2 : ℝ) * ∑ i, |μ.real {i} - ν.real {i}|) / 2 ≤
      max ((μ.prod ξ).real Aᶜ) ((ν.prod ξ).real Bᶜ) := by
  have hSum : (ν.prod ξ).real A + (ν.prod ξ).real B ≤ 1 := by
    rw [← measureReal_union hAB hB]
    exact measureReal_le_one
  have hEvent := finite_seed_event_bound μ ν ξ hA
  have hAc := probReal_add_probReal_compl (μ := μ.prod ξ) hA
  have hBc := probReal_add_probReal_compl (μ := ν.prod ξ) hB
  have hMaxA := le_max_left ((μ.prod ξ).real Aᶜ) ((ν.prod ξ).real Bᶜ)
  have hMaxB := le_max_right ((μ.prod ξ).real Aᶜ) ((ν.prod ξ).real Bᶜ)
  linarith

def LowerEstimateSuccess {n : ℕ} {Ω : Type*} (rho : DiamondPoint → ℝ) (r : ℝ)
    (estimate : UnlabeledOrderCode n → Ω → DiamondPoint → ℝ) : Set (UnlabeledOrderCode n × Ω) :=
  {p | DensityEstimateGood rho r (estimate p.1 p.2)}

/-- Strict-error testing for the actual order laws and arbitrary independent
randomization. The divergence bound for these laws is supplied separately. -/
theorem lower_order_randomized_testing {h : ℝ} (hh : 0 < h) (hSmall : h ≤ 1 / 2)
    (n : ℕ) {Ω : Type*} [MeasurableSpace Ω] (ξ : Measure Ω) [IsProbabilityMeasure ξ]
    (estimate : UnlabeledOrderCode n → Ω → DiamondPoint → ℝ)
    (hMeas0 : MeasurableSet (LowerEstimateSuccess lowerFlat (h / 6) estimate))
    (hMeas1 : MeasurableSet (LowerEstimateSuccess (lowerAlternative h) (h / 6) estimate)) :
    (1 - unlabeledOrderLawTV lowerFlat (lowerAlternative h) n) / 2 ≤
      max (((unlabeledOrderLaw lowerFlat n).prod ξ).real
        (LowerEstimateSuccess lowerFlat (h / 6) estimate)ᶜ)
      (((unlabeledOrderLaw (lowerAlternative h) n).prod ξ).real
        (LowerEstimateSuccess (lowerAlternative h) (h / 6) estimate)ᶜ) := by
  letI := lower_flat_in_class.unlabeledOrderLaw_isProbabilityMeasure n
  letI := (lower_alternative_in_class hh hSmall).unlabeledOrderLaw_isProbabilityMeasure n
  apply finite_seed_two_point_lower_bound _ _ ξ hMeas0 hMeas1
  rw [Set.disjoint_left]
  intro p h0 h1
  exact lower_success_disjoint hh hSmall (estimate p.1 p.2) ⟨h0, h1⟩

#print axioms finite_probability_weight_bound
#print axioms finite_seed_event_decomposition
#print axioms finite_seed_event_bound
#print axioms finite_seed_two_point_lower_bound
#print axioms lower_order_randomized_testing

end QuantyraNullCone
