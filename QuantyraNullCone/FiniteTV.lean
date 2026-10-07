import QuantyraNullCone.OrderSelector

namespace QuantyraNullCone

open MeasureTheory

/-- The half-L1 formula controls every event on the finite observable space. -/
theorem finite_probability_event_bound {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (S : Set α) :
    μ.real S - ν.real S ≤ (1 / 2 : ℝ) * ∑ x : α, |μ.real {x} - ν.real {x}| := by
  classical
  let d : α → ℝ := fun x => μ.real {x} - ν.real {x}
  let s := Finset.univ.filter (fun x => x ∈ S)
  have hs : (s : Set α) = S := by ext x; simp [s]
  have hTotal : ∑ x : α, d x = 0 := by
    simp only [d, Finset.sum_sub_distrib, sum_measureReal_singleton,
      Finset.coe_univ, probReal_univ, sub_self]
  have hSelected : (∑ x : α, if x ∈ S then d x else 0) = μ.real S - ν.real S := by
    rw [← Finset.sum_filter]
    change (∑ x ∈ s, (μ.real {x} - ν.real {x})) = _
    rw [Finset.sum_sub_distrib, sum_measureReal_singleton, sum_measureReal_singleton, hs]
  have hPoint (x : α) : (if x ∈ S then d x else 0) ≤ (d x + |d x|) / 2 := by
    split_ifs
    · have h := le_abs_self (d x)
      linarith
    · have h := neg_abs_le (d x)
      linarith
  have hSum := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hPoint x)
  rw [hSelected, ← Finset.sum_div, Finset.sum_add_distrib, hTotal, zero_add] at hSum
  simpa only [d, div_eq_mul_inv, one_mul, mul_comm] using hSum

theorem InDensityClass.orderLawTV_event_bound {rho sigma : DiamondPoint → ℝ}
    (hR : InDensityClass rho) (hS : InDensityClass sigma) (n : ℕ) (S : Set (OrderCode n)) :
    (orderLaw rho n).real S - (orderLaw sigma n).real S ≤ orderLawTV rho sigma n := by
  letI := hR.orderLaw_isProbabilityMeasure n
  letI := hS.orderLaw_isProbabilityMeasure n
  exact finite_probability_event_bound _ _ S

theorem InDensityClass.orderCDFGood_intersects {rho sigma : DiamondPoint → ℝ}
    (hR : InDensityClass rho) (hS : InDensityClass sigma) {n : ℕ} (hn : 65536 ≤ n)
    (hTV : orderLawTV rho sigma n < (4 / 5 : ℝ)) :
    ∃ code : OrderCode n,
      OrderCDFGood rho (174 * (n : ℝ) ^ (-1 / 4 : ℝ)) code ∧
      OrderCDFGood sigma (174 * (n : ℝ) ^ (-1 / 4 : ℝ)) code := by
  classical
  letI := hR.orderLaw_isProbabilityMeasure n
  letI := hS.orderLaw_isProbabilityMeasure n
  let A : Set (OrderCode n) := {code | OrderCDFGood rho (174 * (n : ℝ) ^ (-1 / 4 : ℝ)) code}
  let B : Set (OrderCode n) := {code | OrderCDFGood sigma (174 * (n : ℝ) ^ (-1 / 4 : ℝ)) code}
  by_contra hEmpty
  have hDisjoint : Disjoint A B := by
    rw [Set.disjoint_left]
    exact fun code hA hB => hEmpty ⟨code, hA, hB⟩
  have hSum : (orderLaw sigma n).real A + (orderLaw sigma n).real B ≤ 1 := by
    rw [← measureReal_union (μ := orderLaw sigma n) hDisjoint (orderCDFGood_measurable _ _)]
    exact (measureReal_mono (Set.subset_univ _)).trans_eq probReal_univ
  have hA := hR.orderCDFGood_probability hn
  have hB := hS.orderCDFGood_probability hn
  have hEvent := hR.orderLawTV_event_bound hS n A
  change (9 / 10 : ℝ) ≤ (orderLaw rho n).real A at hA
  change (9 / 10 : ℝ) ≤ (orderLaw sigma n).real B at hB
  linarith

theorem cdf_close_from_common {f g z a : ℝ} (hf : |z - f| ≤ a) (hg : |z - g| ≤ a) :
    |f - g| ≤ 2 * a := by
  have h := abs_sub_le f z g
  rw [abs_sub_comm f z] at h
  linarith

theorem orderCDFGood_common_orbit {n : ℕ} {rho sigma : DiamondPoint → ℝ} {a : ℝ}
    {code : OrderCode n} (hR : OrderCDFGood rho a code) (hS : OrderCDFGood sigma a code) :
    (∀ s t : ℝ, |populationCDF rho s t - populationCDF sigma s t| ≤ 2 * a) ∨
    (∀ s t : ℝ, |populationCDF rho s t - populationCDF sigma t s| ≤ 2 * a) := by
  obtain ⟨bR, hR⟩ := hR
  obtain ⟨bS, hS⟩ := hS
  cases bR with
  | false =>
    cases bS with
    | false => exact Or.inl (fun s t => cdf_close_from_common (hR s t) (hS s t))
    | true => exact Or.inr (fun s t => cdf_close_from_common (hR s t) (hS t s))
  | true =>
    cases bS with
    | false => exact Or.inr (fun s t => cdf_close_from_common (hR s t) (hS t s))
    | true => exact Or.inl (fun s t => cdf_close_from_common (hR s t) (hS s t))

theorem InDensityClass.populationCDF_orbit_of_orderLawTV {rho sigma : DiamondPoint → ℝ}
    (hR : InDensityClass rho) (hS : InDensityClass sigma) {n : ℕ} (hn : 65536 ≤ n)
    (hTV : orderLawTV rho sigma n < (4 / 5 : ℝ)) :
    (∀ s t : ℝ, |populationCDF rho s t - populationCDF sigma s t| ≤
      348 * (n : ℝ) ^ (-1 / 4 : ℝ)) ∨
    (∀ s t : ℝ, |populationCDF rho s t - populationCDF sigma t s| ≤
      348 * (n : ℝ) ^ (-1 / 4 : ℝ)) := by
  obtain ⟨code, hA, hB⟩ := hR.orderCDFGood_intersects hS hn hTV
  have h := orderCDFGood_common_orbit hA hB
  simpa only [show 2 * (174 * (n : ℝ) ^ (-1 / 4 : ℝ)) =
    348 * (n : ℝ) ^ (-1 / 4 : ℝ) by ring] using h

#print axioms finite_probability_event_bound
#print axioms InDensityClass.orderLawTV_event_bound
#print axioms InDensityClass.orderCDFGood_intersects
#print axioms InDensityClass.populationCDF_orbit_of_orderLawTV

end QuantyraNullCone
