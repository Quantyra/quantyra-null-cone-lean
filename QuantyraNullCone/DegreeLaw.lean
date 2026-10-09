import QuantyraNullCone.DegreeEstimator

namespace QuantyraNullCone

open MeasureTheory

theorem density_estimate_common_orbit {rho sigma f : DiamondPoint → ℝ} {E : ℝ}
    (hR : DensityEstimateGood rho E f) (hS : DensityEstimateGood sigma E f) :
    (∀ p ∈ diamond, |rho p - sigma p| ≤ 2 * E) ∨
      (∀ p ∈ diamond, |rho p - transposeDensity sigma p| ≤ 2 * E) := by
  obtain ⟨bR, hR⟩ := hR
  obtain ⟨bS, hS⟩ := hS
  cases bR with
  | false =>
    cases bS with
    | false => exact Or.inl (fun p hp => cdf_close_from_common (hR p hp) (hS p hp))
    | true => exact Or.inr (fun p hp => cdf_close_from_common (hR p hp) (hS p hp))
  | true =>
    cases bS with
    | false =>
      right
      intro p hp
      have hpT := (transposePoint_mem_diamond p).mpr hp
      exact cdf_close_from_common (hR (transposePoint p) hpT) (hS (transposePoint p) hpT)
    | true =>
      left
      intro p hp
      have hpT := (transposePoint_mem_diamond p).mpr hp
      exact cdf_close_from_common (hR (transposePoint p) hpT) (hS (transposePoint p) hpT)

theorem InDensityClass.degree_estimate_intersects {rho sigma : DiamondPoint → ℝ}
    (hR : InDensityClass rho) (hS : InDensityClass sigma) {n : ℕ} (hn : 2 ≤ n)
    (hTV : unlabeledOrderLawTV rho sigma n < (9 / 10 : ℝ)) :
    ∃ code : UnlabeledOrderCode n,
      DensityEstimateGood rho (degreeRadius n) (selectedDegreeDensity code) ∧
      DensityEstimateGood sigma (degreeRadius n) (selectedDegreeDensity code) := by
  classical
  letI := hR.unlabeledOrderLaw_isProbabilityMeasure n
  letI := hS.unlabeledOrderLaw_isProbabilityMeasure n
  let A : Set (UnlabeledOrderCode n) :=
    {code | DensityEstimateGood rho (degreeRadius n) (selectedDegreeDensity code)}
  let B : Set (UnlabeledOrderCode n) :=
    {code | DensityEstimateGood sigma (degreeRadius n) (selectedDegreeDensity code)}
  by_contra hEmpty
  have hDisjoint : Disjoint A B := by
    rw [Set.disjoint_left]
    exact fun code hA hB => hEmpty ⟨code, hA, hB⟩
  have hSum : (unlabeledOrderLaw sigma n).real A + (unlabeledOrderLaw sigma n).real B ≤ 1 := by
    rw [← measureReal_union (μ := unlabeledOrderLaw sigma n) hDisjoint
      (densityEstimateGood_measurable _ _)]
    exact (measureReal_mono (Set.subset_univ _)).trans_eq probReal_univ
  have hA := hR.fourth_root_density_estimation hn
  have hB := hS.fourth_root_density_estimation hn
  have hEvent := finite_probability_event_bound (unlabeledOrderLaw rho n) (unlabeledOrderLaw sigma n) A
  change (19 / 20 : ℝ) ≤ (unlabeledOrderLaw rho n).real A at hA
  change (19 / 20 : ℝ) ≤ (unlabeledOrderLaw sigma n).real B at hB
  change (unlabeledOrderLaw rho n).real A - (unlabeledOrderLaw sigma n).real A ≤
    unlabeledOrderLawTV rho sigma n at hEvent
  linarith

theorem InDensityClass.degree_distance_small_TV {rho sigma : DiamondPoint → ℝ}
    (hR : InDensityClass rho) (hS : InDensityClass sigma) {n : ℕ} (hn : 2 ≤ n)
    (hTV : unlabeledOrderLawTV rho sigma n < (9 / 10 : ℝ)) :
    conformalDistance rho sigma ≤ 2 * degreeRadius n := by
  obtain ⟨code, hA, hB⟩ := hR.degree_estimate_intersects hS hn hTV
  rcases density_estimate_common_orbit hA hB with hDirect | hSwap
  · obtain ⟨p, hp, hValue⟩ := hR.coefficientDeviation_attained hS
    exact (min_le_left _ _).trans (hValue.symm ▸ hDirect p hp)
  · obtain ⟨p, hp, hValue⟩ := hR.coefficientDeviation_attained hS.transpose
    exact (min_le_right _ _).trans (hValue.symm ▸ hSwap p hp)

/-- Fourth-root stability from the actual law of a single unlabeled n-point
order. This makes no assertion that a law distance can be estimated from one order. -/
theorem InDensityClass.fourth_root_actual_law_inverse {rho sigma : DiamondPoint → ℝ}
    (hR : InDensityClass rho) (hS : InDensityClass sigma) {n : ℕ} (hn : 2 ≤ n) :
    conformalDistance rho sigma ≤ min 1
      (1300 * (Real.log (n : ℝ) / n) ^ (1 / 4 : ℝ) + (10 / 9 : ℝ) * unlabeledOrderLawTV rho sigma n) := by
  have hBounds := hR.conformalDistance_bounds hS
  have hTVnonneg : 0 ≤ unlabeledOrderLawTV rho sigma n := by
    unfold unlabeledOrderLawTV
    positivity
  have hRate : 0 ≤ (Real.log (n : ℝ) / n) ^ (1 / 4 : ℝ) :=
    Real.rpow_nonneg (log_ratio_positive hn).le _
  apply le_min hBounds.2
  by_cases hTV : unlabeledOrderLawTV rho sigma n < (9 / 10 : ℝ)
  · have h := hR.degree_distance_small_TV hS hn hTV
    have hRadius : degreeRadius n ≤ 650 * (Real.log (n : ℝ) / n) ^ (1 / 4 : ℝ) := min_le_right _ _
    linarith
  · have hTVlarge := le_of_not_gt hTV
    linarith

#print axioms density_estimate_common_orbit
#print axioms InDensityClass.degree_estimate_intersects
#print axioms InDensityClass.degree_distance_small_TV
#print axioms InDensityClass.fourth_root_actual_law_inverse

end QuantyraNullCone
