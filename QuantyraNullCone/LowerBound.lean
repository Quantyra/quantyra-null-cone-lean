import QuantyraNullCone.LowerDataProcessing

namespace QuantyraNullCone

open MeasureTheory

/-- The explicit finite lower risk, for the actual single-order observation and
any independent probability-space random seed. Success means one global
orientation on the entire closed square; its complement is strict error. -/
theorem fourth_root_randomized_lower_bound {n : ℕ} (hn : 1 ≤ n)
    {Ω : Type*} [MeasurableSpace Ω] (ξ : Measure Ω) [IsProbabilityMeasure ξ]
    (estimate : UnlabeledOrderCode n → Ω → DiamondPoint → ℝ)
    (hMeas0 : MeasurableSet (LowerEstimateSuccess lowerFlat (lowerBandwidth n / 6) estimate))
    (hMeas1 : MeasurableSet
      (LowerEstimateSuccess (lowerAlternative (lowerBandwidth n)) (lowerBandwidth n / 6) estimate)) :
    (1 - lowerTVBound n (lowerBandwidth n)) / 2 ≤
      max (((unlabeledOrderLaw lowerFlat n).prod ξ).real
        (LowerEstimateSuccess lowerFlat (lowerBandwidth n / 6) estimate)ᶜ)
      (((unlabeledOrderLaw (lowerAlternative (lowerBandwidth n)) n).prod ξ).real
        (LowerEstimateSuccess (lowerAlternative (lowerBandwidth n)) (lowerBandwidth n / 6) estimate)ᶜ) := by
  obtain ⟨hh, hSmall⟩ := lower_bandwidth_bounds hn
  have hTest := lower_order_randomized_testing hh hSmall n ξ estimate hMeas0 hMeas1
  have hTV := lower_order_TV_bound hh hSmall n
  linarith

/-- Existential full-original-K form, retaining the explicit finite bound. -/
theorem fourth_root_lower_exists {n : ℕ} (hn : 1 ≤ n)
    {Ω : Type*} [MeasurableSpace Ω] (ξ : Measure Ω) [IsProbabilityMeasure ξ]
    (estimate : UnlabeledOrderCode n → Ω → DiamondPoint → ℝ)
    (hMeas : ∀ rho, InDensityClass rho →
      MeasurableSet (LowerEstimateSuccess rho (lowerBandwidth n / 6) estimate)) :
    ∃ rho, InDensityClass rho ∧ (1 - lowerTVBound n (lowerBandwidth n)) / 2 ≤
      (((unlabeledOrderLaw rho n).prod ξ).real
        (LowerEstimateSuccess rho (lowerBandwidth n / 6) estimate)ᶜ) := by
  obtain ⟨hh, hSmall⟩ := lower_bandwidth_bounds hn
  have hK := lower_alternative_in_class hh hSmall
  have hBound := fourth_root_randomized_lower_bound hn ξ estimate
    (hMeas lowerFlat lower_flat_in_class) (hMeas _ hK)
  rcases le_max_iff.mp hBound with h | h
  · exact ⟨lowerFlat, lower_flat_in_class, h⟩
  · exact ⟨lowerAlternative (lowerBandwidth n), hK, h⟩

/-- For n >= 16 no estimator, including randomized estimators, has uniform
95% radius n^(-1/4)/6 in the original class. The strict failure probability
exceeds 1/4, with no hypothesis that estimator outputs belong to the class. -/
theorem fourth_root_minimax_obstruction {n : ℕ} (hn : 16 ≤ n)
    {Ω : Type*} [MeasurableSpace Ω] (ξ : Measure Ω) [IsProbabilityMeasure ξ]
    (estimate : UnlabeledOrderCode n → Ω → DiamondPoint → ℝ)
    (hMeas : ∀ rho, InDensityClass rho →
      MeasurableSet (LowerEstimateSuccess rho ((n : ℝ) ^ (-1 / 4 : ℝ) / 6) estimate)) :
    ∃ rho, InDensityClass rho ∧ (1 / 4 : ℝ) <
      (((unlabeledOrderLaw rho n).prod ξ).real
        (LowerEstimateSuccess rho ((n : ℝ) ^ (-1 / 4 : ℝ) / 6) estimate)ᶜ) := by
  have hn1 : 1 ≤ n := by omega
  have hm : ∀ rho, InDensityClass rho →
      MeasurableSet (LowerEstimateSuccess rho (lowerBandwidth n / 6) estimate) := by
    simpa only [lower_bandwidth_large hn] using hMeas
  obtain ⟨rho, hK, hRisk⟩ := fourth_root_lower_exists hn1 ξ estimate hm
  refine ⟨rho, hK, ?_⟩
  have hStrict := (lower_probability_strict hn1).trans_le hRisk
  simpa only [lower_bandwidth_large hn] using hStrict

#print axioms fourth_root_randomized_lower_bound
#print axioms fourth_root_lower_exists
#print axioms fourth_root_minimax_obstruction

end QuantyraNullCone
