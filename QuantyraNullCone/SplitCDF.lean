import QuantyraNullCone.SplitCalibration
import QuantyraNullCone.FiniteCDF
import QuantyraNullCone.FinitePositions

namespace QuantyraNullCone

open MeasureTheory

theorem empirical_CDF_bounds {n : ℕ} (hn : 0 < n) (u v : Fin n → ℝ) (s t : ℝ) :
    0 ≤ empiricalCDF u v s t ∧ empiricalCDF u v s t ≤ 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hCard : (rectangleCount u v s t).card ≤ n := by
    simpa using Finset.card_le_card (Finset.subset_univ (rectangleCount u v s t))
  constructor
  · unfold empiricalCDF
    positivity
  · unfold empiricalCDF
    apply (div_le_one hnR).mpr
    exact_mod_cast hCard

theorem InDensityClass.population_CDF_bounds {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) (s t : ℝ) :
    0 ≤ populationCDF rho s t ∧ populationCDF rho s t ≤ 1 := by
  letI : IsProbabilityMeasure (densityMeasure rho) := h.isProbabilityMeasure
  exact ⟨measureReal_nonneg, measureReal_le_one⟩

/-- A CDF radius of one is deterministic for arbitrary coordinates. -/
theorem InDensityClass.CDF_radius_one {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) {n : ℕ} (hn : 0 < n) (u v : Fin n → ℝ) (s t : ℝ) :
    |empiricalCDF u v s t - populationCDF rho s t| ≤ 1 := by
  obtain ⟨hE0, hE1⟩ := empirical_CDF_bounds hn u v s t
  obtain ⟨hP0, hP1⟩ := h.population_CDF_bounds s t
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem split_accuracy_marginal {n q : ℕ} {rho : DiamondPoint → ℝ}
    {eM eJ : ℝ} {w : Fin n → DiamondPoint}
    (hGood : w ∉ splitCalibrationBad rho n q eM eJ)
    (hU : ∀ i, (w i).1 ∈ Set.Icc (0 : ℝ) 1)
    (hV : ∀ i, (w i).2 ∈ Set.Icc (0 : ℝ) 1) :
    (∀ i, |marginalCDF (fun j => (w j).1) (w i).1 - (w i).1| ≤ eM) ∧
    (∀ i, |marginalCDF (fun j => (w j).2) (w i).2 - (w i).2| ≤ eM) := by
  constructor
  · intro i
    apply le_of_not_gt
    intro hBad
    apply hGood
    apply Or.inl
    apply Or.inl
    change ∃ t : ℝ, eM < |marginalCDF (coordinateSample Prod.fst w) t - uniformPopulationCDF t|
    exact ⟨(w i).1, by simpa [coordinateSample, uniform_population_CDF_unit (hU i)] using hBad⟩
  · intro i
    apply le_of_not_gt
    intro hBad
    apply hGood
    apply Or.inl
    apply Or.inr
    change ∃ t : ℝ, eM < |marginalCDF (coordinateSample Prod.snd w) t - uniformPopulationCDF t|
    exact ⟨(w i).2, by simpa [coordinateSample, uniform_population_CDF_unit (hV i)] using hBad⟩

theorem split_accuracy_joint_grid {n q : ℕ} {rho : DiamondPoint → ℝ}
    {eM eJ : ℝ} {w : Fin n → DiamondPoint}
    (hGood : w ∉ splitCalibrationBad rho n q eM eJ) :
    ∀ j k : ℕ, j ≤ q → k ≤ q →
      |empiricalCDF (fun i => (w i).1) (fun i => (w i).2) ((j : ℝ) / q) ((k : ℝ) / q) -
        populationCDF rho ((j : ℝ) / q) ((k : ℝ) / q)| ≤ eJ := by
  intro j k hj hk
  apply le_of_not_gt
  intro hBad
  apply hGood
  apply Or.inr
  apply Set.mem_iUnion.mpr
  exact ⟨(⟨j, Nat.lt_succ_of_le hj⟩, ⟨k, Nat.lt_succ_of_le hk⟩), hBad⟩

/-- Actual accuracy-event membership discharges all empirical accuracy premises.
    One orientation controls every cutoff and every real threshold. -/
theorem InDensityClass.split_checked_sample_CDF {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) {n q : ℕ} (hn : 0 < n) (hq : 0 < q)
    {eM eJ : ℝ} (hM : 0 ≤ eM) (hJ : 0 ≤ eJ) (w : Fin n → DiamondPoint)
    (hSquare : ∀ i, w i ∈ diamond)
    (hu : Function.Injective (fun i => (w i).1))
    (hv : Function.Injective (fun i => (w i).2))
    (hGood : w ∉ splitCalibrationBad rho n q eM eJ)
    (L : Realizer (rowRelation (sampledOrder w)))
    (anchor : FiniteArc n) (trace : List (ForcingEntry n))
    (hAccept : checkForcingTrace (sampledOrder w) anchor trace = true) :
    ∃ swap : Bool, ∀ cutoff : ℕ, ∀ s t : ℝ,
      |(L.aligned swap).rankCDF s t - populationCDF rho s t| ≤
        (trimTailCount (sampledOrder w) trace cutoff : ℝ) / n + 2 * cutoff / n +
          2 * eM + eJ + 2 / q := by
  have hU : ∀ i, (w i).1 ∈ Set.Icc (0 : ℝ) 1 := fun i => (hSquare i).1
  have hV : ∀ i, (w i).2 ∈ Set.Icc (0 : ℝ) 1 := fun i => (hSquare i).2
  obtain ⟨hMU, hMV⟩ := split_accuracy_marginal hGood hU hV
  have hGrid := split_accuracy_joint_grid hGood
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hRows : ∀ i j, rowRelation (sampledOrder w) i j ↔
      Chronological (fun i => (w i).1) (fun i => (w i).2) i j := by
    intro i j
    simp [rowRelation, sampledOrder, Chronological]
  have hGrid' : ∀ j k : ℕ, j ≤ q → k ≤ q →
      |empiricalCDF (fun i => (w i).1) (fun i => (w i).2)
        ((j : ℝ) * (1 / q)) ((k : ℝ) * (1 / q)) -
        populationCDF rho ((j : ℝ) * (1 / q)) ((k : ℝ) * (1 / q))| ≤ eJ := by
    simpa only [mul_one_div] using hGrid
  obtain ⟨swap, hCDF⟩ := checked_trimmed_CDF h hn (sampledOrder w)
    (fun i => (w i).1) (fun i => (w i).2) hu hv hRows hU hV L anchor trace hAccept
    hM hJ (one_div_pos.mpr hqR) (mul_one_div_cancel hqR.ne') hMU hMV hGrid'
  exact ⟨swap, by simpa only [mul_one_div] using hCDF⟩

#print axioms empirical_CDF_bounds
#print axioms InDensityClass.CDF_radius_one
#print axioms InDensityClass.split_checked_sample_CDF

end QuantyraNullCone
