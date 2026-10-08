import QuantyraNullCone.DensityReportBands
import QuantyraNullCone.CDFReportCalibration

namespace QuantyraNullCone

open MeasureTheory

def densityReportTruth (rho : DiamondPoint → ℝ) : Bool → DiamondPoint → ℝ
  | false => rho
  | true => transposeDensity rho

theorem InDensityClass.density_report_truth {rho : DiamondPoint → ℝ} (h : InDensityClass rho)
    (swap : Bool) : InDensityClass (densityReportTruth rho swap) := by
  cases swap
  · exact h
  · exact h.transpose

theorem CDFReport.good_oriented_density {n : ℕ} (R : CDFReport n) {rho : DiamondPoint → ℝ}
    (hGood : R.Good rho) : ∃ swap : Bool, ∀ s t : ℝ,
    |R.cdf s t - populationCDF (densityReportTruth rho swap) s t| ≤ (R.radius : ℝ) := by
  obtain ⟨swap, hCDF⟩ := hGood
  refine ⟨swap, ?_⟩
  cases swap
  · exact hCDF
  · intro s t
    simpa only [densityReportTruth, populationCDF_transpose, orientCDF] using hCDF t s

/-- One density orientation simultaneously controls the CDF, all cell/point bands and histogram. -/
def DensityReport.Good {n : ℕ} (R : DensityReport n) (rho : DiamondPoint → ℝ) : Prop :=
  ∃ swap : Bool,
    (∀ s t : ℝ, |R.cdf.cdf s t - populationCDF (densityReportTruth rho swap) s t| ≤ (R.cdf.radius : ℝ)) ∧
      DensityBandsGood (densityReportTruth rho swap) R.bands

theorem InDensityClass.density_report_checked {rho : DiamondPoint → ℝ} (h : InDensityClass rho)
    {n : ℕ} (hn : 0 < n) (R : DensityReport n)
    (hCDF : R.cdf.Good rho) (hBands : checkDensityBands R.cdf R.bands = true) : R.Good rho := by
  obtain ⟨swap, hAccuracy⟩ := R.cdf.good_oriented_density hCDF
  exact ⟨swap, hAccuracy, (h.density_report_truth swap).density_bands_checked hn R.cdf R.bands hAccuracy hBands⟩

/-- A radius-one output is deterministically correct for all original-K densities. -/
theorem InDensityClass.density_report_radius_one {rho : DiamondPoint → ℝ} (h : InDensityClass rho)
    {n : ℕ} (hn : 0 < n) (R : DensityReport n) (hRadius : (1 : ℚ) ≤ R.cdf.radius)
    (hBands : checkDensityBands R.cdf R.bands = true) : R.Good rho :=
  h.density_report_checked hn R (R.cdf.radius_one_good h hn hRadius) hBands

theorem InDensityClass.density_sample_report_checked {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) {n q : ℕ} (hn : 0 < n) {eM eJ : ℚ} (w : Fin n → DiamondPoint)
    (hSquare : ∀ i, w i ∈ diamond)
    (hu : Function.Injective (fun i => (w i).1)) (hv : Function.Injective (fun i => (w i).2))
    (hAccuracy : w ∉ splitCalibrationBad rho n q eM eJ) (R : DensityReport n)
    (hCheck : checkDensityReport (sampledOrder w) R q eM eJ = true) : R.Good rho := by
  have hc : checkCDFReport (sampledOrder w) R.cdf q eM eJ = true ∧
      checkDensityBands R.cdf R.bands = true := of_decide_eq_true hCheck
  exact h.density_report_checked hn R (R.cdf.checked_good h hn w hSquare hu hv hAccuracy hc.1) hc.2

/-- Universal checked-output success is a predicate of the finite observed order code.
    Solver and certificate choices may depend on the data; calibration parameters are fixed. -/
def densityReportCoverage {n : ℕ} (rho : DiamondPoint → ℝ) (q : ℕ) (eM eJ : ℚ) :
    Set (Fin n → DiamondPoint) :=
  sampledOrder ⁻¹' {rows | ∀ R : DensityReport n, checkDensityReport rows R q eM eJ = true → R.Good rho}

theorem density_report_coverage_measurable {n : ℕ} (rho : DiamondPoint → ℝ) (q : ℕ) (eM eJ : ℚ) :
    MeasurableSet (densityReportCoverage (n := n) rho q eM eJ) :=
  (Set.to_countable _ |>.measurableSet).preimage (sampledOrder_measurable n)

/-- Exact actual original-K full-report coverage, with no assumed density accuracy or feasibility. -/
theorem InDensityClass.density_report_coverage {rho : DiamondPoint → ℝ} (h : InDensityClass rho)
    {n q : ℕ} (hn : 0 < n) {eM eJ bM bJ : ℚ} (hM : 0 ≤ eM) (hJ : 0 ≤ eJ) :
    1 - (splitRoundedFailureQ n q eM eJ bM bJ : ℝ) ≤
      (sampleMeasure rho n).real (densityReportCoverage (n := n) rho q eM eJ) := by
  letI : IsProbabilityMeasure (sampleMeasure rho n) := h.sample_isProbabilityMeasure n
  have hSub : (densityReportCoverage (n := n) rho q eM eJ)ᶜ ≤ᶠ[ae (sampleMeasure rho n)]
      splitCalibrationBad rho n q eM eJ := by
    filter_upwards [h.sample_ae_mem_diamond n, h.sample_coordinates_injective n] with w hSquare hInj
    intro hNot
    by_contra hAccuracy
    apply hNot
    intro R hCheck
    exact h.density_sample_report_checked hn w hSquare hInj.1 hInj.2 hAccuracy R hCheck
  have hMono := ENNReal.toReal_mono
    (measure_ne_top (sampleMeasure rho n) (splitCalibrationBad rho n q eM eJ)) (measure_mono_ae hSub)
  have hFailure := hMono.trans (h.split_rounded_failure (bM := bM) (bJ := bJ) hn hM hJ)
  change (sampleMeasure rho n).real (densityReportCoverage (n := n) rho q eM eJ)ᶜ ≤
    (splitRoundedFailureQ n q eM eJ bM bJ : ℝ) at hFailure
  rw [probReal_compl_eq_one_sub (density_report_coverage_measurable rho q eM eJ)] at hFailure
  linarith

theorem InDensityClass.density_report_fallback_probability {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) {n q : ℕ} (hn : 0 < n) {eM eJ : ℚ}
    (hCost : 1 ≤ splitRadiusQ q eM eJ) :
    (sampleMeasure rho n).real (densityReportCoverage (n := n) rho q eM eJ) = 1 := by
  letI : IsProbabilityMeasure (sampleMeasure rho n) := h.sample_isProbabilityMeasure n
  have hUniv : densityReportCoverage (n := n) rho q eM eJ = Set.univ := by
    apply Set.eq_univ_of_forall
    intro w R hCheck
    have hc : checkCDFReport (sampledOrder w) R.cdf q eM eJ = true ∧
        checkDensityBands R.cdf R.bands = true := of_decide_eq_true hCheck
    exact h.density_report_checked hn R
      (R.cdf.checked_fallback_good h hn (sampledOrder w) hCost hc.1) hc.2
  rw [hUniv, probReal_univ]

theorem InDensityClass.checked_density_report_coverage {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) {n q : ℕ} (hn : 0 < n) {eM eJ bM bJ delta : ℚ}
    (hCal : checkSplitCalibrationOrFallback n q eM eJ bM bJ delta = true) :
    1 - (delta : ℝ) ≤ (sampleMeasure rho n).real (densityReportCoverage (n := n) rho q eM eJ) := by
  have hc : 0 ≤ delta ∧ 0 < q ∧ 0 ≤ eM ∧ 0 ≤ eJ ∧
      (1 ≤ splitRadiusQ q eM eJ ∨ checkSplitCalibration n q eM eJ bM bJ delta = true) :=
    of_decide_eq_true hCal
  rcases hc.2.2.2.2 with hCost | hChecked
  · rw [h.density_report_fallback_probability hn hCost]
    have hDelta : (0 : ℝ) ≤ delta := by exact_mod_cast hc.1
    linarith
  · have hBudget : (splitRoundedFailureQ n q eM eJ bM bJ : ℝ) ≤ delta := by
      exact_mod_cast checked_split_rounded_budget hChecked
    have hCoverage := h.density_report_coverage (q := q) (bM := bM) (bJ := bJ) hn hc.2.2.1 hc.2.2.2.1
    linarith

#print axioms CDFReport.good_oriented_density
#print axioms InDensityClass.density_report_checked
#print axioms InDensityClass.density_report_radius_one
#print axioms density_report_coverage_measurable
#print axioms InDensityClass.density_report_coverage
#print axioms InDensityClass.density_report_fallback_probability
#print axioms InDensityClass.checked_density_report_coverage

end QuantyraNullCone
