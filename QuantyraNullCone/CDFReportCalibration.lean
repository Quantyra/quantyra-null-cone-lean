import QuantyraNullCone.CDFReportEncoding

namespace QuantyraNullCone

open MeasureTheory

def splitRadiusQ (q : ℕ) (eM eJ : ℚ) : ℚ := 2 * eM + eJ + 2 / q

/-- Fixed calibration is either budget checked or forces deterministic CDF radius one. -/
def checkSplitCalibrationOrFallback (n q : ℕ) (eM eJ bM bJ delta : ℚ) : Bool :=
  decide (0 ≤ delta ∧ 0 < q ∧ 0 ≤ eM ∧ 0 ≤ eJ ∧
    (1 ≤ splitRadiusQ q eM eJ ∨ checkSplitCalibration n q eM eJ bM bJ delta = true))

theorem report_trim_raw_nonneg {n : ℕ} (rows : OrderCode n) (R : CDFReport n) :
    0 ≤ reportTrimRawQ rows R := by unfold reportTrimRawQ; positivity

theorem report_radius_fallback {n : ℕ} (rows : OrderCode n) (R : CDFReport n)
    {q : ℕ} {eM eJ : ℚ} (hCost : 1 ≤ splitRadiusQ q eM eJ) :
    reportRadiusQ rows R q eM eJ = 1 := by
  have hTrim : 0 ≤ min 1 (reportTrimRawQ rows R) := le_min (by norm_num) (report_trim_raw_nonneg rows R)
  have hTotal : 1 ≤ min 1 (reportTrimRawQ rows R) + 2 * eM + eJ + 2 / q := by
    unfold splitRadiusQ at hCost
    linarith
  exact min_eq_left hTotal

/-- Failed calibration search with cost at least one cannot produce a nontrivial accepted radius. -/
theorem CDFReport.checked_fallback_good {rho : DiamondPoint → ℝ} (h : InDensityClass rho)
    {n q : ℕ} (hn : 0 < n) {eM eJ : ℚ} (rows : OrderCode n) (R : CDFReport n)
    (hCost : 1 ≤ splitRadiusQ q eM eJ)
    (hCheck : checkCDFReport rows R q eM eJ = true) : R.Good rho := by
  have hc : checkPositionRealizer rows R.first R.second = true ∧
      checkForcingTrace rows R.anchor R.trace = true ∧
      0 < q ∧ 0 ≤ eM ∧ 0 ≤ eJ ∧ reportRadiusQ rows R q eM eJ ≤ R.radius := of_decide_eq_true hCheck
  have hRadius := hc.2.2.2.2.2
  rw [report_radius_fallback rows R hCost] at hRadius
  exact R.radius_one_good h hn hRadius

theorem InDensityClass.cdf_report_fallback_probability {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) {n q : ℕ} (hn : 0 < n) {eM eJ : ℚ}
    (hCost : 1 ≤ splitRadiusQ q eM eJ) (report : OrderCode n → CDFReport n) :
    (sampleMeasure rho n).real (cdfReportCoverage rho q eM eJ report) = 1 := by
  letI : IsProbabilityMeasure (sampleMeasure rho n) := h.sample_isProbabilityMeasure n
  have hUniv : cdfReportCoverage rho q eM eJ report = Set.univ := by
    apply Set.eq_univ_of_forall
    intro w hCheck
    exact CDFReport.checked_fallback_good h hn (sampledOrder w) _ hCost hCheck
  rw [hUniv, probReal_univ]

/-- Current split-DKW report coverage, including budget-search fallback. -/
theorem InDensityClass.checked_cdf_report_or_fallback {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) {n q : ℕ} (hn : 0 < n) {eM eJ bM bJ delta : ℚ}
    (hCal : checkSplitCalibrationOrFallback n q eM eJ bM bJ delta = true)
    (report : OrderCode n → CDFReport n) :
    1 - (delta : ℝ) ≤ (sampleMeasure rho n).real (cdfReportCoverage rho q eM eJ report) := by
  have hc : 0 ≤ delta ∧ 0 < q ∧ 0 ≤ eM ∧ 0 ≤ eJ ∧
      (1 ≤ splitRadiusQ q eM eJ ∨ checkSplitCalibration n q eM eJ bM bJ delta = true) :=
    of_decide_eq_true hCal
  rcases hc.2.2.2.2 with hCost | hChecked
  · rw [h.cdf_report_fallback_probability hn hCost report]
    have hDelta : (0 : ℝ) ≤ delta := by exact_mod_cast hc.1
    linarith
  · exact h.checked_cdf_report_coverage hn hChecked report

#print axioms report_radius_fallback
#print axioms CDFReport.checked_fallback_good
#print axioms InDensityClass.cdf_report_fallback_probability
#print axioms InDensityClass.checked_cdf_report_or_fallback

end QuantyraNullCone
