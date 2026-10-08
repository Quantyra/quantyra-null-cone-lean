import QuantyraNullCone.SplitCDF

namespace QuantyraNullCone

open MeasureTheory

/-- Decoded finite fields of an order-only CDF certificate. Positions are zero based. -/
structure CDFReport (n : ℕ) where
  first : Fin n → Fin n
  second : Fin n → Fin n
  anchor : FiniteArc n
  trace : List (ForcingEntry n)
  cutoff : ℕ
  radius : ℚ

def reportTrimRawQ {n : ℕ} (rows : OrderCode n) (R : CDFReport n) : ℚ :=
  ((trimTailCount rows R.trace R.cutoff : ℚ) + 2 * R.cutoff) / n

/-- Both caps match the runtime: first trim-budget cap, then CDF-radius cap. -/
def reportRadiusQ {n : ℕ} (rows : OrderCode n) (R : CDFReport n)
    (q : ℕ) (eM eJ : ℚ) : ℚ :=
  min 1 (min 1 (reportTrimRawQ rows R) + 2 * eM + eJ + 2 / q)

def checkCDFReport {n : ℕ} (rows : OrderCode n) (R : CDFReport n)
    (q : ℕ) (eM eJ : ℚ) : Bool :=
  decide (checkPositionRealizer rows R.first R.second = true ∧
    checkForcingTrace rows R.anchor R.trace = true ∧
    0 < q ∧ 0 ≤ eM ∧ 0 ≤ eJ ∧ reportRadiusQ rows R q eM eJ ≤ R.radius)

noncomputable def CDFReport.cdf {n : ℕ} (R : CDFReport n) : ℝ → ℝ → ℝ :=
  empiricalCDF (fun i => ((R.first i).val + 1 : ℝ) / n)
    (fun i => ((R.second i).val + 1 : ℝ) / n)

def CDFReport.Good {n : ℕ} (R : CDFReport n) (rho : DiamondPoint → ℝ) : Prop :=
  ∃ swap : Bool, ∀ s t : ℝ,
    |orientCDF R.cdf swap s t - populationCDF rho s t| ≤ (R.radius : ℝ)

theorem clipped_trim_radius {a b : ℝ} (hb : 0 ≤ b) :
    min 1 (min 1 a + b) = min 1 (a + b) := by
  by_cases ha : a ≤ 1
  · rw [min_eq_right ha]
  · have h1a : 1 ≤ a := le_of_not_ge ha
    rw [min_eq_left h1a, min_eq_left (by linarith : 1 ≤ 1 + b),
      min_eq_left (by linarith : 1 ≤ a + b)]

theorem CDFReport.checked_rankCDF {n : ℕ} (rows : OrderCode n) (R : CDFReport n)
    (hPos : checkPositionRealizer rows R.first R.second = true) :
    (checkedPositionRealizer rows R.first R.second hPos).rankCDF = R.cdf := by
  funext s t
  have hRanks := checkedPositionRealizer_ranks rows R.first R.second hPos
  unfold Realizer.rankCDF CDFReport.cdf
  congr 1
  · funext i
    rw [(hRanks i).1]
    push_cast
    rfl
  · funext i
    rw [(hRanks i).2]
    push_cast
    rfl

theorem CDFReport.radius_one_good {rho : DiamondPoint → ℝ} (h : InDensityClass rho)
    {n : ℕ} (hn : 0 < n) (R : CDFReport n) (hRadius : (1 : ℚ) ≤ R.radius) :
    R.Good rho := by
  have hR : (1 : ℝ) ≤ R.radius := by exact_mod_cast hRadius
  refine ⟨false, fun s t => ?_⟩
  exact (h.CDF_radius_one hn _ _ s t).trans hR

/-- Checker soundness on the actual accuracy event, including both runtime caps. -/
theorem CDFReport.checked_good {rho : DiamondPoint → ℝ} (h : InDensityClass rho)
    {n q : ℕ} (hn : 0 < n) {eM eJ : ℚ} (w : Fin n → DiamondPoint)
    (hSquare : ∀ i, w i ∈ diamond)
    (hu : Function.Injective (fun i => (w i).1))
    (hv : Function.Injective (fun i => (w i).2))
    (hGood : w ∉ splitCalibrationBad rho n q eM eJ) (R : CDFReport n)
    (hCheck : checkCDFReport (sampledOrder w) R q eM eJ = true) : R.Good rho := by
  have hc : checkPositionRealizer (sampledOrder w) R.first R.second = true ∧
      checkForcingTrace (sampledOrder w) R.anchor R.trace = true ∧
      0 < q ∧ 0 ≤ eM ∧ 0 ≤ eJ ∧ reportRadiusQ (sampledOrder w) R q eM eJ ≤ R.radius :=
    of_decide_eq_true hCheck
  let L := checkedPositionRealizer (sampledOrder w) R.first R.second hc.1
  have hM : (0 : ℝ) ≤ eM := by exact_mod_cast hc.2.2.2.1
  have hJ : (0 : ℝ) ≤ eJ := by exact_mod_cast hc.2.2.2.2.1
  obtain ⟨swap, hCDF⟩ := h.split_checked_sample_CDF hn hc.2.2.1 hM hJ w hSquare hu hv hGood
    L R.anchor R.trace hc.2.1
  have hEq : ∀ s t : ℝ, (L.aligned swap).rankCDF s t = orientCDF R.cdf swap s t := by
    cases swap
    · exact fun s t => congrFun (congrFun (R.checked_rankCDF (sampledOrder w) hc.1) s) t
    · intro s t
      change L.swap.rankCDF s t = R.cdf t s
      rw [Realizer.rankCDF_swap]
      exact congrFun (congrFun (R.checked_rankCDF (sampledOrder w) hc.1) t) s
  have hRadius : min 1 ((reportTrimRawQ (sampledOrder w) R : ℝ) + 2 * (eM : ℝ) +
      (eJ : ℝ) + 2 / (q : ℝ)) = (reportRadiusQ (sampledOrder w) R q eM eJ : ℝ) := by
    have hCost : 0 ≤ 2 * (eM : ℝ) + (eJ : ℝ) + 2 / (q : ℝ) := by positivity
    simpa [reportRadiusQ, add_assoc] using
      (clipped_trim_radius (a := (reportTrimRawQ (sampledOrder w) R : ℝ)) hCost).symm
  have hReported : (reportRadiusQ (sampledOrder w) R q eM eJ : ℝ) ≤ R.radius := by
    exact_mod_cast hc.2.2.2.2.2
  refine ⟨swap, fun s t => ?_⟩
  have hRaw := hCDF R.cutoff s t
  rw [hEq] at hRaw
  have hRaw' : |orientCDF R.cdf swap s t - populationCDF rho s t| ≤
      (reportTrimRawQ (sampledOrder w) R : ℝ) + 2 * (eM : ℝ) + (eJ : ℝ) + 2 / (q : ℝ) := by
    simpa [reportTrimRawQ, add_div, add_assoc] using hRaw
  have hOne : |orientCDF R.cdf swap s t - populationCDF rho s t| ≤ 1 := by
    have hEmp : 0 ≤ orientCDF R.cdf swap s t ∧ orientCDF R.cdf swap s t ≤ 1 := by
      cases swap
      · exact empirical_CDF_bounds hn _ _ s t
      · exact empirical_CDF_bounds hn _ _ t s
    have hPop := h.population_CDF_bounds s t
    exact abs_le.mpr ⟨by linarith [hEmp.1, hPop.2], by linarith [hEmp.2, hPop.1]⟩
  exact ((le_min hOne hRaw').trans_eq hRadius).trans hReported

/-- Success is a predicate of a finite order code, so all real thresholds are measurable. -/
def cdfReportCoverage {n : ℕ} (rho : DiamondPoint → ℝ) (q : ℕ) (eM eJ : ℚ)
    (report : OrderCode n → CDFReport n) : Set (Fin n → DiamondPoint) :=
  sampledOrder ⁻¹' {rows | checkCDFReport rows (report rows) q eM eJ = true → (report rows).Good rho}

theorem cdf_report_coverage_measurable {n : ℕ} (rho : DiamondPoint → ℝ)
    (q : ℕ) (eM eJ : ℚ) (report : OrderCode n → CDFReport n) :
    MeasurableSet (cdfReportCoverage rho q eM eJ report) :=
  (Set.to_countable _ |>.measurableSet).preimage (sampledOrder_measurable n)

/-- Any order-only, possibly data-dependent certificate selection has this coverage.
    Rejected certificates make no output claim; accepted outputs use one orientation. -/
theorem InDensityClass.cdf_report_coverage {rho : DiamondPoint → ℝ} (h : InDensityClass rho)
    {n q : ℕ} (hn : 0 < n) {eM eJ bM bJ : ℚ} (hM : 0 ≤ eM) (hJ : 0 ≤ eJ)
    (report : OrderCode n → CDFReport n) :
    1 - (splitRoundedFailureQ n q eM eJ bM bJ : ℝ) ≤
      (sampleMeasure rho n).real (cdfReportCoverage rho q eM eJ report) := by
  letI : IsProbabilityMeasure (sampleMeasure rho n) := h.sample_isProbabilityMeasure n
  have hSub : (cdfReportCoverage rho q eM eJ report)ᶜ ≤ᶠ[ae (sampleMeasure rho n)]
      splitCalibrationBad rho n q eM eJ := by
    filter_upwards [h.sample_ae_mem_diamond n, h.sample_coordinates_injective n] with w hSquare hInj
    intro hNot
    by_contra hGood
    apply hNot
    intro hCheck
    exact CDFReport.checked_good h hn w hSquare hInj.1 hInj.2 hGood _ hCheck
  have hMono := ENNReal.toReal_mono
    (measure_ne_top (sampleMeasure rho n) (splitCalibrationBad rho n q eM eJ)) (measure_mono_ae hSub)
  have hFailure := hMono.trans (h.split_rounded_failure (bM := bM) (bJ := bJ) hn hM hJ)
  change (sampleMeasure rho n).real (cdfReportCoverage rho q eM eJ report)ᶜ ≤
    (splitRoundedFailureQ n q eM eJ bM bJ : ℝ) at hFailure
  rw [probReal_compl_eq_one_sub (cdf_report_coverage_measurable rho q eM eJ report)] at hFailure
  linarith

theorem InDensityClass.checked_cdf_report_coverage {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) {n q : ℕ} (hn : 0 < n) {eM eJ bM bJ delta : ℚ}
    (hCal : checkSplitCalibration n q eM eJ bM bJ delta = true)
    (report : OrderCode n → CDFReport n) :
    1 - (delta : ℝ) ≤ (sampleMeasure rho n).real (cdfReportCoverage rho q eM eJ report) := by
  have hc : 0 ≤ eM ∧ 0 ≤ eJ ∧ splitMarginRawQ n eM ≤ bM ∧
      splitJointRawQ n q eJ ≤ bJ ∧ bM + bJ = delta := of_decide_eq_true hCal
  have hBudget : (splitRoundedFailureQ n q eM eJ bM bJ : ℝ) ≤ delta := by
    exact_mod_cast checked_split_rounded_budget hCal
  have hCoverage := h.cdf_report_coverage (q := q) (bM := bM) (bJ := bJ) hn hc.1 hc.2.1 report
  linarith

#print axioms CDFReport.checked_rankCDF
#print axioms CDFReport.radius_one_good
#print axioms CDFReport.checked_good
#print axioms cdf_report_coverage_measurable
#print axioms InDensityClass.cdf_report_coverage
#print axioms InDensityClass.checked_cdf_report_coverage

end QuantyraNullCone
