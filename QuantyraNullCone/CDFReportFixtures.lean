import QuantyraNullCone.CDFReportCalibration

namespace QuantyraNullCone

def cdfFixtureChain : OrderCode 3 := fun i j => decide (i < j)

def cdfFixtureReport : CDFReport 3 where
  first := id
  second := id
  anchor := (0, 0)
  trace := []
  cutoff := 0
  radius := 1 / 50

theorem cdf_fixture_tail : trimTailCount cdfFixtureChain [] 0 = 0 := by decide

theorem cdf_fixture_radius : reportRadiusQ cdfFixtureChain cdfFixtureReport 100 0 0 = 1 / 50 := by
  norm_num [reportRadiusQ, reportTrimRawQ, cdfFixtureReport, cdf_fixture_tail]

example : checkCDFReport cdfFixtureChain cdfFixtureReport 100 0 0 = true := by
  simp only [checkCDFReport, decide_eq_true_eq]
  exact ⟨by decide, by decide, by decide, by decide, by decide,
    by rw [cdf_fixture_radius]; exact le_rfl⟩
example : checkCDFReport cdfFixtureChain {cdfFixtureReport with radius := 0} 100 0 0 = false := by
  simp only [checkCDFReport, decide_eq_false_iff_not]
  intro h
  have hBad := h.2.2.2.2.2
  norm_num [reportRadiusQ, reportTrimRawQ, cdfFixtureReport, cdf_fixture_tail] at hBad
example : reportCornerCount cdfFixtureReport 3 1 1 = 1 := by decide
example : reportCornerCount cdfFixtureReport 3 0 3 = 0 := by decide
example : reportCornerCount cdfFixtureReport 3 3 3 = 3 := by decide
example : permutationPositions (by decide : 0 < 3) ![2, 0, 1] 2 = 0 := by decide
example : checkSplitCalibrationOrFallback 1 1 0 0 (1 / 40) (1 / 40) (1 / 20) = true := by
  norm_num [checkSplitCalibrationOrFallback, splitRadiusQ]
example : reportRadiusQ cdfFixtureChain cdfFixtureReport 1 0 0 = 1 :=
  report_radius_fallback _ _ (by norm_num [splitRadiusQ])

end QuantyraNullCone
