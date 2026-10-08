import QuantyraNullCone.DensityReportData

namespace QuantyraNullCone

def DensityBandsGood {k : ℕ} (rho : DiamondPoint → ℝ) (B : DensityBands k) : Prop :=
  ∀ cell : Fin (k * k),
    (B.cellLower cell : ℝ) ≤ densityCellVector (densityGridCellMean rho k) cell ∧
    densityCellVector (densityGridCellMean rho k) cell ≤ (B.cellUpper cell : ℝ) ∧
    ∀ p ∈ closedSquareCell (((densityCellPair cell).1.val : ℝ) / k)
      (((densityCellPair cell).2.val : ℝ) / k) (1 / k),
      (B.pointLower cell : ℝ) ≤ rho p ∧ rho p ≤ (B.pointUpper cell : ℝ) ∧
        |(B.histogram cell : ℝ) - rho p| ≤ (B.histogramError : ℝ)

theorem density_histogram_box {k : ℕ} (H : Fin (k * k) → ℚ)
    (hBox : ∀ cell, (1 / 2 : ℚ) ≤ H cell ∧ H cell ≤ 3 / 2) :
    ∀ i j : ℕ, i < k → j < k →
      (1 / 2 : ℝ) ≤ densityHistogramReal H i j ∧ densityHistogramReal H i j ≤ 3 / 2 := by
  intro i j hi hj
  have hb := hBox (densityCellFlat (⟨i, hi⟩, ⟨j, hj⟩))
  have hbR : (1 / 2 : ℝ) ≤ (H (densityCellFlat (⟨i, hi⟩, ⟨j, hj⟩)) : ℝ) ∧
      (H (densityCellFlat (⟨i, hi⟩, ⟨j, hj⟩)) : ℝ) ≤ 3 / 2 := by
    constructor
    · simpa using (Rat.cast_le (K := ℝ)).mpr hb.1
    · simpa using (Rat.cast_le (K := ℝ)).mpr hb.2
  simpa [densityHistogramReal, densityHistogramQ, hi, hj] using hbR

theorem density_histogram_corners {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (R : CDFReport n) (H : Fin (k * k) → ℚ) {eta : ℚ}
    (hEta : eta = densityHistogramViolationQ R H) :
    ∀ p q : ℕ, p ≤ k → q ≤ k →
      |histogramGridCDF (densityHistogramReal H) k p q - R.cdf ((p : ℝ) / k) ((q : ℝ) / k)| ≤
        (R.radius : ℝ) + (eta : ℝ) := by
  intro p q hp hq
  have hQ := density_histogram_violation_corner R H
    ⟨p, Nat.lt_succ_of_le hp⟩ ⟨q, Nat.lt_succ_of_le hq⟩
  change |densityHistogramCornerQ H p q - (reportCornerCount R k p q : ℚ) / n| ≤
    R.radius + densityHistogramViolationQ R H at hQ
  have hReal : |(densityHistogramCornerQ H p q : ℝ) -
      ((reportCornerCount R k p q : ℚ) / n : ℚ)| ≤
      (R.radius : ℝ) + (densityHistogramViolationQ R H : ℝ) := by exact_mod_cast hQ
  rw [density_histogram_corner_cast, ← R.corner_CDF_rational hn hk p q] at hReal
  simpa only [hEta] using hReal

/-- Every accepted density field is sound on the proved CDF-quality event.
    The fallback branch enforces full cell and point ranges and histogram error one. -/
theorem InDensityClass.density_bands_checked {rho : DiamondPoint → ℝ} (h : InDensityClass rho)
    {n k : ℕ} (hn : 0 < n) (R : CDFReport n) (B : DensityBands k)
    (hAccuracy : ∀ s t : ℝ, |R.cdf s t - populationCDF rho s t| ≤ (R.radius : ℝ))
    (hCheck : checkDensityBands R B = true) : DensityBandsGood rho B := by
  have hc : 0 < k ∧ (∀ cell, (1 / 2 : ℚ) ≤ B.histogram cell ∧ B.histogram cell ≤ 3 / 2) ∧
      B.cornerExcess = densityHistogramViolationQ R B.histogram ∧
      ((B.fallback = true ∧ DensityBandsFallbackFields B) ∨
        (B.fallback = false ∧ DensityBandsCertifiedFields R B)) := of_decide_eq_true hCheck
  obtain ⟨hk, hHistogram, hEta, hMode⟩ := hc
  have hBoxReal := density_histogram_box B.histogram hHistogram
  have hCorners := density_histogram_corners hn hk R B.histogram hEta
  rcases hMode with ⟨_hFlag, hFallback⟩ | ⟨_hFlag, hCertified⟩
  · obtain ⟨hFields, hError⟩ := hFallback
    intro cell
    obtain ⟨hCL, hCU, hPL, hPU⟩ := hFields cell
    have hi := (densityCellPair cell).1.isLt
    have hj := (densityCellPair cell).2.isLt
    have hCell : (1 / 2 : ℝ) ≤ densityCellVector (densityGridCellMean rho k) cell ∧
        densityCellVector (densityGridCellMean rho k) cell ≤ 3 / 2 := h.grid_cell_bounds hk hi hj
    refine ⟨by simpa [hCL] using hCell.1, by simpa [hCU] using hCell.2, ?_⟩
    intro p hp
    have hI := grid_cell_location hk hi
    have hJ := grid_cell_location hk hj
    have hTruth := h.bounds p (closed_square_cell_subset hI.1 hJ.1 hI.2 hJ.2 hp)
    have hCoeff : (1 / 2 : ℝ) ≤ (B.histogram cell : ℝ) ∧ (B.histogram cell : ℝ) ≤ 3 / 2 := by
      constructor
      · simpa using (Rat.cast_le (K := ℝ)).mpr (hHistogram cell).1
      · simpa using (Rat.cast_le (K := ℝ)).mpr (hHistogram cell).2
    have hOne : |(B.histogram cell : ℝ) - rho p| ≤ 1 := abs_le.mpr ⟨by linarith [hTruth.2, hCoeff.1],
      by linarith [hTruth.1, hCoeff.2]⟩
    exact ⟨by simpa [hPL] using hTruth.1, by simpa [hPU] using hTruth.2, by simpa [hError] using hOne⟩
  · obtain ⟨hFields, hError⟩ := hCertified
    intro cell
    obtain ⟨hD, hCL, hCU, _hNonempty, hPL, hPU⟩ := hFields cell
    have hCell := h.density_cell_dual_bounds hn hk R hAccuracy (B.dual cell) hD cell
    refine ⟨by simpa only [hCL] using hCell.1, by simpa only [hCU] using hCell.2, ?_⟩
    intro p hp
    have hPoint := h.density_point_dual_bounds hn hk R hAccuracy (B.dual cell) hD cell hp
    have hi := (densityCellPair cell).1.isLt
    have hj := (densityCellPair cell).2.isLt
    have hHist := h.histogram_point_error hk hi hj (densityHistogramReal B.histogram) R.cdf
      hBoxReal hAccuracy hCorners hp
    rw [density_histogram_flat_value] at hHist
    have hErrorReal : (B.histogramError : ℝ) =
        min 1 (8 * (R.radius : ℝ) * (k : ℝ) ^ 2 + 4 * (B.cornerExcess : ℝ) * (k : ℝ) ^ 2 + 2 / (k : ℝ)) := by
      simpa [densityHistogramErrorQ] using congrArg (fun x : ℚ => (x : ℝ)) hError
    rw [← hErrorReal] at hHist
    exact ⟨by simpa only [hPL] using hPoint.1, by simpa only [hPU] using hPoint.2, hHist⟩

#print axioms density_histogram_box
#print axioms density_histogram_corners
#print axioms InDensityClass.density_bands_checked

end QuantyraNullCone
