import QuantyraNullCone.DensityLPFeasible

namespace QuantyraNullCone

structure DensityDualPair (k : ℕ) where
  lowerY : Fin (densityInequalityRows k).length → ℚ
  lowerZ : Fin (densityEqualityRows k).length → ℚ
  upperY : Fin (densityInequalityRows k).length → ℚ
  upperZ : Fin (densityEqualityRows k).length → ℚ

def checkDensityDualPair {k : ℕ} (D : DensityDualPair k) : Bool :=
  decide (rationalDualValid D.lowerY = true ∧ rationalDualValid D.upperY = true)

def densityCellLowerQ {n k : ℕ} (R : CDFReport n) (D : DensityDualPair k)
    (cell : Fin (k * k)) : ℚ :=
  max (1 / 2) (densityLPDualLower R k (densityCellObjective cell) D.lowerY D.lowerZ)

def densityCellUpperQ {n k : ℕ} (R : CDFReport n) (D : DensityDualPair k)
    (cell : Fin (k * k)) : ℚ :=
  min (3 / 2) (-densityLPDualLower R k (fun j => -densityCellObjective cell j) D.upperY D.upperZ)

def densityPointLowerQ {n k : ℕ} (R : CDFReport n) (D : DensityDualPair k)
    (cell : Fin (k * k)) : ℚ := max (1 / 2) (densityCellLowerQ R D cell - 2 / k)

def densityPointUpperQ {n k : ℕ} (R : CDFReport n) (D : DensityDualPair k)
    (cell : Fin (k * k)) : ℚ := min (3 / 2) (densityCellUpperQ R D cell + 2 / k)

theorem density_negative_objective_sum {k : ℕ} (x : Fin (k * k) → ℝ) (cell : Fin (k * k)) :
    (∑ j, (-densityCellObjective cell j : ℝ) * x j) = -x cell := by
  simp only [neg_mul, Finset.sum_neg_distrib]
  rw [density_objective_sum]

/-- Both checked objectives give clipped cell bounds for the actual real density mean. -/
theorem InDensityClass.density_cell_dual_bounds {rho : DiamondPoint → ℝ} (h : InDensityClass rho)
    {n k : ℕ} (hn : 0 < n) (hk : 0 < k) (R : CDFReport n)
    (hAccuracy : ∀ s t : ℝ, |R.cdf s t - populationCDF rho s t| ≤ (R.radius : ℝ))
    (D : DensityDualPair k) (hValid : checkDensityDualPair D = true) (cell : Fin (k * k)) :
    (densityCellLowerQ R D cell : ℝ) ≤ densityCellVector (densityGridCellMean rho k) cell ∧
      densityCellVector (densityGridCellMean rho k) cell ≤ (densityCellUpperQ R D cell : ℝ) := by
  have hc : rationalDualValid D.lowerY = true ∧ rationalDualValid D.upperY = true := of_decide_eq_true hValid
  have hLower := h.density_LP_dual_sound hn hk R hAccuracy (densityCellObjective cell) D.lowerY D.lowerZ hc.1
  rw [density_objective_sum] at hLower
  have hUpper := h.density_LP_dual_sound hn hk R hAccuracy
    (fun j => -densityCellObjective cell j) D.upperY D.upperZ hc.2
  simp only [Rat.cast_neg, neg_mul, Finset.sum_neg_distrib, density_objective_sum] at hUpper
  have hUpper' : densityCellVector (densityGridCellMean rho k) cell ≤
      -(densityLPDualLower R k (fun j => -densityCellObjective cell j) D.upperY D.upperZ : ℝ) := by linarith
  have hBox := (h.density_LP_feasible hn hk R hAccuracy).2.2 cell
  constructor
  · simpa [densityCellLowerQ] using max_le hBox.1 hLower
  · simpa [densityCellUpperQ] using le_min hBox.2 hUpper'

/-- Exact reported pointwise expansion and clipping, for every closed-cell point. -/
theorem InDensityClass.density_point_dual_bounds {rho : DiamondPoint → ℝ} (h : InDensityClass rho)
    {n k : ℕ} (hn : 0 < n) (hk : 0 < k) (R : CDFReport n)
    (hAccuracy : ∀ s t : ℝ, |R.cdf s t - populationCDF rho s t| ≤ (R.radius : ℝ))
    (D : DensityDualPair k) (hValid : checkDensityDualPair D = true) (cell : Fin (k * k))
    {p : DiamondPoint} (hp : p ∈ closedSquareCell
      (((densityCellPair cell).1.val : ℝ) / k) (((densityCellPair cell).2.val : ℝ) / k) (1 / k)) :
    (densityPointLowerQ R D cell : ℝ) ≤ rho p ∧ rho p ≤ (densityPointUpperQ R D cell : ℝ) := by
  obtain ⟨hCellL, hCellU⟩ := h.density_cell_dual_bounds hn hk R hAccuracy D hValid cell
  have hi := (densityCellPair cell).1.isLt
  have hj := (densityCellPair cell).2.isLt
  have hBias := h.grid_cell_point_bias hk hi hj hp
  have hILoc := grid_cell_location hk hi
  have hJLoc := grid_cell_location hk hj
  have hBox := h.bounds p (closed_square_cell_subset hILoc.1 hJLoc.1 hILoc.2 hJLoc.2 hp)
  have hLower : (densityCellLowerQ R D cell : ℝ) - 2 / (k : ℝ) ≤ rho p := by
    have hb := (abs_le.mp hBias).2
    change (densityCellLowerQ R D cell : ℝ) ≤ densityGridCellMean rho k _ _ at hCellL
    linarith
  have hUpper : rho p ≤ (densityCellUpperQ R D cell : ℝ) + 2 / (k : ℝ) := by
    have hb := (abs_le.mp hBias).1
    change densityGridCellMean rho k _ _ ≤ (densityCellUpperQ R D cell : ℝ) at hCellU
    linarith
  constructor
  · simpa [densityPointLowerQ] using max_le hBox.1 hLower
  · simpa [densityPointUpperQ] using le_min hBox.2 hUpper

#print axioms InDensityClass.density_cell_dual_bounds
#print axioms InDensityClass.density_point_dual_bounds

end QuantyraNullCone
