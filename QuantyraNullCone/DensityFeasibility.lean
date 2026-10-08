import QuantyraNullCone.DensityHistogram

namespace QuantyraNullCone

/-- Semantic restrictions of the density LP. The executable matrix representation
    is a separate bridge; feasibility is proved for actual original-K cell means. -/
structure DensityCellFeasible (k : ℕ) (F : ℝ → ℝ → ℝ) (radius : ℝ)
    (cell : ℕ → ℕ → ℝ) : Prop where
  bounds : ∀ i j : ℕ, i < k → j < k → (1 / 2 : ℝ) ≤ cell i j ∧ cell i j ≤ 3 / 2
  rows : ∀ i : Fin k, (∑ j : Fin k, cell i.val j.val) = (k : ℝ)
  columns : ∀ j : Fin k, (∑ i : Fin k, cell i.val j.val) = (k : ℝ)
  prefixBounds : ∀ p q : ℕ, p ≤ k → q ≤ k →
    (k : ℝ) ^ 2 * (F ((p : ℝ) / k) ((q : ℝ) / k) - radius) ≤
      (∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q, cell i j) ∧
    (∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q, cell i j) ≤
      (k : ℝ) ^ 2 * (F ((p : ℝ) / k) ((q : ℝ) / k) + radius)
  horizontal : ∀ i j : ℕ, i + 1 < k → j < k → |cell (i + 1) j - cell i j| ≤ 2 / (k : ℝ)
  vertical : ∀ i j : ℕ, i < k → j + 1 < k → |cell i (j + 1) - cell i j| ≤ 2 / (k : ℝ)

/-- On the CDF-quality event, actual cell means satisfy every LP restriction.
    No primal-feasibility, cell bounds, marginal sums or Lipschitz budget is assumed. -/
theorem InDensityClass.grid_cell_feasible {rho : DiamondPoint → ℝ} (h : InDensityClass rho)
    {k : ℕ} (hk : 0 < k) (F : ℝ → ℝ → ℝ) {radius : ℝ}
    (hAccuracy : ∀ s t : ℝ, |F s t - populationCDF rho s t| ≤ radius) :
    DensityCellFeasible k F radius (densityGridCellMean rho k) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hi hj
    exact h.grid_cell_bounds hk hi hj
  · exact h.grid_cell_row_fin hk
  · exact h.grid_cell_column_fin hk
  · intro p q hp hq
    exact h.grid_cell_prefix_restriction hk hp hq F (hAccuracy _ _)
  · intro i j hi hj
    exact h.grid_cell_horizontal hk hi hj
  · intro i j hi hj
    exact h.grid_cell_vertical hk hi hj

#print axioms InDensityClass.grid_cell_feasible

end QuantyraNullCone
