import QuantyraNullCone.DensityLPModel

namespace QuantyraNullCone

theorem density_difference_sum {k : ℕ} (x : Fin (k * k) → ℝ) (a b : Fin (k * k)) :
    (∑ j, (densityDifferenceCoefficient a b j : ℝ) * x j) = x a - x b := by
  simp only [densityDifferenceCoefficient, Rat.cast_sub, sub_mul, Finset.sum_sub_distrib]
  rw [density_objective_sum, density_objective_sum]

theorem density_negative_difference_sum {k : ℕ} (x : Fin (k * k) → ℝ) (a b : Fin (k * k)) :
    (∑ j, (-densityDifferenceCoefficient a b j : ℝ) * x j) = x b - x a := by
  simp only [neg_mul, Finset.sum_neg_distrib]
  rw [density_difference_sum]
  ring

theorem DensityCellFeasible.equality_matrix {k : ℕ} {F : ℝ → ℝ → ℝ} {radius : ℝ}
    {cell : ℕ → ℕ → ℝ} (h : DensityCellFeasible k F radius cell) (row : DensityEqualityRow k) :
    (∑ j, (densityEqualityCoefficient row j : ℝ) * densityCellVector cell j) = (k : ℝ) := by
  cases row with
  | row i =>
    change (∑ j, (densityRowCoefficient i j : ℝ) * densityCellVector cell j) = _
    rw [density_row_sum]
    exact h.rows i
  | column j =>
    change (∑ i, (densityColumnCoefficient j i : ℝ) * densityCellVector cell i) = _
    rw [density_column_sum]
    exact h.columns j

theorem DensityCellFeasible.inequality_matrix {k n : ℕ} {F : ℝ → ℝ → ℝ} {radius : ℚ}
    {cell : ℕ → ℕ → ℝ} (h : DensityCellFeasible k F radius cell)
    (counts : Fin (k + 1) → Fin (k + 1) → ℕ)
    (hCounts : ∀ p q, (counts p q : ℝ) / n = F ((p.val : ℝ) / k) ((q.val : ℝ) / k))
    (row : DensityInequalityRow k) :
    (∑ j, (densityInequalityCoefficient row j : ℝ) * densityCellVector cell j) ≤
      (densityInequalityRight n counts radius row : ℝ) := by
  cases row with
  | prefixUpper p q =>
    have hp : p.val ≤ k := Nat.le_of_lt_succ p.isLt
    have hq : q.val ≤ k := Nat.le_of_lt_succ q.isLt
    simp only [densityInequalityCoefficient, densityInequalityRight]
    rw [density_prefix_sum hp hq]
    push_cast
    rw [hCounts]
    exact (h.prefixBounds p.val q.val hp hq).2
  | prefixLower p q =>
    have hp : p.val ≤ k := Nat.le_of_lt_succ p.isLt
    have hq : q.val ≤ k := Nat.le_of_lt_succ q.isLt
    simp only [densityInequalityCoefficient, densityInequalityRight, Rat.cast_neg, neg_mul,
      Finset.sum_neg_distrib]
    rw [density_prefix_sum hp hq]
    push_cast
    rw [hCounts]
    have hLower := (h.prefixBounds p.val q.val hp hq).1
    nlinarith only [hLower]
  | horizontalForward i j =>
    have hi : i.val + 1 < k := by have hi := i.isLt; omega
    have hBound := (abs_le.mp (h.horizontal i.val j.val hi j.isLt)).1
    simp only [densityInequalityCoefficient, densityInequalityRight, density_difference_sum,
      density_cell_vector_flat, densityNeighborStart, densityNeighborEnd]
    push_cast
    linarith only [hBound]
  | horizontalReverse i j =>
    have hi : i.val + 1 < k := by have hi := i.isLt; omega
    have hBound := (abs_le.mp (h.horizontal i.val j.val hi j.isLt)).2
    simp only [densityInequalityCoefficient, densityInequalityRight, Rat.cast_neg,
      density_negative_difference_sum, density_cell_vector_flat, densityNeighborStart, densityNeighborEnd]
    push_cast
    exact hBound
  | verticalForward i j =>
    have hj : j.val + 1 < k := by have hj := j.isLt; omega
    have hBound := (abs_le.mp (h.vertical i.val j.val i.isLt hj)).1
    simp only [densityInequalityCoefficient, densityInequalityRight, density_difference_sum,
      density_cell_vector_flat, densityNeighborStart, densityNeighborEnd]
    push_cast
    linarith only [hBound]
  | verticalReverse i j =>
    have hj : j.val + 1 < k := by have hj := j.isLt; omega
    have hBound := (abs_le.mp (h.vertical i.val j.val i.isLt hj)).2
    simp only [densityInequalityCoefficient, densityInequalityRight, Rat.cast_neg,
      density_negative_difference_sum, density_cell_vector_flat, densityNeighborStart, densityNeighborEnd]
    push_cast
    exact hBound

/-- The actual original-K mean vector is feasible for the exact executable matrices. -/
theorem InDensityClass.density_LP_feasible {rho : DiamondPoint → ℝ} (h : InDensityClass rho)
    {n k : ℕ} (hn : 0 < n) (hk : 0 < k) (R : CDFReport n)
    (hAccuracy : ∀ s t : ℝ, |R.cdf s t - populationCDF rho s t| ≤ (R.radius : ℝ)) :
    (∀ i, (∑ j, (densityLP_A k i j : ℝ) * densityCellVector (densityGridCellMean rho k) j) ≤
      (densityLP_b R k i : ℝ)) ∧
    (∀ i, (∑ j, (densityLP_E k i j : ℝ) * densityCellVector (densityGridCellMean rho k) j) =
      (densityLP_d k i : ℝ)) ∧
    (∀ j : Fin (k * k), (1 / 2 : ℝ) ≤ densityCellVector (densityGridCellMean rho k) j ∧
      densityCellVector (densityGridCellMean rho k) j ≤ 3 / 2) := by
  have hFeasible := h.grid_cell_feasible hk R.cdf hAccuracy
  have hCounts : ∀ p q : Fin (k + 1), (reportLPCounts R k p q : ℝ) / n =
      R.cdf ((p.val : ℝ) / k) ((q.val : ℝ) / k) := fun p q => (R.corner_CDF hn hk p.val q.val).symm
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact hFeasible.inequality_matrix (reportLPCounts R k) hCounts ((densityInequalityRows k).get i)
  · intro i
    simpa [densityLP_E, densityLP_d] using hFeasible.equality_matrix ((densityEqualityRows k).get i)
  · intro j
    exact hFeasible.bounds _ _ (densityCellPair j).1.isLt (densityCellPair j).2.isLt

/-- Rational dual data bound actual cell means; primal feasibility is derived above. -/
theorem InDensityClass.density_LP_dual_sound {rho : DiamondPoint → ℝ} (h : InDensityClass rho)
    {n k : ℕ} (hn : 0 < n) (hk : 0 < k) (R : CDFReport n)
    (hAccuracy : ∀ s t : ℝ, |R.cdf s t - populationCDF rho s t| ≤ (R.radius : ℝ))
    (c : Fin (k * k) → ℚ) (y : Fin (densityInequalityRows k).length → ℚ)
    (z : Fin (densityEqualityRows k).length → ℚ) (hValid : rationalDualValid y = true) :
    (densityLPDualLower R k c y z : ℝ) ≤
      ∑ j, (c j : ℝ) * densityCellVector (densityGridCellMean rho k) j := by
  obtain ⟨hA, hE, hBox⟩ := h.density_LP_feasible hn hk R hAccuracy
  exact rationalDual_checker_sound (densityLP_A k) (densityLP_E k) (densityLP_b R k) (densityLP_d k)
    c (fun _ => 1 / 2) (fun _ => 3 / 2) y z _ hValid hA hE
    (fun j => by simpa using (hBox j).1) (fun j => by simpa using (hBox j).2)

#print axioms DensityCellFeasible.inequality_matrix
#print axioms InDensityClass.density_LP_feasible
#print axioms InDensityClass.density_LP_dual_sound

end QuantyraNullCone
