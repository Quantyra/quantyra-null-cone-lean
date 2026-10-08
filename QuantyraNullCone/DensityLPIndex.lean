import QuantyraNullCone.DensityFeasibility
import QuantyraNullCone.FiniteLP
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.BigOperators

namespace QuantyraNullCone

def densityCellPair {k : ℕ} (j : Fin (k * k)) : Fin k × Fin k := finProdFinEquiv.symm j

def densityCellFlat {k : ℕ} (ij : Fin k × Fin k) : Fin (k * k) := finProdFinEquiv ij

theorem density_cell_flat_value {k : ℕ} (ij : Fin k × Fin k) :
    (densityCellFlat ij).val = ij.1.val * k + ij.2.val := by
  simp [densityCellFlat, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

theorem density_cell_pair_div_mod {k : ℕ} (j : Fin (k * k)) :
    (densityCellPair j).1.val = j.val / k ∧ (densityCellPair j).2.val = j.val % k := ⟨rfl, rfl⟩

def densityCellVector {k : ℕ} (cell : ℕ → ℕ → ℝ) (j : Fin (k * k)) : ℝ :=
  cell (densityCellPair j).1.val (densityCellPair j).2.val

theorem density_cell_vector_flat {k : ℕ} (cell : ℕ → ℕ → ℝ) (ij : Fin k × Fin k) :
    densityCellVector cell (densityCellFlat ij) = cell ij.1.val ij.2.val := by
  simp [densityCellVector, densityCellFlat, densityCellPair]

theorem density_flat_sum {k : ℕ} (f : Fin k × Fin k → ℝ) :
    (∑ j : Fin (k * k), f (densityCellPair j)) = ∑ i : Fin k, ∑ j : Fin k, f (i, j) := by
  have h := finProdFinEquiv.sum_comp (fun j : Fin (k * k) => f (densityCellPair j))
  simpa [densityCellPair, Fintype.sum_prod_type] using h.symm

theorem sum_fin_if_lt {k p : ℕ} (hp : p ≤ k) (f : ℕ → ℝ) :
    (∑ i : Fin k, if i.val < p then f i.val else 0) = ∑ i ∈ Finset.range p, f i := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < p then f i else 0) k, ← Finset.sum_filter]
  have hSet : (Finset.range k).filter (fun i => i < p) = Finset.range p := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hSet]

def densityRowCoefficient {k : ℕ} (i : Fin k) (j : Fin (k * k)) : ℚ :=
  if (densityCellPair j).1 = i then 1 else 0

def densityColumnCoefficient {k : ℕ} (i : Fin k) (j : Fin (k * k)) : ℚ :=
  if (densityCellPair j).2 = i then 1 else 0

def densityPrefixCoefficient {k : ℕ} (p q : ℕ) (j : Fin (k * k)) : ℚ :=
  if (densityCellPair j).1.val < p ∧ (densityCellPair j).2.val < q then 1 else 0

def densityCellObjective {k : ℕ} (target : Fin (k * k)) (j : Fin (k * k)) : ℚ :=
  if j = target then 1 else 0

theorem density_row_sum {k : ℕ} (cell : ℕ → ℕ → ℝ) (i : Fin k) :
    (∑ j, (densityRowCoefficient i j : ℝ) * densityCellVector cell j) =
      ∑ j : Fin k, cell i.val j.val := by
  simp only [densityRowCoefficient, apply_ite, Rat.cast_one, Rat.cast_zero, ite_mul, one_mul, zero_mul]
  change (∑ j : Fin (k * k), (fun ij : Fin k × Fin k =>
    if ij.1 = i then cell ij.1.val ij.2.val else 0) (densityCellPair j)) = _
  rw [density_flat_sum (fun ij : Fin k × Fin k => if ij.1 = i then cell ij.1.val ij.2.val else 0)]
  simp

theorem density_column_sum {k : ℕ} (cell : ℕ → ℕ → ℝ) (i : Fin k) :
    (∑ j, (densityColumnCoefficient i j : ℝ) * densityCellVector cell j) =
      ∑ j : Fin k, cell j.val i.val := by
  simp only [densityColumnCoefficient, apply_ite, Rat.cast_one, Rat.cast_zero, ite_mul, one_mul, zero_mul]
  change (∑ j : Fin (k * k), (fun ij : Fin k × Fin k =>
    if ij.2 = i then cell ij.1.val ij.2.val else 0) (densityCellPair j)) = _
  rw [density_flat_sum (fun ij : Fin k × Fin k => if ij.2 = i then cell ij.1.val ij.2.val else 0)]
  simp

theorem density_prefix_sum {k p q : ℕ} (hp : p ≤ k) (hq : q ≤ k) (cell : ℕ → ℕ → ℝ) :
    (∑ j, (densityPrefixCoefficient p q j : ℝ) * densityCellVector (k := k) cell j) =
      ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q, cell i j := by
  simp only [densityPrefixCoefficient, apply_ite, Rat.cast_one, Rat.cast_zero, ite_mul, one_mul, zero_mul]
  change (∑ j : Fin (k * k), (fun ij : Fin k × Fin k =>
    if ij.1.val < p ∧ ij.2.val < q then cell ij.1.val ij.2.val else 0) (densityCellPair j)) = _
  rw [density_flat_sum (fun ij : Fin k × Fin k =>
    if ij.1.val < p ∧ ij.2.val < q then cell ij.1.val ij.2.val else 0)]
  simp_rw [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero, sum_fin_if_lt hq]
  exact sum_fin_if_lt hp (fun i => ∑ j ∈ Finset.range q, cell i j)

theorem density_objective_sum {k : ℕ} (x : Fin (k * k) → ℝ) (target : Fin (k * k)) :
    (∑ j, (densityCellObjective target j : ℝ) * x j) = x target := by
  simp [densityCellObjective, apply_ite]

#print axioms density_cell_flat_value
#print axioms density_row_sum
#print axioms density_column_sum
#print axioms density_prefix_sum
#print axioms density_objective_sum

end QuantyraNullCone
