import QuantyraNullCone.DensityLPIndex
import QuantyraNullCone.CDFReportEncoding
import Mathlib.Data.List.FinRange

namespace QuantyraNullCone

inductive DensityEqualityRow (k : ℕ) where
  | row (i : Fin k)
  | column (j : Fin k)
  deriving DecidableEq

inductive DensityInequalityRow (k : ℕ) where
  | prefixUpper (p q : Fin (k + 1))
  | prefixLower (p q : Fin (k + 1))
  | horizontalForward (i : Fin (k - 1)) (j : Fin k)
  | horizontalReverse (i : Fin (k - 1)) (j : Fin k)
  | verticalForward (i : Fin k) (j : Fin (k - 1))
  | verticalReverse (i : Fin k) (j : Fin (k - 1))
  deriving DecidableEq

def densityNeighborStart {k : ℕ} (i : Fin (k - 1)) : Fin k :=
  ⟨i.val, by have hi := i.isLt; omega⟩

def densityNeighborEnd {k : ℕ} (i : Fin (k - 1)) : Fin k :=
  ⟨i.val + 1, by have hi := i.isLt; omega⟩

def densityEqualityRows (k : ℕ) : List (DensityEqualityRow k) :=
  (List.finRange k).map DensityEqualityRow.row ++ (List.finRange k).map DensityEqualityRow.column

/-- Exact runtime loop order: each corner and neighbor row followed by its negative. -/
def densityInequalityRows (k : ℕ) : List (DensityInequalityRow k) :=
  (List.finRange (k + 1)).flatMap (fun p =>
    (List.finRange (k + 1)).flatMap (fun q => [.prefixUpper p q, .prefixLower p q])) ++
  (List.finRange k).flatMap (fun i => (List.finRange k).flatMap (fun j =>
    (if hi : i.val + 1 < k then
      [.horizontalForward ⟨i.val, by omega⟩ j, .horizontalReverse ⟨i.val, by omega⟩ j] else []) ++
    (if hj : j.val + 1 < k then
      [.verticalForward i ⟨j.val, by omega⟩, .verticalReverse i ⟨j.val, by omega⟩] else [])))

def densityEqualityCoefficient {k : ℕ} (row : DensityEqualityRow k) (j : Fin (k * k)) : ℚ :=
  match row with
  | .row i => densityRowCoefficient i j
  | .column i => densityColumnCoefficient i j

def densityDifferenceCoefficient {k : ℕ} (a b j : Fin (k * k)) : ℚ :=
  densityCellObjective a j - densityCellObjective b j

def densityInequalityCoefficient {k : ℕ} (row : DensityInequalityRow k) (cell : Fin (k * k)) : ℚ :=
  match row with
  | .prefixUpper p q => densityPrefixCoefficient p.val q.val cell
  | .prefixLower p q => -densityPrefixCoefficient p.val q.val cell
  | .horizontalForward i j => densityDifferenceCoefficient
      (densityCellFlat (densityNeighborStart i, j)) (densityCellFlat (densityNeighborEnd i, j)) cell
  | .horizontalReverse i j => -densityDifferenceCoefficient
      (densityCellFlat (densityNeighborStart i, j)) (densityCellFlat (densityNeighborEnd i, j)) cell
  | .verticalForward i j => densityDifferenceCoefficient
      (densityCellFlat (i, densityNeighborStart j)) (densityCellFlat (i, densityNeighborEnd j)) cell
  | .verticalReverse i j => -densityDifferenceCoefficient
      (densityCellFlat (i, densityNeighborStart j)) (densityCellFlat (i, densityNeighborEnd j)) cell

def densityInequalityRight {k : ℕ} (n : ℕ) (counts : Fin (k + 1) → Fin (k + 1) → ℕ)
    (radius : ℚ) (row : DensityInequalityRow k) : ℚ :=
  match row with
  | .prefixUpper p q => (k : ℚ) ^ 2 * ((counts p q : ℚ) / n + radius)
  | .prefixLower p q => (k : ℚ) ^ 2 * (radius - (counts p q : ℚ) / n)
  | .horizontalForward _ _ => 2 / k
  | .horizontalReverse _ _ => 2 / k
  | .verticalForward _ _ => 2 / k
  | .verticalReverse _ _ => 2 / k

def reportLPCounts {n : ℕ} (R : CDFReport n) (k : ℕ) : Fin (k + 1) → Fin (k + 1) → ℕ :=
  fun p q => reportCornerCount R k p.val q.val

def densityLP_A (k : ℕ) : Fin (densityInequalityRows k).length → Fin (k * k) → ℚ :=
  fun row cell => densityInequalityCoefficient ((densityInequalityRows k).get row) cell

def densityLP_E (k : ℕ) : Fin (densityEqualityRows k).length → Fin (k * k) → ℚ :=
  fun row cell => densityEqualityCoefficient ((densityEqualityRows k).get row) cell

def densityLP_b {n : ℕ} (R : CDFReport n) (k : ℕ) : Fin (densityInequalityRows k).length → ℚ :=
  fun row => densityInequalityRight n (reportLPCounts R k) R.radius ((densityInequalityRows k).get row)

def densityLP_d (k : ℕ) : Fin (densityEqualityRows k).length → ℚ := fun _ => k

def densityLPDualLower {n : ℕ} (R : CDFReport n) (k : ℕ) (c : Fin (k * k) → ℚ)
    (y : Fin (densityInequalityRows k).length → ℚ) (z : Fin (densityEqualityRows k).length → ℚ) : ℚ :=
  rationalDualLower (densityLP_A k) (densityLP_E k) (densityLP_b R k) (densityLP_d k)
    c (fun _ => 1 / 2) (fun _ => 3 / 2) y z

/-- Dimensions are typed; exact coefficient/right-side equality is independently checked. -/
def checkDensityLPModel {n : ℕ} (R : CDFReport n) (k : ℕ)
    (A : Fin (densityInequalityRows k).length → Fin (k * k) → ℚ)
    (E : Fin (densityEqualityRows k).length → Fin (k * k) → ℚ)
    (b : Fin (densityInequalityRows k).length → ℚ) (d : Fin (densityEqualityRows k).length → ℚ) : Bool :=
  decide ((∀ i j, A i j = densityLP_A k i j) ∧ (∀ i j, E i j = densityLP_E k i j) ∧
    (∀ i, b i = densityLP_b R k i) ∧ (∀ i, d i = densityLP_d k i))

theorem check_density_LP_model_sound {n k : ℕ} (R : CDFReport n)
    (A : Fin (densityInequalityRows k).length → Fin (k * k) → ℚ)
    (E : Fin (densityEqualityRows k).length → Fin (k * k) → ℚ)
    (b : Fin (densityInequalityRows k).length → ℚ) (d : Fin (densityEqualityRows k).length → ℚ)
    (h : checkDensityLPModel R k A E b d = true) :
    A = densityLP_A k ∧ E = densityLP_E k ∧ b = densityLP_b R k ∧ d = densityLP_d k := by
  have hc : (∀ i j, A i j = densityLP_A k i j) ∧ (∀ i j, E i j = densityLP_E k i j) ∧
      (∀ i, b i = densityLP_b R k i) ∧ (∀ i, d i = densityLP_d k i) := of_decide_eq_true h
  exact ⟨funext (fun i => funext (hc.1 i)), funext (fun i => funext (hc.2.1 i)),
    funext hc.2.2.1, funext hc.2.2.2⟩

#print axioms check_density_LP_model_sound

end QuantyraNullCone
