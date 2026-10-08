import QuantyraNullCone.DensityLPBands
import Mathlib.Data.Finset.Max

namespace QuantyraNullCone

def densityHistogramQ {k : ℕ} (H : Fin (k * k) → ℚ) (i j : ℕ) : ℚ :=
  if hi : i < k then if hj : j < k then H (densityCellFlat (⟨i, hi⟩, ⟨j, hj⟩)) else 0 else 0

noncomputable def densityHistogramReal {k : ℕ} (H : Fin (k * k) → ℚ) (i j : ℕ) : ℝ :=
  densityHistogramQ H i j

def densityHistogramCornerQ {k : ℕ} (H : Fin (k * k) → ℚ) (p q : ℕ) : ℚ :=
  (∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q, densityHistogramQ H i j) / (k : ℚ) ^ 2

def densityHistogramResiduals {n k : ℕ} (R : CDFReport n) (H : Fin (k * k) → ℚ) : Finset ℚ :=
  insert 0 (Finset.univ.image (fun pq : Fin (k + 1) × Fin (k + 1) =>
    |densityHistogramCornerQ H pq.1.val pq.2.val - (reportLPCounts R k pq.1 pq.2 : ℚ) / n| - R.radius))

def densityHistogramViolationQ {n k : ℕ} (R : CDFReport n) (H : Fin (k * k) → ℚ) : ℚ :=
  (densityHistogramResiduals R H).max' (by exact Finset.insert_nonempty _ _)

theorem density_histogram_violation_nonneg {n k : ℕ} (R : CDFReport n) (H : Fin (k * k) → ℚ) :
    0 ≤ densityHistogramViolationQ R H :=
  Finset.le_max' _ 0 (Finset.mem_insert_self _ _)

theorem density_histogram_violation_corner {n k : ℕ} (R : CDFReport n) (H : Fin (k * k) → ℚ)
    (p q : Fin (k + 1)) :
    |densityHistogramCornerQ H p.val q.val - (reportLPCounts R k p q : ℚ) / n| ≤
      R.radius + densityHistogramViolationQ R H := by
  have hMem : |densityHistogramCornerQ H p.val q.val - (reportLPCounts R k p q : ℚ) / n| - R.radius ∈
      densityHistogramResiduals R H := by
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨(p, q), Finset.mem_univ _, rfl⟩
  have hLe := Finset.le_max' (densityHistogramResiduals R H) _ hMem
  change _ ≤ densityHistogramViolationQ R H at hLe
  linarith

theorem density_histogram_corner_cast {k : ℕ} (H : Fin (k * k) → ℚ) (p q : ℕ) :
    (densityHistogramCornerQ H p q : ℝ) = histogramGridCDF (densityHistogramReal H) k p q := by
  unfold densityHistogramCornerQ histogramGridCDF densityHistogramReal
  push_cast
  rfl

theorem density_histogram_flat_value {k : ℕ} (H : Fin (k * k) → ℚ) (cell : Fin (k * k)) :
    densityHistogramReal H (densityCellPair cell).1.val (densityCellPair cell).2.val = (H cell : ℝ) := by
  unfold densityHistogramReal densityHistogramQ
  rw [dif_pos (densityCellPair cell).1.isLt, dif_pos (densityCellPair cell).2.isLt]
  change (H (densityCellFlat (densityCellPair cell)) : ℝ) = (H cell : ℝ)
  rw [show densityCellFlat (densityCellPair cell) = cell from finProdFinEquiv.apply_symm_apply cell]

structure DensityBands (k : ℕ) where
  dual : Fin (k * k) → DensityDualPair k
  cellLower : Fin (k * k) → ℚ
  cellUpper : Fin (k * k) → ℚ
  pointLower : Fin (k * k) → ℚ
  pointUpper : Fin (k * k) → ℚ
  histogram : Fin (k * k) → ℚ
  cornerExcess : ℚ
  histogramError : ℚ
  fallback : Bool

def densityHistogramErrorQ {n k : ℕ} (R : CDFReport n) (B : DensityBands k) : ℚ :=
  min 1 (8 * R.radius * (k : ℚ) ^ 2 + 4 * B.cornerExcess * (k : ℚ) ^ 2 + 2 / k)

def DensityBandsFallbackFields {k : ℕ} (B : DensityBands k) : Prop :=
  (∀ cell, B.cellLower cell = 1 / 2 ∧ B.cellUpper cell = 3 / 2 ∧
    B.pointLower cell = 1 / 2 ∧ B.pointUpper cell = 3 / 2) ∧ B.histogramError = 1

def DensityBandsCertifiedFields {n k : ℕ} (R : CDFReport n) (B : DensityBands k) : Prop :=
  (∀ cell, checkDensityDualPair (B.dual cell) = true ∧
    B.cellLower cell = densityCellLowerQ R (B.dual cell) cell ∧
    B.cellUpper cell = densityCellUpperQ R (B.dual cell) cell ∧
    B.cellLower cell ≤ B.cellUpper cell ∧
    B.pointLower cell = densityPointLowerQ R (B.dual cell) cell ∧
    B.pointUpper cell = densityPointUpperQ R (B.dual cell) cell) ∧
      B.histogramError = densityHistogramErrorQ R B

instance {k : ℕ} (B : DensityBands k) : Decidable (DensityBandsFallbackFields B) := by
  unfold DensityBandsFallbackFields
  infer_instance

instance {n k : ℕ} (R : CDFReport n) (B : DensityBands k) : Decidable (DensityBandsCertifiedFields R B) := by
  unfold DensityBandsCertifiedFields
  infer_instance

def checkDensityBands {n k : ℕ} (R : CDFReport n) (B : DensityBands k) : Bool :=
  decide (0 < k ∧ (∀ cell, (1 / 2 : ℚ) ≤ B.histogram cell ∧ B.histogram cell ≤ 3 / 2) ∧
    B.cornerExcess = densityHistogramViolationQ R B.histogram ∧
    ((B.fallback = true ∧ DensityBandsFallbackFields B) ∨
      (B.fallback = false ∧ DensityBandsCertifiedFields R B)))

structure DensityReport (n : ℕ) where
  cdf : CDFReport n
  grid : ℕ
  bands : DensityBands grid

def checkDensityReport {n : ℕ} (rows : OrderCode n) (R : DensityReport n)
    (q : ℕ) (eM eJ : ℚ) : Bool :=
  decide (checkCDFReport rows R.cdf q eM eJ = true ∧ checkDensityBands R.cdf R.bands = true)

#print axioms density_histogram_violation_nonneg
#print axioms density_histogram_violation_corner
#print axioms density_histogram_corner_cast
#print axioms density_histogram_flat_value

end QuantyraNullCone
