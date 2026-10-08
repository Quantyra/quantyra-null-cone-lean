import QuantyraNullCone.DensityInterpolation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace QuantyraNullCone

open MeasureTheory

def squareCell (a c w : ℝ) : Set DiamondPoint :=
  Set.Ioc a (a + w) ×ˢ Set.Ioc c (c + w)

def closedSquareCell (a c w : ℝ) : Set DiamondPoint :=
  Set.Icc a (a + w) ×ˢ Set.Icc c (c + w)

theorem square_cell_measurable (a c w : ℝ) : MeasurableSet (squareCell a c w) :=
  measurableSet_Ioc.prod measurableSet_Ioc

theorem square_cell_subset_closed (a c w : ℝ) : squareCell a c w ⊆ closedSquareCell a c w := by
  rintro p ⟨hx, hy⟩
  exact ⟨⟨hx.1.le, hx.2⟩, ⟨hy.1.le, hy.2⟩⟩

theorem closed_square_cell_subset {a c w : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (haw : a + w ≤ 1) (hcw : c + w ≤ 1) : closedSquareCell a c w ⊆ diamond := by
  rintro p ⟨hx, hy⟩
  exact ⟨⟨ha.trans hx.1, hx.2.trans haw⟩, ⟨hc.trans hy.1, hy.2.trans hcw⟩⟩

theorem square_cell_volume {a c w : ℝ} (hw : 0 ≤ w) :
    ((volume : Measure ℝ).prod volume) (squareCell a c w) = ENNReal.ofReal (w ^ 2) := by
  rw [squareCell, Measure.prod_prod, Real.volume_Ioc, Real.volume_Ioc]
  simp only [add_sub_cancel_left]
  rw [← ENNReal.ofReal_mul hw]
  congr 1
  ring

/-- Actual normalized cell mass, rather than an assumed feasible LP vector. -/
noncomputable def densityCellMean (rho : DiamondPoint → ℝ) (a c w : ℝ) : ℝ :=
  (densityMeasure rho).real (squareCell a c w) / w ^ 2

theorem square_cell_integral {a c w : ℝ} (hw : 0 ≤ w) (f : DiamondPoint → ℝ)
    (hInt : IntegrableOn f (squareCell a c w) ((volume : Measure ℝ).prod volume)) :
    (∫ q in squareCell a c w, f q ∂(volume : Measure ℝ).prod volume) =
      ∫ x in a..a + w, ∫ y in c..c + w, f (x, y) := by
  rw [squareCell, setIntegral_prod f hInt]
  simp only [intervalIntegral.integral_of_le (by linarith : a ≤ a + w),
    intervalIntegral.integral_of_le (by linarith : c ≤ c + w)]

theorem InDensityClass.cell_integrable {rho : DiamondPoint → ℝ} (h : InDensityClass rho)
    {a c w : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (haw : a + w ≤ 1) (hcw : c + w ≤ 1) :
    IntegrableOn rho (squareCell a c w) ((volume : Measure ℝ).prod volume) :=
  (show IntegrableOn rho diamond ((volume : Measure ℝ).prod volume) from h.integrable).mono_set
    ((square_cell_subset_closed a c w).trans
    (closed_square_cell_subset ha hc haw hcw))

theorem InDensityClass.cell_mean_integral {rho : DiamondPoint → ℝ} (h : InDensityClass rho)
    {a c w : ℝ} (hw : 0 ≤ w) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (haw : a + w ≤ 1) (hcw : c + w ≤ 1) :
    densityCellMean rho a c w =
      (∫ x in a..a + w, ∫ y in c..c + w, rho (x, y)) / w ^ 2 := by
  have hSub := (square_cell_subset_closed a c w).trans (closed_square_cell_subset ha hc haw hcw)
  unfold densityCellMean
  rw [h.densityMeasure_real_subset (square_cell_measurable a c w) hSub,
    squareCell, setIntegral_prod rho (h.cell_integrable ha hc haw hcw)]
  simp only [intervalIntegral.integral_of_le (by linarith : a ≤ a + w),
    intervalIntegral.integral_of_le (by linarith : c ≤ c + w)]

theorem InDensityClass.cell_mean_bounds {rho : DiamondPoint → ℝ} (h : InDensityClass rho)
    {a c w : ℝ} (hw : 0 < w) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (haw : a + w ≤ 1) (hcw : c + w ≤ 1) :
    (1 / 2 : ℝ) ≤ densityCellMean rho a c w ∧ densityCellMean rho a c w ≤ 3 / 2 := by
  let Q := squareCell a c w
  let V : Measure DiamondPoint := (volume : Measure ℝ).prod volume
  have hQM : MeasurableSet Q := square_cell_measurable a c w
  have hSub : Q ⊆ diamond := (square_cell_subset_closed a c w).trans
    (closed_square_cell_subset ha hc haw hcw)
  have hArea : V Q = ENNReal.ofReal (w ^ 2) := square_cell_volume hw.le
  letI : IsFiniteMeasure (V.restrict Q) := ⟨by rw [Measure.restrict_apply_univ, hArea]; finiteness⟩
  have hInt : IntegrableOn rho Q V := h.cell_integrable ha hc haw hcw
  have hLower : (∫ _p in Q, (1 / 2 : ℝ) ∂V) ≤ ∫ p in Q, rho p ∂V :=
    integral_mono_ae (integrable_const _) hInt
      ((ae_restrict_mem hQM).mono fun p hp => (h.bounds p (hSub hp)).1)
  have hUpper : (∫ p in Q, rho p ∂V) ≤ ∫ _p in Q, (3 / 2 : ℝ) ∂V :=
    integral_mono_ae hInt (integrable_const _)
      ((ae_restrict_mem hQM).mono fun p hp => (h.bounds p (hSub hp)).2)
  rw [setIntegral_const, Measure.real, hArea, ENNReal.toReal_ofReal (sq_nonneg w), smul_eq_mul] at hLower hUpper
  unfold densityCellMean
  rw [h.densityMeasure_real_subset hQM hSub]
  have hwSq : (0 : ℝ) < w ^ 2 := sq_pos_of_pos hw
  constructor
  · apply (le_div_iff₀ hwSq).mpr
    nlinarith only [hLower]
  · apply (div_le_iff₀ hwSq).mpr
    nlinarith only [hUpper]

theorem InDensityClass.cell_mean_CDF {rho : DiamondPoint → ℝ} (h : InDensityClass rho)
    {a c w : ℝ} (hw : 0 ≤ w) :
    densityCellMean rho a c w =
      (populationCDF rho (a + w) (c + w) - populationCDF rho a (c + w) -
        populationCDF rho (a + w) c + populationCDF rho a c) / w ^ 2 := by
  unfold densityCellMean squareCell
  rw [h.rectangle_mass_cdf (by linarith : a ≤ a + w) (by linarith : c ≤ c + w)]

#print axioms square_cell_volume
#print axioms InDensityClass.cell_mean_integral
#print axioms InDensityClass.cell_mean_bounds
#print axioms InDensityClass.cell_mean_CDF

end QuantyraNullCone
