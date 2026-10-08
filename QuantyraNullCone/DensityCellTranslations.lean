import QuantyraNullCone.DensityCells
import QuantyraNullCone.Transpose

namespace QuantyraNullCone

open MeasureTheory

theorem normalized_square_integral_error {a c w B : ℝ} (hw : 0 < w)
    (f g : DiamondPoint → ℝ)
    (hf : IntegrableOn f (squareCell a c w) ((volume : Measure ℝ).prod volume))
    (hg : IntegrableOn g (squareCell a c w) ((volume : Measure ℝ).prod volume))
    (hPoint : ∀ q ∈ squareCell a c w, |f q - g q| ≤ B) :
    |(∫ q in squareCell a c w, f q ∂(volume : Measure ℝ).prod volume) / w ^ 2 -
      (∫ q in squareCell a c w, g q ∂(volume : Measure ℝ).prod volume) / w ^ 2| ≤ B := by
  let Q := squareCell a c w
  let V : Measure DiamondPoint := (volume : Measure ℝ).prod volume
  have hArea : V Q = ENNReal.ofReal (w ^ 2) := square_cell_volume hw.le
  letI : IsFiniteMeasure (V.restrict Q) := ⟨by rw [Measure.restrict_apply_univ, hArea]; finiteness⟩
  have hCompare : (∫ q in Q, |f q - g q| ∂V) ≤ ∫ _q in Q, B ∂V :=
    integral_mono_ae (hf.sub hg).abs (integrable_const _)
      ((ae_restrict_mem (square_cell_measurable a c w)).mono fun q hq => hPoint q hq)
  rw [setIntegral_const, Measure.real, hArea, ENNReal.toReal_ofReal (sq_nonneg w), smul_eq_mul] at hCompare
  have hAbs : |∫ q in Q, f q - g q ∂V| ≤ w ^ 2 * B := abs_integral_le_integral_abs.trans hCompare
  rw [integral_sub hf hg] at hAbs
  rw [← sub_div, abs_div, abs_of_pos (sq_pos_of_pos hw)]
  apply (div_le_iff₀ (sq_pos_of_pos hw)).mpr
  simpa only [mul_comm] using hAbs

theorem InDensityClass.cell_mean_horizontal {rho : DiamondPoint → ℝ} (h : InDensityClass rho)
    {a c w : ℝ} (hw : 0 < w) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (ha2w : a + w + w ≤ 1) (hcw : c + w ≤ 1) :
    |densityCellMean rho (a + w) c w - densityCellMean rho a c w| ≤ 2 * w := by
  let Q := squareCell a c w
  let V : Measure DiamondPoint := (volume : Measure ℝ).prod volume
  let T : DiamondPoint → DiamondPoint := fun q => (q.1 + w, q.2)
  have hT : Continuous T := (continuous_fst.add continuous_const).prodMk continuous_snd
  have hMap : Set.MapsTo T (closedSquareCell a c w) diamond := by
    rintro q ⟨hx, hy⟩
    exact ⟨⟨by dsimp [T]; linarith [hx.1], by dsimp [T]; linarith [hx.2]⟩,
      ⟨hc.trans hy.1, hy.2.trans hcw⟩⟩
  have hShiftInt : IntegrableOn (rho ∘ T) Q V :=
    ((h.continuousOn.comp hT.continuousOn hMap).integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set (square_cell_subset_closed a c w)
  have haw : a + w ≤ 1 := by linarith
  have hInt : IntegrableOn rho Q V := h.cell_integrable ha hc haw hcw
  have hPoint : ∀ q ∈ Q, |(rho ∘ T) q - rho q| ≤ 2 * w := by
    intro q hq
    have hQ := square_cell_subset_closed a c w hq
    have hSub := closed_square_cell_subset ha hc haw hcw
    have hLip := h.lipschitz (T q) (hMap hQ) q (hSub hQ)
    simpa [T, Function.comp_def, Real.sqrt_sq_eq_abs, abs_of_pos hw] using hLip
  have hOriginal : (∫ q in Q, rho q ∂V) / w ^ 2 = densityCellMean rho a c w := by
    unfold densityCellMean
    rw [h.densityMeasure_real_subset (square_cell_measurable a c w)
      ((square_cell_subset_closed a c w).trans (closed_square_cell_subset ha hc haw hcw))]
  have hShift : (∫ q in Q, (rho ∘ T) q ∂V) / w ^ 2 = densityCellMean rho (a + w) c w := by
    rw [square_cell_integral hw.le _ hShiftInt]
    rw [h.cell_mean_integral hw.le (by linarith : 0 ≤ a + w) hc ha2w hcw]
    congr 1
    change (∫ x in a..a + w, ∫ y in c..c + w, rho (x + w, y)) = _
    exact intervalIntegral.integral_comp_add_right (fun x => ∫ y in c..c + w, rho (x, y)) w
  have hError := normalized_square_integral_error hw (rho ∘ T) rho hShiftInt hInt hPoint
  rwa [hShift, hOriginal] at hError

theorem InDensityClass.cell_mean_transpose {rho : DiamondPoint → ℝ} (h : InDensityClass rho)
    {a c w : ℝ} (hw : 0 ≤ w) :
    densityCellMean (transposeDensity rho) a c w = densityCellMean rho c a w := by
  rw [h.transpose.cell_mean_CDF hw, h.cell_mean_CDF hw]
  simp_rw [populationCDF_transpose]
  ring

theorem InDensityClass.cell_mean_vertical {rho : DiamondPoint → ℝ} (h : InDensityClass rho)
    {a c w : ℝ} (hw : 0 < w) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (haw : a + w ≤ 1) (hc2w : c + w + w ≤ 1) :
    |densityCellMean rho a (c + w) w - densityCellMean rho a c w| ≤ 2 * w := by
  have hBound := h.transpose.cell_mean_horizontal hw hc ha hc2w haw
  rwa [h.cell_mean_transpose hw.le, h.cell_mean_transpose hw.le] at hBound

#print axioms InDensityClass.cell_mean_horizontal
#print axioms InDensityClass.cell_mean_transpose
#print axioms InDensityClass.cell_mean_vertical

end QuantyraNullCone
