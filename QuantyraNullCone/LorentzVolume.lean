import QuantyraNullCone.LorentzVolumeCoordinates
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace QuantyraNullCone

open MeasureTheory Set

noncomputable section

def lorentzSliceArea3 (t : ℝ) : ℝ := Real.pi * (max 0 (1 - |t|)) ^ 2

@[fun_prop] theorem continuous_lorentz_slice_area3 : Continuous lorentzSliceArea3 := by
  unfold lorentzSliceArea3
  fun_prop

theorem lorentz_slice_area_nonneg3 (t : ℝ) : 0 ≤ lorentzSliceArea3 t :=
  mul_nonneg Real.pi_pos.le (sq_nonneg _)

theorem lorentz_slice_area_zero3 {t : ℝ} (ht : t ∉ Icc (-1 : ℝ) 1) : lorentzSliceArea3 t = 0 := by
  have hAbs : 1 ≤ |t| := by
    by_contra h
    have hBound := abs_lt.mp (lt_of_not_ge h)
    exact ht ⟨hBound.1.le, hBound.2.le⟩
  simp [lorentzSliceArea3, max_eq_left (by linarith : 1 - |t| ≤ 0)]

theorem integrable_lorentz_slice_area3 : Integrable lorentzSliceArea3 := by
  have hOn : IntegrableOn lorentzSliceArea3 (Icc (-1 : ℝ) 1) :=
    continuous_lorentz_slice_area3.continuousOn.integrableOn_compact isCompact_Icc
  have hIndicator : (Icc (-1 : ℝ) 1).indicator lorentzSliceArea3 = lorentzSliceArea3 := by
    funext t
    by_cases ht : t ∈ Icc (-1 : ℝ) 1
    · simp [ht]
    · simp [ht, lorentz_slice_area_zero3 ht]
  rw [← hIndicator]
  exact (integrable_indicator_iff measurableSet_Icc).mpr hOn

theorem lorentz_slice_area_left3 {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 0) :
    lorentzSliceArea3 t = Real.pi * (1 + t) ^ 2 := by
  simp only [lorentzSliceArea3, abs_of_nonpos ht.2]
  rw [max_eq_right (by linarith [ht.1] : 0 ≤ 1 - -t)]
  ring

theorem lorentz_slice_area_right3 {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    lorentzSliceArea3 t = Real.pi * (1 - t) ^ 2 := by
  simp [lorentzSliceArea3, abs_of_nonneg ht.1, max_eq_right (by linarith [ht.2] : 0 ≤ 1 - t)]

theorem integral_lorentz_slice_left3 : (∫ t in (-1 : ℝ)..0, lorentzSliceArea3 t) = Real.pi / 3 := by
  have hFunc : (fun t : ℝ => Real.pi * (1 + t) ^ 2) =
      (fun t => Real.pi + 2 * Real.pi * t + Real.pi * t ^ 2) := by funext t; ring
  rw [intervalIntegral.integral_congr (fun t ht =>
    lorentz_slice_area_left3 (by simpa [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] using ht))]
  rw [hFunc]
  rw [intervalIntegral.integral_add ((show Continuous (fun t : ℝ => Real.pi + 2 * Real.pi * t) by fun_prop).intervalIntegrable (-1) 0)
    ((show Continuous (fun t : ℝ => Real.pi * t ^ 2) by fun_prop).intervalIntegrable (-1) 0)]
  rw [intervalIntegral.integral_add ((show Continuous (fun _ : ℝ => Real.pi) by fun_prop).intervalIntegrable (-1) 0)
    ((show Continuous (fun t : ℝ => 2 * Real.pi * t) by fun_prop).intervalIntegrable (-1) 0)]
  rw [intervalIntegral.integral_const_mul (2 * Real.pi) (fun t : ℝ => t),
    intervalIntegral.integral_const_mul Real.pi (fun t : ℝ => t ^ 2),
    integral_id, integral_pow, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  norm_num
  ring

theorem integral_lorentz_slice_right3 : (∫ t in (0 : ℝ)..1, lorentzSliceArea3 t) = Real.pi / 3 := by
  have hFunc : (fun t : ℝ => Real.pi * (1 - t) ^ 2) =
      (fun t => Real.pi + (-2 * Real.pi) * t + Real.pi * t ^ 2) := by funext t; ring
  rw [intervalIntegral.integral_congr (fun t ht =>
    lorentz_slice_area_right3 (by simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht))]
  rw [hFunc]
  rw [intervalIntegral.integral_add ((show Continuous (fun t : ℝ => Real.pi + (-2 * Real.pi) * t) by fun_prop).intervalIntegrable 0 1)
    ((show Continuous (fun t : ℝ => Real.pi * t ^ 2) by fun_prop).intervalIntegrable 0 1)]
  rw [intervalIntegral.integral_add ((show Continuous (fun _ : ℝ => Real.pi) by fun_prop).intervalIntegrable 0 1)
    ((show Continuous (fun t : ℝ => (-2 * Real.pi) * t) by fun_prop).intervalIntegrable 0 1)]
  rw [intervalIntegral.integral_const_mul (-2 * Real.pi) (fun t : ℝ => t),
    intervalIntegral.integral_const_mul Real.pi (fun t : ℝ => t ^ 2),
    integral_id, integral_pow, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  norm_num
  ring

theorem integral_lorentz_slice_area3 : (∫ t, lorentzSliceArea3 t) = lorentzVolume3 := by
  have hIndicator : (Icc (-1 : ℝ) 1).indicator lorentzSliceArea3 = lorentzSliceArea3 := by
    funext t
    by_cases ht : t ∈ Icc (-1 : ℝ) 1
    · simp [ht]
    · simp [ht, lorentz_slice_area_zero3 ht]
  rw [← hIndicator, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (continuous_lorentz_slice_area3.intervalIntegrable (-1) 0)
    (continuous_lorentz_slice_area3.intervalIntegrable 0 1),
    integral_lorentz_slice_left3, integral_lorentz_slice_right3]
  unfold lorentzVolume3
  ring

theorem lorentz_slice_area_ofReal3 (t : ℝ) : ENNReal.ofReal (lorentzSliceArea3 t) =
    ENNReal.ofReal (1 - |t|) ^ 2 * ENNReal.ofReal Real.pi := by
  by_cases ht : 0 ≤ 1 - |t|
  · simp [lorentzSliceArea3, max_eq_right ht, ENNReal.ofReal_mul Real.pi_pos.le,
      ENNReal.ofReal_pow ht, mul_comm]
  · have ht' : 1 - |t| ≤ 0 := le_of_not_ge ht
    simp [lorentzSliceArea3, max_eq_left ht', ENNReal.ofReal_eq_zero.mpr ht']

/-- Volume of the actual Euclidean diamond, rather than a normalization assumption. -/
theorem lorentz_diamond_volume3 : (volume : Measure LorentzPoint3) lorentzDiamond3 =
    ENNReal.ofReal lorentzVolume3 := by
  rw [lorentz_diamond_volume_slices3]
  simp_rw [← lorentz_slice_area_ofReal3]
  rw [← ofReal_integral_eq_lintegral_ofReal integrable_lorentz_slice_area3
    (ae_of_all _ lorentz_slice_area_nonneg3), integral_lorentz_slice_area3]

#print axioms integrable_lorentz_slice_area3
#print axioms integral_lorentz_slice_area3
#print axioms lorentz_diamond_volume3

end

end QuantyraNullCone
