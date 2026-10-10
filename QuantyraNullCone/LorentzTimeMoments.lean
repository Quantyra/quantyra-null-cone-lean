import QuantyraNullCone.LorentzFlat

namespace QuantyraNullCone
open MeasureTheory Set
noncomputable section
set_option maxHeartbeats 800000

/-- The actual time pushforward of unnormalized volume on the genuine diamond. -/
theorem lorentz_time_volume_map3 :
    Measure.map (fun p : LorentzPoint3 => p 0)
      ((volume : Measure LorentzPoint3).restrict lorentzDiamond3) =
    (volume : Measure ℝ).withDensity (fun t => ENNReal.ofReal (lorentzSliceArea3 t)) := by
  classical
  ext s hs
  have hm : Measurable (fun p : LorentzPoint3 => p 0) := by fun_prop
  rw [Measure.map_apply hm hs, Measure.restrict_apply (hs.preimage hm),
    withDensity_apply _ hs]
  have he : splitLorentzEquiv3 ⁻¹' (Prod.fst ⁻¹' s ∩ splitLorentzDiamond3) =
      (fun p : LorentzPoint3 => p 0) ⁻¹' s ∩ lorentzDiamond3 := by
    ext p
    simp only [mem_preimage, mem_inter_iff, split_lorentz_time3,
      split_lorentz_diamond_mem3]
  rw [← he, split_lorentz_volume_preserving3.measure_preimage_equiv]
  change ((volume : Measure ℝ).prod (volume : Measure SpatialPoint3))
    (Prod.fst ⁻¹' s ∩ splitLorentzDiamond3) = _
  rw [Measure.prod_apply ((hs.preimage measurable_fst).inter
      isOpen_splitLorentzDiamond3.measurableSet), ← lintegral_indicator hs]
  apply lintegral_congr
  intro t
  have hsec : Prod.mk t ⁻¹' (Prod.fst ⁻¹' s ∩ splitLorentzDiamond3) =
      if t ∈ s then Metric.ball (0 : SpatialPoint3) (1 - |t|) else ∅ := by
    ext z
    by_cases ht : t ∈ s <;> simp [ht, splitLorentzDiamond3]
  rw [hsec]
  by_cases ht : t ∈ s
  · rw [if_pos ht, indicator_of_mem ht]
    rw [EuclideanSpace.volume_ball_fin_two, ← lorentz_slice_area_ofReal3]
  · simp [ht]

theorem flat_diamond_time_map3 :
    Measure.map (fun p : LorentzPoint3 => p 0) flatDiamondMeasure3 =
      (ENNReal.ofReal lorentzVolume3)⁻¹ •
        (volume : Measure ℝ).withDensity (fun t => ENNReal.ofReal (lorentzSliceArea3 t)) := by
  rw [flatDiamondMeasure3, Measure.map_smul, lorentz_time_volume_map3]

/-- Fubini reduction for any continuous time statistic, with the model's actual normalization. -/
theorem integral_flat_time3 {f : ℝ → ℝ} (hf : Continuous f) :
    (∫ p, f (p 0) ∂flatDiamondMeasure3) =
      lorentzVolume3⁻¹ * ∫ t, lorentzSliceArea3 t * f t := by
  rw [← integral_map (show AEMeasurable (fun p : LorentzPoint3 => p 0)
      flatDiamondMeasure3 by fun_prop) hf.aestronglyMeasurable,
    flat_diamond_time_map3, integral_smul_measure,
    integral_withDensity_eq_integral_toReal_smul
      continuous_lorentz_slice_area3.measurable.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofReal lorentz_volume_pos3.le,
    ENNReal.toReal_ofReal (lorentz_slice_area_nonneg3 _), smul_eq_mul]

theorem continuous_integrable_flat3 {f : LorentzPoint3 → ℝ} (hf : Continuous f) :
    Integrable f flatDiamondMeasure3 := by
  have h : IntegrableOn f closedLorentzDiamond3 (volume : Measure LorentzPoint3) :=
    hf.continuousOn.integrableOn_compact isCompact_closedLorentzDiamond3
  exact (h.mono_set lorentz_diamond_subset_closed3).smul_measure
    (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr lorentz_volume_pos3))

theorem integral_slice_statistic3 {f : ℝ → ℝ} (hf : Continuous f) :
    (∫ t, lorentzSliceArea3 t * f t) =
      (∫ t in (-1 : ℝ)..0, Real.pi * (1+t)^2 * f t) +
      ∫ t in (0 : ℝ)..1, Real.pi * (1-t)^2 * f t := by
  have hi : (Icc (-1 : ℝ) 1).indicator (fun t => lorentzSliceArea3 t * f t) =
      (fun t => lorentzSliceArea3 t * f t) := by
    funext t
    by_cases ht : t ∈ Icc (-1 : ℝ) 1
    · simp [ht]
    · simp [ht, lorentz_slice_area_zero3 ht]
  rw [← hi, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (f := fun t => lorentzSliceArea3 t * f t) (μ := volume)
    ((continuous_lorentz_slice_area3.mul hf).intervalIntegrable (μ := volume) (-1) 0)
    ((continuous_lorentz_slice_area3.mul hf).intervalIntegrable (μ := volume) 0 1)]
  congr 1
  · apply intervalIntegral.integral_congr
    intro t ht
    change lorentzSliceArea3 t * f t = _
    rw [lorentz_slice_area_left3
      (by simpa [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] using ht)]
  · apply intervalIntegral.integral_congr
    intro t ht
    change lorentzSliceArea3 t * f t = _
    rw [lorentz_slice_area_right3
      (by simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht)]

theorem integral_slice_power_left3 (n : ℕ) :
    (∫ t in (-1 : ℝ)..0, Real.pi * (1+t)^2 * t^n) =
      Real.pi * ((0^(n+1)-(-1)^(n+1))/(n+1) +
        2*((0^(n+2)-(-1)^(n+2))/(n+2)) +
        (0^(n+3)-(-1)^(n+3))/(n+3)) := by
  have he : (fun t : ℝ => Real.pi * (1+t)^2 * t^n) =
      (fun t => Real.pi * (t^n + 2*t^(n+1) + t^(n+2))) := by
    funext t
    simp only [pow_add, pow_one]
    ring
  have h0 := (show Continuous (fun t : ℝ => t^n) by fun_prop).intervalIntegrable (μ := volume) (-1) 0
  have h1 := (show Continuous (fun t : ℝ => 2*t^(n+1)) by fun_prop).intervalIntegrable (μ := volume) (-1) 0
  have h2 := (show Continuous (fun t : ℝ => t^(n+2)) by fun_prop).intervalIntegrable (μ := volume) (-1) 0
  rw [he, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (h0.add h1) h2,
    intervalIntegral.integral_add h0 h1,
    intervalIntegral.integral_const_mul, integral_pow, integral_pow, integral_pow]
  push_cast
  ring

theorem integral_slice_power_right3 (n : ℕ) :
    (∫ t in (0 : ℝ)..1, Real.pi * (1-t)^2 * t^n) =
      Real.pi * ((1^(n+1)-0^(n+1))/(n+1) -
        2*((1^(n+2)-0^(n+2))/(n+2)) +
        (1^(n+3)-0^(n+3))/(n+3)) := by
  have he : (fun t : ℝ => Real.pi * (1-t)^2 * t^n) =
      (fun t => Real.pi * (t^n - 2*t^(n+1) + t^(n+2))) := by
    funext t
    simp only [pow_add, pow_one]
    ring
  have h0 := (show Continuous (fun t : ℝ => t^n) by fun_prop).intervalIntegrable (μ := volume) 0 1
  have h1 := (show Continuous (fun t : ℝ => 2*t^(n+1)) by fun_prop).intervalIntegrable (μ := volume) 0 1
  have h2 := (show Continuous (fun t : ℝ => t^(n+2)) by fun_prop).intervalIntegrable (μ := volume) 0 1
  rw [he, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (h0.sub h1) h2,
    intervalIntegral.integral_sub h0 h1,
    intervalIntegral.integral_const_mul, integral_pow, integral_pow, integral_pow]
  push_cast
  ring

theorem flat_time_second_moment3 :
    (∫ p : LorentzPoint3, p 0 ^ 2 ∂flatDiamondMeasure3) = 1/10 := by
  rw [integral_flat_time3 (f := fun t : ℝ => t^2) (by fun_prop),
    integral_slice_statistic3 (by fun_prop),
    integral_slice_power_left3, integral_slice_power_right3]
  norm_num [lorentzVolume3]
  field_simp [Real.pi_ne_zero]
  ring

theorem flat_time_fourth_moment3 :
    (∫ p : LorentzPoint3, p 0 ^ 4 ∂flatDiamondMeasure3) = 1/35 := by
  rw [integral_flat_time3 (f := fun t : ℝ => t^4) (by fun_prop),
    integral_slice_statistic3 (by fun_prop),
    integral_slice_power_left3, integral_slice_power_right3]
  norm_num [lorentzVolume3]
  field_simp [Real.pi_ne_zero]
  ring

#print axioms lorentz_time_volume_map3
#print axioms flat_diamond_time_map3
#print axioms integral_flat_time3
#print axioms flat_time_second_moment3
#print axioms flat_time_fourth_moment3
end
end QuantyraNullCone
