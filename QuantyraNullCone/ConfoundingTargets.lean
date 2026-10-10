import QuantyraNullCone.ConfoundingGeometry

namespace QuantyraNullCone

open MeasureTheory

theorem calibration_coefficient_separation {epsilon : ℝ} (he : 0 ≤ epsilon)
    (heSmall : epsilon ≤ 1/2) :
    coefficientDeviation lowerFlat (calibrationDensity epsilon) = epsilon := by
  have hBdd : BddAbove ((fun p => |lowerFlat p-calibrationDensity epsilon p|) '' diamond) := by
    refine ⟨epsilon, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    simpa only [lowerFlat, abs_sub_comm] using calibration_density_deviation he hp
  have h0 : (0,0) ∈ diamond := by constructor <;> constructor <;> norm_num
  have hLo := le_csSup hBdd ⟨(0,0), h0, rfl⟩
  have hv : |lowerFlat (0,0)-calibrationDensity epsilon (0,0)| = epsilon := by
    simp [lowerFlat, calibrationDensity, calibrationProfile, abs_of_nonneg he]
  change |lowerFlat (0,0)-calibrationDensity epsilon (0,0)| ≤
    coefficientDeviation lowerFlat (calibrationDensity epsilon) at hLo
  rw [hv] at hLo
  obtain ⟨p, hp, hAtt⟩ := lower_flat_in_class.coefficientDeviation_attained
    (calibration_density_in_class he heSmall)
  apply le_antisymm _ hLo
  rw [hAtt]
  simpa only [lowerFlat, abs_sub_comm] using calibration_density_deviation he hp

theorem calibration_quotient_separation {epsilon : ℝ} (he : 0 ≤ epsilon)
    (heSmall : epsilon ≤ 1/2) :
    conformalDistance lowerFlat (calibrationDensity epsilon) = epsilon := by
  have ht : transposeDensity (calibrationDensity epsilon) = calibrationDensity epsilon := by
    funext p
    exact calibration_density_transpose epsilon p
  simp only [conformalDistance, ht, min_self, calibration_coefficient_separation he heSmall]

theorem calibration_rectangle_integral (epsilon b : ℝ) :
    (∫ u in (0 : ℝ)..b, ∫ v in (0 : ℝ)..b, calibrationDensity epsilon (u,v)) =
      b^2 + epsilon * (b^2-b)^2 := by
  have hInner (u : ℝ) :
      (∫ v in (0 : ℝ)..b, calibrationDensity epsilon (u,v)) =
        b + (epsilon * calibrationProfile u) * (b^2-b) := by
    change (∫ v in (0 : ℝ)..b, 1 + (epsilon * calibrationProfile u) * calibrationProfile v) = _
    rw [intervalIntegral.integral_add (continuous_const.intervalIntegrable 0 b)
      ((calibration_profile_smooth.continuous.intervalIntegrable 0 b).const_mul _),
      intervalIntegral.integral_const_mul, calibration_profile_integral]
    simp
  simp_rw [hInner]
  rw [intervalIntegral.integral_add (continuous_const.intervalIntegrable 0 b)
    (((calibration_profile_smooth.continuous.const_mul epsilon).mul_const _).intervalIntegrable 0 b),
    intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
    calibration_profile_integral]
  simp
  ring

/-- The target is the original physical mass of the open marked interval. -/
theorem calibration_marked_volume {epsilon : ℝ} (he : 0 ≤ epsilon)
    (heSmall : epsilon ≤ 1/2) :
    (densityMeasure (calibrationDensity epsilon)).real
      (markedIntervalSet nullChronology (0,0) (1/2,1/2)) = 1/4 + epsilon/16 := by
  let A : Set DiamondPoint := Set.Ioo (0 : ℝ) (1/2) ×ˢ Set.Ioo (0 : ℝ) (1/2)
  have hA : MeasurableSet A := measurableSet_Ioo.prod measurableSet_Ioo
  have hSub : A ⊆ diamond := by
    rintro p ⟨hu, hv⟩
    exact ⟨⟨hu.1.le, hu.2.le.trans (by norm_num)⟩,
      ⟨hv.1.le, hv.2.le.trans (by norm_num)⟩⟩
  have hK := calibration_density_in_class he heSmall
  have hInt : IntegrableOn (calibrationDensity epsilon) A ((volume : Measure ℝ).prod volume) :=
    (show IntegrableOn (calibrationDensity epsilon) diamond ((volume : Measure ℝ).prod volume)
      from hK.integrable).mono_set hSub
  rw [null_interval_rectangle]
  change (densityMeasure (calibrationDensity epsilon) A).toReal = _
  rw [hK.densityMeasure_real_apply hA, diamondVolume, Measure.restrict_restrict_of_subset hSub,
    setIntegral_prod _ hInt]
  simp only [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1/2)]
  rw [calibration_rectangle_integral]
  ring

theorem calibration_flat_marked_volume :
    (densityMeasure lowerFlat).real (markedIntervalSet nullChronology (0,0) (1/2,1/2)) = 1/4 := by
  have h := calibration_marked_volume (epsilon := 0) (by norm_num) (by norm_num)
  simpa only [calibration_density_zero, zero_div, add_zero] using h

end QuantyraNullCone
