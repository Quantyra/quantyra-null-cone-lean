import QuantyraNullCone.VolumeRateUpper

namespace QuantyraNullCone

open MeasureTheory

/-- The frozen experiment: the original geometric class and a measurable globally bounded detector. -/
structure VolumeRateModel (R : ℝ) (rho pi : DiamondPoint → ℝ) : Prop where
  density : InDensityClass rho
  detector_measurable : Measurable pi
  detector_bounds : ∀ x, 1/R ≤ pi x ∧ pi x ≤ 1

noncomputable def physicalMarkedVolume (rho : DiamondPoint → ℝ) : ℝ :=
  (densityMeasure rho).real (markedIntervalSet nullChronology (0,0) (1/2,1/2))

theorem VolumeRateModel.detector_integrable {R : ℝ} {rho pi : DiamondPoint → ℝ}
    (h : VolumeRateModel R rho pi) (hR : 1 ≤ R) : Integrable pi (densityMeasure rho) := by
  letI := h.density.isProbabilityMeasure
  apply thinning_unit_integrable (densityMeasure rho) h.detector_measurable
  intro x
  exact ⟨(one_div_nonneg.mpr (by linarith)).trans (h.detector_bounds x).1,
    (h.detector_bounds x).2⟩

theorem VolumeRateModel.marked_probability {R : ℝ} {rho pi : DiamondPoint → ℝ}
    (h : VolumeRateModel R rho pi) (hR : 1 ≤ R) (n : ℕ) :
    IsProbabilityMeasure (retainedMarkedOrderLaw rho pi n volumeRateAnchors) := by
  letI := h.density.isProbabilityMeasure
  letI := retained_measure_probability (densityMeasure rho) (h.detector_integrable hR)
    (one_div_pos.mpr (by linarith : 0 < R)) h.detector_bounds
  exact Measure.isProbabilityMeasure_map
    (sampled_unlabeled_marked_order_measurable volumeRateAnchors).aemeasurable

theorem VolumeRateModel.volume_rate_upper {R : ℝ} {rho pi : DiamondPoint → ℝ}
    (h : VolumeRateModel R rho pi) (hR : 1 ≤ R) {n : ℕ} (hn : 0 < n) :
    (retainedMarkedOrderLaw rho pi n volumeRateAnchors).real
      {code | 2*physicalVolumeRate n R < |markedOrderFraction 0 1 code-physicalMarkedVolume rho|} ≤
      (1/20 : ℝ) :=
  fixed_marked_physical_volume_rate_upper h.density (h.detector_integrable hR) hR h.detector_bounds hn

theorem calibration_budget_positive {R : ℝ} (hR : 1 < R) : 0 < calibrationBudget R := by
  unfold calibrationBudget
  exact div_pos (by linarith) (by linarith)

theorem calibration_budget_le_third {R : ℝ} (hR : 1 ≤ R) (hR2 : R ≤ 2) :
    calibrationBudget R ≤ 1/3 := by
  unfold calibrationBudget
  apply (div_le_iff₀ (by linarith : 0 < R+1)).mpr
  linarith

theorem calibration_budget_detector_ratio {R : ℝ} (hR : 1 ≤ R) :
    (1-calibrationBudget R)/(1+calibrationBudget R) = 1/R := by
  have hRpos : 0 < R := by linarith
  have hR1 : 0 < R+1 := by linarith
  have hb : 0 < 1+calibrationBudget R := by linarith [calibration_budget_nonneg hR]
  apply (div_eq_div_iff (ne_of_gt hb) (ne_of_gt hRpos)).mpr
  unfold calibrationBudget
  field_simp
  ring

theorem calibration_flat_model {R : ℝ} (hR : 1 ≤ R) :
    VolumeRateModel R lowerFlat (fun _ => 1-calibrationBudget R) := by
  refine ⟨lower_flat_in_class, measurable_const, fun x => ?_⟩
  have hRpos : 0 < R := by linarith
  have hR1 : 0 < R+1 := by linarith
  have hid : 1-calibrationBudget R = 2/(R+1) := by
    unfold calibrationBudget
    field_simp
    ring
  constructor
  · rw [hid, div_le_div_iff₀ hRpos hR1]
    linarith
  · linarith [calibration_budget_nonneg hR]

theorem calibration_alternative_model {R : ℝ} (hR : 1 ≤ R) (hR2 : R ≤ 2) :
    VolumeRateModel R (calibrationDensity (calibrationBudget R))
      (calibrationDetector (calibrationBudget R)) := by
  have he := calibration_budget_nonneg hR
  have heSmall : calibrationBudget R ≤ 1/2 := by linarith [calibration_budget_le_third hR hR2]
  refine ⟨calibration_density_in_class he heSmall,
    (calibration_detector_continuous heSmall).measurable, fun x => ?_⟩
  have hb := calibration_detector_bounds he heSmall x
  rw [calibration_budget_detector_ratio hR] at hb
  exact hb

/-- A model in the frozen class defeats any measurable estimator with any independent probability seed. -/
theorem physical_volume_detector_obstruction {R : ℝ} (hR : 1 < R) (hR2 : R ≤ 2)
    (n : ℕ) {Ω : Type*} [MeasurableSpace Ω] (xi : Measure Ω) [IsProbabilityMeasure xi]
    (T : UnlabeledMarkedOrderCode n 2 × Ω → ℝ) (hT : Measurable T)
    {r : ℝ} (hr : 2*r < calibrationBudget R/16) :
    ∃ rho pi, VolumeRateModel R rho pi ∧
      (1/2 : ℝ) ≤ (((retainedMarkedOrderLaw rho pi n volumeRateAnchors).prod xi).real
        {z | r < |T z-physicalMarkedVolume rho|}) := by
  have he := calibration_budget_positive hR
  have heSmall : calibrationBudget R ≤ 1/2 := by linarith [calibration_budget_le_third hR.le hR2]
  have h := calibration_volume_randomized_obstruction he heSmall n volumeRateAnchors xi T hT r hr
  rcases le_max_iff.mp h with hflat | halt
  · exact ⟨lowerFlat, (fun _ => 1-calibrationBudget R), calibration_flat_model hR.le, hflat⟩
  · exact ⟨calibrationDensity (calibrationBudget R), calibrationDetector (calibrationBudget R),
      calibration_alternative_model hR.le hR2, halt⟩

theorem physical_volume_detector_rate_lower {R : ℝ} (hR : 1 < R) (hR2 : R ≤ 2)
    (n : ℕ) {Ω : Type*} [MeasurableSpace Ω] (xi : Measure Ω) [IsProbabilityMeasure xi]
    (T : UnlabeledMarkedOrderCode n 2 × Ω → ℝ) (hT : Measurable T) :
    ∃ rho pi, VolumeRateModel R rho pi ∧
      (1/2 : ℝ) ≤ (((retainedMarkedOrderLaw rho pi n volumeRateAnchors).prod xi).real
        {z | calibrationBudget R/64 < |T z-physicalMarkedVolume rho|}) := by
  apply physical_volume_detector_obstruction hR hR2 n xi T hT
  linarith [calibration_budget_positive hR]

end QuantyraNullCone
