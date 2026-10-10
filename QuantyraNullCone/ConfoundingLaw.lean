import QuantyraNullCone.ConfoundingDetector
import QuantyraNullCone.ThinningStoppedLaw

namespace QuantyraNullCone

open MeasureTheory

local instance : IsProbabilityMeasure diamondVolume := diamondVolume_probability

theorem calibration_detected_submeasure {epsilon : ℝ} (he : 0 ≤ epsilon)
    (heSmall : epsilon ≤ 1/2) :
    (densityMeasure (calibrationDensity epsilon)).withDensity
      (fun x => ENNReal.ofReal (calibrationDetector epsilon x)) =
      ENNReal.ofReal (1-epsilon) • diamondVolume := by
  rw [densityMeasure, ← withDensity_mul _
    (calibration_density_smooth epsilon).continuous.measurable.ennreal_ofReal
    (calibration_detector_continuous heSmall).measurable.ennreal_ofReal]
  rw [← withDensity_const]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem diamond_measurableSet] with p hp
  change ENNReal.ofReal (calibrationDensity epsilon p) *
    ENNReal.ofReal (calibrationDetector epsilon p) = ENNReal.ofReal (1-epsilon)
  rw [← ENNReal.ofReal_mul (by
    have h := (calibration_density_bounds he hp).1
    linarith), calibration_detector_density he heSmall hp]

theorem calibration_detector_integrable {epsilon : ℝ} (he : 0 ≤ epsilon)
    (heSmall : epsilon ≤ 1/2) :
    Integrable (calibrationDetector epsilon) (densityMeasure (calibrationDensity epsilon)) := by
  letI := (calibration_density_in_class he heSmall).isProbabilityMeasure
  exact thinning_unit_integrable _ (calibration_detector_continuous heSmall).measurable
    (calibration_detector_unit he heSmall)

theorem calibration_acceptance_mass {epsilon : ℝ} (he : 0 ≤ epsilon)
    (heSmall : epsilon ≤ 1/2) :
    (∫ x, calibrationDetector epsilon x ∂densityMeasure (calibrationDensity epsilon)) =
      1-epsilon := by
  have h := congrArg (fun mu : Measure DiamondPoint => mu Set.univ)
    (calibration_detected_submeasure he heSmall)
  dsimp only at h
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (calibration_detector_integrable he heSmall)
      (ae_of_all _ (fun p => (calibration_detector_unit he heSmall p).1))] at h
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one] at h
  have ht := congrArg ENNReal.toReal h
  simpa only [ENNReal.toReal_ofReal
    (integral_nonneg (fun p => (calibration_detector_unit he heSmall p).1)),
    ENNReal.toReal_ofReal (show 0 ≤ 1-epsilon by linarith)] using ht

theorem calibration_retained_flat {epsilon : ℝ} (he : 0 ≤ epsilon)
    (heSmall : epsilon ≤ 1/2) :
    retainedMeasure (densityMeasure (calibrationDensity epsilon)) (calibrationDetector epsilon) =
      diamondVolume := by
  rw [retainedMeasure, calibration_acceptance_mass he heSmall, densityMeasure,
    ← withDensity_mul _ (calibration_density_smooth epsilon).continuous.measurable.ennreal_ofReal
      ((calibration_detector_continuous heSmall).measurable.div_const _).ennreal_ofReal]
  trans diamondVolume.withDensity (fun _ => 1)
  swap
  · exact withDensity_one
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem diamond_measurableSet] with p hp
  change ENNReal.ofReal (calibrationDensity epsilon p) *
    ENNReal.ofReal (calibrationDetector epsilon p / (1-epsilon)) = 1
  have hr : 0 < calibrationDensity epsilon p := by
    have h := (calibration_density_bounds he hp).1
    linarith
  rw [← ENNReal.ofReal_mul hr.le]
  have hc : 1-epsilon ≠ 0 := by linarith
  rw [← mul_div_assoc, calibration_detector_density he heSmall hp, div_self hc,
    ENNReal.ofReal_one]

theorem calibration_flat_retained {epsilon : ℝ} (heSmall : epsilon ≤ 1/2) :
    retainedMeasure (densityMeasure lowerFlat) (fun _ => 1-epsilon) = diamondVolume := by
  have hf : densityMeasure lowerFlat = diamondVolume := by
    simp only [densityMeasure, lowerFlat, ENNReal.ofReal_one]
    exact withDensity_one
  rw [hf, retainedMeasure]
  simp only [integral_const, probReal_univ, one_smul]
  have hc : 1-epsilon ≠ 0 := by linarith
  simp only [div_self hc, ENNReal.ofReal_one]
  exact withDensity_one

theorem calibration_flat_detected_submeasure {epsilon : ℝ} :
    (densityMeasure lowerFlat).withDensity (fun _ => ENNReal.ofReal (1-epsilon)) =
      ENNReal.ofReal (1-epsilon) • diamondVolume := by
  have hf : densityMeasure lowerFlat = diamondVolume := by
    simp only [densityMeasure, lowerFlat, ENNReal.ofReal_one]
    exact withDensity_one
  rw [hf, withDensity_const]

/-- Equal full coordinate laws imply equal laws for every common measurable observation. -/
theorem calibration_retained_observable_equal {epsilon : ℝ} (he : 0 ≤ epsilon)
    (heSmall : epsilon ≤ 1/2) (n : ℕ) {Y : Type*} [MeasurableSpace Y]
    (F : (Fin n → DiamondPoint) → Y) :
    (Measure.pi (fun _ : Fin n => retainedMeasure (densityMeasure lowerFlat)
      (fun _ => 1-epsilon))).map F =
    (Measure.pi (fun _ : Fin n => retainedMeasure (densityMeasure (calibrationDensity epsilon))
      (calibrationDetector epsilon))).map F := by
  rw [calibration_flat_retained heSmall, calibration_retained_flat he heSmall]

theorem calibration_actual_detected_equal {epsilon : ℝ} (he : 0 ≤ epsilon)
    (heSmall : epsilon ≤ 1/2) :
    (((densityMeasure lowerFlat).prod uniform01Measure).restrict
      (retentionEvent (fun _ => 1-epsilon))).map Prod.fst =
    (((densityMeasure (calibrationDensity epsilon)).prod uniform01Measure).restrict
      (retentionEvent (calibrationDetector epsilon))).map Prod.fst := by
  rw [detected_submeasure _ measurable_const (fun _ => ⟨by linarith, by linarith⟩),
    detected_submeasure _ (calibration_detector_continuous heSmall).measurable
      (calibration_detector_unit he heSmall), calibration_flat_detected_submeasure,
    calibration_detected_submeasure he heSmall]

theorem calibration_stopped_observable_equal {epsilon : ℝ} (he : 0 ≤ epsilon)
    (heSmall : epsilon ≤ 1/2) (n : ℕ) (fallback : DiamondPoint)
    {Y : Type*} [MeasurableSpace Y] (F : (Fin n → DiamondPoint) → Y) (hF : Measurable F) :
    (generatedStreamLaw (densityMeasure lowerFlat)).map
      (fun sample => F (stoppedRetainedView (fun _ => 1-epsilon) fallback n sample)) =
    (generatedStreamLaw (densityMeasure (calibrationDensity epsilon))).map
      (fun sample => F (stoppedRetainedView (calibrationDetector epsilon) fallback n sample)) := by
  letI := lower_flat_in_class.isProbabilityMeasure
  letI := (calibration_density_in_class he heSmall).isProbabilityMeasure
  have hc : 0 < 1-epsilon := by linarith
  have hZ : 0 < ∫ _ : DiamondPoint, 1-epsilon ∂densityMeasure lowerFlat := by simpa using hc
  change (generatedStreamLaw (densityMeasure lowerFlat)).map
    (F ∘ stoppedRetainedView (fun _ => 1-epsilon) fallback n) =
    (generatedStreamLaw (densityMeasure (calibrationDensity epsilon))).map
      (F ∘ stoppedRetainedView (calibrationDetector epsilon) fallback n)
  rw [stopped_retained_observable_law _ measurable_const (integrable_const _)
    (fun _ => ⟨hc.le, by linarith⟩) hZ n fallback hF,
    stopped_retained_observable_law _ (calibration_detector_continuous heSmall).measurable
      (calibration_detector_integrable he heSmall) (calibration_detector_unit he heSmall)
      (by rw [calibration_acceptance_mass he heSmall]; exact hc) n fallback hF]
  exact calibration_retained_observable_equal he heSmall n F

end QuantyraNullCone
