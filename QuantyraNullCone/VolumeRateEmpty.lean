import QuantyraNullCone.VolumeRateJoint

namespace QuantyraNullCone

open MeasureTheory

theorem physical_marked_volume_range {rho : DiamondPoint → ℝ} (hK : InDensityClass rho) :
    physicalMarkedVolume rho ∈ Set.Icc (1/8 : ℝ) (3/8) := by
  letI := diamondVolume_probability
  let A := markedIntervalSet nullChronology (0,0) (1/2,1/2)
  have hA : MeasurableSet A := null_interval_measurable _ _
  have hflat : densityMeasure lowerFlat = diamondVolume := by
    simp only [densityMeasure, lowerFlat, ENNReal.ofReal_one]
    exact withDensity_one
  have harea : diamondVolume.real A = 1/4 := by
    rw [← hflat]
    exact calibration_flat_marked_volume
  have hd : ∀ᵐ p ∂diamondVolume, p ∈ diamond := ae_restrict_mem diamond_measurableSet
  have hl : (∫ p in A, (1/2 : ℝ) ∂diamondVolume) ≤ ∫ p in A, rho p ∂diamondVolume :=
    integral_mono_ae (integrable_const (1/2 : ℝ)) hK.integrable.restrict
    ((ae_restrict_of_ae hd).mono (fun p hp => (hK.bounds p hp).1))
  have hu : (∫ p in A, rho p ∂diamondVolume) ≤ ∫ p in A, (3/2 : ℝ) ∂diamondVolume :=
    integral_mono_ae hK.integrable.restrict (integrable_const (3/2 : ℝ))
    ((ae_restrict_of_ae hd).mono (fun p hp => (hK.bounds p hp).2))
  have hlo : diamondVolume.real A*(1/2) ≤ ∫ p in A, rho p ∂diamondVolume := by
    simpa only [setIntegral_const, smul_eq_mul] using hl
  have hup : (∫ p in A, rho p ∂diamondVolume) ≤ diamondVolume.real A*(3/2) := by
    simpa only [setIntegral_const, smul_eq_mul] using hu
  have hid : physicalMarkedVolume rho = ∫ p in A, rho p ∂diamondVolume := hK.densityMeasure_real_apply hA
  rw [harea] at hlo hup
  rw [hid]
  constructor <;> linarith

theorem no_data_physical_volume_error {rho : DiamondPoint → ℝ} (hK : InDensityClass rho) :
    |(1/4 : ℝ)-physicalMarkedVolume rho| ≤ 1/8 := by
  obtain ⟨hl, hu⟩ := physical_marked_volume_range hK
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem empty_full_marked_law (mu : Measure DiamondPoint) [IsProbabilityMeasure mu]
    {m : ℕ} (anchors : Fin m → DiamondPoint) :
    ((Measure.pi (fun _ : Fin 0 => mu)).map (sampledUnlabeledMarkedOrder anchors)) =
      Measure.dirac (sampledUnlabeledMarkedOrder anchors (fun i : Fin 0 => Fin.elim0 i)) := by
  have hf : sampledUnlabeledMarkedOrder (n := 0) anchors =
      fun _ => sampledUnlabeledMarkedOrder anchors (fun i : Fin 0 => Fin.elim0 i) := by
    funext sample
    congr 1
    exact Subsingleton.elim _ _
  rw [hf, Measure.map_const, measure_univ, one_smul]

theorem zero_sample_marked_law_equal {rho sigma : DiamondPoint → ℝ}
    (h0 : InDensityClass rho) (h1 : InDensityClass sigma) {m : ℕ} (anchors : Fin m → DiamondPoint) :
    retainedMarkedOrderLaw rho (fun _ => 1) 0 anchors =
      retainedMarkedOrderLaw sigma (fun _ => 1) 0 anchors := by
  letI := h0.isProbabilityMeasure
  letI := h1.isProbabilityMeasure
  rw [unthinned_marked_law h0, unthinned_marked_law h1]
  change ((Measure.pi (fun _ : Fin 0 => densityMeasure rho)).map (sampledUnlabeledMarkedOrder anchors)) =
    ((Measure.pi (fun _ : Fin 0 => densityMeasure sigma)).map (sampledUnlabeledMarkedOrder anchors))
  rw [empty_full_marked_law, empty_full_marked_law]

theorem no_data_physical_volume_obstruction {R : ℝ} (hR : 1 ≤ R)
    {Ω : Type*} [MeasurableSpace Ω] (xi : Measure Ω) [IsProbabilityMeasure xi]
    (T : UnlabeledMarkedOrderCode 0 2 × Ω → ℝ) (hT : Measurable T) :
    ∃ rho pi, VolumeRateModel R rho pi ∧
      (1/2 : ℝ) ≤ (((retainedMarkedOrderLaw rho pi 0 volumeRateAnchors).prod xi).real
        {z | (1/128 : ℝ) < |T z-physicalMarkedVolume rho|}) := by
  have he : (0 : ℝ) ≤ 1/2 := by norm_num
  have hK := calibration_density_in_class he (le_rfl : (1/2 : ℝ) ≤ 1/2)
  have h0 := unit_detector_volume_model hR lower_flat_in_class
  have h1 := unit_detector_volume_model hR hK
  letI := h0.marked_probability hR 0
  have hgap : 2*(1/128 : ℝ) < physicalMarkedVolume (calibrationDensity (1/2)) -
      physicalMarkedVolume lowerFlat := by
    unfold physicalMarkedVolume
    rw [calibration_marked_volume he le_rfl, calibration_flat_marked_volume]
    norm_num
  have h := identical_law_randomized_scalar_obstruction _ _ xi
    (zero_sample_marked_law_equal lower_flat_in_class hK volumeRateAnchors) T hT hgap
  rcases le_max_iff.mp h with hflat | halt
  · exact ⟨lowerFlat, (fun _ => 1), h0, hflat⟩
  · exact ⟨calibrationDensity (1/2), (fun _ => 1), h1, halt⟩

end QuantyraNullCone
