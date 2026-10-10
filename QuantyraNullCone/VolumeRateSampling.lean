import QuantyraNullCone.VolumeRateScale
import QuantyraNullCone.LowerTesting

namespace QuantyraNullCone

open MeasureTheory

theorem unit_detector_volume_model {R : ℝ} (hR : 1 ≤ R) {rho : DiamondPoint → ℝ}
    (hK : InDensityClass rho) : VolumeRateModel R rho (fun _ => 1) := by
  refine ⟨hK, measurable_const, fun _ => ⟨?_, le_rfl⟩⟩
  exact (div_le_one (by linarith : 0 < R)).mpr hR

theorem unthinned_marked_law {rho : DiamondPoint → ℝ} (hK : InDensityClass rho)
    (n : ℕ) {m : ℕ} (anchors : Fin m → DiamondPoint) :
    retainedMarkedOrderLaw rho (fun _ => 1) n anchors =
      (sampleMeasure rho n).map (sampledUnlabeledMarkedOrder anchors) := by
  letI := hK.isProbabilityMeasure
  simp only [retainedMarkedOrderLaw, retained_measure_one, sampleMeasure]

/-- The comparison controls every marked relation, before the estimator discards information. -/
theorem full_marked_sampling_TV_bound {n : ℕ} (hn : 0 < n)
    {m : ℕ} (anchors : Fin m → DiamondPoint) :
    (1/2 : ℝ) * ∑ code,
      |(retainedMarkedOrderLaw lowerFlat (fun _ => 1) n anchors).real {code} -
       (retainedMarkedOrderLaw (calibrationDensity (volumeSamplingEpsilon n)) (fun _ => 1) n anchors).real {code}|
      ≤ 1/4 := by
  have he := (volume_sampling_epsilon_positive hn).le
  have heSmall := volume_sampling_epsilon_small hn
  have hK := calibration_density_in_class he heSmall
  letI := hK.sample_isProbabilityMeasure n
  have hL1 := finite_observation_L1_bound (lowerBaseSample n)
    (sampleMeasure (calibrationDensity (volumeSamplingEpsilon n)) n)
    (calibration_likelihood_integrable he heSmall n)
    (fun S hS => calibration_sample_real_apply he heSmall n hS)
    (sampled_unlabeled_marked_order_measurable anchors)
  have hCS := integral_abs_le_sqrt_second
    ((calibration_likelihood_integrable he heSmall n).sub (integrable_const 1))
    (calibration_central_square_integrable he heSmall n)
  have hDiv := Real.sqrt_le_sqrt (volume_sampling_divergence_bound hn)
  rw [unthinned_marked_law lower_flat_in_class, unthinned_marked_law hK, lower_flat_sample]
  calc
    _ ≤ (1/2 : ℝ)*Real.sqrt (1/35) :=
      mul_le_mul_of_nonneg_left (hL1.trans (hCS.trans hDiv)) (by norm_num)
    _ ≤ 1/4 := by
      have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1/35)
      have hp := Real.sqrt_nonneg (1/35 : ℝ)
      nlinarith

theorem finite_randomized_scalar_obstruction {Y Ω : Type*} [Fintype Y]
    [MeasurableSpace Y] [MeasurableSingletonClass Y] [MeasurableSpace Ω]
    (mu nu : Measure Y) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (xi : Measure Ω) [IsProbabilityMeasure xi]
    (hTV : (1/2 : ℝ)*∑ y, |mu.real {y}-nu.real {y}| ≤ 1/4)
    (T : Y × Ω → ℝ) (hT : Measurable T) {v0 v1 r : ℝ} (hgap : 2*r < v1-v0) :
    (3/8 : ℝ) ≤ max ((mu.prod xi).real {z | r < |T z-v0|})
      ((nu.prod xi).real {z | r < |T z-v1|}) := by
  have hA : MeasurableSet {z | |T z-v0| ≤ r} :=
    measurableSet_le (hT.sub_const v0).abs measurable_const
  have hB : MeasurableSet {z | |T z-v1| ≤ r} :=
    measurableSet_le (hT.sub_const v1).abs measurable_const
  have hAB : Disjoint {z | |T z-v0| ≤ r} {z | |T z-v1| ≤ r} := by
    rw [Set.disjoint_left]
    intro z hz0 hz1
    change |T z-v0| ≤ r at hz0
    change |T z-v1| ≤ r at hz1
    obtain ⟨_, h0⟩ := abs_le.mp hz0
    obtain ⟨h1, _⟩ := abs_le.mp hz1
    linarith
  have h := finite_seed_two_point_lower_bound mu nu xi hA hB hAB
  simp only [Set.compl_setOf, not_le] at h
  linarith

theorem physical_volume_sampling_obstruction {R : ℝ} (hR : 1 ≤ R)
    {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω]
    (xi : Measure Ω) [IsProbabilityMeasure xi]
    (T : UnlabeledMarkedOrderCode n 2 × Ω → ℝ) (hT : Measurable T)
    {r : ℝ} (hr : 2*r < volumeSamplingEpsilon n/16) :
    ∃ rho pi, VolumeRateModel R rho pi ∧
      (3/8 : ℝ) ≤ (((retainedMarkedOrderLaw rho pi n volumeRateAnchors).prod xi).real
        {z | r < |T z-physicalMarkedVolume rho|}) := by
  have he := (volume_sampling_epsilon_positive hn).le
  have heSmall := volume_sampling_epsilon_small hn
  have h0 := unit_detector_volume_model hR lower_flat_in_class
  have h1 := unit_detector_volume_model hR (calibration_density_in_class he heSmall)
  letI := h0.marked_probability hR n
  letI := h1.marked_probability hR n
  have hgap : 2*r < physicalMarkedVolume (calibrationDensity (volumeSamplingEpsilon n)) -
      physicalMarkedVolume lowerFlat := by
    unfold physicalMarkedVolume
    rw [calibration_marked_volume he heSmall, calibration_flat_marked_volume]
    linarith
  have h := finite_randomized_scalar_obstruction _ _ xi
    (full_marked_sampling_TV_bound hn volumeRateAnchors) T hT hgap
  rcases le_max_iff.mp h with hflat | halt
  · exact ⟨lowerFlat, (fun _ => 1), h0, hflat⟩
  · exact ⟨calibrationDensity (volumeSamplingEpsilon n), (fun _ => 1), h1, halt⟩

theorem physical_volume_sampling_rate_lower {R : ℝ} (hR : 1 ≤ R)
    {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω]
    (xi : Measure Ω) [IsProbabilityMeasure xi]
    (T : UnlabeledMarkedOrderCode n 2 × Ω → ℝ) (hT : Measurable T) :
    ∃ rho pi, VolumeRateModel R rho pi ∧
      (3/8 : ℝ) ≤ (((retainedMarkedOrderLaw rho pi n volumeRateAnchors).prod xi).real
        {z | volumeSamplingScale n/128 < |T z-physicalMarkedVolume rho|}) := by
  apply physical_volume_sampling_obstruction hR hn xi T hT
  unfold volumeSamplingEpsilon
  linarith [volume_sampling_scale_positive hn]

end QuantyraNullCone
