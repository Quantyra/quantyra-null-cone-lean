import QuantyraNullCone.VolumeRateSampling

namespace QuantyraNullCone

open MeasureTheory

/-- Joint lower bound, with constants uniform even when R approaches 1 with n. -/
theorem physical_volume_joint_rate_lower {R : ℝ} (hR : 1 ≤ R) (hR2 : R ≤ 2)
    {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω]
    (xi : Measure Ω) [IsProbabilityMeasure xi]
    (T : UnlabeledMarkedOrderCode n 2 × Ω → ℝ) (hT : Measurable T) :
    ∃ rho pi, VolumeRateModel R rho pi ∧
      (1/4 : ℝ) ≤ (((retainedMarkedOrderLaw rho pi n volumeRateAnchors).prod xi).real
        {z | physicalVolumeRate n R/256 < |T z-physicalMarkedVolume rho|}) := by
  have ha := volume_sampling_scale_positive hn
  have hs : physicalVolumeRate n R ≤ volumeSamplingScale n+calibrationBudget R := min_le_right _ _
  by_cases hab : calibrationBudget R ≤ volumeSamplingScale n
  · have hr : 2*(physicalVolumeRate n R/256) < volumeSamplingEpsilon n/16 := by
      unfold volumeSamplingEpsilon
      linarith
    obtain ⟨rho, pi, hmodel, hfail⟩ := physical_volume_sampling_obstruction hR hn xi T hT hr
    exact ⟨rho, pi, hmodel, (by norm_num : (1/4 : ℝ) ≤ 3/8).trans hfail⟩
  · have hba : volumeSamplingScale n < calibrationBudget R := lt_of_not_ge hab
    have hRstrict : 1 < R := by
      by_contra h
      have hReq : R = 1 := le_antisymm (le_of_not_gt h) hR
      subst R
      norm_num [calibrationBudget] at hba
      linarith
    have hr : 2*(physicalVolumeRate n R/256) < calibrationBudget R/16 := by linarith
    obtain ⟨rho, pi, hmodel, hfail⟩ := physical_volume_detector_obstruction hRstrict hR2 n xi T hT hr
    exact ⟨rho, pi, hmodel, (by norm_num : (1/4 : ℝ) ≤ 1/2).trans hfail⟩

/-- Complete positive-sample upper/lower statement for the frozen physical-functional experiment. -/
theorem physical_volume_joint_rate {R : ℝ} (hR : 1 ≤ R) (hR2 : R ≤ 2)
    {n : ℕ} (hn : 0 < n) :
    (∀ rho pi, VolumeRateModel R rho pi →
      (retainedMarkedOrderLaw rho pi n volumeRateAnchors).real
        {code | 2*physicalVolumeRate n R < |markedOrderFraction 0 1 code-physicalMarkedVolume rho|}
        ≤ (1/20 : ℝ)) ∧
    (∀ (Ω : Type*) [MeasurableSpace Ω] (xi : Measure Ω) [IsProbabilityMeasure xi]
      (T : UnlabeledMarkedOrderCode n 2 × Ω → ℝ), Measurable T →
      ∃ rho pi, VolumeRateModel R rho pi ∧
        (1/4 : ℝ) ≤ (((retainedMarkedOrderLaw rho pi n volumeRateAnchors).prod xi).real
          {z | physicalVolumeRate n R/256 < |T z-physicalMarkedVolume rho|})) := by
  constructor
  · intro rho pi hmodel
    exact hmodel.volume_rate_upper hR hn
  · intro Ω _ xi _ T hT
    exact physical_volume_joint_rate_lower hR hR2 hn xi T hT

end QuantyraNullCone
