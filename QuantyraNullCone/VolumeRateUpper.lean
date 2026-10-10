import QuantyraNullCone.VolumeRateBounds

namespace QuantyraNullCone

open MeasureTheory

/-- One observable estimator works uniformly over the original class and every allowed detector.
The theorem in fact holds for every R ≥ 1, including R = 1, and every anchor pair. -/
theorem physical_volume_rate_upper {rho : DiamondPoint → ℝ} (hK : InDensityClass rho)
    {pi : DiamondPoint → ℝ} (hpi : Integrable pi (densityMeasure rho))
    {R : ℝ} (hR : 1 ≤ R) (hbounds : ∀ x, 1/R ≤ pi x ∧ pi x ≤ 1)
    {n m : ℕ} (hn : 0 < n) (anchors : Fin m → DiamondPoint) (p q : Fin m) :
    (retainedMarkedOrderLaw rho pi n anchors).real
      {code | 2*physicalVolumeRate n R < |markedOrderFraction p q code -
        (densityMeasure rho).real (markedIntervalSet nullChronology (anchors p) (anchors q))|} ≤
      (1/20 : ℝ) := by
  let mu := densityMeasure rho
  letI : IsProbabilityMeasure mu := hK.isProbabilityMeasure
  have ha : 0 < 1/R := one_div_pos.mpr (by linarith)
  letI := retained_measure_probability mu hpi ha hbounds
  let nu := retainedMarkedOrderLaw rho pi n anchors
  let theta := (retainedMeasure mu pi).real
    (markedIntervalSet nullChronology (anchors p) (anchors q))
  have hunit : mu.real (markedIntervalSet nullChronology (anchors p) (anchors q)) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨measureReal_nonneg, measureReal_le_one⟩
  have hbias := retained_volume_bias mu hpi hR hbounds
    (null_interval_measurable (anchors p) (anchors q))
  have hinc : {code : UnlabeledMarkedOrderCode n m | 2*physicalVolumeRate n R < |markedOrderFraction p q code -
      mu.real (markedIntervalSet nullChronology (anchors p) (anchors q))|} ⊆
      {code | 2*volumeSamplingScale n ≤ |markedOrderFraction p q code - theta|} := by
    intro code hcode
    exact volume_rate_error_inclusion (calibration_budget_nonneg hR)
      (marked_order_fraction_unit hn p q code) hunit hbias hcode
  have hnu : IsProbabilityMeasure nu :=
    Measure.isProbabilityMeasure_map (sampled_unlabeled_marked_order_measurable anchors).aemeasurable
  letI := hnu
  have hmono := measureReal_mono (μ := nu) hinc
  have htail := full_marked_order_fraction_hoeffding (retainedMeasure mu pi) hn anchors p q
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (volume_sampling_scale_positive hn).le)
  have hbudget : 2 ≤ (n : ℝ)*(2*volumeSamplingScale n)^2 := by
    rw [volume_sampling_budget hn]
    norm_num
  exact hmono.trans (htail.trans (marked_hoeffding_95 hbudget))

theorem fixed_marked_physical_volume_rate_upper {rho : DiamondPoint → ℝ} (hK : InDensityClass rho)
    {pi : DiamondPoint → ℝ} (hpi : Integrable pi (densityMeasure rho))
    {R : ℝ} (hR : 1 ≤ R) (hbounds : ∀ x, 1/R ≤ pi x ∧ pi x ≤ 1)
    {n : ℕ} (hn : 0 < n) :
    (retainedMarkedOrderLaw rho pi n volumeRateAnchors).real
      {code | 2*physicalVolumeRate n R < |markedOrderFraction 0 1 code -
        (densityMeasure rho).real (markedIntervalSet nullChronology (0,0) (1/2,1/2))|} ≤
      (1/20 : ℝ) :=
  physical_volume_rate_upper hK hpi hR hbounds hn volumeRateAnchors 0 1

end QuantyraNullCone
