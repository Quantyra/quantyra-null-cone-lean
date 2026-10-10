import QuantyraNullCone.LorentzPairIntegral

namespace QuantyraNullCone
open MeasureTheory Set
noncomputable section
set_option maxHeartbeats 1200000

theorem flat_diamond3_ae_interior : ∀ᵐ p ∂flatDiamondMeasure3, p ∈ lorentzDiamond3 :=
  Measure.ae_smul_measure (ae_restrict_mem isOpen_lorentzDiamond3.measurableSet) _

theorem InDensityClass3.integral3 {rho : LorentzPoint3 → ℝ} (h : InDensityClass3 rho)
    (g : LorentzPoint3 → ℝ) :
    (∫ p, g p ∂densityMeasure3 rho) = ∫ p, rho p*g p ∂flatDiamondMeasure3 := by
  rw [densityMeasure3,integral_withDensity_eq_integral_toReal_smul₀
    h.integrable.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [flat_diamond3_ae_mem] with p hp
  rw [ENNReal.toReal_ofReal ((by norm_num : (0 : ℝ) ≤ 1/2).trans (h.bounds p hp).1)]
  rfl

theorem measurableSet_chronological_pairs3 : MeasurableSet {z : LorentzPoint3 × LorentzPoint3 |
    chronological3 z.1 z.2} :=
  (isOpen_lt (continuous_spatial_radius3.comp (continuous_snd.sub continuous_fst))
    (by fun_prop)).measurableSet

def timeOrderedPairProbability3 (theta : ℝ) : ℝ :=
  4/35+(36/1925)*theta-(151/375375)*theta^2

/-- Actual probability of a strict ordered pair under two independent density samples. -/
theorem time_quadratic_ordered_pair_probability3 {theta : ℝ}
    (ht : theta ∈ Icc (0 : ℝ) (1/2)) :
    ((densityMeasure3 (timeQuadraticDensity3 theta)).prod
      (densityMeasure3 (timeQuadraticDensity3 theta))).real
        {z | chronological3 z.1 z.2} = timeOrderedPairProbability3 theta := by
  let rho := timeQuadraticDensity3 theta
  have hR : InDensityClass3 rho := time_quadratic_density_class3 ht
  letI := hR.isProbabilityMeasure
  rw [Measure.real,Measure.prod_apply measurableSet_chronological_pairs3,
    ← integral_toReal (measurable_measure_prodMk_left measurableSet_chronological_pairs3).aemeasurable
      (Filter.Eventually.of_forall (fun p => measure_lt_top (densityMeasure3 rho) _)),hR.integral3]
  change (∫ p, rho p*(densityMeasure3 rho {q | chronological3 p q}).toReal
    ∂flatDiamondMeasure3) = _
  rw [timeOrderedPairProbability3,← time_pair_outer_integral3 theta]
  apply integral_congr_ae
  filter_upwards [flat_diamond3_ae_interior] with p hp
  have hn : 0 ≤ (intervalDuration3 p lorentzTop3/2)^3*(1+theta*futureTimeShapeMean3 p) := by
    rw [← integral_flat_future_density3 theta hp]
    apply integral_nonneg_of_ae
    filter_upwards [flat_diamond3_ae_mem.filter_mono ae_restrict_le] with q hq
    exact (by norm_num : (0 : ℝ) ≤ 1/2).trans (hR.bounds q hq).1
  rw [time_quadratic_future_probability3 ht hp,ENNReal.toReal_ofReal hn]
  dsimp [rho]
  ring

theorem time_quadratic_two_sample_probability3 {theta : ℝ}
    (ht : theta ∈ Icc (0 : ℝ) (1/2)) :
    (sampleMeasure3 (timeQuadraticDensity3 theta) 2).real {w | chronological3 (w 0) (w 1)} =
      timeOrderedPairProbability3 theta := by
  letI := (time_quadratic_density_class3 ht).isProbabilityMeasure
  have hm := (measurePreserving_finTwoArrow (densityMeasure3 (timeQuadraticDensity3 theta))).measure_preimage
    measurableSet_chronological_pairs3.nullMeasurableSet
  have he := congrArg ENNReal.toReal hm
  change (sampleMeasure3 (timeQuadraticDensity3 theta) 2).real {w | chronological3 (w 0) (w 1)} =
    ((densityMeasure3 (timeQuadraticDensity3 theta)).prod
      (densityMeasure3 (timeQuadraticDensity3 theta))).real {z | chronological3 z.1 z.2} at he
  exact he.trans (time_quadratic_ordered_pair_probability3 ht)

/-- The computed law is an event in the original finite order observation. -/
theorem time_quadratic_order_law_pair3 {theta : ℝ}
    (ht : theta ∈ Icc (0 : ℝ) (1/2)) :
    (orderLaw3 (timeQuadraticDensity3 theta) 2).real {code | code 0 1 = true} =
      timeOrderedPairProbability3 theta := by
  rw [Measure.real,orderLaw3,Measure.map_apply (sampledOrder3_measurable 2) (by measurability)]
  have he : sampledOrder3 ⁻¹' {code : OrderCode 2 | code 0 1 = true} =
      {w | chronological3 (w 0) (w 1)} := by
    ext w
    simp [sampledOrder3]
  rw [he]
  exact time_quadratic_two_sample_probability3 ht

#print axioms time_quadratic_ordered_pair_probability3
#print axioms time_quadratic_two_sample_probability3
#print axioms time_quadratic_order_law_pair3
end
end QuantyraNullCone
