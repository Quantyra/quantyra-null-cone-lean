import QuantyraNullCone.LorentzTransport

namespace QuantyraNullCone

open MeasureTheory

noncomputable section

theorem density_measure3_ae_closed (rho : LorentzPoint3 → ℝ) :
    ∀ᵐ p ∂densityMeasure3 rho, p ∈ closedLorentzDiamond3 :=
  (withDensity_absolutelyContinuous flatDiamondMeasure3 _).ae_le flat_diamond3_ae_mem

theorem gauge_density_integrable3 : Integrable gaugeDensity3 flatDiamondMeasure3 := by
  have hContinuous := gauge_density_smooth3.continuousOn.mono gauge_smooth_domain_contains3
  have hOn : IntegrableOn gaugeDensity3 closedLorentzDiamond3 (volume : Measure LorentzPoint3) :=
    hContinuous.integrableOn_compact isCompact_closedLorentzDiamond3
  have hDiamond := hOn.mono_set lorentz_diamond_subset_closed3
  exact hDiamond.smul_measure
    (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr lorentz_volume_pos3))

theorem gauge_density_mass3 : densityMeasure3 gaugeDensity3 Set.univ = 1 := by
  have h := congrArg (fun mu : Measure LorentzPoint3 => mu Set.univ) gauge_inverse_transport3
  dsimp only at h
  rw [Measure.map_apply (lorentz_flow_measurable3 _) MeasurableSet.univ,
    Set.preimage_univ, flat_diamond_measure_mass3] at h
  exact h

theorem gauge_density_normalized3 : (∫ p, gaugeDensity3 p ∂flatDiamondMeasure3) = 1 := by
  have hNonneg : 0 ≤ᵐ[flatDiamondMeasure3] gaugeDensity3 := flat_diamond3_ae_mem.mono
    (fun p hp => (by norm_num : (0 : ℝ) ≤ 1 / 2).trans (gauge_density_bounds3 hp).1)
  have h := gauge_density_mass3
  rw [densityMeasure3, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal gauge_density_integrable3 hNonneg] at h
  have hReal := congrArg ENNReal.toReal h
  simpa only [ENNReal.toReal_ofReal (integral_nonneg_of_ae hNonneg), ENNReal.toReal_one] using hReal

theorem gauge_density_class3 : InDensityClass3 gaugeDensity3 := by
  constructor
  · exact ⟨gaugeSmoothDomain3, gauge_smooth_domain_open3,
      gauge_smooth_domain_contains3, gauge_density_smooth3⟩
  · exact fun _ hp => gauge_density_bounds3 hp
  · exact fun _ hp _ hq => gauge_density_lipschitz3 hp hq
  · exact gauge_density_normalized3

theorem gauge_forward_transport3 : Measure.map (lorentzFlow3 gaugeParameter3) flatDiamondMeasure3 =
    densityMeasure3 gaugeDensity3 := by
  rw [← gauge_inverse_transport3, Measure.map_map (lorentz_flow_measurable3 _)
    (lorentz_flow_measurable3 _)]
  have hEq : lorentzFlow3 gaugeParameter3 ∘ lorentzFlow3 (-gaugeParameter3) =ᵐ[densityMeasure3 gaugeDensity3] id := by
    filter_upwards [density_measure3_ae_closed gaugeDensity3] with p hp
    simpa only [Function.comp_apply, neg_neg, id_eq] using
      lorentz_flow_inverse_closed3 gauge_parameter_abs3 hp
  rw [Measure.map_congr hEq, Measure.map_id]

#print axioms gauge_density_normalized3
#print axioms gauge_density_class3
#print axioms gauge_forward_transport3

end

end QuantyraNullCone
