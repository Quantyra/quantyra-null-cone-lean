import QuantyraNullCone.LorentzFlat
import QuantyraNullCone.LorentzJacobian
import Mathlib.MeasureTheory.Function.Jacobian

namespace QuantyraNullCone

open MeasureTheory

noncomputable section

theorem lorentz_flow_measurable3 (a : ℝ) : Measurable (lorentzFlow3 a) := by
  have hCompose : lorentzFlow3 a = (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm ∘
      (fun p : LorentzPoint3 => ![flowTimeNumerator3 a p / flowDenominator3 a p,
        flowFactor3 a p * p 1, flowFactor3 a p * p 2]) := rfl
  rw [hCompose]
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.continuous.measurable.comp
  apply measurable_pi_lambda
  intro i
  fin_cases i <;>
    dsimp [flowTimeNumerator3, flowDenominator3, flowFactor3, spatialSquared3] <;> fun_prop

/-- The Jacobian theorem applied to the actual inverse automorphism and actual Lebesgue measure. -/
theorem gauge_inverse_transport_volume3 :
    Measure.map (lorentzFlow3 (-gaugeParameter3))
      (((volume : Measure LorentzPoint3).restrict lorentzDiamond3).withDensity
        (fun p => ENNReal.ofReal (gaugeDensity3 p))) =
      (volume : Measure LorentzPoint3).restrict lorentzDiamond3 := by
  have hJac := map_withDensity_abs_det_fderiv_eq_addHaar (volume : Measure LorentzPoint3)
    isOpen_lorentzDiamond3.measurableSet.nullMeasurableSet
    (fun p hp => (hasFDerivAt_lorentz_flow3 (-gaugeParameter3) p
      (flow_denominator_pos3 gauge_parameter_abs3 (lorentz_diamond_subset_closed3 hp)).ne').hasFDerivWithinAt)
    (lorentz_flow_injectiveOn3 gauge_parameter_abs3)
  rw [lorentz_flow_image3 gauge_parameter_abs3] at hJac
  have hDensity : ((volume : Measure LorentzPoint3).restrict lorentzDiamond3).withDensity
      (fun p => ENNReal.ofReal |(lorentzFlowDerivative3 (-gaugeParameter3) p).det|) =
      ((volume : Measure LorentzPoint3).restrict lorentzDiamond3).withDensity
        (fun p => ENNReal.ofReal (gaugeDensity3 p)) := by
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem isOpen_lorentzDiamond3.measurableSet] with p hp
    have hClosed := lorentz_diamond_subset_closed3 hp
    rw [lorentz_flow_derivative_det3 _ _ (flow_denominator_pos3 gauge_parameter_abs3 hClosed).ne',
      abs_of_pos (pow_pos (flow_factor_pos3 gauge_parameter_abs3 hClosed) 3)]
    rfl
  rw [hDensity] at hJac
  exact hJac

theorem gauge_inverse_transport3 :
    Measure.map (lorentzFlow3 (-gaugeParameter3)) (densityMeasure3 gaugeDensity3) = flatDiamondMeasure3 := by
  unfold densityMeasure3 flatDiamondMeasure3
  rw [withDensity_smul_measure, Measure.map_smul, gauge_inverse_transport_volume3]

#print axioms lorentz_flow_measurable3
#print axioms gauge_inverse_transport_volume3
#print axioms gauge_inverse_transport3

end

end QuantyraNullCone
