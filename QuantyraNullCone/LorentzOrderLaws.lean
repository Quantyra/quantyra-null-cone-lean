import QuantyraNullCone.LorentzGaugeClass
import QuantyraNullCone.Unlabeled

namespace QuantyraNullCone

open MeasureTheory

noncomputable section

theorem flat_density_measure3 : densityMeasure3 flatDensity3 = flatDiamondMeasure3 := by
  simp [densityMeasure3, flatDensity3]

def lorentzSampleFlow3 (a : ℝ) {n : ℕ} (w : Fin n → LorentzPoint3) : Fin n → LorentzPoint3 :=
  fun i => lorentzFlow3 a (w i)

theorem lorentz_sample_flow_measurable3 (a : ℝ) (n : ℕ) : Measurable (@lorentzSampleFlow3 a n) :=
  measurable_pi_lambda _ (fun i => (lorentz_flow_measurable3 a).comp (measurable_pi_apply i))

theorem gauge_sample_forward_transport3 (n : ℕ) :
    Measure.map (lorentzSampleFlow3 gaugeParameter3) (sampleMeasure3 flatDensity3 n) =
      sampleMeasure3 gaugeDensity3 n := by
  letI := flat_diamond_probability3
  letI : IsProbabilityMeasure (Measure.map (lorentzFlow3 gaugeParameter3) flatDiamondMeasure3) :=
    Measure.isProbabilityMeasure_map (lorentz_flow_measurable3 _).aemeasurable
  unfold sampleMeasure3 lorentzSampleFlow3
  rw [flat_density_measure3, Measure.pi_map_pi (fun _ => (lorentz_flow_measurable3 _).aemeasurable)]
  simp_rw [gauge_forward_transport3]

theorem InDensityClass3.sample_ae_closed {rho : LorentzPoint3 → ℝ} (h : InDensityClass3 rho) (n : ℕ) :
    ∀ᵐ w ∂sampleMeasure3 rho n, ∀ i, w i ∈ closedLorentzDiamond3 := by
  letI := h.isProbabilityMeasure
  exact Filter.eventually_all.mpr fun i =>
    (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => densityMeasure3 rho) (i := i)).eventually
      (density_measure3_ae_closed rho)

/-- Equality of every actual finite directed labeled-order pushforward. -/
theorem gauge_order_laws_equal3 (n : ℕ) : orderLaw3 gaugeDensity3 n = orderLaw3 flatDensity3 n := by
  have hParam : |gaugeParameter3| < 1 := by norm_num [gaugeParameter3]
  unfold orderLaw3
  rw [← gauge_sample_forward_transport3 n, Measure.map_map (sampledOrder3_measurable n)
    (lorentz_sample_flow_measurable3 _ n)]
  apply Measure.map_congr
  filter_upwards [flat_density_class3.sample_ae_closed n] with w hw
  exact sampledOrder3_flow_eq hParam w hw

def unlabeledOrderLaw3 (rho : LorentzPoint3 → ℝ) (n : ℕ) : Measure (UnlabeledOrderCode n) :=
  (orderLaw3 rho n).map forgetOrderLabels

theorem gauge_unlabeled_order_laws_equal3 (n : ℕ) :
    unlabeledOrderLaw3 gaugeDensity3 n = unlabeledOrderLaw3 flatDensity3 n := by
  simp only [unlabeledOrderLaw3, gauge_order_laws_equal3]

#print axioms gauge_sample_forward_transport3
#print axioms gauge_order_laws_equal3
#print axioms gauge_unlabeled_order_laws_equal3

end

end QuantyraNullCone
