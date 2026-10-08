import QuantyraNullCone.LorentzOrderLaws
import QuantyraNullCone.LorentzSmooth

namespace QuantyraNullCone

noncomputable section

theorem gauge_metric_coefficient3 {p : LorentzPoint3} (hp : p ∈ closedLorentzDiamond3) :
    Real.rpow (gaugeDensity3 p) (2 / 3) = flowFactor3 (-gaugeParameter3) p ^ 2 := by
  have hPos := flow_factor_pos3 gauge_parameter_abs3 hp
  unfold gaugeDensity3
  rw [Real.rpow_eq_pow, ← Real.rpow_natCast_mul hPos.le 3 (2 / 3)]
  norm_num

/-- Actual metric pullback by the inverse map; these densities describe isometric geometries. -/
theorem gauge_metric_isometry3 {p : LorentzPoint3} (hp : p ∈ closedLorentzDiamond3)
    (u v : LorentzPoint3) :
    densityMetric3 gaugeDensity3 p u v =
      densityMetric3 flatDensity3 (lorentzFlow3 (-gaugeParameter3) p)
        (lorentzFlowDerivative3 (-gaugeParameter3) p u) (lorentzFlowDerivative3 (-gaugeParameter3) p v) := by
  simp only [densityMetric3, flatDensity3]
  rw [gauge_metric_coefficient3 hp, lorentz_flow_derivative_bilinear3 _ _ _ _
    (flow_denominator_pos3 gauge_parameter_abs3 hp).ne']
  simp only [Real.rpow_eq_pow, Real.one_rpow, mul_one]
  ring

/-- Explicit counterexample to coordinate-gauge identifiability, with the isometry boundary included. -/
theorem higher_dimensional_gauge_counterexample3 :
    InDensityClass3 flatDensity3 ∧ InDensityClass3 gaugeDensity3 ∧
    (∀ n, orderLaw3 gaugeDensity3 n = orderLaw3 flatDensity3 n) ∧
    (∀ n, unlabeledOrderLaw3 gaugeDensity3 n = unlabeledOrderLaw3 flatDensity3 n) ∧
    0 < gaugeO2Distance3 ∧
    (∀ p ∈ closedLorentzDiamond3, ∀ u v,
      densityMetric3 gaugeDensity3 p u v =
        densityMetric3 flatDensity3 (lorentzFlow3 (-gaugeParameter3) p)
          (lorentzFlowDerivative3 (-gaugeParameter3) p u) (lorentzFlowDerivative3 (-gaugeParameter3) p v)) :=
  ⟨flat_density_class3, gauge_density_class3, gauge_order_laws_equal3,
    gauge_unlabeled_order_laws_equal3, gauge_o2_distance_positive3, fun _ hp u v => gauge_metric_isometry3 hp u v⟩

#print axioms gauge_metric_isometry3
#print axioms higher_dimensional_gauge_counterexample3

end

end QuantyraNullCone
