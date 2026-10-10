import QuantyraNullCone.LorentzInteriorMeasure

namespace QuantyraNullCone
open MeasureTheory Set
noncomputable section
set_option maxHeartbeats 800000

/-- Time preservation on a set of full sampling measure suffices for the actual quotient loss. -/
theorem geometricDistortion3_eq_zero_of_ae_time_transport {rho sigma : LorentzPoint3 → ℝ}
    (hR : InDensityClass3 rho) (hS : InDensityClass3 sigma)
    {F : LorentzPoint3 → LorentzPoint3}
    (hC : MapsTo F closedLorentzDiamond3 closedLorentzDiamond3) (hF : Measurable F)
    (hmu : (densityMeasure3 rho).map F = densityMeasure3 sigma)
    (htime : ∀ᵐ z ∂(closedDensityMeasure3 rho).prod (closedDensityMeasure3 rho),
      weightedTimeSeparation3 (densityTimeWeight3 rho) z.1.val z.2.val =
        weightedTimeSeparation3 (densityTimeWeight3 sigma) (F z.1.val) (F z.2.val)) :
    geometricDistortion3 hR hS = 0 := by
  letI := hR.closedDensity_isProbabilityMeasure
  let f := closedLorentzMap3 F hC
  have hf : Measurable f := measurable_closedLorentzMap3 hC hF
  have hm : (closedDensityMeasure3 rho).map f = closedDensityMeasure3 sigma :=
    closed_density_transport3 hC hF hmu
  let g : ClosedLorentzPoint3 → TimeProfileSpace3 hR.timeWeight × TimeProfileSpace3 hS.timeWeight :=
    fun p => (timeProfileProjection3 hR.timeWeight p,timeProfileProjection3 hS.timeWeight (f p))
  have hpr := (continuous_timeProfileProjection3 hR.timeWeight).measurable
  have hps := (continuous_timeProfileProjection3 hS.timeWeight).measurable
  have hg : Measurable g := hpr.prodMk (hps.comp hf)
  apply (geometricDistortion3_eq_zero_iff hR hS).mpr
  refine ⟨(closedDensityMeasure3 rho).map g,
    { left := ?_, right := ?_, time_eq := ?_ }⟩
  · rw [Measure.map_map measurable_fst hg]
    rfl
  · rw [Measure.map_map measurable_snd hg]
    change (closedDensityMeasure3 rho).map ((timeProfileProjection3 hS.timeWeight) ∘ f) = _
    rw [← Measure.map_map hps hf,hm]
    rfl
  · rw [Measure.map_prod_map _ _ hg hg]
    have hx : Measurable (fun z : (TimeProfileSpace3 hR.timeWeight × TimeProfileSpace3 hS.timeWeight) ×
        (TimeProfileSpace3 hR.timeWeight × TimeProfileSpace3 hS.timeWeight) =>
        quotientTime3 hR.timeWeight z.1.1 z.2.1) :=
      (continuous_quotientTime3 hR.timeWeight).measurable.comp
        (measurable_fst.fst.prodMk measurable_snd.fst)
    have hy : Measurable (fun z : (TimeProfileSpace3 hR.timeWeight × TimeProfileSpace3 hS.timeWeight) ×
        (TimeProfileSpace3 hR.timeWeight × TimeProfileSpace3 hS.timeWeight) =>
        quotientTime3 hS.timeWeight z.1.2 z.2.2) :=
      (continuous_quotientTime3 hS.timeWeight).measurable.comp
        (measurable_fst.snd.prodMk measurable_snd.snd)
    apply (ae_map_iff (hg.prodMap hg).aemeasurable (measurableSet_eq_fun hx hy)).mpr
    filter_upwards [htime] with z hz
    change quotientTime3 hR.timeWeight (timeProfileProjection3 hR.timeWeight z.1)
      (timeProfileProjection3 hR.timeWeight z.2) =
      quotientTime3 hS.timeWeight (timeProfileProjection3 hS.timeWeight (f z.1))
        (timeProfileProjection3 hS.timeWeight (f z.2))
    rw [quotientTime3_projection,quotientTime3_projection]
    exact hz

theorem InteriorDensityIsometry3.geometric_distortion_zero
    {rho sigma : LorentzPoint3 → ℝ} {F G : LorentzPoint3 → LorentzPoint3}
    {DF DG : LorentzPoint3 → LorentzPoint3 →L[ℝ] LorentzPoint3}
    (h : InteriorDensityIsometry3 rho sigma F G DF DG)
    (hR : InDensityClass3 rho) (hS : InDensityClass3 sigma) : geometricDistortion3 hR hS = 0 := by
  letI := hR.closedDensity_isProbabilityMeasure
  apply geometricDistortion3_eq_zero_of_ae_time_transport hR hS
    (openLorentzCompletion3_maps_closed h.forward.mapsTo)
    (measurable_openLorentzCompletion3 h.forward.smooth.continuousOn)
    (h.density_transport hR hS)
  have hmem := closed_density3_ae_open rho
  have hl : ∀ᵐ z ∂(closedDensityMeasure3 rho).prod (closedDensityMeasure3 rho),
      z.1.val ∈ lorentzDiamond3 := Measure.quasiMeasurePreserving_fst.ae hmem
  have hr : ∀ᵐ z ∂(closedDensityMeasure3 rho).prod (closedDensityMeasure3 rho),
      z.2.val ∈ lorentzDiamond3 := Measure.quasiMeasurePreserving_snd.ae hmem
  filter_upwards [hl,hr] with z hz1 hz2
  rw [openLorentzCompletion3_of_mem F hz1,openLorentzCompletion3_of_mem F hz2]
  exact h.time_eq hR hS hz1 hz2

theorem InteriorDensityIsometry3.quotient_time_homeomorph
    {rho sigma : LorentzPoint3 → ℝ} {F G : LorentzPoint3 → LorentzPoint3}
    {DF DG : LorentzPoint3 → LorentzPoint3 →L[ℝ] LorentzPoint3}
    (h : InteriorDensityIsometry3 rho sigma F G DF DG)
    (hR : InDensityClass3 rho) (hS : InDensityClass3 sigma) :
    ∃ e : TimeProfileSpace3 hR.timeWeight ≃ₜ TimeProfileSpace3 hS.timeWeight,
      MeasurePreserving e (quotientDensityMeasure3 hR.timeWeight rho)
        (quotientDensityMeasure3 hS.timeWeight sigma) ∧
      ∀ x y, quotientTime3 hR.timeWeight x y = quotientTime3 hS.timeWeight (e x) (e y) :=
  (geometricDistortion3_eq_zero_iff_homeomorph hR hS).mp (h.geometric_distortion_zero hR hS)

theorem lorentz_flow_isInteriorCausalMap3 {a : ℝ} (ha : |a| < 1) :
    IsInteriorCausalMap3 (lorentzFlow3 a) (lorentzFlowDerivative3 a) where
  smooth := ((lorentz_flow_smooth3 a).mono
    (fun _ hp => flow_smooth_domain_contains3 ha (lorentz_diamond_subset_closed3 hp))).of_le (by simp)
  hasFDerivAt p hp := hasFDerivAt_lorentz_flow3 a p
    (flow_denominator_pos3 ha (lorentz_diamond_subset_closed3 hp)).ne'
  mapsTo := fun _ hp => lorentz_flow_preserves_open3 ha hp
  future := fun _ hp _ hv => lorentz_flow_derivative_future3 ha (lorentz_diamond_subset_closed3 hp) hv

/-- The original nontrivial counterexample satisfies the general interior contract. -/
theorem gauge_interior_isometry3 :
    InteriorDensityIsometry3 gaugeDensity3 flatDensity3
      (lorentzFlow3 (-gaugeParameter3)) (lorentzFlow3 gaugeParameter3)
      (lorentzFlowDerivative3 (-gaugeParameter3)) (lorentzFlowDerivative3 gaugeParameter3) where
  forward := lorentz_flow_isInteriorCausalMap3 gauge_parameter_abs3
  inverse := lorentz_flow_isInteriorCausalMap3 (by simpa using gauge_parameter_abs3)
  left_inv p hp := by
    simpa only [neg_neg] using lorentz_flow_inverse_closed3 gauge_parameter_abs3 (lorentz_diamond_subset_closed3 hp)
  right_inv p hp := lorentz_flow_inverse_closed3 (by simpa using gauge_parameter_abs3)
    (lorentz_diamond_subset_closed3 hp)
  metric p hp := gauge_metric_isometry3 (lorentz_diamond_subset_closed3 hp)

theorem gauge_geometric_zero_via_interior3 :
    geometricDistortion3 gauge_density_class3 flat_density_class3 = 0 :=
  gauge_interior_isometry3.geometric_distortion_zero gauge_density_class3 flat_density_class3

#print axioms geometricDistortion3_eq_zero_of_ae_time_transport
#print axioms InteriorDensityIsometry3.geometric_distortion_zero
#print axioms InteriorDensityIsometry3.quotient_time_homeomorph
#print axioms lorentz_flow_isInteriorCausalMap3
#print axioms gauge_interior_isometry3
#print axioms gauge_geometric_zero_via_interior3

end
end QuantyraNullCone
