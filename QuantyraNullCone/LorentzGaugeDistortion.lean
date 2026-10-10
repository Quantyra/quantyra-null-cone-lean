import QuantyraNullCone.LorentzFlowTime
import QuantyraNullCone.LorentzDistortionIsomorphy

namespace QuantyraNullCone

open Set MeasureTheory
noncomputable section

def closedLorentzMap3 (F : LorentzPoint3 → LorentzPoint3)
    (hC : MapsTo F closedLorentzDiamond3 closedLorentzDiamond3)
    (p : ClosedLorentzPoint3) : ClosedLorentzPoint3 := ⟨F p.val,hC p.property⟩

theorem measurable_closedLorentzMap3 {F : LorentzPoint3 → LorentzPoint3}
    (hC : MapsTo F closedLorentzDiamond3 closedLorentzDiamond3) (hF : Measurable F) :
    Measurable (closedLorentzMap3 F hC) :=
  (hF.comp measurable_subtype_coe).subtype_mk

theorem closed_density_transport3 {rho sigma : LorentzPoint3 → ℝ}
    {F : LorentzPoint3 → LorentzPoint3}
    (hC : MapsTo F closedLorentzDiamond3 closedLorentzDiamond3) (hF : Measurable F)
    (hmu : (densityMeasure3 rho).map F = densityMeasure3 sigma) :
    (closedDensityMeasure3 rho).map (closedLorentzMap3 F hC) = closedDensityMeasure3 sigma := by
  apply (MeasurableEmbedding.subtype_coe isClosed_closedLorentzDiamond3.measurableSet).map_injective
  rw [Measure.map_map measurable_subtype_coe (measurable_closedLorentzMap3 hC hF),
    closedDensityMeasure3_map_val]
  change (closedDensityMeasure3 rho).map (F ∘ Subtype.val) = densityMeasure3 sigma
  rw [← Measure.map_map hF measurable_subtype_coe,closedDensityMeasure3_map_val,hmu]

set_option maxHeartbeats 800000 in
/-- A measure- and time-preserving map on the original diamond constructs a zero coupling
of the actual quotient laws, without assuming a chosen quotient map is measurable. -/
theorem geometricDistortion3_eq_zero_of_time_transport {rho sigma : LorentzPoint3 → ℝ}
    (hR : InDensityClass3 rho) (hS : InDensityClass3 sigma)
    {F : LorentzPoint3 → LorentzPoint3}
    (hC : MapsTo F closedLorentzDiamond3 closedLorentzDiamond3) (hF : Measurable F)
    (hmu : (densityMeasure3 rho).map F = densityMeasure3 sigma)
    (htime : ∀ p ∈ closedLorentzDiamond3, ∀ q ∈ closedLorentzDiamond3,
      weightedTimeSeparation3 (densityTimeWeight3 rho) p q =
        weightedTimeSeparation3 (densityTimeWeight3 sigma) (F p) (F q)) :
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
    apply ae_of_all
    intro z
    change quotientTime3 hR.timeWeight (timeProfileProjection3 hR.timeWeight z.1)
      (timeProfileProjection3 hR.timeWeight z.2) =
      quotientTime3 hS.timeWeight (timeProfileProjection3 hS.timeWeight (f z.1))
        (timeProfileProjection3 hS.timeWeight (f z.2))
    rw [quotientTime3_projection,quotientTime3_projection]
    exact htime _ z.1.property _ z.2.property

theorem gauge_geometric_distortion_zero3 :
    geometricDistortion3 gauge_density_class3 flat_density_class3 = 0 := by
  apply geometricDistortion3_eq_zero_of_time_transport gauge_density_class3 flat_density_class3
    (fun _ hp => lorentz_flow_preserves_closed3 gauge_parameter_abs3 hp)
    (lorentz_flow_measurable3 (-gaugeParameter3))
  · simpa only [flat_density_measure3] using gauge_inverse_transport3
  · exact fun _ hp _ hq => (gauge_inverse_time_separation3 hp hq).symm

/-- The selected geometric loss removes the accepted coordinate-gauge obstruction. -/
theorem gauge_geometric_loss_removes_obstruction3 :
    geometricDistortion3 gauge_density_class3 flat_density_class3 = 0 ∧ 0 < gaugeO2Distance3 :=
  ⟨gauge_geometric_distortion_zero3,gauge_o2_distance_positive3⟩

theorem gauge_quotient_time_homeomorph3 :
    ∃ e : TimeProfileSpace3 gauge_density_class3.timeWeight ≃ₜ TimeProfileSpace3 flat_density_class3.timeWeight,
      MeasurePreserving e (quotientDensityMeasure3 gauge_density_class3.timeWeight gaugeDensity3)
        (quotientDensityMeasure3 flat_density_class3.timeWeight flatDensity3) ∧
      ∀ x y, quotientTime3 gauge_density_class3.timeWeight x y =
        quotientTime3 flat_density_class3.timeWeight (e x) (e y) :=
  (geometricDistortion3_eq_zero_iff_homeomorph gauge_density_class3 flat_density_class3).mp
    gauge_geometric_distortion_zero3

#print axioms measurable_closedLorentzMap3
#print axioms closed_density_transport3
#print axioms geometricDistortion3_eq_zero_of_time_transport
#print axioms gauge_geometric_distortion_zero3
#print axioms gauge_geometric_loss_removes_obstruction3
#print axioms gauge_quotient_time_homeomorph3

end
end QuantyraNullCone
