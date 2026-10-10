import QuantyraNullCone.LorentzInteriorIsometry
import QuantyraNullCone.LorentzGaugeDistortion

namespace QuantyraNullCone
open MeasureTheory Set Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 800000

/-- A measurable boundary completion; its boundary values have no sampling mass. -/
def openLorentzCompletion3 (F : LorentzPoint3 → LorentzPoint3) : LorentzPoint3 → LorentzPoint3 := by
  classical
  exact lorentzDiamond3.piecewise F (fun _ => 0)

theorem openLorentzCompletion3_of_mem (F : LorentzPoint3 → LorentzPoint3)
    {p : LorentzPoint3} (hp : p ∈ lorentzDiamond3) : openLorentzCompletion3 F p = F p := by
  classical
  simp [openLorentzCompletion3,hp]

theorem measurable_openLorentzCompletion3 {F : LorentzPoint3 → LorentzPoint3}
    (hF : ContinuousOn F lorentzDiamond3) : Measurable (openLorentzCompletion3 F) := by
  classical
  exact hF.measurable_piecewise continuousOn_const isOpen_lorentzDiamond3.measurableSet

theorem openLorentzCompletion3_maps_closed {F : LorentzPoint3 → LorentzPoint3}
    (hF : MapsTo F lorentzDiamond3 lorentzDiamond3) :
    MapsTo (openLorentzCompletion3 F) closedLorentzDiamond3 closedLorentzDiamond3 := by
  classical
  intro p _
  by_cases hp : p ∈ lorentzDiamond3
  · rw [openLorentzCompletion3_of_mem F hp]
    exact lorentz_diamond_subset_closed3 (hF hp)
  · simp [openLorentzCompletion3,hp,closedLorentzDiamond3,spatialRadius3,spatialSquared3]

theorem hasFDerivAt_openLorentzCompletion3 {F : LorentzPoint3 → LorentzPoint3}
    {L : LorentzPoint3 →L[ℝ] LorentzPoint3} {p : LorentzPoint3}
    (hp : p ∈ lorentzDiamond3) (hF : HasFDerivAt F L p) :
    HasFDerivAt (openLorentzCompletion3 F) L p := by
  apply hF.congr_of_eventuallyEq
  filter_upwards [isOpen_lorentzDiamond3.mem_nhds hp] with q hq
  exact openLorentzCompletion3_of_mem F hq

theorem openLorentzCompletion3_bijOn {F : LorentzPoint3 → LorentzPoint3}
    (hF : BijOn F lorentzDiamond3 lorentzDiamond3) :
    BijOn (openLorentzCompletion3 F) lorentzDiamond3 lorentzDiamond3 := by
  refine ⟨?_,?_,?_⟩
  · intro p hp
    rw [openLorentzCompletion3_of_mem F hp]
    exact hF.mapsTo hp
  · intro p hp q hq he
    rw [openLorentzCompletion3_of_mem F hp,openLorentzCompletion3_of_mem F hq] at he
    exact hF.injOn hp hq he
  · intro q hq
    obtain ⟨p,hp,he⟩ := hF.surjOn hq
    exact ⟨p,hp,(openLorentzCompletion3_of_mem F hp).trans he⟩

theorem density_measure3_ae_open (rho : LorentzPoint3 → ℝ) :
    ∀ᵐ p ∂densityMeasure3 rho, p ∈ lorentzDiamond3 := by
  apply (withDensity_absolutelyContinuous flatDiamondMeasure3 _).ae_le
  exact Measure.ae_smul_measure (ae_restrict_mem isOpen_lorentzDiamond3.measurableSet) _

theorem closed_density3_ae_open (rho : LorentzPoint3 → ℝ) :
    ∀ᵐ p ∂closedDensityMeasure3 rho, p.val ∈ lorentzDiamond3 := by
  have h := density_measure3_ae_open rho
  rw [← closedDensityMeasure3_map_val rho] at h
  exact (ae_map_iff measurable_subtype_coe.aemeasurable isOpen_lorentzDiamond3.measurableSet).mp h

/-- Change of variables for the actual density laws; the Jacobian equation is explicit. -/
theorem density_transport_of_jacobian3 {rho sigma : LorentzPoint3 → ℝ}
    {F : LorentzPoint3 → LorentzPoint3}
    {DF : LorentzPoint3 → LorentzPoint3 →L[ℝ] LorentzPoint3}
    (hf : Measurable F) (hd : ∀ p ∈ lorentzDiamond3, HasFDerivAt F (DF p) p)
    (hb : BijOn F lorentzDiamond3 lorentzDiamond3)
    (hj : ∀ p ∈ lorentzDiamond3, sigma (F p) * |(DF p).det| = rho p) :
    (densityMeasure3 rho).map F = densityMeasure3 sigma := by
  have hvolume : (((volume : Measure LorentzPoint3).restrict lorentzDiamond3).withDensity
      (fun p => ENNReal.ofReal (rho p))).map F =
      ((volume : Measure LorentzPoint3).restrict lorentzDiamond3).withDensity
        (fun p => ENNReal.ofReal (sigma p)) := by
    ext t ht
    rw [Measure.map_apply hf ht,withDensity_apply _ (hf ht),withDensity_apply _ ht,
      Measure.restrict_restrict (hf ht),Measure.restrict_restrict ht]
    have hset := (hf ht).inter isOpen_lorentzDiamond3.measurableSet
    have he := lintegral_image_eq_lintegral_abs_det_fderiv_mul (volume : Measure LorentzPoint3)
      hset (fun p hp => (hd p hp.2).hasFDerivWithinAt) (hb.injOn.mono inter_subset_right)
      (fun p => ENNReal.ofReal (sigma p))
    rw [image_preimage_inter,hb.image_eq] at he
    rw [he]
    apply setLIntegral_congr_fun hset
    intro p hp
    change ENNReal.ofReal (rho p) = ENNReal.ofReal |(DF p).det| * ENNReal.ofReal (sigma (F p))
    rw [← ENNReal.ofReal_mul (abs_nonneg ((DF p).det)),mul_comm,hj p hp.2]
  unfold densityMeasure3 flatDiamondMeasure3
  rw [withDensity_smul_measure,withDensity_smul_measure,Measure.map_smul,hvolume]

theorem InteriorDensityIsometry3.density_transport
    {rho sigma : LorentzPoint3 → ℝ} {F G : LorentzPoint3 → LorentzPoint3}
    {DF DG : LorentzPoint3 → LorentzPoint3 →L[ℝ] LorentzPoint3}
    (h : InteriorDensityIsometry3 rho sigma F G DF DG)
    (hR : InDensityClass3 rho) (hS : InDensityClass3 sigma) :
    (densityMeasure3 rho).map (openLorentzCompletion3 F) = densityMeasure3 sigma := by
  apply density_transport_of_jacobian3 (measurable_openLorentzCompletion3 h.forward.smooth.continuousOn)
    (fun p hp => hasFDerivAt_openLorentzCompletion3 hp (h.forward.hasFDerivAt p hp))
    (openLorentzCompletion3_bijOn h.forward_bijOn)
  intro p hp
  rw [openLorentzCompletion3_of_mem F hp]
  exact h.jacobian hR hS hp

#print axioms openLorentzCompletion3_of_mem
#print axioms measurable_openLorentzCompletion3
#print axioms openLorentzCompletion3_maps_closed
#print axioms hasFDerivAt_openLorentzCompletion3
#print axioms openLorentzCompletion3_bijOn
#print axioms density_measure3_ae_open
#print axioms closed_density3_ae_open
#print axioms density_transport_of_jacobian3
#print axioms InteriorDensityIsometry3.density_transport

end
end QuantyraNullCone
