import QuantyraNullCone.LorentzInteriorCurveMap
import QuantyraNullCone.LorentzMetricJacobian

namespace QuantyraNullCone
open Set Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 800000

/-- A time-oriented C1 isometry on the open diamond with its C1 inverse.
Only the forward metric identity is assumed; inverse metric and volume transport are derived. -/
structure InteriorDensityIsometry3 (rho sigma : LorentzPoint3 → ℝ)
    (F G : LorentzPoint3 → LorentzPoint3)
    (DF DG : LorentzPoint3 → LorentzPoint3 →L[ℝ] LorentzPoint3) : Prop where
  forward : IsInteriorCausalMap3 F DF
  inverse : IsInteriorCausalMap3 G DG
  left_inv : ∀ p ∈ lorentzDiamond3, G (F p) = p
  right_inv : ∀ q ∈ lorentzDiamond3, F (G q) = q
  metric : ∀ p ∈ lorentzDiamond3, ∀ u v,
    densityMetric3 rho p u v = densityMetric3 sigma (F p) (DF p u) (DF p v)

variable {rho sigma : LorentzPoint3 → ℝ}
  {F G : LorentzPoint3 → LorentzPoint3}
  {DF DG : LorentzPoint3 → LorentzPoint3 →L[ℝ] LorentzPoint3}

theorem InteriorDensityIsometry3.forward_bijOn (h : InteriorDensityIsometry3 rho sigma F G DF DG) :
    BijOn F lorentzDiamond3 lorentzDiamond3 := by
  refine ⟨h.forward.mapsTo,?_,?_⟩
  · intro p hp q hq he
    have hh := congrArg G he
    rwa [h.left_inv p hp,h.left_inv q hq] at hh
  · intro q hq
    exact ⟨G q,h.inverse.mapsTo hq,h.right_inv q hq⟩

theorem InteriorDensityIsometry3.derivative_right_inverse
    (h : InteriorDensityIsometry3 rho sigma F G DF DG) {q : LorentzPoint3}
    (hq : q ∈ lorentzDiamond3) : (DF (G q)).comp (DG q) = ContinuousLinearMap.id ℝ LorentzPoint3 := by
  have hd := (h.forward.hasFDerivAt _ (h.inverse.mapsTo hq)).comp q (h.inverse.hasFDerivAt q hq)
  have he : (fun x : LorentzPoint3 => x) =ᶠ[𝓝 q] (F ∘ G) := by
    filter_upwards [isOpen_lorentzDiamond3.mem_nhds hq] with x hx
    exact (h.right_inv x hx).symm
  exact (hd.congr_of_eventuallyEq he).unique (hasFDerivAt_id q)

theorem InteriorDensityIsometry3.inverse_metric (h : InteriorDensityIsometry3 rho sigma F G DF DG)
    {q : LorentzPoint3} (hq : q ∈ lorentzDiamond3) (u v : LorentzPoint3) :
    densityMetric3 sigma q u v = densityMetric3 rho (G q) (DG q u) (DG q v) := by
  have he := h.metric (G q) (h.inverse.mapsTo hq) (DG q u) (DG q v)
  have hu := congrArg (fun L : LorentzPoint3 →L[ℝ] LorentzPoint3 => L u) (h.derivative_right_inverse hq)
  have hv := congrArg (fun L : LorentzPoint3 →L[ℝ] LorentzPoint3 => L v) (h.derivative_right_inverse hq)
  change DF (G q) (DG q u) = u at hu
  change DF (G q) (DG q v) = v at hv
  rw [h.right_inv q hq,hu,hv] at he
  exact he.symm

theorem InteriorDensityIsometry3.time_eq (h : InteriorDensityIsometry3 rho sigma F G DF DG)
    (hR : InDensityClass3 rho) (hS : InDensityClass3 sigma)
    {p q : LorentzPoint3} (hp : p ∈ lorentzDiamond3) (hq : q ∈ lorentzDiamond3) :
    weightedTimeSeparation3 (densityTimeWeight3 rho) p q =
      weightedTimeSeparation3 (densityTimeWeight3 sigma) (F p) (F q) := by
  apply le_antisymm
  · exact weighted_time_le_of_interior_causal_map3 h.forward hS.timeWeight
      (fun x hx v hv => density_metric_speed_transport3 hR hS h.forward h.metric hx hv) hp hq
  · have hi := weighted_time_le_of_interior_causal_map3 h.inverse hR.timeWeight
      (fun x hx v hv => density_metric_speed_transport3 hS hR h.inverse
        (fun y hy u v => h.inverse_metric hy u v) hx hv) (h.forward.mapsTo hp) (h.forward.mapsTo hq)
    simpa only [h.left_inv p hp,h.left_inv q hq] using hi

theorem InteriorDensityIsometry3.jacobian (h : InteriorDensityIsometry3 rho sigma F G DF DG)
    (hR : InDensityClass3 rho) (hS : InDensityClass3 sigma)
    {p : LorentzPoint3} (hp : p ∈ lorentzDiamond3) : sigma (F p) * |(DF p).det| = rho p := by
  apply density_metric_jacobian3 (L := DF p)
  · linarith [(hR.bounds p (lorentz_diamond_subset_closed3 hp)).1]
  · linarith [(hS.bounds (F p) (lorentz_diamond_subset_closed3 (h.forward.mapsTo hp))).1]
  · exact h.metric p hp

#print axioms InteriorDensityIsometry3.forward_bijOn
#print axioms InteriorDensityIsometry3.derivative_right_inverse
#print axioms InteriorDensityIsometry3.inverse_metric
#print axioms InteriorDensityIsometry3.time_eq
#print axioms InteriorDensityIsometry3.jacobian

end
end QuantyraNullCone
