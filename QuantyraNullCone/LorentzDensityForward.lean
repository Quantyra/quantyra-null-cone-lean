import QuantyraNullCone.LorentzDensityWeight
import QuantyraNullCone.LorentzCommonDensity
import QuantyraNullCone.TimeCommonCoupling
import QuantyraNullCone.LorentzDistortionTriangle

namespace QuantyraNullCone
open MeasureTheory Set
noncomputable section
set_option maxHeartbeats 800000

/-- The selected geometric loss is at most the uniform density error on the original class. -/
theorem geometricDistortion3_le_of_density_close {rho sigma : LorentzPoint3 → ℝ}
    (hR : InDensityClass3 rho) (hS : InDensityClass3 sigma) {delta : ℝ} (hd : 0 ≤ delta)
    (hc : ∀ p ∈ closedLorentzDiamond3, |rho p - sigma p| ≤ delta) :
    geometricDistortion3 hR hS ≤ delta := by
  letI := hR.closedDensity_isProbabilityMeasure
  letI := hS.closedDensity_isProbabilityMeasure
  letI : IsFiniteMeasure (commonDensityMeasure3 rho sigma) :=
    isFiniteMeasure_of_le (closedDensityMeasure3 rho) (common_density_le_left3 rho sigma)
  apply timeDistortionLoss_le_of_common
    (tx := quotientTime3 hR.timeWeight) (ty := quotientTime3 hS.timeWeight)
    (common_density_le_left3 rho sigma) (common_density_le_right3 rho sigma)
    (continuous_timeProfileProjection3 hR.timeWeight).measurable
    (continuous_timeProfileProjection3 hS.timeWeight).measurable
    (continuous_quotientTime3 hR.timeWeight).measurable
    (continuous_quotientTime3 hS.timeWeight).measurable hd
  · have h := common_density_missing_mass3 hR hS hd hc
    calc
      _ ≤ ENNReal.ofReal (delta / 2) + ENNReal.ofReal (delta / 2) := add_le_add h h
      _ = ENNReal.ofReal delta := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
  · intro p q
    rw [quotientTime3_projection,quotientTime3_projection]
    exact density_time_separation_difference3 hR hS hd hc p.val q.val

theorem geometricDistortion3_same_density_on_closed {rho sigma : LorentzPoint3 → ℝ}
    (hR : InDensityClass3 rho) (hS : InDensityClass3 sigma)
    (hc : Set.EqOn rho sigma closedLorentzDiamond3) : geometricDistortion3 hR hS = 0 := by
  apply le_antisymm _ (geometricDistortion3_nonneg hR hS)
  apply geometricDistortion3_le_of_density_close hR hS le_rfl
  intro p hp
  rw [hc hp,sub_self,abs_zero]

/-- Joint control of the geometric loss in the original coordinates; no inverse claim is made. -/
theorem geometricDistortion3_density_perturbation {rho sigma rho' sigma' : LorentzPoint3 → ℝ}
    (hR : InDensityClass3 rho) (hS : InDensityClass3 sigma)
    (hR' : InDensityClass3 rho') (hS' : InDensityClass3 sigma')
    {delta eta : ℝ} (hd : 0 ≤ delta) (he : 0 ≤ eta)
    (hr : ∀ p ∈ closedLorentzDiamond3, |rho p - rho' p| ≤ delta)
    (hs : ∀ p ∈ closedLorentzDiamond3, |sigma p - sigma' p| ≤ eta) :
    |geometricDistortion3 hR hS - geometricDistortion3 hR' hS'| ≤ delta + eta := by
  have h1 := (geometricDistortion3_reverse_triangle hR hR' hS).trans
    (geometricDistortion3_le_of_density_close hR hR' hd hr)
  have h2 := (geometricDistortion3_reverse_triangle hS hS' hR').trans
    (geometricDistortion3_le_of_density_close hS hS' he hs)
  rw [geometricDistortion3_symm hS hR',geometricDistortion3_symm hS' hR'] at h2
  exact (abs_sub_le _ _ _).trans (add_le_add h1 h2)

#print axioms geometricDistortion3_le_of_density_close
#print axioms geometricDistortion3_same_density_on_closed
#print axioms geometricDistortion3_density_perturbation

end
end QuantyraNullCone
