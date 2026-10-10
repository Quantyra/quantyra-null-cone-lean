import QuantyraNullCone.TimeCouplingLoss
import QuantyraNullCone.LorentzQuotientLaws

/-! The selected coupling-distortion functional on the original normalized 2+1 class.
The elementary properties below do not yet assert the full metric/isomorphy theorem. -/

namespace QuantyraNullCone
open MeasureTheory
noncomputable section

def geometricDistortion3 {rho sigma : LorentzPoint3 → ℝ}
    (hR : InDensityClass3 rho) (hS : InDensityClass3 sigma) : ℝ :=
  timeDistortionLoss (quotientDensityMeasure3 hR.timeWeight rho)
    (quotientDensityMeasure3 hS.timeWeight sigma)
    (quotientTime3 hR.timeWeight) (quotientTime3 hS.timeWeight)

theorem geometricDistortion3_nonneg {rho sigma : LorentzPoint3 → ℝ}
    (hR : InDensityClass3 rho) (hS : InDensityClass3 sigma) : 0 ≤ geometricDistortion3 hR hS := by
  letI := hR.quotientDensity_isProbabilityMeasure hR.timeWeight
  letI := hS.quotientDensity_isProbabilityMeasure hS.timeWeight
  exact timeDistortionLoss_nonneg _ _ _ _

theorem geometricDistortion3_le_one {rho sigma : LorentzPoint3 → ℝ}
    (hR : InDensityClass3 rho) (hS : InDensityClass3 sigma) : geometricDistortion3 hR hS ≤ 1 := by
  letI := hR.quotientDensity_isProbabilityMeasure hR.timeWeight
  letI := hS.quotientDensity_isProbabilityMeasure hS.timeWeight
  exact timeDistortionLoss_le_one _ _ _ _

theorem geometricDistortion3_symm {rho sigma : LorentzPoint3 → ℝ}
    (hR : InDensityClass3 rho) (hS : InDensityClass3 sigma) :
    geometricDistortion3 hR hS = geometricDistortion3 hS hR := by
  letI := hR.quotientDensity_isProbabilityMeasure hR.timeWeight
  letI := hS.quotientDensity_isProbabilityMeasure hS.timeWeight
  exact timeDistortionLoss_symm _ _ (continuous_quotientTime3 hR.timeWeight).measurable
    (continuous_quotientTime3 hS.timeWeight).measurable

theorem geometricDistortion3_self {rho : LorentzPoint3 → ℝ} (hR : InDensityClass3 rho) :
    geometricDistortion3 hR hR = 0 := by
  letI := hR.quotientDensity_isProbabilityMeasure hR.timeWeight
  exact timeDistortionLoss_self _ (continuous_quotientTime3 hR.timeWeight).measurable

theorem geometricDistortion3_le_of_transport {rho sigma : LorentzPoint3 → ℝ}
    (hR : InDensityClass3 rho) (hS : InDensityClass3 sigma)
    {f : TimeProfileSpace3 hR.timeWeight → TimeProfileSpace3 hS.timeWeight}
    (hf : MeasurePreserving f (quotientDensityMeasure3 hR.timeWeight rho)
      (quotientDensityMeasure3 hS.timeWeight sigma)) {delta : ℝ} (hd : 0 ≤ delta)
    (hb : ∀ x y, |quotientTime3 hR.timeWeight x y - quotientTime3 hS.timeWeight (f x) (f y)| ≤ delta) :
    geometricDistortion3 hR hS ≤ delta := by
  letI := hR.quotientDensity_isProbabilityMeasure hR.timeWeight
  letI := hS.quotientDensity_isProbabilityMeasure hS.timeWeight
  exact timeDistortionLoss_le_of_transport
    (tx := quotientTime3 hR.timeWeight) (ty := quotientTime3 hS.timeWeight)
    hf (continuous_quotientTime3 hR.timeWeight).measurable
    (continuous_quotientTime3 hS.timeWeight).measurable hd hb

theorem geometricDistortion3_eq_zero_of_isometry {rho sigma : LorentzPoint3 → ℝ}
    (hR : InDensityClass3 rho) (hS : InDensityClass3 sigma)
    {f : TimeProfileSpace3 hR.timeWeight → TimeProfileSpace3 hS.timeWeight}
    (hf : MeasurePreserving f (quotientDensityMeasure3 hR.timeWeight rho)
      (quotientDensityMeasure3 hS.timeWeight sigma))
    (ht : ∀ x y, quotientTime3 hR.timeWeight x y = quotientTime3 hS.timeWeight (f x) (f y)) :
    geometricDistortion3 hR hS = 0 := by
  letI := hR.quotientDensity_isProbabilityMeasure hR.timeWeight
  letI := hS.quotientDensity_isProbabilityMeasure hS.timeWeight
  exact timeDistortionLoss_eq_zero_of_isometry hf (continuous_quotientTime3 hR.timeWeight).measurable
    (continuous_quotientTime3 hS.timeWeight).measurable ht

#print axioms geometricDistortion3_nonneg
#print axioms geometricDistortion3_le_one
#print axioms geometricDistortion3_symm
#print axioms geometricDistortion3_self
#print axioms geometricDistortion3_le_of_transport
#print axioms geometricDistortion3_eq_zero_of_isometry

end
end QuantyraNullCone
