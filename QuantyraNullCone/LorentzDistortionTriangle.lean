import QuantyraNullCone.TimeDistortionTriangle
import QuantyraNullCone.LorentzDistortion

/-! Triangle inequality on the original normalized 2+1 density class and its time-profile quotients. -/

namespace QuantyraNullCone
open MeasureTheory
noncomputable section

theorem geometricDistortion3_triangle {rho sigma omega : LorentzPoint3 → ℝ}
    (hR : InDensityClass3 rho) (hS : InDensityClass3 sigma) (hT : InDensityClass3 omega) :
    geometricDistortion3 hR hT ≤ geometricDistortion3 hR hS + geometricDistortion3 hS hT := by
  letI := hR.quotientDensity_isProbabilityMeasure hR.timeWeight
  letI := hS.quotientDensity_isProbabilityMeasure hS.timeWeight
  letI := hT.quotientDensity_isProbabilityMeasure hT.timeWeight
  exact timeDistortionLoss_triangle _ _ _ (continuous_quotientTime3 hR.timeWeight).measurable
    (continuous_quotientTime3 hS.timeWeight).measurable (continuous_quotientTime3 hT.timeWeight).measurable

/-- Changing one input changes its distortion to a fixed input by at most the intervening distortion. -/
theorem geometricDistortion3_reverse_triangle {rho sigma omega : LorentzPoint3 → ℝ}
    (hR : InDensityClass3 rho) (hS : InDensityClass3 sigma) (hT : InDensityClass3 omega) :
    |geometricDistortion3 hR hT - geometricDistortion3 hS hT| ≤ geometricDistortion3 hR hS := by
  apply abs_le.mpr
  have h1 := geometricDistortion3_triangle hR hS hT
  have h2 := geometricDistortion3_triangle hS hR hT
  rw [geometricDistortion3_symm hS hR] at h2
  constructor <;> linarith

#print axioms geometricDistortion3_triangle
#print axioms geometricDistortion3_reverse_triangle

end
end QuantyraNullCone
