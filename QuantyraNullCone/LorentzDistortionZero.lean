import QuantyraNullCone.TimeZeroAttainment
import QuantyraNullCone.LorentzDistortion

/-! Zero-distortion attainment for the original 2+1 density class. -/

namespace QuantyraNullCone
open MeasureTheory
noncomputable section

theorem geometricDistortion3_eq_zero_iff {rho sigma : LorentzPoint3 → ℝ}
    (hR : InDensityClass3 rho) (hS : InDensityClass3 sigma) :
    geometricDistortion3 hR hS = 0 ↔
      ∃ pi : Measure (TimeProfileSpace3 hR.timeWeight × TimeProfileSpace3 hS.timeWeight),
        IsZeroTimeCoupling (quotientDensityMeasure3 hR.timeWeight rho)
          (quotientDensityMeasure3 hS.timeWeight sigma)
          (quotientTime3 hR.timeWeight) (quotientTime3 hS.timeWeight) pi := by
  letI := hR.quotientDensity_isProbabilityMeasure hR.timeWeight
  letI := hS.quotientDensity_isProbabilityMeasure hS.timeWeight
  exact timeDistortionLoss_eq_zero_iff _ _ (continuous_quotientTime3 hR.timeWeight)
    (continuous_quotientTime3 hS.timeWeight)

#print axioms geometricDistortion3_eq_zero_iff

end
end QuantyraNullCone
