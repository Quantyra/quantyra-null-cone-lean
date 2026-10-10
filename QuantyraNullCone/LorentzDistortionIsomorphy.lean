import QuantyraNullCone.TimeZeroIsomorphy
import QuantyraNullCone.LorentzDistortionZero

/-! The exact zero-isomorphy characterization on the original 2+1 time-profile quotients. -/

namespace QuantyraNullCone
open MeasureTheory
noncomputable section

theorem geometricDistortion3_eq_zero_iff_homeomorph {rho sigma : LorentzPoint3 → ℝ}
    (hR : InDensityClass3 rho) (hS : InDensityClass3 sigma) :
    geometricDistortion3 hR hS = 0 ↔
      ∃ e : TimeProfileSpace3 hR.timeWeight ≃ₜ TimeProfileSpace3 hS.timeWeight,
        MeasurePreserving e (quotientDensityMeasure3 hR.timeWeight rho)
          (quotientDensityMeasure3 hS.timeWeight sigma) ∧
        ∀ x y, quotientTime3 hR.timeWeight x y = quotientTime3 hS.timeWeight (e x) (e y) := by
  letI := hR.quotientDensity_isProbabilityMeasure hR.timeWeight
  letI := hS.quotientDensity_isProbabilityMeasure hS.timeWeight
  letI := hR.quotientDensity_isOpenPosMeasure hR.timeWeight
  letI := hS.quotientDensity_isOpenPosMeasure hS.timeWeight
  exact timeDistortionLoss_eq_zero_iff_homeomorph _ _ (continuous_quotientTime3 hR.timeWeight)
    (continuous_quotientTime3 hS.timeWeight) (quotientTime3_distinguishes hR.timeWeight)
    (quotientTime3_distinguishes hS.timeWeight)

#print axioms geometricDistortion3_eq_zero_iff_homeomorph

end
end QuantyraNullCone
