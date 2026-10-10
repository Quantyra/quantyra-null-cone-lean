import QuantyraNullCone.LorentzDistortionIsomorphy

/-! Zero geometric distortion preserves every law of the original finite order experiment. -/

namespace QuantyraNullCone
open MeasureTheory
noncomputable section

theorem orderLaw3_eq_of_time_isometry {rho sigma : LorentzPoint3 → ℝ}
    (hR : InDensityClass3 rho) (hS : InDensityClass3 sigma)
    {f : TimeProfileSpace3 hR.timeWeight → TimeProfileSpace3 hS.timeWeight}
    (hf : MeasurePreserving f (quotientDensityMeasure3 hR.timeWeight rho)
      (quotientDensityMeasure3 hS.timeWeight sigma))
    (ht : ∀ x y, quotientTime3 hR.timeWeight x y = quotientTime3 hS.timeWeight (f x) (f y))
    (n : ℕ) : orderLaw3 rho n = orderLaw3 sigma n := by
  classical
  letI := hR.quotientDensity_isProbabilityMeasure hR.timeWeight
  letI := hS.quotientDensity_isProbabilityMeasure hS.timeWeight
  letI : IsProbabilityMeasure ((quotientDensityMeasure3 hR.timeWeight rho).map f) :=
    Measure.isProbabilityMeasure_map hf.measurable.aemeasurable
  let F : (Fin n → TimeProfileSpace3 hR.timeWeight) → Fin n → TimeProfileSpace3 hS.timeWeight :=
    fun s i => f (s i)
  have hF : Measurable F := measurable_pi_lambda _ (fun i =>
    hf.measurable.comp (measurable_pi_apply i))
  have hm : (quotientSampleMeasure3 hR.timeWeight rho n).map F =
      quotientSampleMeasure3 hS.timeWeight sigma n := by
    unfold quotientSampleMeasure3
    dsimp [F]
    rw [Measure.pi_map_pi (fun _ => hf.measurable.aemeasurable)]
    simp_rw [hf.map_eq]
  rw [← hR.quotientOrderLaw_eq hR.timeWeight n, ← hS.quotientOrderLaw_eq hS.timeWeight n]
  unfold quotientOrderLaw3
  rw [← hm, Measure.map_map (measurable_quotientSampledOrder3 hS.timeWeight n) hF]
  have hc : quotientSampledOrder3 hS.timeWeight ∘ F =
      @quotientSampledOrder3 _ _ _ hR.timeWeight n := by
    funext s i j
    simp only [Function.comp_apply, F, quotientSampledOrder3, ← ht]
  rw [hc]

theorem geometricDistortion3_zero_orderLaw_eq {rho sigma : LorentzPoint3 → ℝ}
    (hR : InDensityClass3 rho) (hS : InDensityClass3 sigma)
    (hz : geometricDistortion3 hR hS = 0) (n : ℕ) : orderLaw3 rho n = orderLaw3 sigma n := by
  obtain ⟨e, he, ht⟩ := (geometricDistortion3_eq_zero_iff_homeomorph hR hS).mp hz
  exact orderLaw3_eq_of_time_isometry hR hS he ht n

theorem geometricDistortion3_zero_unlabeledOrderLaw_eq {rho sigma : LorentzPoint3 → ℝ}
    (hR : InDensityClass3 rho) (hS : InDensityClass3 sigma)
    (hz : geometricDistortion3 hR hS = 0) (n : ℕ) :
    unlabeledOrderLaw3 rho n = unlabeledOrderLaw3 sigma n := by
  unfold unlabeledOrderLaw3
  rw [geometricDistortion3_zero_orderLaw_eq hR hS hz n]

#print axioms orderLaw3_eq_of_time_isometry
#print axioms geometricDistortion3_zero_orderLaw_eq
#print axioms geometricDistortion3_zero_unlabeledOrderLaw_eq

end
end QuantyraNullCone
