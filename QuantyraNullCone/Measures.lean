import QuantyraNullCone.Model
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LocallyIntegrable

namespace QuantyraNullCone

open MeasureTheory

theorem diamond_isCompact : IsCompact diamond :=
  isCompact_Icc.prod isCompact_Icc

theorem diamond_measurableSet : MeasurableSet diamond :=
  diamond_isCompact.measurableSet

theorem InDensityClass.integrable {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) : Integrable rho diamondVolume := by
  exact h.continuousOn.integrableOn_compact diamond_isCompact

theorem InDensityClass.integral_eq_one {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) : (∫ p, rho p ∂diamondVolume) = 1 := by
  have hInt : IntegrableOn rho
      ((Set.Icc (0 : ℝ) 1) ×ˢ (Set.Icc (0 : ℝ) 1))
      ((volume : Measure ℝ).prod volume) := h.integrable
  change (∫ p in ((Set.Icc (0 : ℝ) 1) ×ˢ (Set.Icc (0 : ℝ) 1)),
    rho p ∂(volume : Measure ℝ).prod volume) = 1
  rw [setIntegral_prod rho hInt]
  have hInner : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      (∫ v in Set.Icc (0 : ℝ) 1, rho (u, v)) = 1 := by
    intro u hu
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact h.marginalU u hu
  calc
    (∫ u in Set.Icc (0 : ℝ) 1, ∫ v in Set.Icc (0 : ℝ) 1, rho (u, v))
        = ∫ _ in Set.Icc (0 : ℝ) 1, (1 : ℝ) :=
      setIntegral_congr_fun measurableSet_Icc hInner
    _ = 1 := by simp

theorem InDensityClass.densityMeasure_univ {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) : densityMeasure rho Set.univ = 1 := by
  have hNonneg : 0 ≤ᵐ[diamondVolume] rho := by
    exact (ae_restrict_mem diamond_measurableSet).mono fun p hp =>
      le_trans (by norm_num : (0 : ℝ) ≤ 1 / 2) (h.bounds p hp).1
  rw [densityMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal h.integrable hNonneg,
    h.integral_eq_one, ENNReal.ofReal_one]

theorem InDensityClass.isProbabilityMeasure {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) : IsProbabilityMeasure (densityMeasure rho) :=
  ⟨h.densityMeasure_univ⟩

theorem InDensityClass.sample_isProbabilityMeasure {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) (n : ℕ) : IsProbabilityMeasure (sampleMeasure rho n) := by
  letI : IsProbabilityMeasure (densityMeasure rho) := h.isProbabilityMeasure
  unfold sampleMeasure
  infer_instance

theorem InDensityClass.orderLaw_isProbabilityMeasure {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) (n : ℕ) : IsProbabilityMeasure (orderLaw rho n) := by
  letI : IsProbabilityMeasure (sampleMeasure rho n) := h.sample_isProbabilityMeasure n
  exact Measure.isProbabilityMeasure_map (sampledOrder_measurable n).aemeasurable

#print axioms InDensityClass.densityMeasure_univ
#print axioms InDensityClass.orderLaw_isProbabilityMeasure

end QuantyraNullCone
