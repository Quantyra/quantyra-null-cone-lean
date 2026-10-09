import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.IntegrableOn

namespace QuantyraNullCone

open MeasureTheory ProbabilityTheory

/-- The local exponential remainder suffices for the selected fixed-mass tail
bound; no normal approximation or independence of recovered points is used. -/
theorem exp_remainder_le_square {t : ℝ} (ht : |t| ≤ 1) :
    Real.exp t - 1 - t ≤ t ^ 2 := by
  have hb := Real.norm_exp_sub_one_sub_id_le (by simpa only [Real.norm_eq_abs] using ht)
  simp only [Real.norm_eq_abs, sq_abs] at hb
  exact (le_abs_self _).trans hb

theorem centered_indicator_exp_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {S : Set Ω} (hS : MeasurableSet S)
    (p t : ℝ) : Integrable (fun q =>
      Real.exp (t * (S.indicator (fun _ => (1 : ℝ)) q - p))) μ := by
  classical
  have hEq : (fun q => Real.exp (t * (S.indicator (fun _ => (1 : ℝ)) q - p))) =
      S.piecewise (fun _ => Real.exp (t * (1 - p))) (fun _ => Real.exp (t * (0 - p))) := by
    funext q
    by_cases hq : q ∈ S <;> simp [hq]
  rw [hEq]
  exact Integrable.piecewise hS (integrable_const _) (integrable_const _)

theorem indicator_mgf {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {S : Set Ω}
    (hS : MeasurableSet S) (t : ℝ) :
    mgf (S.indicator (fun _ => (1 : ℝ))) μ t =
      1 + μ.real S * (Real.exp t - 1) := by
  classical
  have hEq : (fun q => Real.exp (t * S.indicator (fun _ => (1 : ℝ)) q)) =
      (fun q => 1 + S.indicator (fun _ => Real.exp t - 1) q) := by
    funext q
    by_cases hq : q ∈ S <;> simp [hq]
  rw [mgf, hEq, integral_add (integrable_const _) ((integrable_const _).indicator hS)]
  simp [integral_indicator hS, Measure.real]

theorem centered_indicator_mgf_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {S : Set Ω}
    (hS : MeasurableSet S) {t : ℝ} (ht : |t| ≤ 1) :
    mgf (fun q => S.indicator (fun _ => (1 : ℝ)) q - μ.real S) μ t ≤
      Real.exp (μ.real S * t ^ 2) := by
  let p := μ.real S
  have hp : 0 ≤ p := measureReal_nonneg
  have hMGF : mgf (fun q => S.indicator (fun _ => (1 : ℝ)) q - p) μ t =
      (1 + p * (Real.exp t - 1)) * Real.exp (t * (-p)) := by
    simpa only [sub_eq_add_neg, indicator_mgf hS, p] using
      (mgf_add_const (X := S.indicator (fun _ => (1 : ℝ))) (μ := μ) (t := t) (-p))
  change mgf (fun q => S.indicator (fun _ => (1 : ℝ)) q - p) μ t ≤ _
  rw [hMGF]
  calc
    _ ≤ Real.exp (p * (Real.exp t - 1)) * Real.exp (t * (-p)) := by
      gcongr
      simpa only [add_comm] using Real.add_one_le_exp (p * (Real.exp t - 1))
    _ = Real.exp (p * (Real.exp t - 1 - t)) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (p * t ^ 2) := Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (exp_remainder_le_square ht) hp)

#print axioms exp_remainder_le_square
#print axioms centered_indicator_exp_integrable
#print axioms indicator_mgf
#print axioms centered_indicator_mgf_le

end QuantyraNullCone
