import QuantyraNullCone.ThinningMixedCoverage
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace QuantyraNullCone

open MeasureTheory

theorem thinning_unit_integrable {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsFiniteMeasure mu] {f : Ω → ℝ} (hf : Measurable f)
    (hunit : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) : Integrable f mu := by
  apply (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
  exact ae_of_all _ (fun x => by simpa [Real.norm_eq_abs, abs_of_nonneg (hunit x).1] using (hunit x).2)

theorem retained_integral_identity {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) {pi : Ω → ℝ} (hpi : Measurable pi)
    (hpi0 : ∀ x, 0 ≤ pi x) (hZ : 0 < ∫ x, pi x ∂mu) (f : Ω → ℝ) :
    ∫ x, f x ∂retainedMeasure mu pi = (∫ x, pi x * f x ∂mu) / ∫ x, pi x ∂mu := by
  rw [retainedMeasure, integral_withDensity_eq_integral_toReal_smul
    (hpi.div_const _).ennreal_ofReal (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (div_nonneg (hpi0 _) hZ.le), smul_eq_mul,
    div_mul_eq_mul_div]
  exact integral_div _ _

theorem poisson_power_hasSum (kappa t : ℝ) :
    HasSum (fun n : ℕ => (Real.exp (-kappa) * kappa^n / n.factorial) * t^n)
      (Real.exp (kappa*(t-1))) := by
  convert (NormedSpace.expSeries_div_hasSum_exp (kappa*t)).mul_left (Real.exp (-kappa)) using 1
  · funext n
    rw [mul_pow]
    ring
  · rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add]
    congr 1
    ring

theorem poisson_power_series (kappa : NNReal) {t : ℝ} (ht : 0 ≤ t) :
    (∑' n : ℕ, (ProbabilityTheory.poissonMeasure kappa) {n} * ENNReal.ofReal (t^n)) =
      ENNReal.ofReal (Real.exp ((kappa : ℝ)*(t-1))) := by
  have hs := poisson_power_hasSum (kappa : ℝ) t
  have hn (n : ℕ) : 0 ≤ Real.exp (-(kappa : ℝ)) * (kappa : ℝ)^n / n.factorial := by
    positivity
  simp_rw [ProbabilityTheory.poissonMeasure_singleton, ← ENNReal.ofReal_mul (hn _)]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (hn n) (pow_nonneg ht n))
    hs.summable, hs.tsum_eq]

noncomputable def retainedSampleProduct {Ω : Type*} (f : Ω → ℝ) (n : ℕ)
    (sample : Fin n → Ω) : ℝ := ∏ i, f (sample i)

theorem retained_sample_product_measurable {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → ℝ} (hf : Measurable f) (n : ℕ) : Measurable (retainedSampleProduct f n) := by
  unfold retainedSampleProduct
  fun_prop

theorem retained_sample_product_unit {Ω : Type*} {f : Ω → ℝ}
    (hunit : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) (sample : Fin n → Ω) :
    retainedSampleProduct f n sample ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨Finset.prod_nonneg (fun i _ => (hunit (sample i)).1),
    Finset.prod_le_one (fun i _ => (hunit (sample i)).1) (fun i _ => (hunit (sample i)).2)⟩

theorem retained_sample_product_integral {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (f : Ω → ℝ) (n : ℕ) :
    ∫ sample, retainedSampleProduct f n sample ∂Measure.pi (fun _ : Fin n => mu) =
      (∫ x, f x ∂mu)^n := by
  simpa [retainedSampleProduct] using
    (integral_fintype_prod_eq_pow (ι := Fin n) (μ := mu) f)

end QuantyraNullCone
