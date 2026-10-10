import QuantyraNullCone.ThinningGenerating

namespace QuantyraNullCone

open MeasureTheory

theorem poisson_retained_product_lintegral {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (kappa : NNReal)
    {pi : Ω → ℝ} (hpi : Measurable pi) (hInt : Integrable pi mu)
    (hbounds : ∀ x, pi x ∈ Set.Icc 0 1) (hZ : 0 < ∫ x, pi x ∂mu)
    (fallback : Ω) {f : Ω → ℝ} (hf : Measurable f)
    (hunit : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) :
    (∫⁻ z, ENNReal.ofReal (mixedRetainedObservable pi fallback (retainedSampleProduct f) z)
      ∂randomGeneratedLaw mu (ProbabilityTheory.poissonMeasure kappa)) =
        ENNReal.ofReal (Real.exp ((retainedPoissonRate kappa mu pi : ℝ) *
          ((∫ x, f x ∂retainedMeasure mu pi)-1))) := by
  letI := retained_probability_of_channel mu hpi hInt hbounds hZ
  have hF := retained_sample_product_measurable hf
  have hObs := mixed_retained_observable_measurable hpi fallback (retainedSampleProduct f) hF
  rw [← lintegral_map ENNReal.measurable_ofReal hObs,
    poisson_retained_observable_law mu kappa hpi hInt hbounds hZ fallback
      (retainedSampleProduct f) hF, lintegral_sum_measure]
  simp only [lintegral_smul_measure, smul_eq_mul]
  have hterm (n : ℕ) :
      (∫⁻ y, ENNReal.ofReal y ∂(Measure.pi (fun _ : Fin n => retainedMeasure mu pi)).map
        (retainedSampleProduct f n)) = ENNReal.ofReal ((∫ x, f x ∂retainedMeasure mu pi)^n) := by
    rw [lintegral_map ENNReal.measurable_ofReal (hF n),
      ← ofReal_integral_eq_lintegral_ofReal
        (thinning_unit_integrable _ (hF n) (retained_sample_product_unit hunit n))
        (ae_of_all _ (fun s => (retained_sample_product_unit hunit n s).1)),
      retained_sample_product_integral]
  simp_rw [hterm]
  exact poisson_power_series _ (integral_nonneg (fun x => (hunit x).1))

theorem poisson_retained_product_integral {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (kappa : NNReal)
    {pi : Ω → ℝ} (hpi : Measurable pi) (hInt : Integrable pi mu)
    (hbounds : ∀ x, pi x ∈ Set.Icc 0 1) (hZ : 0 < ∫ x, pi x ∂mu)
    (fallback : Ω) {f : Ω → ℝ} (hf : Measurable f)
    (hunit : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) :
    (∫ z, mixedRetainedObservable pi fallback (retainedSampleProduct f) z
      ∂randomGeneratedLaw mu (ProbabilityTheory.poissonMeasure kappa)) =
        Real.exp ((retainedPoissonRate kappa mu pi : ℝ) *
          ((∫ x, f x ∂retainedMeasure mu pi)-1)) := by
  have hObs := mixed_retained_observable_measurable hpi fallback (retainedSampleProduct f)
    (retained_sample_product_measurable hf)
  have hunitObs : ∀ z, mixedRetainedObservable pi fallback (retainedSampleProduct f) z ∈
      Set.Icc (0 : ℝ) 1 := fun z => retained_sample_product_unit hunit _ _
  have h := poisson_retained_product_lintegral mu kappa hpi hInt hbounds hZ fallback hf hunit
  rw [← ofReal_integral_eq_lintegral_ofReal (thinning_unit_integrable _ hObs hunitObs)
    (ae_of_all _ (fun z => (hunitObs z).1))] at h
  have hi : 0 ≤ ∫ z, mixedRetainedObservable pi fallback (retainedSampleProduct f) z
      ∂randomGeneratedLaw mu (ProbabilityTheory.poissonMeasure kappa) :=
    integral_nonneg (fun z => (hunitObs z).1)
  simpa only [ENNReal.toReal_ofReal hi, ENNReal.toReal_ofReal (Real.exp_pos _).le] using
    congrArg ENNReal.toReal h

theorem poisson_retained_product_intensity {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (kappa : NNReal)
    {pi : Ω → ℝ} (hpi : Measurable pi) (hInt : Integrable pi mu)
    (hbounds : ∀ x, pi x ∈ Set.Icc 0 1) (hZ : 0 < ∫ x, pi x ∂mu)
    (fallback : Ω) {f : Ω → ℝ} (hf : Measurable f)
    (hunit : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) :
    (∫ z, mixedRetainedObservable pi fallback (retainedSampleProduct f) z
      ∂randomGeneratedLaw mu (ProbabilityTheory.poissonMeasure kappa)) =
        Real.exp ((kappa : ℝ) * ∫ x, pi x * (f x-1) ∂mu) := by
  have hprod : Integrable (fun x => pi x * f x) mu :=
    hInt.mul_bdd hf.aestronglyMeasurable (ae_of_all _ (fun x => by
      simpa [Real.norm_eq_abs, abs_of_nonneg (hunit x).1] using (hunit x).2))
  have hint : (∫ x, pi x * (f x-1) ∂mu) = (∫ x, pi x * f x ∂mu) - ∫ x, pi x ∂mu := by
    simp_rw [mul_sub, mul_one]
    exact integral_sub hprod hInt
  rw [poisson_retained_product_integral mu kappa hpi hInt hbounds hZ fallback hf hunit,
    retained_integral_identity mu hpi (fun x => (hbounds x).1) hZ, hint]
  simp only [retainedPoissonRate, NNReal.coe_mul, Real.coe_toNNReal _ hZ.le]
  congr 1
  field_simp [ne_of_gt hZ]

/-- The Laplace functional of the actual thinned Poisson experiment, including multiplicity.
The nonnegative measurable test function may be unbounded. -/
theorem poisson_retained_laplace_functional {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (kappa : NNReal)
    {pi : Ω → ℝ} (hpi : Measurable pi) (hInt : Integrable pi mu)
    (hbounds : ∀ x, pi x ∈ Set.Icc 0 1) (hZ : 0 < ∫ x, pi x ∂mu)
    (fallback : Ω) {h : Ω → ℝ} (hh : Measurable h) (hnonneg : ∀ x, 0 ≤ h x) :
    (∫ z, Real.exp (-∑ i : Fin (mixedRetainedCount pi z),
      h (mixedRetainedView pi fallback (mixedRetainedCount pi z) z i))
      ∂randomGeneratedLaw mu (ProbabilityTheory.poissonMeasure kappa)) =
        Real.exp ((kappa : ℝ) * ∫ x, pi x * (Real.exp (-h x)-1) ∂mu) := by
  have hf : Measurable (fun x => Real.exp (-h x)) := hh.neg.exp
  have hu : ∀ x, Real.exp (-h x) ∈ Set.Icc (0 : ℝ) 1 := fun x =>
    ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hnonneg x))⟩
  have heq : (fun z : ℕ × (ℕ → Ω × ℝ) => Real.exp (-∑ i : Fin (mixedRetainedCount pi z),
      h (mixedRetainedView pi fallback (mixedRetainedCount pi z) z i))) =
      mixedRetainedObservable pi fallback (retainedSampleProduct (fun x => Real.exp (-h x))) := by
    funext z
    dsimp only [mixedRetainedObservable, retainedSampleProduct]
    rw [← Real.exp_sum, Finset.sum_neg_distrib]
  rw [heq]
  exact poisson_retained_product_intensity mu kappa hpi hInt hbounds hZ fallback hf hu

end QuantyraNullCone
