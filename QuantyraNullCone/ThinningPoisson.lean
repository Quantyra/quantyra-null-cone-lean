import QuantyraNullCone.ThinningPoissonMass

namespace QuantyraNullCone

open MeasureTheory

noncomputable def retainedPoissonRate {Ω : Type*} [MeasurableSpace Ω]
    (kappa : NNReal) (mu : Measure Ω) (pi : Ω → ℝ) : NNReal :=
  kappa * Real.toNNReal (∫ x, pi x ∂mu)

theorem poisson_retained_submeasure_law {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (kappa : NNReal)
    {pi : Ω → ℝ} (hpi : Measurable pi) (hInt : Integrable pi mu)
    (hbounds : ∀ x, pi x ∈ Set.Icc 0 1) (hZ : 0 < ∫ x, pi x ∂mu)
    (n : ℕ) (fallback : Ω) :
    ((randomGeneratedLaw mu (ProbabilityTheory.poissonMeasure kappa)).restrict
        {z | mixedRetainedCount pi z = n}).map (mixedRetainedView pi fallback n) =
      (ProbabilityTheory.poissonMeasure (retainedPoissonRate kappa mu pi)) {n} •
        Measure.pi (fun _ : Fin n => retainedMeasure mu pi) := by
  rw [mixed_retained_submeasure_series mu _ hpi hInt hbounds hZ]
  simp_rw [finite_retained_count_mass mu hpi hInt hbounds]
  rw [poisson_binomial_series kappa (retention_mean_unit mu hInt hbounds),
    ProbabilityTheory.poissonMeasure_singleton]
  simp only [retainedPoissonRate, NNReal.coe_mul, Real.coe_toNNReal _ hZ.le]

theorem poisson_retained_count_mass {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (kappa : NNReal)
    {pi : Ω → ℝ} (hpi : Measurable pi) (hInt : Integrable pi mu)
    (hbounds : ∀ x, pi x ∈ Set.Icc 0 1) (hZ : 0 < ∫ x, pi x ∂mu)
    (n : ℕ) (fallback : Ω) :
    (randomGeneratedLaw mu (ProbabilityTheory.poissonMeasure kappa))
      {z | mixedRetainedCount pi z = n} =
        (ProbabilityTheory.poissonMeasure (retainedPoissonRate kappa mu pi)) {n} := by
  letI := retained_probability_of_channel mu hpi hInt hbounds hZ
  have h := congrArg (fun m : Measure (Fin n → Ω) => m Set.univ)
    (poisson_retained_submeasure_law mu kappa hpi hInt hbounds hZ n fallback)
  simpa [Measure.map_apply (mixed_retained_view_measurable hpi fallback n)] using h

theorem poisson_retained_count_law {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (kappa : NNReal)
    {pi : Ω → ℝ} (hpi : Measurable pi) (hInt : Integrable pi mu)
    (hbounds : ∀ x, pi x ∈ Set.Icc 0 1) (hZ : 0 < ∫ x, pi x ∂mu) (fallback : Ω) :
    (randomGeneratedLaw mu (ProbabilityTheory.poissonMeasure kappa)).map (mixedRetainedCount pi) =
      ProbabilityTheory.poissonMeasure (retainedPoissonRate kappa mu pi) := by
  apply Measure.ext_of_singleton
  intro n
  rw [Measure.map_apply (mixed_retained_count_measurable hpi) (measurableSet_singleton n)]
  exact poisson_retained_count_mass mu kappa hpi hInt hbounds hZ n fallback

end QuantyraNullCone
