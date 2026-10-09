import QuantyraNullCone.ThinningStream

namespace QuantyraNullCone

open MeasureTheory

noncomputable def randomGeneratedLaw {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (q : Measure ℕ) : Measure (ℕ × (ℕ → Ω × ℝ)) :=
  q.prod (generatedStreamLaw mu)

instance randomGeneratedLaw_probability {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (q : Measure ℕ) [IsProbabilityMeasure q] :
    IsProbabilityMeasure (randomGeneratedLaw mu q) :=
  inferInstanceAs (IsProbabilityMeasure (q.prod (generatedStreamLaw mu)))

noncomputable def mixedRetainedCount {Ω : Type*} (pi : Ω → ℝ)
    (z : ℕ × (ℕ → Ω × ℝ)) : ℕ := streamRetainedCount pi z.1 z.2

noncomputable def mixedRetainedView {Ω : Type*} (pi : Ω → ℝ) (fallback : Ω) (n : ℕ)
    (z : ℕ × (ℕ → Ω × ℝ)) : Fin n → Ω :=
  retainedOrderedView pi fallback n (finitePrefix z.1 z.2)

theorem mixed_retained_count_measurable {Ω : Type*} [MeasurableSpace Ω]
    {pi : Ω → ℝ} (hpi : Measurable pi) : Measurable (mixedRetainedCount pi) :=
  measurable_from_prod_countable_right (stream_retained_count_measurable hpi)

theorem mixed_retained_view_measurable {Ω : Type*} [MeasurableSpace Ω]
    {pi : Ω → ℝ} (hpi : Measurable pi) (fallback : Ω) (n : ℕ) :
    Measurable (mixedRetainedView pi fallback n) :=
  measurable_from_prod_countable_right (fun N =>
    (retained_ordered_view_measurable hpi fallback n).comp (finite_prefix_measurable N))

theorem mixed_retained_submeasure_series {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (q : Measure ℕ)
    {pi : Ω → ℝ} (hpi : Measurable pi) (hInt : Integrable pi mu)
    (hbounds : ∀ x, pi x ∈ Set.Icc 0 1) (hZ : 0 < ∫ x, pi x ∂mu)
    (n : ℕ) (fallback : Ω) :
    ((randomGeneratedLaw mu q).restrict {z | mixedRetainedCount pi z = n}).map
        (mixedRetainedView pi fallback n) =
      (∑' N, q {N} * (Measure.pi (fun _ : Fin N => mu.prod uniform01Measure))
        (retainedCountEvent pi N n)) • Measure.pi (fun _ : Fin n => retainedMeasure mu pi) := by
  rw [randomGeneratedLaw]
  change ((q.prod (generatedStreamLaw mu)).restrict
    {z | z.2 ∈ {sample | streamRetainedCount pi z.1 sample = n}}).map
      (fun z => (retainedOrderedView pi fallback n ∘ finitePrefix z.1) z.2) = _
  rw [nat_product_restriction_map q (generatedStreamLaw mu)
    (fun N => {sample | streamRetainedCount pi N sample = n})
    (fun N => (measurableSet_singleton n).preimage (stream_retained_count_measurable hpi N))
    (fun N => retainedOrderedView pi fallback n ∘ finitePrefix N)
    (fun N => (retained_ordered_view_measurable hpi fallback n).comp (finite_prefix_measurable N))]
  simp_rw [stream_retained_submeasure_law mu hpi hInt hbounds hZ, smul_smul]
  ext T hT
  simp only [Measure.sum_apply _ hT, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.tsum_mul_right

theorem mixed_retained_count_mass {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (q : Measure ℕ)
    {pi : Ω → ℝ} (hpi : Measurable pi) (hInt : Integrable pi mu)
    (hbounds : ∀ x, pi x ∈ Set.Icc 0 1) (hZ : 0 < ∫ x, pi x ∂mu) (n : ℕ) (fallback : Ω) :
    (randomGeneratedLaw mu q) {z | mixedRetainedCount pi z = n} =
      ∑' N, q {N} * (Measure.pi (fun _ : Fin N => mu.prod uniform01Measure))
        (retainedCountEvent pi N n) := by
  letI := retained_probability_of_channel mu hpi hInt hbounds hZ
  have h := congrArg (fun m : Measure (Fin n → Ω) => m Set.univ)
    (mixed_retained_submeasure_series mu q hpi hInt hbounds hZ n fallback)
  simpa [Measure.map_apply (mixed_retained_view_measurable hpi fallback n)] using h

theorem mixed_retained_conditional_law {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (q : Measure ℕ) [IsProbabilityMeasure q]
    {pi : Ω → ℝ} (hpi : Measurable pi) (hInt : Integrable pi mu)
    (hbounds : ∀ x, pi x ∈ Set.Icc 0 1) (hZ : 0 < ∫ x, pi x ∂mu)
    (n : ℕ) (fallback : Ω)
    (hc : (randomGeneratedLaw mu q) {z | mixedRetainedCount pi z = n} ≠ 0) :
    (ProbabilityTheory.cond (randomGeneratedLaw mu q) {z | mixedRetainedCount pi z = n}).map
      (mixedRetainedView pi fallback n) = Measure.pi (fun _ : Fin n => retainedMeasure mu pi) := by
  rw [ProbabilityTheory.cond, Measure.map_smul,
    mixed_retained_submeasure_series mu q hpi hInt hbounds hZ,
    ← mixed_retained_count_mass mu q hpi hInt hbounds hZ n fallback, smul_smul,
    ENNReal.inv_mul_cancel hc (measure_ne_top _ _), one_smul]

end QuantyraNullCone
