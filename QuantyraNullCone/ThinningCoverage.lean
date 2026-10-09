import QuantyraNullCone.ThinningCount

namespace QuantyraNullCone

open MeasureTheory

noncomputable def generatedMarkedCode {Ω : Type*} {N : ℕ} (pi : Ω → ℝ)
    (fallback : Ω) (n : ℕ) (C : Ω → Ω → Prop) (p q : Ω)
    (sample : Fin N → Ω × ℝ) : Fin n → Bool :=
  markedIntervalCode C p q (retainedOrderedView pi fallback n sample)

theorem generated_marked_code_measurable {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    {pi : Ω → ℝ} (hpi : Measurable pi) (fallback : Ω) (n : ℕ)
    (C : Ω → Ω → Prop) (p q : Ω) (hS : MeasurableSet (markedIntervalSet C p q)) :
    Measurable (@generatedMarkedCode Ω N pi fallback n C p q) :=
  (marked_interval_code_measurable C p q hS).comp
    (retained_ordered_view_measurable hpi fallback n)

theorem generated_retained_marked_law {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] {pi : Ω → ℝ}
    (hpi : Measurable pi) (hInt : Integrable pi mu)
    (hbounds : ∀ x, pi x ∈ Set.Icc 0 1) (hZ : 0 < ∫ x, pi x ∂mu)
    (N n : ℕ) (fallback : Ω)
    (hc : (Measure.pi (fun _ : Fin N => mu.prod uniform01Measure))
      (retainedCountEvent pi N n) ≠ 0)
    (C : Ω → Ω → Prop) (p q : Ω) (hS : MeasurableSet (markedIntervalSet C p q)) :
    (ProbabilityTheory.cond (Measure.pi (fun _ : Fin N => mu.prod uniform01Measure))
      (retainedCountEvent pi N n)).map (generatedMarkedCode pi fallback n C p q) =
      markedIntervalLaw (retainedMeasure mu pi) n C p q := by
  change (ProbabilityTheory.cond (Measure.pi (fun _ : Fin N => mu.prod uniform01Measure))
    (retainedCountEvent pi N n)).map
      (markedIntervalCode C p q ∘ retainedOrderedView pi fallback n) = _
  rw [← Measure.map_map (marked_interval_code_measurable C p q hS)
    (retained_ordered_view_measurable hpi fallback n),
    retained_count_conditional_law mu hpi hInt hbounds hZ N n fallback hc]
  rfl

/-- Physical-volume coverage for actually generated and independently detected
events, conditional only on their positive-probability retained count. -/
theorem generated_retained_binomial_coverage {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] {pi : Ω → ℝ}
    (hpi : Measurable pi) (hInt : Integrable pi mu) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1)
    (hbounds : ∀ x, a ≤ pi x ∧ pi x ≤ b) (N n : ℕ) (fallback : Ω)
    (hc : (Measure.pi (fun _ : Fin N => mu.prod uniform01Measure))
      (retainedCountEvent pi N n) ≠ 0)
    (C : Ω → Ω → Prop) (p q : Ω) (hS : MeasurableSet (markedIntervalSet C p q))
    {delta : ℚ} (hd : 0 ≤ delta) (L U : Fin (n+1) → ℚ)
    (hvalid : BinomialReportValid n delta L U) :
    (ProbabilityTheory.cond (Measure.pi (fun _ : Fin N => mu.prod uniform01Measure))
      (retainedCountEvent pi N n)).real {sample |
        ¬ (retentionLower (b/a)
            (L (boundedBitCount (generatedMarkedCode pi fallback n C p q sample)) : ℝ) ≤
              mu.real (markedIntervalSet C p q) ∧
          mu.real (markedIntervalSet C p q) ≤ retentionUpper (b/a)
            (U (boundedBitCount (generatedMarkedCode pi fallback n C p q sample)) : ℝ))} ≤
      (delta : ℝ) := by
  have hunit : ∀ x, pi x ∈ Set.Icc 0 1 :=
    fun x => ⟨ha.le.trans (hbounds x).1, (hbounds x).2.trans hb⟩
  have hZ := retention_total_positive mu hInt ha hbounds
  have h := retained_binomial_report_coverage mu hInt ha hab hbounds n C p q hS hd L U hvalid
  rw [← generated_retained_marked_law mu hpi hInt hunit hZ N n fallback hc C p q hS,
    map_measureReal_apply (generated_marked_code_measurable hpi fallback n C p q hS)
      (Set.to_countable _ |>.measurableSet)] at h
  exact h

theorem InDensityClass.generated_retained_binomial_coverage {rho : DiamondPoint → ℝ}
    (hK : InDensityClass rho) {pi : DiamondPoint → ℝ}
    (hpi : Measurable pi) (hInt : Integrable pi (densityMeasure rho)) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1)
    (hbounds : ∀ x, a ≤ pi x ∧ pi x ≤ b) (N n : ℕ) (p q : DiamondPoint)
    (hc : (Measure.pi (fun _ : Fin N => (densityMeasure rho).prod uniform01Measure))
      (retainedCountEvent pi N n) ≠ 0)
    {delta : ℚ} (hd : 0 ≤ delta) (L U : Fin (n+1) → ℚ)
    (hcheck : binomialReportCheck n delta L U = true) :
    (ProbabilityTheory.cond
      (Measure.pi (fun _ : Fin N => (densityMeasure rho).prod uniform01Measure))
      (retainedCountEvent pi N n)).real {sample |
        ¬ (retentionLower (b/a)
            (L (boundedBitCount (generatedMarkedCode pi p n nullChronology p q sample)) : ℝ) ≤
              (densityMeasure rho).real ((Set.Ioo p.1 q.1).prod (Set.Ioo p.2 q.2)) ∧
          (densityMeasure rho).real ((Set.Ioo p.1 q.1).prod (Set.Ioo p.2 q.2)) ≤ retentionUpper (b/a)
            (U (boundedBitCount (generatedMarkedCode pi p n nullChronology p q sample)) : ℝ))} ≤
      (delta : ℝ) := by
  letI := hK.isProbabilityMeasure
  have h := QuantyraNullCone.generated_retained_binomial_coverage
    (densityMeasure rho) hpi hInt ha hab hb hbounds
    N n p hc nullChronology p q (null_interval_measurable p q) hd L U
      (binomial_report_check_sound hcheck)
  simpa only [null_interval_rectangle] using h

end QuantyraNullCone
