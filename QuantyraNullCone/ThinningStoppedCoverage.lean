import QuantyraNullCone.ThinningStoppedLaw

namespace QuantyraNullCone

open MeasureTheory

theorem stopped_marked_interval_law {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] {pi : Ω → ℝ}
    (hpi : Measurable pi) (hInt : Integrable pi mu)
    (hbounds : ∀ x, pi x ∈ Set.Icc 0 1) (hZ : 0 < ∫ x, pi x ∂mu)
    (n : ℕ) (fallback : Ω) (C : Ω → Ω → Prop) (p q : Ω)
    (hS : MeasurableSet (markedIntervalSet C p q)) :
    (generatedStreamLaw mu).map (markedIntervalCode C p q ∘ stoppedRetainedView pi fallback n) =
      markedIntervalLaw (retainedMeasure mu pi) n C p q :=
  stopped_retained_observable_law mu hpi hInt hbounds hZ n fallback
    (marked_interval_code_measurable C p q hS)

/-- Fixed-retained-count report coverage under the actual rejection-sampling stream. -/
theorem stopped_physical_report_coverage {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] {pi : Ω → ℝ}
    (hpi : Measurable pi) (hInt : Integrable pi mu) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1) (hbounds : ∀ x, a ≤ pi x ∧ pi x ≤ b)
    (n : ℕ) (fallback : Ω) (C : Ω → Ω → Prop) (p q : Ω)
    (hS : MeasurableSet (markedIntervalSet C p q)) {delta : ℚ} (hd : 0 ≤ delta)
    (L U : Fin (n+1) → ℚ) (hvalid : BinomialReportValid n delta L U) :
    (generatedStreamLaw mu).real {sample | physicalReportFailure mu (b/a) n C p q L U
      (stoppedRetainedView pi fallback n sample) = true} ≤ (delta : ℝ) := by
  have hF := physical_report_failure_measurable mu (b/a) n C p q hS L U
  have h : ((generatedStreamLaw mu).map
      (physicalReportFailure mu (b/a) n C p q L U ∘ stoppedRetainedView pi fallback n)) {true} ≤
        ENNReal.ofReal (delta : ℝ) := by
    rw [stopped_retained_observable_law mu hpi hInt
      (fun x => ⟨ha.le.trans (hbounds x).1, (hbounds x).2.trans hb⟩)
      (retention_total_positive mu hInt ha hbounds) n fallback hF]
    exact retained_physical_report_failure_bound mu hpi hInt ha hab hb hbounds n C p q hS hd L U hvalid
  rw [Measure.map_apply (hF.comp (stopped_retained_view_measurable hpi fallback n))
    (measurableSet_singleton true)] at h
  have hdR : (0 : ℝ) ≤ delta := by exact_mod_cast hd
  simpa only [ENNReal.toReal_ofReal hdR] using ENNReal.toReal_mono ENNReal.ofReal_ne_top h

theorem InDensityClass.stopped_physical_report_coverage {rho : DiamondPoint → ℝ}
    (hK : InDensityClass rho) {pi : DiamondPoint → ℝ} (hpi : Measurable pi)
    (hInt : Integrable pi (densityMeasure rho)) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1) (hbounds : ∀ x, a ≤ pi x ∧ pi x ≤ b)
    (n : ℕ) (p q : DiamondPoint) {delta : ℚ} (hd : 0 ≤ delta)
    (L U : Fin (n+1) → ℚ) (hcheck : binomialReportCheck n delta L U = true) :
    (generatedStreamLaw (densityMeasure rho)).real {sample |
      physicalReportFailure (densityMeasure rho) (b/a) n nullChronology p q L U
        (stoppedRetainedView pi p n sample) = true} ≤ (delta : ℝ) := by
  letI := hK.isProbabilityMeasure
  exact QuantyraNullCone.stopped_physical_report_coverage (densityMeasure rho) hpi hInt
    ha hab hb hbounds n p nullChronology p q (null_interval_measurable p q) hd L U
      (binomial_report_check_sound hcheck)

end QuantyraNullCone
