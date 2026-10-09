import QuantyraNullCone.ThinningFunctional

namespace QuantyraNullCone

open MeasureTheory

noncomputable def physicalReportFailure {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (R : ℝ) (n : ℕ) (C : Ω → Ω → Prop) (p q : Ω)
    (L U : Fin (n+1) → ℚ) (sample : Fin n → Ω) : Bool := by
  classical
  exact decide (¬ (retentionLower R (L (boundedBitCount (markedIntervalCode C p q sample)) : ℝ) ≤
      mu.real (markedIntervalSet C p q) ∧
    mu.real (markedIntervalSet C p q) ≤
      retentionUpper R (U (boundedBitCount (markedIntervalCode C p q sample)) : ℝ)))

theorem physical_report_failure_measurable {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (R : ℝ) (n : ℕ) (C : Ω → Ω → Prop) (p q : Ω)
    (hS : MeasurableSet (markedIntervalSet C p q)) (L U : Fin (n+1) → ℚ) :
    Measurable (physicalReportFailure mu R n C p q L U) := by
  classical
  let g : (Fin n → Bool) → Bool := fun code => decide (¬
    (retentionLower R (L (boundedBitCount code) : ℝ) ≤ mu.real (markedIntervalSet C p q) ∧
      mu.real (markedIntervalSet C p q) ≤ retentionUpper R (U (boundedBitCount code) : ℝ)))
  exact (measurable_of_countable g).comp (marked_interval_code_measurable C p q hS)

theorem retained_physical_report_failure_bound {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] {pi : Ω → ℝ}
    (hpi : Measurable pi) (hInt : Integrable pi mu) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1) (hbounds : ∀ x, a ≤ pi x ∧ pi x ≤ b)
    (n : ℕ) (C : Ω → Ω → Prop) (p q : Ω) (hS : MeasurableSet (markedIntervalSet C p q))
    {delta : ℚ} (hd : 0 ≤ delta) (L U : Fin (n+1) → ℚ)
    (hvalid : BinomialReportValid n delta L U) :
    ((Measure.pi (fun _ : Fin n => retainedMeasure mu pi)).map
      (physicalReportFailure mu (b/a) n C p q L U)) {true} ≤ ENNReal.ofReal (delta : ℝ) := by
  letI := retained_probability_of_channel mu hpi hInt
    (fun x => ⟨ha.le.trans (hbounds x).1, (hbounds x).2.trans hb⟩)
    (retention_total_positive mu hInt ha hbounds)
  letI : IsProbabilityMeasure (markedIntervalLaw (retainedMeasure mu pi) n C p q) :=
    Measure.isProbabilityMeasure_map (marked_interval_code_measurable C p q hS).aemeasurable
  have h := retained_binomial_report_coverage mu hInt ha hab hbounds n C p q hS hd L U hvalid
  have hmap : ((Measure.pi (fun _ : Fin n => retainedMeasure mu pi)).map
      (physicalReportFailure mu (b/a) n C p q L U)) {true} =
      (markedIntervalLaw (retainedMeasure mu pi) n C p q) {code | ¬
        (retentionLower (b/a) (L (boundedBitCount code) : ℝ) ≤ mu.real (markedIntervalSet C p q) ∧
          mu.real (markedIntervalSet C p q) ≤ retentionUpper (b/a) (U (boundedBitCount code) : ℝ))} := by
    rw [Measure.map_apply (physical_report_failure_measurable mu (b/a) n C p q hS L U)
      (measurableSet_singleton true), markedIntervalLaw,
      Measure.map_apply (marked_interval_code_measurable C p q hS) (Set.to_countable _ |>.measurableSet)]
    congr 1
    ext sample
    simp only [Set.mem_preimage, Set.mem_singleton_iff, physicalReportFailure,
      decide_eq_true_eq, Set.mem_setOf_eq]
  rw [hmap]
  have h' := ENNReal.ofReal_le_ofReal h
  rw [ofReal_measureReal (μ := markedIntervalLaw (retainedMeasure mu pi) n C p q)
    (measure_ne_top _ _)] at h'
  exact h'

/-- Coverage under an arbitrary independently generated count, without conditioning on the
retained count. Each count's actual report must pass its own exact contract. -/
theorem mixed_physical_report_coverage {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (Q : Measure ℕ) [IsProbabilityMeasure Q]
    {pi : Ω → ℝ} (hpi : Measurable pi) (hInt : Integrable pi mu) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1) (hbounds : ∀ x, a ≤ pi x ∧ pi x ≤ b)
    (fallback : Ω) (C : Ω → Ω → Prop) (p q : Ω) (hS : MeasurableSet (markedIntervalSet C p q))
    {delta : ℚ} (hd : 0 ≤ delta) (L U : (n : ℕ) → Fin (n+1) → ℚ)
    (hvalid : ∀ n, BinomialReportValid n delta (L n) (U n)) :
    (randomGeneratedLaw mu Q).real {z | mixedRetainedObservable pi fallback
      (fun n => physicalReportFailure mu (b/a) n C p q (L n) (U n)) z = true} ≤ (delta : ℝ) := by
  let F := fun n => physicalReportFailure mu (b/a) n C p q (L n) (U n)
  have hF : ∀ n, Measurable (F n) :=
    fun n => physical_report_failure_measurable mu (b/a) n C p q hS (L n) (U n)
  have h := mixed_retained_observable_bound mu Q hpi hInt
    (fun x => ⟨ha.le.trans (hbounds x).1, (hbounds x).2.trans hb⟩)
    (retention_total_positive mu hInt ha hbounds) fallback F hF (measurableSet_singleton true)
    (fun n => retained_physical_report_failure_bound mu hpi hInt ha hab hb hbounds
      n C p q hS hd (L n) (U n) (hvalid n))
  rw [Measure.map_apply (mixed_retained_observable_measurable hpi fallback F hF)
    (measurableSet_singleton true)] at h
  have hdR : (0 : ℝ) ≤ delta := by exact_mod_cast hd
  simpa only [ENNReal.toReal_ofReal hdR] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top h

theorem InDensityClass.mixed_physical_report_coverage {rho : DiamondPoint → ℝ}
    (hK : InDensityClass rho) (Q : Measure ℕ) [IsProbabilityMeasure Q]
    {pi : DiamondPoint → ℝ} (hpi : Measurable pi) (hInt : Integrable pi (densityMeasure rho))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1)
    (hbounds : ∀ x, a ≤ pi x ∧ pi x ≤ b) (p q : DiamondPoint)
    {delta : ℚ} (hd : 0 ≤ delta) (L U : (n : ℕ) → Fin (n+1) → ℚ)
    (hcheck : ∀ n, binomialReportCheck n delta (L n) (U n) = true) :
    (randomGeneratedLaw (densityMeasure rho) Q).real {z | mixedRetainedObservable pi p
      (fun n => physicalReportFailure (densityMeasure rho) (b/a) n nullChronology p q (L n) (U n)) z = true}
      ≤ (delta : ℝ) := by
  letI := hK.isProbabilityMeasure
  exact QuantyraNullCone.mixed_physical_report_coverage (densityMeasure rho) Q hpi hInt
    ha hab hb hbounds p nullChronology p q (null_interval_measurable p q) hd L U
      (fun n => binomial_report_check_sound (hcheck n))

end QuantyraNullCone
