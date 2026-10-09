import QuantyraNullCone.BinomialFixtures

namespace QuantyraNullCone

open MeasureTheory

def nullChronology (p q : DiamondPoint) : Prop := p.1 < q.1 ∧ p.2 < q.2

theorem null_interval_rectangle (p q : DiamondPoint) :
    markedIntervalSet nullChronology p q = (Set.Ioo p.1 q.1).prod (Set.Ioo p.2 q.2) := by
  ext x
  change ((p.1 < x.1 ∧ p.2 < x.2) ∧ x.1 < q.1 ∧ x.2 < q.2) ↔
    ((p.1 < x.1 ∧ x.1 < q.1) ∧ p.2 < x.2 ∧ x.2 < q.2)
  tauto

theorem null_interval_measurable (p q : DiamondPoint) :
    MeasurableSet (markedIntervalSet nullChronology p q) := by
  rw [null_interval_rectangle]
  exact measurableSet_Ioo.prod measurableSet_Ioo

theorem bit_count_relabel {n : ℕ} (code : Fin n → Bool) (e : Fin n ≃ Fin n) :
    bitCount (code ∘ e) = bitCount code := by
  unfold bitCount trueBits
  apply Finset.card_bij (fun i _ => e i)
  · intro i hi
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply] using hi
  · intro i hi j hj heq
    exact e.injective heq
  · intro j hj
    refine ⟨e.symm j, ?_, by simp⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply,
      Equiv.apply_symm_apply] using hj

theorem bounded_bit_count_relabel {n : ℕ} (code : Fin n → Bool) (e : Fin n ≃ Fin n) :
    boundedBitCount (code ∘ e) = boundedBitCount code :=
  Fin.ext (bit_count_relabel code e)

theorem marked_fraction_bit_count {n : ℕ} (code : Fin n → Bool) :
    markedFraction code = (bitCount code : ℝ)/n := by
  simp [markedFraction, bitCount, trueBits, Finset.sum_boole]

/-- Specialization to the original density class and actual null-coordinate chronology. -/
theorem InDensityClass.marked_binomial_coverage {rho : DiamondPoint → ℝ}
    (hK : InDensityClass rho) (n : ℕ) (p q : DiamondPoint) {delta : ℚ} (hd : 0 ≤ delta)
    (L U : Fin (n+1) → ℚ) (hcheck : binomialReportCheck n delta L U = true) :
    (markedIntervalLaw (densityMeasure rho) n nullChronology p q).real {code |
      ¬ ((L (boundedBitCount code) : ℝ) ≤ (densityMeasure rho).real
          ((Set.Ioo p.1 q.1).prod (Set.Ioo p.2 q.2)) ∧
        (densityMeasure rho).real ((Set.Ioo p.1 q.1).prod (Set.Ioo p.2 q.2)) ≤
          (U (boundedBitCount code) : ℝ))} ≤ (delta : ℝ) := by
  letI := hK.isProbabilityMeasure
  have h := marked_binomial_report_coverage (densityMeasure rho) n nullChronology p q
    (null_interval_measurable p q) hd L U (binomial_report_check_sound hcheck)
  simpa only [null_interval_rectangle] using h

theorem InDensityClass.retained_marked_binomial_coverage {rho : DiamondPoint → ℝ}
    (hK : InDensityClass rho) {pi : DiamondPoint → ℝ}
    (hpi : Integrable pi (densityMeasure rho)) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hbounds : ∀ x, a ≤ pi x ∧ pi x ≤ b) (n : ℕ) (p q : DiamondPoint)
    {delta : ℚ} (hd : 0 ≤ delta) (L U : Fin (n+1) → ℚ)
    (hcheck : binomialReportCheck n delta L U = true) :
    (markedIntervalLaw (retainedMeasure (densityMeasure rho) pi) n nullChronology p q).real
      {code | ¬ (retentionLower (b/a) (L (boundedBitCount code) : ℝ) ≤
          (densityMeasure rho).real ((Set.Ioo p.1 q.1).prod (Set.Ioo p.2 q.2)) ∧
        (densityMeasure rho).real ((Set.Ioo p.1 q.1).prod (Set.Ioo p.2 q.2)) ≤
          retentionUpper (b/a) (U (boundedBitCount code) : ℝ))} ≤ (delta : ℝ) := by
  letI := hK.isProbabilityMeasure
  have h := retained_binomial_report_coverage (densityMeasure rho) hpi ha hab hbounds n
    nullChronology p q (null_interval_measurable p q) hd L U (binomial_report_check_sound hcheck)
  simpa only [null_interval_rectangle] using h

end QuantyraNullCone
