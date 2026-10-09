import QuantyraNullCone.BinomialObservation
import Mathlib.Data.Finset.Max

namespace QuantyraNullCone

open MeasureTheory

theorem finite_measure_event_sum {Alpha : Type*} [Fintype Alpha] [MeasurableSpace Alpha]
    [MeasurableSingletonClass Alpha] (mu : Measure Alpha) [IsFiniteMeasure mu] (S : Set Alpha)
    [DecidablePred (fun x => x ∈ S)] :
    mu.real S = ∑ x : Alpha, if x ∈ S then mu.real {x} else 0 := by
  classical
  let s := Finset.univ.filter (fun x : Alpha => x ∈ S)
  have hs : (s : Set Alpha) = S := by ext x; simp [s]
  calc
    _ = mu.real (s : Set Alpha) := by rw [hs]
    _ = ∑ x ∈ s, mu.real {x} := (sum_measureReal_singleton s).symm
    _ = _ := by simp [s, Finset.sum_filter]

noncomputable def binomialUpperTail (n : ℕ) (k : Fin (n+1)) (p : ℝ) : ℝ :=
  ∑ j : Fin (n+1), if k ≤ j then binomialMass n j p else 0

noncomputable def binomialLowerTail (n : ℕ) (k : Fin (n+1)) (p : ℝ) : ℝ :=
  ∑ j : Fin (n+1), if j ≤ k then binomialMass n j p else 0

theorem binomial_upper_tail_identity {n : ℕ} {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (k : Fin (n+1)) : (binomialCountLaw n p).real (Set.Ici k) = binomialUpperTail n k p := by
  rw [finite_measure_event_sum]
  simp_rw [binomial_count_atom hp]
  rfl

theorem binomial_lower_tail_identity {n : ℕ} {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (k : Fin (n+1)) : (binomialCountLaw n p).real (Set.Iic k) = binomialLowerTail n k p := by
  rw [finite_measure_event_sum]
  simp_rw [binomial_count_atom hp]
  rfl

theorem finite_upper_tail_pvalue {Alpha : Type*} [Fintype Alpha] [LinearOrder Alpha]
    [MeasurableSpace Alpha] (mu : Measure Alpha) [IsFiniteMeasure mu]
    {alpha : ℝ} (ha : 0 ≤ alpha) :
    mu.real {x | mu.real (Set.Ici x) ≤ alpha} ≤ alpha := by
  classical
  let s := Finset.univ.filter (fun x : Alpha => mu.real (Set.Ici x) ≤ alpha)
  by_cases hs : s.Nonempty
  · let m := s.min' hs
    have hm : mu.real (Set.Ici m) ≤ alpha := (Finset.mem_filter.mp (s.min'_mem hs)).2
    refine (measureReal_mono ?_).trans hm
    intro x hx
    exact s.min'_le x (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩)
  · have hEmpty : {x | mu.real (Set.Ici x) ≤ alpha} = (∅ : Set Alpha) := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hx
      exact hs ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩
    simpa [hEmpty] using ha

theorem finite_lower_tail_pvalue {Alpha : Type*} [Fintype Alpha] [LinearOrder Alpha]
    [MeasurableSpace Alpha] (mu : Measure Alpha) [IsFiniteMeasure mu]
    {alpha : ℝ} (ha : 0 ≤ alpha) :
    mu.real {x | mu.real (Set.Iic x) ≤ alpha} ≤ alpha := by
  classical
  let s := Finset.univ.filter (fun x : Alpha => mu.real (Set.Iic x) ≤ alpha)
  by_cases hs : s.Nonempty
  · let m := s.max' hs
    have hm : mu.real (Set.Iic m) ≤ alpha := (Finset.mem_filter.mp (s.max'_mem hs)).2
    refine (measureReal_mono ?_).trans hm
    intro x hx
    exact s.le_max' x (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩)
  · have hEmpty : {x | mu.real (Set.Iic x) ≤ alpha} = (∅ : Set Alpha) := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hx
      exact hs ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩
    simpa [hEmpty] using ha

/-- Tail-checked endpoints need not be monotone as functions of the observed count. -/
theorem binomial_tail_interval_coverage {n : ℕ} {p delta : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (hd : 0 ≤ delta)
    (L U : Fin (n+1) → ℝ)
    (hL : ∀ k, L k ∈ Set.Icc (0 : ℝ) 1)
    (hU : ∀ k, U k ∈ Set.Icc (0 : ℝ) 1)
    (hcL : ∀ k, L k = 0 ∨ binomialUpperTail n k (L k) ≤ delta/2)
    (hcU : ∀ k, U k = 1 ∨ binomialLowerTail n k (U k) ≤ delta/2) :
    (binomialCountLaw n p).real {k | ¬ (L k ≤ p ∧ p ≤ U k)} ≤ delta := by
  have hsub : {k : Fin (n+1) | ¬ (L k ≤ p ∧ p ≤ U k)} ⊆
      {k | (binomialCountLaw n p).real (Set.Ici k) ≤ delta/2} ∪
      {k | (binomialCountLaw n p).real (Set.Iic k) ≤ delta/2} := by
    intro k hbad
    by_cases hlo : L k ≤ p
    · right
      have hlt : U k < p := lt_of_not_ge (fun h => hbad ⟨hlo, h⟩)
      obtain heq | hc := hcU k
      · linarith [hp.2]
      · exact (binomial_lower_tail_antitone k hlt.le).trans
          (by rwa [binomial_lower_tail_identity (hU k)])
    · left
      have hlt : p < L k := lt_of_not_ge hlo
      obtain heq | hc := hcL k
      · linarith [hp.1]
      · exact (binomial_upper_tail_mono k hlt.le).trans
          (by rwa [binomial_upper_tail_identity (hL k)])
  calc
    _ ≤ (binomialCountLaw n p).real
        ({k | (binomialCountLaw n p).real (Set.Ici k) ≤ delta/2} ∪
         {k | (binomialCountLaw n p).real (Set.Iic k) ≤ delta/2}) := measureReal_mono hsub
    _ ≤ (binomialCountLaw n p).real {k | (binomialCountLaw n p).real (Set.Ici k) ≤ delta/2} +
        (binomialCountLaw n p).real {k | (binomialCountLaw n p).real (Set.Iic k) ≤ delta/2} :=
      measureReal_union_le _ _
    _ ≤ delta := by
      have h1 := finite_upper_tail_pvalue (binomialCountLaw n p) (alpha := delta/2) (by positivity)
      have h2 := finite_lower_tail_pvalue (binomialCountLaw n p) (alpha := delta/2) (by positivity)
      linarith

def binomialMassQ (n k : ℕ) (p : ℚ) : ℚ := (n.choose k : ℚ) * p^k * (1-p)^(n-k)
def binomialUpperTailQ (n : ℕ) (k : Fin (n+1)) (p : ℚ) : ℚ :=
  ∑ j : Fin (n+1), if k ≤ j then binomialMassQ n j p else 0
def binomialLowerTailQ (n : ℕ) (k : Fin (n+1)) (p : ℚ) : ℚ :=
  ∑ j : Fin (n+1), if j ≤ k then binomialMassQ n j p else 0

theorem binomial_mass_rat_cast (n k : ℕ) (p : ℚ) :
    (binomialMassQ n k p : ℝ) = binomialMass n k (p : ℝ) := by
  simp [binomialMassQ, binomialMass]

theorem binomial_upper_rat_cast (n : ℕ) (k : Fin (n+1)) (p : ℚ) :
    (binomialUpperTailQ n k p : ℝ) = binomialUpperTail n k (p : ℝ) := by
  simp only [binomialUpperTailQ, binomialUpperTail, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : k ≤ j
  · simp only [if_pos h, binomial_mass_rat_cast]
  · simp only [if_neg h, Rat.cast_zero]

theorem binomial_lower_rat_cast (n : ℕ) (k : Fin (n+1)) (p : ℚ) :
    (binomialLowerTailQ n k p : ℝ) = binomialLowerTail n k (p : ℝ) := by
  simp only [binomialLowerTailQ, binomialLowerTail, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : j ≤ k
  · simp only [if_pos h, binomial_mass_rat_cast]
  · simp only [if_neg h, Rat.cast_zero]

def BinomialReportValid (n : ℕ) (delta : ℚ) (L U : Fin (n+1) → ℚ) : Prop :=
  ∀ k, 0 ≤ L k ∧ L k ≤ U k ∧ U k ≤ 1 ∧
    (L k = 0 ∨ binomialUpperTailQ n k (L k) ≤ delta/2) ∧
    (U k = 1 ∨ binomialLowerTailQ n k (U k) ≤ delta/2)

theorem binomial_report_coverage {n : ℕ} {p : ℝ} {delta : ℚ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (hd : 0 ≤ delta)
    (L U : Fin (n+1) → ℚ) (hvalid : BinomialReportValid n delta L U) :
    (binomialCountLaw n p).real {k | ¬ ((L k : ℝ) ≤ p ∧ p ≤ (U k : ℝ))} ≤ (delta : ℝ) := by
  apply binomial_tail_interval_coverage hp (by exact_mod_cast hd)
  · intro k
    exact ⟨by exact_mod_cast (hvalid k).1,
      by exact_mod_cast (hvalid k).2.1.trans (hvalid k).2.2.1⟩
  · intro k
    exact ⟨by exact_mod_cast (hvalid k).1.trans (hvalid k).2.1,
      by exact_mod_cast (hvalid k).2.2.1⟩
  · intro k
    obtain hz | ht := (hvalid k).2.2.2.1
    · left; exact_mod_cast hz
    · right
      rw [← binomial_upper_rat_cast]
      exact_mod_cast ht
  · intro k
    obtain hz | ht := (hvalid k).2.2.2.2
    · left; exact_mod_cast hz
    · right
      rw [← binomial_lower_rat_cast]
      exact_mod_cast ht

theorem marked_binomial_report_coverage {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] (n : ℕ)
    (C : Omega → Omega → Prop) (p q : Omega)
    (hS : MeasurableSet (markedIntervalSet C p q)) {delta : ℚ} (hd : 0 ≤ delta)
    (L U : Fin (n+1) → ℚ) (hvalid : BinomialReportValid n delta L U) :
    (markedIntervalLaw mu n C p q).real {code |
      ¬ ((L (boundedBitCount code) : ℝ) ≤ mu.real (markedIntervalSet C p q) ∧
        mu.real (markedIntervalSet C p q) ≤ (U (boundedBitCount code) : ℝ))} ≤ (delta : ℝ) := by
  have h := binomial_report_coverage (p := mu.real (markedIntervalSet C p q))
    ⟨measureReal_nonneg, measureReal_le_one⟩ hd L U hvalid
  rw [← marked_count_eq_binomial mu n C p q hS,
    map_measureReal_apply (measurable_of_countable boundedBitCount)
      (Set.to_countable _ |>.measurableSet)] at h
  exact h

theorem retained_binomial_report_coverage {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] {pi : Omega → ℝ}
    (hpi : Integrable pi mu) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hbounds : ∀ x, a ≤ pi x ∧ pi x ≤ b) (n : ℕ)
    (C : Omega → Omega → Prop) (p q : Omega)
    (hS : MeasurableSet (markedIntervalSet C p q)) {delta : ℚ} (hd : 0 ≤ delta)
    (L U : Fin (n+1) → ℚ) (hvalid : BinomialReportValid n delta L U) :
    (markedIntervalLaw (retainedMeasure mu pi) n C p q).real {code |
      ¬ (retentionLower (b/a) (L (boundedBitCount code) : ℝ) ≤ mu.real (markedIntervalSet C p q) ∧
        mu.real (markedIntervalSet C p q) ≤ retentionUpper (b/a) (U (boundedBitCount code) : ℝ))} ≤
      (delta : ℝ) := by
  letI := retained_measure_probability mu hpi ha hbounds
  letI : IsProbabilityMeasure (markedIntervalLaw (retainedMeasure mu pi) n C p q) :=
    Measure.isProbabilityMeasure_map (marked_interval_code_measurable C p q hS).aemeasurable
  have hR : 1 ≤ b/a := (le_div_iff₀ ha).mpr (by simpa using hab)
  have htheta : (retainedMeasure mu pi).real (markedIntervalSet C p q) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨measureReal_nonneg, measureReal_le_one⟩
  have hid := retained_physical_identification mu hpi ha hab hbounds hS
  have hsub : {code : Fin n → Bool |
      ¬ (retentionLower (b/a) (L (boundedBitCount code) : ℝ) ≤ mu.real (markedIntervalSet C p q) ∧
        mu.real (markedIntervalSet C p q) ≤ retentionUpper (b/a) (U (boundedBitCount code) : ℝ))} ⊆
      {code | ¬ ((L (boundedBitCount code) : ℝ) ≤ (retainedMeasure mu pi).real (markedIntervalSet C p q) ∧
        (retainedMeasure mu pi).real (markedIntervalSet C p q) ≤ (U (boundedBitCount code) : ℝ))} := by
    intro code hbad hcover
    have hv := hvalid (boundedBitCount code)
    apply hbad
    apply retention_interval_composition hR htheta ?_ ?_ hid hcover
    · exact ⟨by exact_mod_cast hv.1, by exact_mod_cast hv.2.1.trans hv.2.2.1⟩
    · exact ⟨by exact_mod_cast hv.1.trans hv.2.1, by exact_mod_cast hv.2.2.1⟩
  exact (measureReal_mono hsub).trans
    (marked_binomial_report_coverage (retainedMeasure mu pi) n C p q hS hd L U hvalid)

end QuantyraNullCone
