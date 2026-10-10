import QuantyraNullCone.ThinningStopping

namespace QuantyraNullCone

open MeasureTheory

noncomputable def patternPrefixCount {N : ℕ} (code : Fin N → Bool) (M : ℕ) : ℕ := by
  classical
  exact Nat.count (fun i => ∃ j : Fin N, j.val = i ∧ code j = true) M

theorem pattern_prefix_count_stream {Ω : Type*} (pi : Ω → ℝ) (N M : ℕ)
    (sample : ℕ → Ω × ℝ) (hMN : M ≤ N) :
    patternPrefixCount (membershipCode (retentionEvent pi) (finitePrefix N sample)) M =
      streamRetainedCount pi M sample := by
  classical
  unfold patternPrefixCount
  rw [stream_retained_count_eq_nat_count]
  simp only [Nat.count_eq_card_filter_range]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro i hi
  have hiM : i < M := Finset.mem_range.mp hi
  constructor
  · rintro ⟨j, hj, hjs⟩
    simpa [membershipCode, finitePrefix, hj] using hjs
  · intro his
    refine ⟨⟨i, lt_of_lt_of_le hiM hMN⟩, rfl, ?_⟩
    simpa [membershipCode, finitePrefix] using his

noncomputable def retainedTerminalCodes (n N : ℕ) : Finset (Fin N → Bool) := by
  classical
  exact Finset.univ.filter (fun code => bitCount code = n ∧ ∀ M < N, patternPrefixCount code M ≠ n)

def retainedTerminalEvent {Ω : Type*} (pi : Ω → ℝ) (n N : ℕ) : Set (Fin N → Ω × ℝ) :=
  membershipCode (retentionEvent pi) ⁻¹' (retainedTerminalCodes n N : Set _)

theorem retained_terminal_event_measurable {Ω : Type*} [MeasurableSpace Ω]
    {pi : Ω → ℝ} (hpi : Measurable pi) (n N : ℕ) : MeasurableSet (retainedTerminalEvent pi n N) :=
  (retainedTerminalCodes n N).finite_toSet.measurableSet.preimage
    (membership_code_measurable (retention_event_measurable hpi))

theorem retained_terminal_event_iff {Ω : Type*} (pi : Ω → ℝ) (n N : ℕ)
    (sample : ℕ → Ω × ℝ) :
    finitePrefix N sample ∈ retainedTerminalEvent pi n N ↔
      retainedStopPrefix pi n sample = N ∧ retainedCountHit pi n sample := by
  classical
  change membershipCode (retentionEvent pi) (finitePrefix N sample) ∈ retainedTerminalCodes n N ↔ _
  simp only [retainedTerminalCodes, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hN, hmin⟩
    have hcount : streamRetainedCount pi N sample = n := hN
    have hfirst (M : ℕ) (hMN : M < N) : streamRetainedCount pi M sample ≠ n := by
      have h := hmin M hMN
      rwa [pattern_prefix_count_stream pi N M sample hMN.le] at h
    exact ⟨retained_stop_prefix_eq_of_first pi n sample N hcount hfirst, ⟨N, hcount⟩⟩
  · rintro ⟨hstop, hhit⟩
    constructor
    · have h := retained_stop_prefix_spec pi n sample hhit
      rw [hstop] at h
      exact h
    · intro M hMN
      rw [pattern_prefix_count_stream pi N M sample hMN.le]
      exact retained_stop_prefix_min pi n sample (by rwa [hstop])

/-- Any collection of patterns with the same retained count gives the same iid location law. -/
theorem retained_pattern_collection_submeasure {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] {pi : Ω → ℝ}
    (hpi : Measurable pi) (hInt : Integrable pi mu)
    (hbounds : ∀ x, pi x ∈ Set.Icc 0 1) (hZ : 0 < ∫ x, pi x ∂mu)
    {N n : ℕ} (fallback : Ω) (codes : Finset (Fin N → Bool))
    (hcodes : ∀ code ∈ codes, bitCount code = n) :
    ((Measure.pi (fun _ : Fin N => mu.prod uniform01Measure)).restrict
      (membershipCode (retentionEvent pi) ⁻¹' (codes : Set _))).map (retainedOrderedView pi fallback n) =
      (Measure.pi (fun _ : Fin N => mu.prod uniform01Measure))
        (membershipCode (retentionEvent pi) ⁻¹' (codes : Set _)) •
          Measure.pi (fun _ : Fin n => retainedMeasure mu pi) := by
  rw [finite_fiber_restriction_map _ (membership_code_measurable (retention_event_measurable hpi))
    (retained_ordered_view_measurable hpi fallback n)]
  calc
    _ = ∑ code ∈ codes, (Measure.pi (fun _ : Fin N => mu.prod uniform01Measure))
        (membershipCode (retentionEvent pi) ⁻¹' {code}) •
          Measure.pi (fun _ : Fin n => retainedMeasure mu pi) := by
      apply Finset.sum_congr rfl
      intro code hc
      exact retained_pattern_submeasure_law mu hpi hInt hbounds hZ fallback code (hcodes code hc)
    _ = _ := by
      rw [← Finset.sum_smul, finite_fiber_mass_sum _
        (membership_code_measurable (retention_event_measurable hpi))]

theorem stream_terminal_pattern_submeasure {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] {pi : Ω → ℝ}
    (hpi : Measurable pi) (hInt : Integrable pi mu)
    (hbounds : ∀ x, pi x ∈ Set.Icc 0 1) (hZ : 0 < ∫ x, pi x ∂mu)
    (N n : ℕ) (fallback : Ω) :
    ((generatedStreamLaw mu).restrict (finitePrefix N ⁻¹' retainedTerminalEvent pi n N)).map
        (retainedOrderedView pi fallback n ∘ finitePrefix N) =
      (Measure.pi (fun _ : Fin N => mu.prod uniform01Measure)) (retainedTerminalEvent pi n N) •
        Measure.pi (fun _ : Fin n => retainedMeasure mu pi) := by
  classical
  rw [← Measure.map_map (retained_ordered_view_measurable hpi fallback n) (finite_prefix_measurable N),
    ← Measure.restrict_map (finite_prefix_measurable N) (retained_terminal_event_measurable hpi n N),
    generated_stream_prefix_law]
  exact retained_pattern_collection_submeasure mu hpi hInt hbounds hZ fallback
    (retainedTerminalCodes n N) (fun _ hc => (Finset.mem_filter.mp hc).2.1)

end QuantyraNullCone
