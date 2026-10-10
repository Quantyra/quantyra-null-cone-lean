import QuantyraNullCone.ThinningTermination

namespace QuantyraNullCone

open MeasureTheory

def retainedCountHit {Ω : Type*} (pi : Ω → ℝ) (n : ℕ) (sample : ℕ → Ω × ℝ) : Prop :=
  ∃ N, streamRetainedCount pi N sample = n

theorem retained_count_hit_measurable {Ω : Type*} [MeasurableSpace Ω]
    {pi : Ω → ℝ} (hpi : Measurable pi) (n : ℕ) : MeasurableSet {sample | retainedCountHit pi n sample} := by
  simp only [retainedCountHit, Set.setOf_exists]
  exact MeasurableSet.iUnion (fun N => (measurableSet_singleton n).preimage
    (stream_retained_count_measurable hpi N))

theorem retained_stop_witness {Ω : Type*} (pi : Ω → ℝ) (n : ℕ) (sample : ℕ → Ω × ℝ) :
    ∃ N, streamRetainedCount pi N sample = n ∨ ¬retainedCountHit pi n sample := by
  by_cases h : retainedCountHit pi n sample
  · obtain ⟨N, hN⟩ := h
    exact ⟨N, Or.inl hN⟩
  · exact ⟨0, Or.inr h⟩

/-- Least prefix with retained count n; zero on the nontermination set. -/
noncomputable def retainedStopPrefix {Ω : Type*} (pi : Ω → ℝ) (n : ℕ)
    (sample : ℕ → Ω × ℝ) : ℕ := by
  classical
  exact Nat.find (retained_stop_witness pi n sample)

theorem retained_stop_prefix_measurable {Ω : Type*} [MeasurableSpace Ω]
    {pi : Ω → ℝ} (hpi : Measurable pi) (n : ℕ) : Measurable (retainedStopPrefix pi n) := by
  classical
  apply measurable_find (retained_stop_witness pi n)
  intro N
  exact ((measurableSet_singleton n).preimage (stream_retained_count_measurable hpi N)).union
    (retained_count_hit_measurable hpi n).compl

theorem retained_stop_prefix_spec {Ω : Type*} (pi : Ω → ℝ) (n : ℕ)
    (sample : ℕ → Ω × ℝ) (hhit : retainedCountHit pi n sample) :
    streamRetainedCount pi (retainedStopPrefix pi n sample) sample = n := by
  classical
  exact (Nat.find_spec (retained_stop_witness pi n sample)).resolve_right (not_not.mpr hhit)

theorem retained_stop_prefix_min {Ω : Type*} (pi : Ω → ℝ) (n : ℕ)
    (sample : ℕ → Ω × ℝ) {M : ℕ} (hM : M < retainedStopPrefix pi n sample) :
    streamRetainedCount pi M sample ≠ n := by
  classical
  intro heq
  exact Nat.find_min (retained_stop_witness pi n sample) hM (Or.inl heq)

theorem retained_stop_prefix_eq_of_first {Ω : Type*} (pi : Ω → ℝ) (n : ℕ)
    (sample : ℕ → Ω × ℝ) (N : ℕ) (hN : streamRetainedCount pi N sample = n)
    (hfirst : ∀ M < N, streamRetainedCount pi M sample ≠ n) :
    retainedStopPrefix pi n sample = N := by
  classical
  apply le_antisymm (Nat.find_min' (retained_stop_witness pi n sample) (Or.inl hN))
  by_contra h
  exact hfirst _ (Nat.lt_of_not_ge h) (retained_stop_prefix_spec pi n sample ⟨N, hN⟩)

theorem retained_stop_prefix_of_no_hit {Ω : Type*} (pi : Ω → ℝ) (n : ℕ)
    (sample : ℕ → Ω × ℝ) (hhit : ¬retainedCountHit pi n sample) :
    retainedStopPrefix pi n sample = 0 := by
  classical
  exact Nat.eq_zero_of_le_zero (Nat.find_min' (retained_stop_witness pi n sample) (Or.inr hhit))

theorem retained_stop_prefix_zero {Ω : Type*} (pi : Ω → ℝ) (sample : ℕ → Ω × ℝ) :
    retainedStopPrefix pi 0 sample = 0 := by
  apply retained_stop_prefix_eq_of_first
  · simp [stream_retained_count_eq_nat_count]
  · intro M hM
    omega

noncomputable def stoppedRetainedView {Ω : Type*} (pi : Ω → ℝ) (fallback : Ω) (n : ℕ)
    (sample : ℕ → Ω × ℝ) : Fin n → Ω :=
  retainedOrderedView pi fallback n (finitePrefix (retainedStopPrefix pi n sample) sample)

theorem stopped_retained_view_measurable {Ω : Type*} [MeasurableSpace Ω]
    {pi : Ω → ℝ} (hpi : Measurable pi) (fallback : Ω) (n : ℕ) :
    Measurable (stoppedRetainedView pi fallback n) := by
  have h : Measurable (fun z : ℕ × (ℕ → Ω × ℝ) =>
      retainedOrderedView pi fallback n (finitePrefix z.1 z.2)) :=
    measurable_from_prod_countable_right (fun N =>
      (retained_ordered_view_measurable hpi fallback n).comp (finite_prefix_measurable N))
  exact h.comp ((retained_stop_prefix_measurable hpi n).prodMk measurable_id)

theorem ae_retained_stop_prefix_spec {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] {pi : Ω → ℝ}
    (hpi : Measurable pi) (hInt : Integrable pi mu)
    (hbounds : ∀ x, pi x ∈ Set.Icc 0 1) (hZ : 0 < ∫ x, pi x ∂mu) (n : ℕ) :
    ∀ᵐ sample ∂generatedStreamLaw mu,
      streamRetainedCount pi (retainedStopPrefix pi n sample) sample = n := by
  filter_upwards [ae_stream_retained_count_surjective mu hpi hInt hbounds hZ] with sample hs
  exact retained_stop_prefix_spec pi n sample (hs n)

end QuantyraNullCone
