import QuantyraNullCone.ThinningSelected

namespace QuantyraNullCone

open MeasureTheory

theorem finite_fiber_restriction_map {Ω A Y : Type*} [MeasurableSpace Ω]
    [MeasurableSpace A] [MeasurableSingletonClass A] [MeasurableSpace Y]
    (mu : Measure Ω) {X : Ω → A} (hX : Measurable X) {f : Ω → Y} (hf : Measurable f)
    (s : Finset A) :
    (mu.restrict (X ⁻¹' (s : Set A))).map f =
      ∑ a ∈ s, (mu.restrict (X ⁻¹' {a})).map f := by
  classical
  ext T hT
  simp only [Measure.map_apply hf hT, Measure.restrict_apply (hf hT),
    Measure.coe_finsetSum, Finset.sum_apply]
  have hset : (⋃ a ∈ s, f ⁻¹' T ∩ X ⁻¹' {a}) = f ⁻¹' T ∩ X ⁻¹' (s : Set A) := by
    ext x
    simp
  have hd : (s : Set A).PairwiseDisjoint (fun a => f ⁻¹' T ∩ X ⁻¹' {a}) := by
    intro a _ b _ hab
    apply Set.disjoint_left.mpr
    rintro x ⟨_, hxa⟩ ⟨_, hxb⟩
    exact hab (hxa.symm.trans hxb)
  rw [← measure_biUnion_finset hd (fun a _ => (hf hT).inter (hX (measurableSet_singleton a))), hset]

theorem finite_fiber_mass_sum {Ω A : Type*} [MeasurableSpace Ω]
    [MeasurableSpace A] [MeasurableSingletonClass A] (mu : Measure Ω)
    {X : Ω → A} (hX : Measurable X) (s : Finset A) :
    ∑ a ∈ s, mu (X ⁻¹' {a}) = mu (X ⁻¹' (s : Set A)) := by
  have h := congrArg (fun m : Measure Ω => m Set.univ)
    (finite_fiber_restriction_map mu hX measurable_id s)
  simpa only [Measure.map_id, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Measure.coe_finsetSum, Finset.sum_apply] using h.symm

theorem restriction_eq_mass_conditional {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsFiniteMeasure mu] {S : Set Ω} (hS : MeasurableSet S) :
    mu.restrict S = mu S • ProbabilityTheory.cond mu S := by
  ext T hT
  rw [Measure.restrict_apply hT, Measure.smul_apply, smul_eq_mul, mul_comm,
    ProbabilityTheory.cond_mul_eq_inter hS, Set.inter_comm]

theorem retained_pattern_submeasure_law {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] {pi : Ω → ℝ}
    (hpi : Measurable pi) (hInt : Integrable pi mu)
    (hbounds : ∀ x, pi x ∈ Set.Icc 0 1) (hZ : 0 < ∫ x, pi x ∂mu)
    {N n : ℕ} (fallback : Ω) (code : Fin N → Bool) (hn : bitCount code = n) :
    ((Measure.pi (fun _ : Fin N => mu.prod uniform01Measure)).restrict
      (membershipCode (retentionEvent pi) ⁻¹' {code})).map (retainedOrderedView pi fallback n) =
      (Measure.pi (fun _ : Fin N => mu.prod uniform01Measure))
        (membershipCode (retentionEvent pi) ⁻¹' {code}) •
          Measure.pi (fun _ : Fin n => retainedMeasure mu pi) := by
  rw [retention_pattern_fiber]
  by_cases hc : (Measure.pi (fun _ : Fin N => mu.prod uniform01Measure))
      (retentionPattern pi (trueBits code)) = 0
  · rw [Measure.restrict_eq_zero.mpr hc, Measure.map_zero, hc, zero_smul]
  · rw [restriction_eq_mass_conditional _ (retention_pattern_measurable hpi (trueBits code)),
      Measure.map_smul, retained_ordered_pattern_law mu hpi hInt hbounds hZ fallback code hn hc]

def retainedCountEvent {Ω : Type*} (pi : Ω → ℝ) (N n : ℕ) : Set (Fin N → Ω × ℝ) :=
  {sample | bitCount (membershipCode (retentionEvent pi) sample) = n}

theorem retained_count_event_measurable {Ω : Type*} [MeasurableSpace Ω]
    {pi : Ω → ℝ} (hpi : Measurable pi) (N n : ℕ) : MeasurableSet (retainedCountEvent pi N n) :=
  (measurableSet_singleton n).preimage ((measurable_of_countable (@bitCount N)).comp
    (membership_code_measurable (retention_event_measurable hpi)))

/-- The actual generated sample, restricted only by its retained count, has the
product location submeasure with exactly that count's probability as its mass. -/
theorem retained_count_submeasure_law {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] {pi : Ω → ℝ}
    (hpi : Measurable pi) (hInt : Integrable pi mu)
    (hbounds : ∀ x, pi x ∈ Set.Icc 0 1) (hZ : 0 < ∫ x, pi x ∂mu)
    (N n : ℕ) (fallback : Ω) :
    ((Measure.pi (fun _ : Fin N => mu.prod uniform01Measure)).restrict
      (retainedCountEvent pi N n)).map (retainedOrderedView pi fallback n) =
      (Measure.pi (fun _ : Fin N => mu.prod uniform01Measure)) (retainedCountEvent pi N n) •
        Measure.pi (fun _ : Fin n => retainedMeasure mu pi) := by
  classical
  let s : Finset (Fin N → Bool) := Finset.univ.filter (fun code => bitCount code = n)
  have hset : retainedCountEvent pi N n = membershipCode (retentionEvent pi) ⁻¹' (s : Set _) := by
    ext sample
    simp [retainedCountEvent, s]
  rw [hset, finite_fiber_restriction_map _
    (membership_code_measurable (retention_event_measurable hpi))
    (retained_ordered_view_measurable hpi fallback n)]
  calc
    _ = ∑ code ∈ s, (Measure.pi (fun _ : Fin N => mu.prod uniform01Measure))
        (membershipCode (retentionEvent pi) ⁻¹' {code}) •
          Measure.pi (fun _ : Fin n => retainedMeasure mu pi) := by
      apply Finset.sum_congr rfl
      intro code hc
      exact retained_pattern_submeasure_law mu hpi hInt hbounds hZ fallback code
        (Finset.mem_filter.mp hc).2
    _ = _ := by
      rw [← Finset.sum_smul, finite_fiber_mass_sum _
        (membership_code_measurable (retention_event_measurable hpi))]

/-- Conditional iid retained locations are derived from independent uniform
marks and an actual count event, not assumed as an input experiment. -/
theorem retained_count_conditional_law {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] {pi : Ω → ℝ}
    (hpi : Measurable pi) (hInt : Integrable pi mu)
    (hbounds : ∀ x, pi x ∈ Set.Icc 0 1) (hZ : 0 < ∫ x, pi x ∂mu)
    (N n : ℕ) (fallback : Ω)
    (hc : (Measure.pi (fun _ : Fin N => mu.prod uniform01Measure))
      (retainedCountEvent pi N n) ≠ 0) :
    (ProbabilityTheory.cond (Measure.pi (fun _ : Fin N => mu.prod uniform01Measure))
      (retainedCountEvent pi N n)).map (retainedOrderedView pi fallback n) =
      Measure.pi (fun _ : Fin n => retainedMeasure mu pi) := by
  rw [ProbabilityTheory.cond, Measure.map_smul,
    retained_count_submeasure_law mu hpi hInt hbounds hZ, smul_smul,
    ENNReal.inv_mul_cancel hc (measure_ne_top _ _), one_smul]

end QuantyraNullCone
