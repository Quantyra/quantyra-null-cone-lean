import QuantyraNullCone.ThinningSubset
import Mathlib.Data.Finset.Sort

namespace QuantyraNullCone

open MeasureTheory

noncomputable def orderedPatternView {Ω : Type*} {N : ℕ} (fallback : Ω) (n : ℕ)
    (code : Fin N → Bool) (sample : Fin N → Ω × ℝ) : Fin n → Ω :=
  if h : (trueBits code).card = n then
    fun j => (sample ((trueBits code).orderEmbOfFin h j)).1
  else fun _ => fallback

noncomputable def retainedOrderedView {Ω : Type*} {N : ℕ} (pi : Ω → ℝ)
    (fallback : Ω) (n : ℕ) (sample : Fin N → Ω × ℝ) : Fin n → Ω :=
  orderedPatternView fallback n (membershipCode (retentionEvent pi) sample) sample

theorem ordered_pattern_view_measurable {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (fallback : Ω) (n : ℕ) (code : Fin N → Bool) :
    Measurable (orderedPatternView fallback n code) := by
  classical
  unfold orderedPatternView
  split_ifs
  · exact measurable_pi_lambda _ (fun _ => measurable_fst.comp (measurable_pi_apply _))
  · exact measurable_const

theorem retained_ordered_view_measurable {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    {pi : Ω → ℝ} (hpi : Measurable pi) (fallback : Ω) (n : ℕ) :
    Measurable (@retainedOrderedView Ω N pi fallback n) := by
  have h : Measurable (fun z : (Fin N → Bool) × (Fin N → Ω × ℝ) =>
      orderedPatternView fallback n z.1 z.2) :=
    measurable_from_prod_countable_right (ordered_pattern_view_measurable fallback n)
  exact h.comp ((membership_code_measurable (retention_event_measurable hpi)).prodMk measurable_id)

theorem retention_pattern_fiber {Ω : Type*} {N : ℕ} (pi : Ω → ℝ) (code : Fin N → Bool) :
    membershipCode (retentionEvent pi) ⁻¹' {code} = retentionPattern pi (trueBits code) := by
  classical
  ext sample
  simp only [Set.mem_preimage, Set.mem_singleton_iff, funext_iff, retentionPattern,
    Set.mem_pi, Set.mem_univ, forall_const]
  apply forall_congr'
  intro i
  cases h : code i <;> simp [membershipCode, trueBits, h]

theorem ordered_pattern_conditional_law {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] {pi : Ω → ℝ}
    (hpi : Measurable pi) (hInt : Integrable pi mu)
    (hbounds : ∀ x, pi x ∈ Set.Icc 0 1) (hZ : 0 < ∫ x, pi x ∂mu)
    {N n : ℕ} (fallback : Ω) (code : Fin N → Bool) (hn : bitCount code = n)
    (hc : (Measure.pi (fun _ : Fin N => mu.prod uniform01Measure))
      (retentionPattern pi (trueBits code)) ≠ 0) :
    (ProbabilityTheory.cond (Measure.pi (fun _ : Fin N => mu.prod uniform01Measure))
      (retentionPattern pi (trueBits code))).map (orderedPatternView fallback n code) =
      Measure.pi (fun _ : Fin n => retainedMeasure mu pi) := by
  classical
  letI := retained_probability_of_channel mu hpi hInt hbounds hZ
  have hn' : (trueBits code).card = n := hn
  let e : (trueBits code) ≃ Fin n := ((trueBits code).orderIsoOfFin hn').toEquiv.symm
  have hview : orderedPatternView fallback n code =
      (fun sample (j : Fin n) => sample (e.symm j)) ∘ retainedSubsetView (trueBits code) := by
    funext sample j
    simp [orderedPatternView, hn', e, retainedSubsetView]
  have hreindex : Measurable (fun sample : (trueBits code) → Ω =>
      fun j : Fin n => sample (e.symm j)) :=
    measurable_pi_lambda _ (fun j => measurable_pi_apply (e.symm j))
  rw [hview, ← Measure.map_map
    hreindex
    (retained_subset_view_measurable (trueBits code)),
    retained_subset_law mu hpi hInt hbounds hZ (trueBits code) hc]
  have heq : (fun sample : (trueBits code) → Ω => fun j : Fin n => sample (e.symm j)) =
      (MeasurableEquiv.piCongrLeft (fun _ : Fin n => Ω) e) := by
    funext sample j
    obtain ⟨i, rfl⟩ := e.surjective j
    simpa using (MeasurableEquiv.piCongrLeft_apply_apply e (β := fun _ : Fin n => Ω) sample i).symm
  rw [heq]
  exact Measure.pi_map_piCongrLeft e (fun _ : Fin n => retainedMeasure mu pi)

/-- On each actual pattern, the observable retained-tuple map agrees with the
fixed-pattern extractor. Its fallback is used only outside the selected count. -/
theorem retained_ordered_pattern_law {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] {pi : Ω → ℝ}
    (hpi : Measurable pi) (hInt : Integrable pi mu)
    (hbounds : ∀ x, pi x ∈ Set.Icc 0 1) (hZ : 0 < ∫ x, pi x ∂mu)
    {N n : ℕ} (fallback : Ω) (code : Fin N → Bool) (hn : bitCount code = n)
    (hc : (Measure.pi (fun _ : Fin N => mu.prod uniform01Measure))
      (retentionPattern pi (trueBits code)) ≠ 0) :
    (ProbabilityTheory.cond (Measure.pi (fun _ : Fin N => mu.prod uniform01Measure))
      (retentionPattern pi (trueBits code))).map (retainedOrderedView pi fallback n) =
      Measure.pi (fun _ : Fin n => retainedMeasure mu pi) := by
  rw [← ordered_pattern_conditional_law mu hpi hInt hbounds hZ fallback code hn hc]
  apply Measure.map_congr
  apply ProbabilityTheory.ae_cond_of_forall_mem (retention_pattern_measurable hpi (trueBits code))
  intro sample hs
  have hcode : membershipCode (retentionEvent pi) sample = code := by
    change sample ∈ membershipCode (retentionEvent pi) ⁻¹' {code}
    rwa [retention_pattern_fiber]
  simp [retainedOrderedView, hcode]

end QuantyraNullCone
