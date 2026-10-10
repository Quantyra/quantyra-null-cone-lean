import QuantyraNullCone.ThinningLaplace
import Mathlib.Data.Nat.Nth
import Mathlib.Analysis.SpecificLimits.Basic

namespace QuantyraNullCone

open MeasureTheory Filter

/-- A fixed tail of an iid stream almost surely contains another positive-probability event. -/
theorem iid_no_further_event_null {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsProbabilityMeasure mu] {S : Set X}
    (hS : MeasurableSet S) (hp : 0 < mu S) (K : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => mu)) {sample | ∀ i, K ≤ i → sample i ∉ S} = 0 := by
  have hq : mu Sᶜ < 1 := by
    rw [prob_compl_eq_one_sub hS]
    exact ENNReal.sub_lt_self (by simp) one_ne_zero (ne_of_gt hp)
  have hbound (r : ℕ) :
      (Measure.infinitePi (fun _ : ℕ => mu)) {sample | ∀ i, K ≤ i → sample i ∉ S} ≤
        (mu Sᶜ)^r := by
    calc
      _ ≤ (Measure.infinitePi (fun _ : ℕ => mu))
          (Set.pi (Finset.Ico K (K+r)) (fun _ => Sᶜ)) := by
        apply measure_mono
        intro sample hs i hi
        exact hs i (Finset.mem_Ico.mp hi).1
      _ = (mu Sᶜ)^r := by
        simpa using (Measure.infinitePi_pi (μ := fun _ : ℕ => mu)
          (s := Finset.Ico K (K+r)) (t := fun _ => Sᶜ) (fun _ _ => hS.compl))
  exact le_antisymm (ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq) hbound)
    bot_le

theorem iid_positive_event_infinite {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsProbabilityMeasure mu] {S : Set X}
    (hS : MeasurableSet S) (hp : 0 < mu S) :
    ∀ᵐ sample ∂Measure.infinitePi (fun _ : ℕ => mu), {i | sample i ∈ S}.Infinite := by
  classical
  apply ae_iff.mpr
  apply measure_mono_null (t := ⋃ K : ℕ, {sample | ∀ i, K ≤ i → sample i ∉ S})
  · intro sample hs
    have hf : {i | sample i ∈ S}.Finite := by simpa only [Set.Infinite, not_not] using hs
    obtain ⟨K, hK⟩ := hf.bddAbove
    apply Set.mem_iUnion.mpr
    refine ⟨K+1, ?_⟩
    intro i hi his
    have hik : i ≤ K := hK his
    omega
  · exact measure_iUnion_null (fun K => iid_no_further_event_null mu hS hp K)

theorem stream_retained_count_eq_nat_count {Ω : Type*} (pi : Ω → ℝ)
    (N : ℕ) (sample : ℕ → Ω × ℝ) :
    streamRetainedCount pi N sample =
      @Nat.count (fun i => sample i ∈ retentionEvent pi) (fun _ => Classical.propDecidable _) N := by
  classical
  rw [Nat.count_eq_card_filter_range]
  unfold streamRetainedCount bitCount
  apply Finset.card_bij (fun i _ => i.val)
  · intro i hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr i.isLt, ?_⟩
    simpa [trueBits, membershipCode, finitePrefix] using hi
  · intro i _ j _ hij
    exact Fin.ext hij
  · intro j hj
    obtain ⟨hjN, hjS⟩ := Finset.mem_filter.mp hj
    refine ⟨⟨j, Finset.mem_range.mp hjN⟩, ?_, rfl⟩
    simpa [trueBits, membershipCode, finitePrefix] using hjS

/-- Positive mean retention gives every prescribed finite retained count almost surely. -/
theorem ae_stream_retained_count_surjective {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] {pi : Ω → ℝ}
    (hpi : Measurable pi) (hInt : Integrable pi mu)
    (hbounds : ∀ x, pi x ∈ Set.Icc 0 1) (hZ : 0 < ∫ x, pi x ∂mu) :
    ∀ᵐ sample ∂generatedStreamLaw mu, Function.Surjective (fun N => streamRetainedCount pi N sample) := by
  classical
  have hp : 0 < (mu.prod uniform01Measure) (retentionEvent pi) := by
    rw [detected_event_mass mu hpi hInt hbounds]
    exact ENNReal.ofReal_pos.mpr hZ
  have h := iid_positive_event_infinite (mu.prod uniform01Measure) (retention_event_measurable hpi) hp
  filter_upwards [h] with sample hs
  intro n
  obtain ⟨N, hN⟩ := Nat.surjective_count_of_infinite_setOf hs n
  exact ⟨N, (stream_retained_count_eq_nat_count pi N sample).trans hN⟩

end QuantyraNullCone
