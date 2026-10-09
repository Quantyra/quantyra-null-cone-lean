import QuantyraNullCone.ThinningCoverage
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

namespace QuantyraNullCone

open MeasureTheory

def finitePrefix {X : Type*} (N : ℕ) (sample : ℕ → X) : Fin N → X :=
  fun i => sample i

theorem finite_prefix_measurable {X : Type*} [MeasurableSpace X] (N : ℕ) :
    Measurable (@finitePrefix X N) :=
  measurable_pi_lambda _ (fun i => measurable_pi_apply i.val)

/-- Every finite prefix of the actual infinite iid stream has its finite product law. -/
theorem infinite_iid_prefix_law {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsProbabilityMeasure mu] (N : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => mu)).map (finitePrefix N) =
      Measure.pi (fun _ : Fin N => mu) := by
  classical
  let e : (Finset.range N) ≃ Fin N :=
    { toFun := fun i => ⟨i.val, Finset.mem_range.mp i.property⟩
      invFun := fun i => ⟨i.val, Finset.mem_range.mpr i.isLt⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hview : finitePrefix (X := X) N =
      (MeasurableEquiv.piCongrLeft (fun _ : Fin N => X) e) ∘ (Finset.range N).restrict := by
    funext sample j
    obtain ⟨i, rfl⟩ := e.surjective j
    simpa [finitePrefix, e] using
      (MeasurableEquiv.piCongrLeft_apply_apply e (β := fun _ : Fin N => X)
        ((Finset.range N).restrict sample) i).symm
  rw [hview, ← Measure.map_map (MeasurableEquiv.piCongrLeft (fun _ : Fin N => X) e).measurable
    ((Finset.range N).measurable_restrict),
    Measure.infinitePi_map_restrict]
  exact Measure.pi_map_piCongrLeft e (fun _ : Fin N => mu)

noncomputable def generatedStreamLaw {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) : Measure (ℕ → Ω × ℝ) :=
  Measure.infinitePi (fun _ : ℕ => mu.prod uniform01Measure)

instance generatedStreamLaw_probability {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] : IsProbabilityMeasure (generatedStreamLaw mu) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi (fun _ : ℕ => mu.prod uniform01Measure)))

theorem generated_stream_prefix_law {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (N : ℕ) :
    (generatedStreamLaw mu).map (finitePrefix N) =
      Measure.pi (fun _ : Fin N => mu.prod uniform01Measure) :=
  infinite_iid_prefix_law _ N

noncomputable def streamRetainedCount {Ω : Type*} (pi : Ω → ℝ) (N : ℕ)
    (sample : ℕ → Ω × ℝ) : ℕ :=
  bitCount (membershipCode (retentionEvent pi) (finitePrefix N sample))

theorem stream_retained_count_measurable {Ω : Type*} [MeasurableSpace Ω]
    {pi : Ω → ℝ} (hpi : Measurable pi) (N : ℕ) :
    Measurable (streamRetainedCount pi N) :=
  (measurable_of_countable (@bitCount N)).comp
    ((membership_code_measurable (retention_event_measurable hpi)).comp (finite_prefix_measurable N))

theorem stream_retained_submeasure_law {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] {pi : Ω → ℝ}
    (hpi : Measurable pi) (hInt : Integrable pi mu)
    (hbounds : ∀ x, pi x ∈ Set.Icc 0 1) (hZ : 0 < ∫ x, pi x ∂mu)
    (N n : ℕ) (fallback : Ω) :
    ((generatedStreamLaw mu).restrict {sample | streamRetainedCount pi N sample = n}).map
        (retainedOrderedView pi fallback n ∘ finitePrefix N) =
      (Measure.pi (fun _ : Fin N => mu.prod uniform01Measure)) (retainedCountEvent pi N n) •
        Measure.pi (fun _ : Fin n => retainedMeasure mu pi) := by
  have hset : {sample | streamRetainedCount pi N sample = n} =
      finitePrefix N ⁻¹' retainedCountEvent pi N n := rfl
  rw [hset, ← Measure.map_map (retained_ordered_view_measurable hpi fallback n)
    (finite_prefix_measurable N), ← Measure.restrict_map (finite_prefix_measurable N)
    (retained_count_event_measurable hpi N n), generated_stream_prefix_law]
  exact retained_count_submeasure_law mu hpi hInt hbounds hZ N n fallback

/-- A countable independent choice of a measurable experiment, with its actual product input. -/
theorem nat_product_restriction_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (q : Measure ℕ) (mu : Measure X) [SFinite mu] (S : ℕ → Set X)
    (hS : ∀ N, MeasurableSet (S N)) (f : ℕ → X → Y) (hf : ∀ N, Measurable (f N)) :
    ((q.prod mu).restrict {z | z.2 ∈ S z.1}).map (fun z => f z.1 z.2) =
      Measure.sum (fun N => q {N} • (mu.restrict (S N)).map (f N)) := by
  have hE : MeasurableSet {z : ℕ × X | z.2 ∈ S z.1} :=
    measurableSet_setOf.mpr (measurable_from_prod_countable_right (fun N => (hS N).mem))
  have hF : Measurable (fun z : ℕ × X => f z.1 z.2) :=
    measurable_from_prod_countable_right hf
  ext T hT
  rw [Measure.map_apply hF hT, Measure.restrict_apply (hF hT),
    Measure.prod_apply ((hF hT).inter hE), lintegral_countable', Measure.sum_apply _ hT]
  apply tsum_congr
  intro N
  rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply (hf N) hT,
    Measure.restrict_apply (hf N hT), mul_comm]
  rfl

end QuantyraNullCone
