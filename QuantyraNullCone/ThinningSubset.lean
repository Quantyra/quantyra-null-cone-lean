import QuantyraNullCone.ThinningChannel

namespace QuantyraNullCone

open MeasureTheory

def retentionPattern {Ω : Type*} {N : ℕ} (pi : Ω → ℝ) (I : Finset (Fin N)) :
    Set (Fin N → Ω × ℝ) :=
  Set.univ.pi (fun i => if i ∈ I then retentionEvent pi else (retentionEvent pi)ᶜ)

def retainedSubsetView {Ω : Type*} {N : ℕ} (I : Finset (Fin N))
    (sample : Fin N → Ω × ℝ) : I → Ω := fun i => (sample i).1

theorem retention_pattern_measurable {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    {pi : Ω → ℝ} (hpi : Measurable pi) (I : Finset (Fin N)) :
    MeasurableSet (retentionPattern pi I) := by
  apply MeasurableSet.univ_pi
  intro i
  split_ifs
  · exact retention_event_measurable hpi
  · exact (retention_event_measurable hpi).compl

theorem retained_subset_view_measurable {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (I : Finset (Fin N)) : Measurable (@retainedSubsetView Ω N I) :=
  measurable_pi_lambda _ (fun i => measurable_fst.comp (measurable_pi_apply i.val))

/-- Any actual positive-probability pattern has iid retained locations, including
patterns with rejected generated events. The retained index subtype carries no coordinates. -/
theorem retained_subset_law {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] {pi : Ω → ℝ}
    (hpi : Measurable pi) (hInt : Integrable pi mu)
    (hbounds : ∀ x, pi x ∈ Set.Icc 0 1) (hZ : 0 < ∫ x, pi x ∂mu)
    {N : ℕ} (I : Finset (Fin N))
    (hc : (Measure.pi (fun _ : Fin N => mu.prod uniform01Measure)) (retentionPattern pi I) ≠ 0) :
    (ProbabilityTheory.cond (Measure.pi (fun _ : Fin N => mu.prod uniform01Measure))
      (retentionPattern pi I)).map (retainedSubsetView I) =
      Measure.pi (fun _ : I => retainedMeasure mu pi) := by
  classical
  let P := mu.prod uniform01Measure
  let cells (i : Fin N) : Set (Ω × ℝ) :=
    if i ∈ I then retentionEvent pi else (retentionEvent pi)ᶜ
  have hcells (i : Fin N) : MeasurableSet (cells i) := by
    dsimp [cells]
    split_ifs
    · exact retention_event_measurable hpi
    · exact (retention_event_measurable hpi).compl
  have hprod : (∏ i : Fin N, P (cells i)) ≠ 0 := by
    simpa only [retentionPattern, Measure.pi_pi] using hc
  have hpos (i : Fin N) : P (cells i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp hprod i (Finset.mem_univ i)
  let Q (i : Fin N) := ProbabilityTheory.cond P (cells i)
  letI (i : Fin N) : IsProbabilityMeasure (Q i) := ProbabilityTheory.cond_isProbabilityMeasure (hpos i)
  have hconditional : ProbabilityTheory.cond (Measure.pi (fun _ : Fin N => P))
      (retentionPattern pi I) = Measure.pi Q :=
    finite_product_conditional (fun _ => P) cells hcells
  change (ProbabilityTheory.cond (Measure.pi (fun _ : Fin N => P))
    (retentionPattern pi I)).map (retainedSubsetView I) = _
  rw [hconditional]
  have hselect : Measurable (fun sample : Fin N → Ω × ℝ => fun i : I => sample i) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply i.val)
  have hlocations : Measurable (fun sample : I → Ω × ℝ => fun i : I => (sample i).1) :=
    measurable_pi_lambda _ (fun i => measurable_fst.comp (measurable_pi_apply i))
  calc
    (Measure.pi Q).map (retainedSubsetView I) =
        ((Measure.pi Q).map (fun sample (i : I) => sample i)).map
          (fun sample (i : I) => (sample i).1) := by
      rw [Measure.map_map hlocations hselect]
      rfl
    _ = (Measure.pi (fun i : I => Q i)).map (fun sample (i : I) => (sample i).1) := by
      rw [finite_product_subset]
    _ = Measure.pi (fun i : I => (Q i).map Prod.fst) :=
      Measure.pi_map_pi (fun _ => measurable_fst.aemeasurable)
    _ = Measure.pi (fun _ : I => retainedMeasure mu pi) := by
      congr 1
      funext i
      dsimp [Q, cells]
      rw [if_pos i.property]
      exact detected_conditional_location mu hpi hInt hbounds hZ

theorem detected_count_atom {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] {pi : Ω → ℝ}
    (hpi : Measurable pi) (hInt : Integrable pi mu)
    (hbounds : ∀ x, pi x ∈ Set.Icc 0 1) (N : ℕ) (k : Fin (N+1)) :
    (membershipCountLaw (mu.prod uniform01Measure) N (retentionEvent pi)).real {k} =
      binomialMass N k (∫ x, pi x ∂mu) := by
  rw [membership_count_atom _ (retention_event_measurable hpi), Measure.real,
    detected_event_mass mu hpi hInt hbounds,
    ENNReal.toReal_ofReal (integral_nonneg (fun x => (hbounds x).1))]

end QuantyraNullCone
