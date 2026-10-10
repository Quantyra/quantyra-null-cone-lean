import QuantyraNullCone.ThinningTerminalPatterns

namespace QuantyraNullCone

open MeasureTheory

theorem stopped_retained_submeasure {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] {pi : Ω → ℝ}
    (hpi : Measurable pi) (hInt : Integrable pi mu)
    (hbounds : ∀ x, pi x ∈ Set.Icc 0 1) (hZ : 0 < ∫ x, pi x ∂mu)
    (N n : ℕ) (fallback : Ω) :
    ((generatedStreamLaw mu).restrict (retainedStopPrefix pi n ⁻¹' {N})).map
        (stoppedRetainedView pi fallback n) =
      (Measure.pi (fun _ : Fin N => mu.prod uniform01Measure)) (retainedTerminalEvent pi n N) •
        Measure.pi (fun _ : Fin n => retainedMeasure mu pi) := by
  let P := generatedStreamLaw mu
  let H : Set (ℕ → Ω × ℝ) := {sample | retainedCountHit pi n sample}
  have hhit : ∀ᵐ sample ∂P, sample ∈ H := by
    filter_upwards [ae_stream_retained_count_surjective mu hpi hInt hbounds hZ] with sample hs
    exact hs n
  have hfull : P.restrict H = P := Measure.restrict_eq_self_of_ae_mem hhit
  have hE : MeasurableSet (retainedStopPrefix pi n ⁻¹' {N}) :=
    (measurableSet_singleton N).preimage (retained_stop_prefix_measurable hpi n)
  have hsets : (retainedStopPrefix pi n ⁻¹' {N}) ∩ H =
      finitePrefix N ⁻¹' retainedTerminalEvent pi n N := by
    ext sample
    exact (retained_terminal_event_iff pi n N sample).symm
  have hr : P.restrict (retainedStopPrefix pi n ⁻¹' {N}) =
      P.restrict (finitePrefix N ⁻¹' retainedTerminalEvent pi n N) := by
    calc
      _ = (P.restrict H).restrict (retainedStopPrefix pi n ⁻¹' {N}) := by rw [hfull]
      _ = _ := by rw [Measure.restrict_restrict hE, hsets]
  change (P.restrict _).map _ = _
  calc
    _ = (P.restrict (retainedStopPrefix pi n ⁻¹' {N})).map
        (retainedOrderedView pi fallback n ∘ finitePrefix N) := by
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem hE] with sample hs
      have hs' : retainedStopPrefix pi n sample = N := hs
      exact congrArg (fun k => retainedOrderedView pi fallback n (finitePrefix k sample)) hs'
    _ = _ := by
      rw [hr]
      exact stream_terminal_pattern_submeasure mu hpi hInt hbounds hZ N n fallback

theorem stopped_retained_conditional_law {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] {pi : Ω → ℝ}
    (hpi : Measurable pi) (hInt : Integrable pi mu)
    (hbounds : ∀ x, pi x ∈ Set.Icc 0 1) (hZ : 0 < ∫ x, pi x ∂mu)
    (N n : ℕ) (fallback : Ω)
    (hc : (generatedStreamLaw mu) (retainedStopPrefix pi n ⁻¹' {N}) ≠ 0) :
    (ProbabilityTheory.cond (generatedStreamLaw mu) (retainedStopPrefix pi n ⁻¹' {N})).map
      (stoppedRetainedView pi fallback n) = Measure.pi (fun _ : Fin n => retainedMeasure mu pi) := by
  letI := retained_probability_of_channel mu hpi hInt hbounds hZ
  have h := stopped_retained_submeasure mu hpi hInt hbounds hZ N n fallback
  have hmass : (Measure.pi (fun _ : Fin N => mu.prod uniform01Measure))
      (retainedTerminalEvent pi n N) = (generatedStreamLaw mu) (retainedStopPrefix pi n ⁻¹' {N}) := by
    have heq := congrArg (fun m : Measure (Fin n → Ω) => m Set.univ) h
    simpa only [Measure.map_apply (stopped_retained_view_measurable hpi fallback n) MeasurableSet.univ,
      Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      Measure.smul_apply, smul_eq_mul, measure_univ, mul_one] using heq.symm
  rw [ProbabilityTheory.cond, Measure.map_smul, h, hmass, smul_smul,
    ENNReal.inv_mul_cancel hc (measure_ne_top _ _), one_smul]

/-- The first n actual accepted locations have the normalized retained iid law.
Termination follows from positive mean retention; it is not an extra assumption. -/
theorem stopped_retained_iid_law {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] {pi : Ω → ℝ}
    (hpi : Measurable pi) (hInt : Integrable pi mu)
    (hbounds : ∀ x, pi x ∈ Set.Icc 0 1) (hZ : 0 < ∫ x, pi x ∂mu)
    (n : ℕ) (fallback : Ω) :
    (generatedStreamLaw mu).map (stoppedRetainedView pi fallback n) =
      Measure.pi (fun _ : Fin n => retainedMeasure mu pi) := by
  letI := retained_probability_of_channel mu hpi hInt hbounds hZ
  have hview := stopped_retained_view_measurable hpi fallback n
  have hsum : (generatedStreamLaw mu).map (stoppedRetainedView pi fallback n) =
      Measure.sum (fun N =>
        (Measure.pi (fun _ : Fin N => mu.prod uniform01Measure)) (retainedTerminalEvent pi n N) •
          Measure.pi (fun _ : Fin n => retainedMeasure mu pi)) := by
    rw [measure_eq_sum_nat_fibers (generatedStreamLaw mu) (retained_stop_prefix_measurable hpi n),
      Measure.map_sum hview.aemeasurable]
    apply Measure.sum_congr
    intro N
    exact stopped_retained_submeasure mu hpi hInt hbounds hZ N n fallback
  have hmass : (∑' N, (Measure.pi (fun _ : Fin N => mu.prod uniform01Measure))
      (retainedTerminalEvent pi n N)) = 1 := by
    have h := congrArg (fun m : Measure (Fin n → Ω) => m Set.univ) hsum
    simpa only [Measure.map_apply hview MeasurableSet.univ, Set.preimage_univ, measure_univ,
      Measure.sum_apply _ MeasurableSet.univ, Measure.smul_apply, smul_eq_mul, mul_one] using h.symm
  ext S hS
  rw [hsum, Measure.sum_apply _ hS]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.tsum_mul_right, hmass, one_mul]

theorem stopped_retained_observable_law {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    (mu : Measure Ω) [IsProbabilityMeasure mu] {pi : Ω → ℝ}
    (hpi : Measurable pi) (hInt : Integrable pi mu)
    (hbounds : ∀ x, pi x ∈ Set.Icc 0 1) (hZ : 0 < ∫ x, pi x ∂mu)
    (n : ℕ) (fallback : Ω) {F : (Fin n → Ω) → Y} (hF : Measurable F) :
    (generatedStreamLaw mu).map (F ∘ stoppedRetainedView pi fallback n) =
      (Measure.pi (fun _ : Fin n => retainedMeasure mu pi)).map F := by
  rw [← Measure.map_map hF (stopped_retained_view_measurable hpi fallback n),
    stopped_retained_iid_law mu hpi hInt hbounds hZ n fallback]

end QuantyraNullCone
