import QuantyraNullCone.ThinningPoisson

namespace QuantyraNullCone

open MeasureTheory

theorem measure_eq_sum_nat_fibers {X : Type*} [MeasurableSpace X]
    (mu : Measure X) {c : X → ℕ} (hc : Measurable c) :
    mu = Measure.sum (fun n => mu.restrict (c ⁻¹' {n})) := by
  ext T hT
  rw [Measure.sum_apply _ hT]
  simp_rw [Measure.restrict_apply hT]
  have heq : (⋃ n : ℕ, T ∩ c ⁻¹' {n}) = T := by ext x; simp
  have hd : Pairwise (fun n m : ℕ => Disjoint (T ∩ c ⁻¹' {n}) (T ∩ c ⁻¹' {m})) := by
    intro n m hnm
    apply Set.disjoint_left.mpr
    rintro x ⟨_, hx⟩ ⟨_, hy⟩
    exact hnm (hx.symm.trans hy)
  rw [← measure_iUnion hd (fun n => hT.inter (hc (measurableSet_singleton n))), heq]

noncomputable def mixedRetainedObservable {Ω Y : Type*} (pi : Ω → ℝ) (fallback : Ω)
    (F : (n : ℕ) → (Fin n → Ω) → Y) (z : ℕ × (ℕ → Ω × ℝ)) : Y :=
  F (mixedRetainedCount pi z) (mixedRetainedView pi fallback (mixedRetainedCount pi z) z)

theorem mixed_retained_observable_measurable {Ω Y : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Y] {pi : Ω → ℝ} (hpi : Measurable pi)
    (fallback : Ω) (F : (n : ℕ) → (Fin n → Ω) → Y) (hF : ∀ n, Measurable (F n)) :
    Measurable (mixedRetainedObservable pi fallback F) := by
  have h : Measurable (fun z : ℕ × (ℕ × (ℕ → Ω × ℝ)) =>
      F z.1 (mixedRetainedView pi fallback z.1 z.2)) :=
    measurable_from_prod_countable_right (fun n =>
      (hF n).comp (mixed_retained_view_measurable hpi fallback n))
  exact h.comp ((mixed_retained_count_measurable hpi).prodMk measurable_id)

/-- Full distribution of every measurable count-dependent observable of the retained tuple.
Point-process and complete marked-order representations may use this after supplying
their measurable observation maps. -/
theorem mixed_retained_observable_law {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (q : Measure ℕ) [IsProbabilityMeasure q]
    {pi : Ω → ℝ} (hpi : Measurable pi) (hInt : Integrable pi mu)
    (hbounds : ∀ x, pi x ∈ Set.Icc 0 1) (hZ : 0 < ∫ x, pi x ∂mu)
    (fallback : Ω) (F : (n : ℕ) → (Fin n → Ω) → Y) (hF : ∀ n, Measurable (F n)) :
    (randomGeneratedLaw mu q).map
      (mixedRetainedObservable pi fallback F) =
        Measure.sum (fun n =>
          (randomGeneratedLaw mu q) {z | mixedRetainedCount pi z = n} •
            (Measure.pi (fun _ : Fin n => retainedMeasure mu pi)).map (F n)) := by
  let P := randomGeneratedLaw mu q
  have hdecomp := measure_eq_sum_nat_fibers P (mixed_retained_count_measurable hpi)
  change P.map _ = _
  rw [hdecomp, Measure.map_sum (mixed_retained_observable_measurable hpi fallback F hF).aemeasurable]
  apply Measure.sum_congr
  intro n
  have hE : MeasurableSet (mixedRetainedCount pi ⁻¹' {n}) :=
    (measurableSet_singleton n).preimage (mixed_retained_count_measurable hpi)
  calc
    _ = (P.restrict (mixedRetainedCount pi ⁻¹' {n})).map
        (F n ∘ mixedRetainedView pi fallback n) := by
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem hE] with z hz
      have hn : mixedRetainedCount pi z = n := hz
      exact congrArg (fun k => F k (mixedRetainedView pi fallback k z)) hn
    _ = ((P.restrict (mixedRetainedCount pi ⁻¹' {n})).map
        (mixedRetainedView pi fallback n)).map (F n) := by
      rw [Measure.map_map (hF n) (mixed_retained_view_measurable hpi fallback n)]
    _ = _ := by
      have hfiber : mixedRetainedCount pi ⁻¹' {n} = {z | mixedRetainedCount pi z = n} := by
        ext z
        simp
      rw [hfiber]
      dsimp only [P]
      rw [mixed_retained_submeasure_series mu q hpi hInt hbounds hZ n fallback,
        ← mixed_retained_count_mass mu q hpi hInt hbounds hZ n fallback,
        Measure.map_smul]

theorem poisson_retained_observable_law {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (kappa : NNReal)
    {pi : Ω → ℝ} (hpi : Measurable pi) (hInt : Integrable pi mu)
    (hbounds : ∀ x, pi x ∈ Set.Icc 0 1) (hZ : 0 < ∫ x, pi x ∂mu)
    (fallback : Ω) (F : (n : ℕ) → (Fin n → Ω) → Y) (hF : ∀ n, Measurable (F n)) :
    (randomGeneratedLaw mu (ProbabilityTheory.poissonMeasure kappa)).map
      (mixedRetainedObservable pi fallback F) =
        Measure.sum (fun n =>
          (ProbabilityTheory.poissonMeasure (retainedPoissonRate kappa mu pi)) {n} •
            (Measure.pi (fun _ : Fin n => retainedMeasure mu pi)).map (F n)) := by
  rw [mixed_retained_observable_law mu _ hpi hInt hbounds hZ fallback F hF]
  simp_rw [poisson_retained_count_mass mu kappa hpi hInt hbounds hZ _ fallback]

theorem mixed_retained_count_weights_sum {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (q : Measure ℕ) [IsProbabilityMeasure q]
    {pi : Ω → ℝ} (hpi : Measurable pi) :
    (∑' n, (randomGeneratedLaw mu q) {z | mixedRetainedCount pi z = n}) = 1 := by
  have h := congrArg (fun m : Measure (ℕ × (ℕ → Ω × ℝ)) => m Set.univ)
    (measure_eq_sum_nat_fibers (randomGeneratedLaw mu q) (mixed_retained_count_measurable hpi))
  simpa [Measure.sum_apply] using h.symm

theorem mixed_retained_observable_bound {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (q : Measure ℕ) [IsProbabilityMeasure q]
    {pi : Ω → ℝ} (hpi : Measurable pi) (hInt : Integrable pi mu)
    (hbounds : ∀ x, pi x ∈ Set.Icc 0 1) (hZ : 0 < ∫ x, pi x ∂mu)
    (fallback : Ω) (F : (n : ℕ) → (Fin n → Ω) → Y) (hF : ∀ n, Measurable (F n))
    {B : Set Y} (hB : MeasurableSet B) {epsilon : ENNReal}
    (hbound : ∀ n, ((Measure.pi (fun _ : Fin n => retainedMeasure mu pi)).map (F n)) B ≤ epsilon) :
    ((randomGeneratedLaw mu q).map (mixedRetainedObservable pi fallback F)) B ≤ epsilon := by
  rw [mixed_retained_observable_law mu q hpi hInt hbounds hZ fallback F hF,
    Measure.sum_apply _ hB]
  simp only [Measure.smul_apply, smul_eq_mul]
  calc
    _ ≤ ∑' n, (randomGeneratedLaw mu q) {z | mixedRetainedCount pi z = n} * epsilon :=
      ENNReal.tsum_le_tsum (fun n => mul_le_mul_right (hbound n) _)
    _ = _ := by rw [ENNReal.tsum_mul_right, mixed_retained_count_weights_sum mu q hpi, one_mul]

end QuantyraNullCone
