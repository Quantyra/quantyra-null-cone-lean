import QuantyraNullCone.BinomialGeometry
import Mathlib.Probability.ConditionalProbability

namespace QuantyraNullCone

open MeasureTheory

def retentionEvent {Ω : Type*} (pi : Ω → ℝ) : Set (Ω × ℝ) :=
  {z | z.2 < pi z.1}

theorem retention_event_measurable {Ω : Type*} [MeasurableSpace Ω]
    {pi : Ω → ℝ} (hpi : Measurable pi) : MeasurableSet (retentionEvent pi) :=
  measurableSet_lt measurable_snd (hpi.comp measurable_fst)

theorem retention_uniform_cell {p : ℝ} (hp : p ∈ Set.Icc 0 1) :
    uniform01Measure (Set.Iio p) = ENNReal.ofReal p := by
  have hset : Set.Iio p ∩ Set.Ioc (0 : ℝ) 1 = Set.Ioo 0 p := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioc, Set.mem_Ioo]
    constructor
    · rintro ⟨hxp, hx0, _⟩
      exact ⟨hx0, hxp⟩
    · rintro ⟨hx0, hxp⟩
      exact ⟨hxp, hx0, hxp.le.trans hp.2⟩
  rw [uniform01Measure, Measure.restrict_apply measurableSet_Iio, hset,
    Real.volume_Ioo, sub_zero]

/-- The actual independent uniform-mark channel, before normalization. -/
theorem detected_submeasure {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) {pi : Ω → ℝ} (hpi : Measurable pi)
    (hbounds : ∀ x, pi x ∈ Set.Icc 0 1) :
    ((mu.prod uniform01Measure).restrict (retentionEvent pi)).map Prod.fst =
      mu.withDensity (fun x => ENNReal.ofReal (pi x)) := by
  ext S hS
  rw [Measure.map_apply measurable_fst hS,
    Measure.restrict_apply (hS.preimage measurable_fst),
    Measure.prod_apply ((hS.preimage measurable_fst).inter (retention_event_measurable hpi)),
    withDensity_apply _ hS]
  have hcell (x : Ω) :
      uniform01Measure (Prod.mk x ⁻¹' (Prod.fst ⁻¹' S ∩ retentionEvent pi)) =
        S.indicator (fun y => ENNReal.ofReal (pi y)) x := by
    by_cases hx : x ∈ S
    · have heq : Prod.mk x ⁻¹' (Prod.fst ⁻¹' S ∩ retentionEvent pi) = Set.Iio (pi x) := by
        ext u
        simp [retentionEvent, hx]
      rw [heq, retention_uniform_cell (hbounds x)]
      simp [hx]
    · have heq : Prod.mk x ⁻¹' (Prod.fst ⁻¹' S ∩ retentionEvent pi) = ∅ := by
        ext u
        simp [hx]
      simp [heq, hx]
  simp_rw [hcell]
  exact lintegral_indicator hS _

theorem detected_event_mass {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) {pi : Ω → ℝ} (hpi : Measurable pi) (hInt : Integrable pi mu)
    (hbounds : ∀ x, pi x ∈ Set.Icc 0 1) :
    (mu.prod uniform01Measure) (retentionEvent pi) = ENNReal.ofReal (∫ x, pi x ∂mu) := by
  have h := congrArg (fun m : Measure Ω => m Set.univ) (detected_submeasure mu hpi hbounds)
  simp only [Measure.map_apply measurable_fst MeasurableSet.univ,
    Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
  rw [← ofReal_integral_eq_lintegral_ofReal hInt (ae_of_all _ (fun x => (hbounds x).1))] at h
  exact h

/-- Conditioning a generated event on actual acceptance gives the retained law. -/
theorem detected_conditional_location {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) {pi : Ω → ℝ} (hpi : Measurable pi) (hInt : Integrable pi mu)
    (hbounds : ∀ x, pi x ∈ Set.Icc 0 1) (hZ : 0 < ∫ x, pi x ∂mu) :
    (ProbabilityTheory.cond (mu.prod uniform01Measure) (retentionEvent pi)).map Prod.fst =
      retainedMeasure mu pi := by
  rw [ProbabilityTheory.cond, Measure.map_smul, detected_submeasure mu hpi hbounds,
    detected_event_mass mu hpi hInt hbounds]
  calc
    _ = mu.withDensity (fun x => (ENNReal.ofReal (∫ y, pi y ∂mu))⁻¹ *
        ENNReal.ofReal (pi x)) := (withDensity_smul _ hpi.ennreal_ofReal).symm
    _ = retainedMeasure mu pi := by
      apply congrArg (fun f : Ω → ENNReal => mu.withDensity f)
      funext x
      change (ENNReal.ofReal (∫ y, pi y ∂mu))⁻¹ * ENNReal.ofReal (pi x) =
        ENNReal.ofReal (pi x / ∫ y, pi y ∂mu)
      rw [ENNReal.ofReal_div_of_pos hZ, div_eq_mul_inv, mul_comm]

theorem retained_probability_of_channel {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] {pi : Ω → ℝ}
    (hpi : Measurable pi) (hInt : Integrable pi mu)
    (hbounds : ∀ x, pi x ∈ Set.Icc 0 1) (hZ : 0 < ∫ x, pi x ∂mu) :
    IsProbabilityMeasure (retainedMeasure mu pi) := by
  have hc : (mu.prod uniform01Measure) (retentionEvent pi) ≠ 0 := by
    rw [detected_event_mass mu hpi hInt hbounds]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hZ)
  letI := ProbabilityTheory.cond_isProbabilityMeasure hc
  rw [← detected_conditional_location mu hpi hInt hbounds hZ]
  exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable

/-- Finite product conditioning factors, including zero-mass cells. -/
theorem finite_product_conditional {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (mu : ∀ i, Measure (X i)) [∀ i, IsFiniteMeasure (mu i)]
    (S : ∀ i, Set (X i)) (hS : ∀ i, MeasurableSet (S i)) :
    ProbabilityTheory.cond (Measure.pi mu) (Set.univ.pi S) =
      Measure.pi (fun i => ProbabilityTheory.cond (mu i) (S i)) := by
  classical
  apply (Measure.pi_eq (fun T hT => ?_)).symm
  rw [ProbabilityTheory.cond_apply (MeasurableSet.univ_pi hS),
    ← Set.pi_inter_distrib, Measure.pi_pi, Measure.pi_pi]
  simp_rw [ProbabilityTheory.cond_apply (hS _)]
  rw [ENNReal.prod_inv_distrib (fun i _ j _ _ => Or.inr (measure_ne_top (mu j) (S j))),
    ← Finset.prod_mul_distrib]

/-- Extracting a fixed subset of independent coordinates preserves its product law. -/
theorem finite_product_subset {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (mu : ι → Measure Ω) [∀ i, IsProbabilityMeasure (mu i)] (I : Finset ι) :
    (Measure.pi mu).map (fun x (i : I) => x i) = Measure.pi (fun i : I => mu i) := by
  classical
  have h := (measurePreserving_fst.comp
    (measurePreserving_piEquivPiSubtypeProd mu (fun i => i ∈ I))).map_eq
  convert h using 1
  congr 1
  exact Subsingleton.elim _ _

end QuantyraNullCone
