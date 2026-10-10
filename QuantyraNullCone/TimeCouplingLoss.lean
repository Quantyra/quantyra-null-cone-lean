import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.Tactic.Linarith

/-! The selected probability-of-time-distortion functional. Triangle and zero-isomorphy
are separate obligations; this module proves its elementary coupling properties. -/

namespace QuantyraNullCone
open MeasureTheory Set
noncomputable section

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

structure IsTimeCoupling (mu : Measure X) (nu : Measure Y) (pi : Measure (X × Y)) : Prop where
  left : pi.map Prod.fst = mu
  right : pi.map Prod.snd = nu

theorem IsTimeCoupling.isProbabilityMeasure {mu : Measure X} {nu : Measure Y}
    {pi : Measure (X × Y)} [IsProbabilityMeasure mu] (h : IsTimeCoupling mu nu pi) :
    IsProbabilityMeasure pi := by
  constructor
  have he := congrArg (fun m : Measure X => m univ) h.left
  simpa only [Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ, measure_univ] using he

theorem isTimeCoupling_prod (mu : Measure X) (nu : Measure Y)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] : IsTimeCoupling mu nu (mu.prod nu) := by
  constructor <;> simp

theorem IsTimeCoupling.swap {mu : Measure X} {nu : Measure Y} {pi : Measure (X × Y)}
    (h : IsTimeCoupling mu nu pi) : IsTimeCoupling nu mu (pi.map Prod.swap) := by
  constructor
  · rw [Measure.map_map measurable_fst measurable_swap]
    exact h.right
  · rw [Measure.map_map measurable_snd measurable_swap]
    exact h.left

def timeBadPairs (tx : X → X → ℝ) (ty : Y → Y → ℝ) (eps : ℝ) : Set ((X × Y) × (X × Y)) :=
  {z | eps < |tx z.1.1 z.2.1 - ty z.1.2 z.2.2|}

theorem measurableSet_timeBadPairs {tx : X → X → ℝ} {ty : Y → Y → ℝ}
    (hx : Measurable (Function.uncurry tx)) (hy : Measurable (Function.uncurry ty)) (eps : ℝ) :
    MeasurableSet (timeBadPairs tx ty eps) := by
  apply measurableSet_lt measurable_const
  simpa only [Real.norm_eq_abs] using ((hx.comp ((measurable_fst.comp measurable_fst).prodMk
      (measurable_fst.comp measurable_snd))).sub
    (hy.comp ((measurable_snd.comp measurable_fst).prodMk
      (measurable_snd.comp measurable_snd)))).norm

def TimeDistortionAdmissible (mu : Measure X) (nu : Measure Y)
    (tx : X → X → ℝ) (ty : Y → Y → ℝ) (eps : ℝ) : Prop :=
  0 < eps ∧ ∃ pi : Measure (X × Y), IsTimeCoupling mu nu pi ∧
    (pi.prod pi) (timeBadPairs tx ty eps) ≤ ENNReal.ofReal eps

def timeDistortionLoss (mu : Measure X) (nu : Measure Y) (tx : X → X → ℝ) (ty : Y → Y → ℝ) : ℝ :=
  sInf {eps | TimeDistortionAdmissible mu nu tx ty eps}

theorem timeDistortion_bddBelow (mu : Measure X) (nu : Measure Y) (tx : X → X → ℝ) (ty : Y → Y → ℝ) :
    BddBelow {eps | TimeDistortionAdmissible mu nu tx ty eps} :=
  ⟨0, fun _ he => he.1.le⟩

theorem timeDistortion_one_admissible (mu : Measure X) (nu : Measure Y)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] (tx : X → X → ℝ) (ty : Y → Y → ℝ) :
    TimeDistortionAdmissible mu nu tx ty 1 := by
  refine ⟨by norm_num, mu.prod nu, isTimeCoupling_prod mu nu, ?_⟩
  simpa only [ENNReal.ofReal_one] using (prob_le_one (μ := (mu.prod nu).prod (mu.prod nu)))

theorem timeDistortion_nonempty (mu : Measure X) (nu : Measure Y)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] (tx : X → X → ℝ) (ty : Y → Y → ℝ) :
    {eps | TimeDistortionAdmissible mu nu tx ty eps}.Nonempty :=
  ⟨1, timeDistortion_one_admissible mu nu tx ty⟩

theorem timeDistortionLoss_nonneg (mu : Measure X) (nu : Measure Y)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] (tx : X → X → ℝ) (ty : Y → Y → ℝ) :
    0 ≤ timeDistortionLoss mu nu tx ty :=
  le_csInf (timeDistortion_nonempty mu nu tx ty) (fun _ he => he.1.le)

theorem timeDistortionLoss_le_of_admissible {mu : Measure X} {nu : Measure Y}
    {tx : X → X → ℝ} {ty : Y → Y → ℝ} {eps : ℝ}
    (h : TimeDistortionAdmissible mu nu tx ty eps) : timeDistortionLoss mu nu tx ty ≤ eps :=
  csInf_le (timeDistortion_bddBelow mu nu tx ty) h

theorem timeDistortionLoss_le_one (mu : Measure X) (nu : Measure Y)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] (tx : X → X → ℝ) (ty : Y → Y → ℝ) :
    timeDistortionLoss mu nu tx ty ≤ 1 :=
  timeDistortionLoss_le_of_admissible (timeDistortion_one_admissible mu nu tx ty)

theorem timeBadPairs_swap_measure {tx : X → X → ℝ} {ty : Y → Y → ℝ}
    (hx : Measurable (Function.uncurry tx)) (hy : Measurable (Function.uncurry ty))
    (pi : Measure (X × Y)) [SFinite pi] (eps : ℝ) :
    ((pi.map Prod.swap).prod (pi.map Prod.swap)) (timeBadPairs ty tx eps) =
      (pi.prod pi) (timeBadPairs tx ty eps) := by
  rw [Measure.map_prod_map pi pi measurable_swap measurable_swap,
    Measure.map_apply (measurable_swap.prodMap measurable_swap) (measurableSet_timeBadPairs hy hx eps)]
  congr 1
  ext z
  change (eps < |ty z.1.2 z.2.2 - tx z.1.1 z.2.1|) ↔ _
  rw [abs_sub_comm]
  rfl

theorem timeDistortionAdmissible_swap {mu : Measure X} {nu : Measure Y}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] {tx : X → X → ℝ} {ty : Y → Y → ℝ}
    (hx : Measurable (Function.uncurry tx)) (hy : Measurable (Function.uncurry ty)) {eps : ℝ} :
    TimeDistortionAdmissible mu nu tx ty eps ↔ TimeDistortionAdmissible nu mu ty tx eps := by
  constructor
  · rintro ⟨he, pi, hpi, hbad⟩
    letI := hpi.isProbabilityMeasure
    exact ⟨he, pi.map Prod.swap, hpi.swap, (timeBadPairs_swap_measure hx hy pi eps).trans_le hbad⟩
  · rintro ⟨he, pi, hpi, hbad⟩
    letI := hpi.isProbabilityMeasure
    exact ⟨he, pi.map Prod.swap, hpi.swap, (timeBadPairs_swap_measure hy hx pi eps).trans_le hbad⟩

theorem timeDistortionLoss_symm (mu : Measure X) (nu : Measure Y)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] {tx : X → X → ℝ} {ty : Y → Y → ℝ}
    (hx : Measurable (Function.uncurry tx)) (hy : Measurable (Function.uncurry ty)) :
    timeDistortionLoss mu nu tx ty = timeDistortionLoss nu mu ty tx := by
  unfold timeDistortionLoss
  congr 1
  ext eps
  exact timeDistortionAdmissible_swap hx hy

def graphTimeCoupling (mu : Measure X) (f : X → Y) : Measure (X × Y) :=
  mu.map (fun x => (x, f x))

theorem isTimeCoupling_graph (mu : Measure X) {f : X → Y} (hf : Measurable f) :
    IsTimeCoupling mu (mu.map f) (graphTimeCoupling mu f) := by
  have hg : Measurable (fun x => (x, f x)) := measurable_id.prodMk hf
  constructor
  · rw [graphTimeCoupling, Measure.map_map measurable_fst hg]
    exact Measure.map_id
  · rw [graphTimeCoupling, Measure.map_map measurable_snd hg]
    rfl

theorem isTimeCoupling_graph_of_preserving {mu : Measure X} {nu : Measure Y} {f : X → Y}
    (hf : MeasurePreserving f mu nu) : IsTimeCoupling mu nu (graphTimeCoupling mu f) := by
  rw [← hf.map_eq]
  exact isTimeCoupling_graph mu hf.measurable

theorem graphTimeCoupling_bad_eq_zero {mu : Measure X} [SFinite mu] {f : X → Y}
    (hf : Measurable f) {tx : X → X → ℝ} {ty : Y → Y → ℝ}
    (hx : Measurable (Function.uncurry tx)) (hy : Measurable (Function.uncurry ty))
    {delta eps : ℝ} (he : delta < eps) (hb : ∀ x y, |tx x y - ty (f x) (f y)| ≤ delta) :
    ((graphTimeCoupling mu f).prod (graphTimeCoupling mu f)) (timeBadPairs tx ty eps) = 0 := by
  have hg : Measurable (fun x => (x, f x)) := measurable_id.prodMk hf
  rw [graphTimeCoupling, Measure.map_prod_map mu mu hg hg,
    Measure.map_apply (hg.prodMap hg)
      (measurableSet_timeBadPairs hx hy eps)]
  have hempty : (Prod.map (fun x => (x, f x)) (fun x => (x, f x))) ⁻¹'
      timeBadPairs tx ty eps = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact (not_lt_of_ge ((hb z.1 z.2).trans he.le)) hz
  rw [hempty, measure_empty]

/-- A measure-preserving transport with uniform time error controls the actual infimum. -/
theorem timeDistortionLoss_le_of_transport {mu : Measure X} {nu : Measure Y}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] {f : X → Y}
    (hf : MeasurePreserving f mu nu) {tx : X → X → ℝ} {ty : Y → Y → ℝ}
    (hx : Measurable (Function.uncurry tx)) (hy : Measurable (Function.uncurry ty))
    {delta : ℝ} (hd : 0 ≤ delta) (hb : ∀ x y, |tx x y - ty (f x) (f y)| ≤ delta) :
    timeDistortionLoss mu nu tx ty ≤ delta := by
  by_contra hn
  have hlt : delta < timeDistortionLoss mu nu tx ty := lt_of_not_ge hn
  let eps := (delta + timeDistortionLoss mu nu tx ty) / 2
  have he : delta < eps := by dsimp [eps]; linarith
  have hepos : 0 < eps := hd.trans_lt he
  have had : TimeDistortionAdmissible mu nu tx ty eps :=
    ⟨hepos, graphTimeCoupling mu f, isTimeCoupling_graph_of_preserving hf, by
      rw [graphTimeCoupling_bad_eq_zero hf.measurable hx hy he hb]
      exact bot_le⟩
  have h := timeDistortionLoss_le_of_admissible had
  dsimp [eps] at h
  linarith

theorem timeDistortionLoss_eq_zero_of_isometry {mu : Measure X} {nu : Measure Y}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] {f : X → Y}
    (hf : MeasurePreserving f mu nu) {tx : X → X → ℝ} {ty : Y → Y → ℝ}
    (hx : Measurable (Function.uncurry tx)) (hy : Measurable (Function.uncurry ty))
    (ht : ∀ x y, tx x y = ty (f x) (f y)) : timeDistortionLoss mu nu tx ty = 0 := by
  apply le_antisymm _ (timeDistortionLoss_nonneg mu nu tx ty)
  apply timeDistortionLoss_le_of_transport hf hx hy le_rfl
  intro x y
  rw [ht, sub_self, abs_zero]

theorem timeDistortionLoss_self (mu : Measure X) [IsProbabilityMeasure mu] {tx : X → X → ℝ}
    (hx : Measurable (Function.uncurry tx)) : timeDistortionLoss mu mu tx tx = 0 :=
  timeDistortionLoss_eq_zero_of_isometry ⟨measurable_id, Measure.map_id⟩ hx hx (fun _ _ => rfl)

#print axioms IsTimeCoupling.isProbabilityMeasure
#print axioms isTimeCoupling_prod
#print axioms IsTimeCoupling.swap
#print axioms measurableSet_timeBadPairs
#print axioms timeDistortion_bddBelow
#print axioms timeDistortion_one_admissible
#print axioms timeDistortion_nonempty
#print axioms timeDistortionLoss_nonneg
#print axioms timeDistortionLoss_le_of_admissible
#print axioms timeDistortionLoss_le_one
#print axioms timeBadPairs_swap_measure
#print axioms timeDistortionAdmissible_swap
#print axioms timeDistortionLoss_symm
#print axioms isTimeCoupling_graph
#print axioms isTimeCoupling_graph_of_preserving
#print axioms graphTimeCoupling_bad_eq_zero
#print axioms timeDistortionLoss_le_of_transport
#print axioms timeDistortionLoss_eq_zero_of_isometry
#print axioms timeDistortionLoss_self

end
end QuantyraNullCone
