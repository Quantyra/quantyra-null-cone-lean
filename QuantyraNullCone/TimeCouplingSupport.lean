import QuantyraNullCone.TimeZeroCoupling
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.Homeomorph.Lemmas

/-! Full support and continuity turn a zero coupling into a closed, everywhere-defined relation. -/

namespace QuantyraNullCone
open MeasureTheory Set Filter Topology
noncomputable section

theorem time_support_prod_mem {A : Type*} [TopologicalSpace A] [MeasurableSpace A]
    (pi : Measure A) [SFinite pi] {x y : A} (hx : x ∈ pi.support) (hy : y ∈ pi.support) :
    (x, y) ∈ (pi.prod pi).support := by
  apply (Measure.mem_support_iff_forall _).mpr
  intro U hU
  obtain ⟨s, hs, t, ht, hst⟩ := mem_nhds_prod_iff.mp hU
  have hp := (Measure.mem_support_iff_forall x).mp hx s hs
  have hq := (Measure.mem_support_iff_forall y).mp hy t ht
  calc
    0 < pi s * pi t := ENNReal.mul_pos hp.ne' hq.ne'
    _ = (pi.prod pi) (s ×ˢ t) := (Measure.prod_prod _ _).symm
    _ ≤ (pi.prod pi) U := measure_mono hst

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
  [BorelSpace X] [BorelSpace Y] [CompactSpace X] [CompactSpace Y]

omit [BorelSpace Y] in
theorem IsTimeCoupling.support_left_surjective {mu : Measure X} {nu : Measure Y}
    [Measure.IsOpenPosMeasure mu] {pi : Measure (X × Y)} (h : IsTimeCoupling mu nu pi) (x : X) :
    ∃ y : Y, (x, y) ∈ pi.support := by
  by_contra hn
  have hx : x ∉ Prod.fst '' pi.support := by
    rintro ⟨⟨a, b⟩, hab, rfl⟩
    exact hn ⟨b, hab⟩
  have hc : IsClosed (Prod.fst '' pi.support) :=
    (pi.isClosed_support.isCompact.image continuous_fst).isClosed
  have hp := hc.isOpen_compl.measure_pos mu ⟨x, hx⟩
  rw [← h.left, Measure.map_apply measurable_fst hc.isOpen_compl.measurableSet] at hp
  obtain ⟨z, hz, hs⟩ := pi.nonempty_inter_support_of_pos hp
  exact hz ⟨z, hs, rfl⟩

omit [BorelSpace X] in
theorem IsTimeCoupling.support_right_surjective {mu : Measure X} {nu : Measure Y}
    [Measure.IsOpenPosMeasure nu] {pi : Measure (X × Y)} (h : IsTimeCoupling mu nu pi) (y : Y) :
    ∃ x : X, (x, y) ∈ pi.support := by
  by_contra hn
  have hy : y ∉ Prod.snd '' pi.support := by
    rintro ⟨⟨a, b⟩, hab, rfl⟩
    exact hn ⟨a, hab⟩
  have hc : IsClosed (Prod.snd '' pi.support) :=
    (pi.isClosed_support.isCompact.image continuous_snd).isClosed
  have hp := hc.isOpen_compl.measure_pos nu ⟨y, hy⟩
  rw [← h.right, Measure.map_apply measurable_snd hc.isOpen_compl.measurableSet] at hp
  obtain ⟨z, hz, hs⟩ := pi.nonempty_inter_support_of_pos hp
  exact hz ⟨z, hs, rfl⟩

omit [BorelSpace X] [BorelSpace Y] [CompactSpace X] [CompactSpace Y] in
theorem IsZeroTimeCoupling.time_eq_on_support {mu : Measure X} {nu : Measure Y}
    [IsProbabilityMeasure mu] {tx : X → X → ℝ} {ty : Y → Y → ℝ} {pi : Measure (X × Y)}
    (h : IsZeroTimeCoupling mu nu tx ty pi)
    (hx : Continuous (Function.uncurry tx)) (hy : Continuous (Function.uncurry ty))
    {p q : X × Y} (hp : p ∈ pi.support) (hq : q ∈ pi.support) : tx p.1 q.1 = ty p.2 q.2 := by
  letI := h.toIsTimeCoupling.isProbabilityMeasure
  have hc : IsClosed {z : (X × Y) × (X × Y) | tx z.1.1 z.2.1 = ty z.1.2 z.2.2} :=
    isClosed_eq (hx.comp ((continuous_fst.comp continuous_fst).prodMk
      (continuous_fst.comp continuous_snd)))
      (hy.comp ((continuous_snd.comp continuous_fst).prodMk (continuous_snd.comp continuous_snd)))
  exact (Measure.support_subset_of_isClosed hc h.time_eq) (time_support_prod_mem pi hp hq)

omit [BorelSpace X] in
theorem IsZeroTimeCoupling.support_left_unique {mu : Measure X} {nu : Measure Y}
    [IsProbabilityMeasure mu] [Measure.IsOpenPosMeasure nu]
    {tx : X → X → ℝ} {ty : Y → Y → ℝ} {pi : Measure (X × Y)}
    (h : IsZeroTimeCoupling mu nu tx ty pi)
    (hx : Continuous (Function.uncurry tx)) (hy : Continuous (Function.uncurry ty))
    (hd : ∀ a b, (∀ z, ty z a = ty z b) → (∀ z, ty a z = ty b z) → a = b)
    {p q : X × Y} (hp : p ∈ pi.support) (hq : q ∈ pi.support) (he : p.1 = q.1) : p.2 = q.2 := by
  apply hd
  · intro z
    obtain ⟨u, hu⟩ := h.toIsTimeCoupling.support_right_surjective z
    have h1 := h.time_eq_on_support hx hy hu hp
    have h2 := h.time_eq_on_support hx hy hu hq
    simpa only [he] using h1.symm.trans (by simpa only [he] using h2)
  · intro z
    obtain ⟨u, hu⟩ := h.toIsTimeCoupling.support_right_surjective z
    have h1 := h.time_eq_on_support hx hy hp hu
    have h2 := h.time_eq_on_support hx hy hq hu
    simpa only [he] using h1.symm.trans (by simpa only [he] using h2)

omit [BorelSpace Y] in
theorem IsZeroTimeCoupling.support_right_unique {mu : Measure X} {nu : Measure Y}
    [IsProbabilityMeasure mu] [Measure.IsOpenPosMeasure mu]
    {tx : X → X → ℝ} {ty : Y → Y → ℝ} {pi : Measure (X × Y)}
    (h : IsZeroTimeCoupling mu nu tx ty pi)
    (hx : Continuous (Function.uncurry tx)) (hy : Continuous (Function.uncurry ty))
    (hd : ∀ a b, (∀ z, tx z a = tx z b) → (∀ z, tx a z = tx b z) → a = b)
    {p q : X × Y} (hp : p ∈ pi.support) (hq : q ∈ pi.support) (he : p.2 = q.2) : p.1 = q.1 := by
  apply hd
  · intro z
    obtain ⟨u, hu⟩ := h.toIsTimeCoupling.support_left_surjective z
    have h1 := h.time_eq_on_support hx hy hu hp
    have h2 := h.time_eq_on_support hx hy hu hq
    simpa only [he] using h1.trans (by simpa only [he] using h2.symm)
  · intro z
    obtain ⟨u, hu⟩ := h.toIsTimeCoupling.support_left_surjective z
    have h1 := h.time_eq_on_support hx hy hp hu
    have h2 := h.time_eq_on_support hx hy hq hu
    simpa only [he] using h1.trans (by simpa only [he] using h2.symm)

#print axioms time_support_prod_mem
#print axioms IsTimeCoupling.support_left_surjective
#print axioms IsTimeCoupling.support_right_surjective
#print axioms IsZeroTimeCoupling.time_eq_on_support
#print axioms IsZeroTimeCoupling.support_left_unique
#print axioms IsZeroTimeCoupling.support_right_unique

end
end QuantyraNullCone
