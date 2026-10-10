import QuantyraNullCone.TimeZeroAttainment
import QuantyraNullCone.TimeCouplingSupport

/-! Zero distortion is exactly measure-preserving time isomorphy for compact,
full-support, point-distinguishing time spaces. -/

namespace QuantyraNullCone
open MeasureTheory Set Filter Topology
noncomputable section

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
  [BorelSpace X] [BorelSpace Y] [CompactSpace X] [CompactSpace Y]

theorem IsZeroTimeCoupling.exists_homeomorph {mu : Measure X} {nu : Measure Y}
    [IsProbabilityMeasure mu] [Measure.IsOpenPosMeasure mu] [Measure.IsOpenPosMeasure nu]
    {tx : X → X → ℝ} {ty : Y → Y → ℝ} {pi : Measure (X × Y)}
    (h : IsZeroTimeCoupling mu nu tx ty pi)
    (hx : Continuous (Function.uncurry tx)) (hy : Continuous (Function.uncurry ty))
    (hdX : ∀ a b, (∀ z, tx z a = tx z b) → (∀ z, tx a z = tx b z) → a = b)
    (hdY : ∀ a b, (∀ z, ty z a = ty z b) → (∀ z, ty a z = ty b z) → a = b) :
    ∃ e : X ≃ₜ Y, MeasurePreserving e mu nu ∧ ∀ x y, tx x y = ty (e x) (e y) := by
  let R := pi.support
  letI : CompactSpace R := isCompact_iff_compactSpace.mp pi.isClosed_support.isCompact
  have ha : Function.Bijective (fun r : R => r.val.1) := by
    constructor
    · intro r s he
      apply Subtype.ext
      exact Prod.ext he (h.support_left_unique hx hy hdY r.property s.property he)
    · intro x
      obtain ⟨y, hy⟩ := h.toIsTimeCoupling.support_left_surjective x
      exact ⟨⟨(x, y), hy⟩, rfl⟩
  have hb : Function.Bijective (fun r : R => r.val.2) := by
    constructor
    · intro r s he
      apply Subtype.ext
      exact Prod.ext (h.support_right_unique hx hy hdX r.property s.property he) he
    · intro y
      obtain ⟨x, hx⟩ := h.toIsTimeCoupling.support_right_surjective y
      exact ⟨⟨(x, y), hx⟩, rfl⟩
  let a : R ≃ X := Equiv.ofBijective (fun r : R => r.val.1) ha
  let b : R ≃ Y := Equiv.ofBijective (fun r : R => r.val.2) hb
  let aH : R ≃ₜ X := Continuous.homeoOfEquivCompactToT2
    (f := a) (continuous_fst.comp continuous_subtype_val)
  let bH : R ≃ₜ Y := Continuous.homeoOfEquivCompactToT2
    (f := b) (continuous_snd.comp continuous_subtype_val)
  let e : X ≃ₜ Y := aH.symm.trans bH
  have hgraph (z : X × Y) (hz : z ∈ pi.support) : e z.1 = z.2 := by
    let r : R := ⟨z, hz⟩
    change bH (aH.symm (aH r)) = bH r
    rw [aH.symm_apply_apply]
  have hmem (x : X) : (x, e x) ∈ pi.support := by
    obtain ⟨y, hy⟩ := h.toIsTimeCoupling.support_left_surjective x
    have he := hgraph (x, y) hy
    simpa only [he] using hy
  refine ⟨e, ⟨e.continuous.measurable, ?_⟩, ?_⟩
  · rw [← h.toIsTimeCoupling.left, Measure.map_map e.continuous.measurable measurable_fst]
    calc
      pi.map (e ∘ Prod.fst) = pi.map Prod.snd := by
        apply Measure.map_congr
        filter_upwards [pi.support_mem_ae] with z hz
        exact hgraph z hz
      _ = nu := h.toIsTimeCoupling.right
  · intro x y
    exact h.time_eq_on_support hx hy (hmem x) (hmem y)

theorem timeDistortionLoss_eq_zero_iff_homeomorph (mu : Measure X) (nu : Measure Y)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] [Measure.IsOpenPosMeasure mu] [Measure.IsOpenPosMeasure nu]
    {tx : X → X → ℝ} {ty : Y → Y → ℝ}
    (hx : Continuous (Function.uncurry tx)) (hy : Continuous (Function.uncurry ty))
    (hdX : ∀ a b, (∀ z, tx z a = tx z b) → (∀ z, tx a z = tx b z) → a = b)
    (hdY : ∀ a b, (∀ z, ty z a = ty z b) → (∀ z, ty a z = ty b z) → a = b) :
    timeDistortionLoss mu nu tx ty = 0 ↔
      ∃ e : X ≃ₜ Y, MeasurePreserving e mu nu ∧ ∀ x y, tx x y = ty (e x) (e y) := by
  constructor
  · intro hz
    obtain ⟨pi, hpi⟩ := exists_zeroTimeCoupling_of_loss_zero mu nu hx hy hz
    exact hpi.exists_homeomorph hx hy hdX hdY
  · rintro ⟨e, he, ht⟩
    exact timeDistortionLoss_eq_zero_of_isometry he hx.measurable hy.measurable ht

#print axioms IsZeroTimeCoupling.exists_homeomorph
#print axioms timeDistortionLoss_eq_zero_iff_homeomorph

end
end QuantyraNullCone
