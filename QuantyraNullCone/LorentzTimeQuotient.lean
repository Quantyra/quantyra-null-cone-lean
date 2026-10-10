import QuantyraNullCone.LorentzTimeContinuity
import QuantyraNullCone.LorentzConcatenation
import Mathlib.Topology.ContinuousMap.Compact

/-! The compact metric realization of the closed diamond modulo equal time profiles.
The projection collapses exactly the waist circle. The metric here supplies the quotient
topology; it is not the coupling-distortion loss between measured geometries. -/

namespace QuantyraNullCone
open Set Topology
noncomputable section

abbrev ClosedLorentzPoint3 := {p : LorentzPoint3 // p ∈ closedLorentzDiamond3}

instance closedLorentzPoint3CompactSpace : CompactSpace ClosedLorentzPoint3 :=
  isCompact_iff_compactSpace.mp isCompact_closedLorentzDiamond3

variable {w : LorentzPoint3 → ℝ} {lo hi : ℝ} (hw : InTimeWeightClass3 w lo hi)

def closedTimeMap3 : C(ClosedLorentzPoint3 × ClosedLorentzPoint3, ℝ) where
  toFun z := weightedTimeSeparation3 w z.1.val z.2.val
  continuous_toFun := (weighted_time_continuousOn3 hw).comp_continuous
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)) (fun z => ⟨z.1.property, z.2.property⟩)

def reversedClosedTimeMap3 : C(ClosedLorentzPoint3 × ClosedLorentzPoint3, ℝ) :=
  (closedTimeMap3 hw).comp ⟨Prod.swap, by fun_prop⟩

/-- Outgoing and incoming profiles, in that order. -/
def timeProfileMap3 (p : ClosedLorentzPoint3) :
    C(ClosedLorentzPoint3, ℝ) × C(ClosedLorentzPoint3, ℝ) :=
  ((closedTimeMap3 hw).curry p, (reversedClosedTimeMap3 hw).curry p)

theorem continuous_timeProfileMap3 : Continuous (timeProfileMap3 hw) :=
  (closedTimeMap3 hw).curry.continuous.prodMk (reversedClosedTimeMap3 hw).curry.continuous

theorem timeProfileMap3_outgoing (p q : ClosedLorentzPoint3) :
    (timeProfileMap3 hw p).1 q = weightedTimeSeparation3 w p.val q.val := rfl

theorem timeProfileMap3_incoming (p q : ClosedLorentzPoint3) :
    (timeProfileMap3 hw p).2 q = weightedTimeSeparation3 w q.val p.val := rfl

theorem timeProfileMap3_eq_iff (p q : ClosedLorentzPoint3) :
    timeProfileMap3 hw p = timeProfileMap3 hw q ↔ SameTimeProfile3 w p.val q.val := by
  constructor
  · intro h
    exact ⟨fun z hz => congrArg (fun f => f.2 (⟨z, hz⟩ : ClosedLorentzPoint3)) h,
      fun z hz => congrArg (fun f => f.1 (⟨z, hz⟩ : ClosedLorentzPoint3)) h⟩
  · intro h
    apply Prod.ext
    · exact ContinuousMap.ext (fun z => h.2 z.val z.property)
    · exact ContinuousMap.ext (fun z => h.1 z.val z.property)

abbrev TimeProfileSpace3 := Set.range (timeProfileMap3 hw)

instance timeProfileSpace3CompactSpace : CompactSpace (TimeProfileSpace3 hw) :=
  isCompact_iff_compactSpace.mp (isCompact_range (continuous_timeProfileMap3 hw))

theorem timeProfileSpace3_isCompact : IsCompact (Set.univ : Set (TimeProfileSpace3 hw)) :=
  isCompact_univ

def timeProfileProjection3 (p : ClosedLorentzPoint3) : TimeProfileSpace3 hw :=
  ⟨timeProfileMap3 hw p, ⟨p, rfl⟩⟩

theorem continuous_timeProfileProjection3 : Continuous (timeProfileProjection3 hw) :=
  (continuous_timeProfileMap3 hw).subtype_mk _

theorem surjective_timeProfileProjection3 : Function.Surjective (timeProfileProjection3 hw) := by
  intro x
  obtain ⟨p, hp⟩ := x.property
  exact ⟨p, Subtype.ext hp⟩

theorem isQuotientMap_timeProfileProjection3 : IsQuotientMap (timeProfileProjection3 hw) :=
  (continuous_timeProfileProjection3 hw).isClosedMap.isQuotientMap
    (continuous_timeProfileProjection3 hw) (surjective_timeProfileProjection3 hw)

theorem timeProfileProjection3_eq_iff_profile (p q : ClosedLorentzPoint3) :
    timeProfileProjection3 hw p = timeProfileProjection3 hw q ↔
      SameTimeProfile3 w p.val q.val := by
  rw [← timeProfileMap3_eq_iff hw]
  exact Subtype.ext_iff

theorem timeProfileProjection3_eq_iff (p q : ClosedLorentzPoint3) :
    timeProfileProjection3 hw p = timeProfileProjection3 hw q ↔
      p = q ∨ (p.val ∈ lorentzWaist3 ∧ q.val ∈ lorentzWaist3) := by
  rw [timeProfileProjection3_eq_iff_profile,
    weighted_time_profile_eq_iff3 hw p.property q.property]
  exact or_congr Subtype.ext_iff.symm Iff.rfl

def timeProfileRepresentative3 (x : TimeProfileSpace3 hw) : ClosedLorentzPoint3 :=
  x.property.choose

theorem timeProfileProjection3_representative (x : TimeProfileSpace3 hw) :
    timeProfileProjection3 hw (timeProfileRepresentative3 hw x) = x :=
  Subtype.ext x.property.choose_spec

theorem timeProfileRepresentative3_profile (p : ClosedLorentzPoint3) :
    SameTimeProfile3 w (timeProfileRepresentative3 hw (timeProfileProjection3 hw p)).val p.val :=
  (timeProfileProjection3_eq_iff_profile hw _ _).mp
    (timeProfileProjection3_representative hw (timeProfileProjection3 hw p))

def quotientTime3 (x y : TimeProfileSpace3 hw) : ℝ :=
  weightedTimeSeparation3 w (timeProfileRepresentative3 hw x).val
    (timeProfileRepresentative3 hw y).val

/-- Exact descent of the original curve supremum, independent of representatives. -/
theorem quotientTime3_projection (p q : ClosedLorentzPoint3) :
    quotientTime3 hw (timeProfileProjection3 hw p) (timeProfileProjection3 hw q) =
      weightedTimeSeparation3 w p.val q.val := by
  unfold quotientTime3
  rw [(timeProfileRepresentative3_profile hw p).2 _
      (timeProfileRepresentative3 hw (timeProfileProjection3 hw q)).property,
    (timeProfileRepresentative3_profile hw q).1 p.val p.property]

theorem isQuotientMap_timeProfileProjection3_prod :
    IsQuotientMap (fun z : ClosedLorentzPoint3 × ClosedLorentzPoint3 =>
      (timeProfileProjection3 hw z.1, timeProfileProjection3 hw z.2)) := by
  have hc : Continuous (fun z : ClosedLorentzPoint3 × ClosedLorentzPoint3 =>
      (timeProfileProjection3 hw z.1, timeProfileProjection3 hw z.2)) :=
    ((continuous_timeProfileProjection3 hw).comp continuous_fst).prodMk
      ((continuous_timeProfileProjection3 hw).comp continuous_snd)
  apply hc.isClosedMap.isQuotientMap hc
  intro z
  obtain ⟨p, hp⟩ := surjective_timeProfileProjection3 hw z.1
  obtain ⟨q, hq⟩ := surjective_timeProfileProjection3 hw z.2
  exact ⟨(p, q), Prod.ext hp hq⟩

theorem continuous_quotientTime3 :
    Continuous (fun z : TimeProfileSpace3 hw × TimeProfileSpace3 hw => quotientTime3 hw z.1 z.2) := by
  apply (isQuotientMap_timeProfileProjection3_prod hw).continuous_iff.mpr
  simpa only [Function.comp_def, quotientTime3_projection] using (closedTimeMap3 hw).continuous

theorem uniformContinuous_quotientTime3 :
    UniformContinuous (fun z : TimeProfileSpace3 hw × TimeProfileSpace3 hw => quotientTime3 hw z.1 z.2) :=
  CompactSpace.uniformContinuous_of_continuous (continuous_quotientTime3 hw)

theorem quotientTime3_nonneg (x y : TimeProfileSpace3 hw) : 0 ≤ quotientTime3 hw x y :=
  weighted_time_separation_nonneg3 hw _ _

theorem quotientTime3_le_two_hi (x y : TimeProfileSpace3 hw) : quotientTime3 hw x y ≤ 2 * hi :=
  weighted_time_le_two_hi3 hw _ _

theorem quotientTime3_self (x : TimeProfileSpace3 hw) : quotientTime3 hw x x = 0 := by
  apply (weighted_time_separation_zero_iff3 hw
    (timeProfileRepresentative3 hw x).property (timeProfileRepresentative3 hw x).property).mpr
  simp [chronological3, spatialRadius3]

theorem quotientTime3_projection_pos_iff (p q : ClosedLorentzPoint3) :
    0 < quotientTime3 hw (timeProfileProjection3 hw p) (timeProfileProjection3 hw q) ↔
      chronological3 p.val q.val := by
  rw [quotientTime3_projection]
  exact weighted_time_separation_pos_iff3 hw p.property q.property

/-- The reverse triangle uses positive time separation, which descends through the waist. -/
theorem quotientTime3_reverse_triangle (x y z : TimeProfileSpace3 hw)
    (hxy : 0 < quotientTime3 hw x y) (hyz : 0 < quotientTime3 hw y z) :
    quotientTime3 hw x y + quotientTime3 hw y z ≤ quotientTime3 hw x z := by
  have hxy' := (weighted_time_separation_pos_iff3 hw
    (timeProfileRepresentative3 hw x).property (timeProfileRepresentative3 hw y).property).mp hxy
  have hyz' := (weighted_time_separation_pos_iff3 hw
    (timeProfileRepresentative3 hw y).property (timeProfileRepresentative3 hw z).property).mp hyz
  exact weighted_time_reverse_triangle3 hw (timeProfileRepresentative3 hw x).property
    (timeProfileRepresentative3 hw y).property (timeProfileRepresentative3 hw z).property hxy'.le hyz'.le

/-- Incoming and outgoing numerical profiles distinguish all quotient points. -/
theorem quotientTime3_distinguishes (x y : TimeProfileSpace3 hw)
    (hin : ∀ z, quotientTime3 hw z x = quotientTime3 hw z y)
    (hout : ∀ z, quotientTime3 hw x z = quotientTime3 hw y z) : x = y := by
  obtain ⟨p, rfl⟩ := surjective_timeProfileProjection3 hw x
  obtain ⟨q, rfl⟩ := surjective_timeProfileProjection3 hw y
  apply (timeProfileProjection3_eq_iff_profile hw p q).mpr
  constructor
  · intro z hz
    simpa only [quotientTime3_projection] using hin (timeProfileProjection3 hw ⟨z, hz⟩)
  · intro z hz
    simpa only [quotientTime3_projection] using hout (timeProfileProjection3 hw ⟨z, hz⟩)

theorem isCompact_quotientTime3_superlevel (eps : ℝ) :
    IsCompact {z : TimeProfileSpace3 hw × TimeProfileSpace3 hw | eps ≤ quotientTime3 hw z.1 z.2} :=
  (isClosed_le continuous_const (continuous_quotientTime3 hw)).isCompact

theorem InDensityClass3.quotientTime_continuous {rho : LorentzPoint3 → ℝ}
    (hR : InDensityClass3 rho) :
    Continuous (fun z : TimeProfileSpace3 hR.timeWeight × TimeProfileSpace3 hR.timeWeight =>
      quotientTime3 hR.timeWeight z.1 z.2) := continuous_quotientTime3 hR.timeWeight

#print axioms continuous_timeProfileMap3
#print axioms timeProfileMap3_outgoing
#print axioms timeProfileMap3_incoming
#print axioms timeProfileMap3_eq_iff
#print axioms timeProfileSpace3_isCompact
#print axioms continuous_timeProfileProjection3
#print axioms surjective_timeProfileProjection3
#print axioms isQuotientMap_timeProfileProjection3
#print axioms timeProfileProjection3_eq_iff_profile
#print axioms timeProfileProjection3_eq_iff
#print axioms timeProfileProjection3_representative
#print axioms timeProfileRepresentative3_profile
#print axioms quotientTime3_projection
#print axioms isQuotientMap_timeProfileProjection3_prod
#print axioms continuous_quotientTime3
#print axioms uniformContinuous_quotientTime3
#print axioms quotientTime3_nonneg
#print axioms quotientTime3_le_two_hi
#print axioms quotientTime3_self
#print axioms quotientTime3_projection_pos_iff
#print axioms quotientTime3_reverse_triangle
#print axioms quotientTime3_distinguishes
#print axioms isCompact_quotientTime3_superlevel
#print axioms InDensityClass3.quotientTime_continuous

end
end QuantyraNullCone
