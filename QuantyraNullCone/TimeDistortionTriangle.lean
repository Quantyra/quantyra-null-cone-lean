import QuantyraNullCone.TimeCouplingGluing

/-! The triangle inequality for the probability-of-time-distortion infimum.
The proof uses two independent draws of a glued coupling and a union bound. -/

namespace QuantyraNullCone
open MeasureTheory Set
noncomputable section

variable {X Y Z W : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace Z] [MeasurableSpace W]

omit [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] in
theorem timeBadPairs_triangle_subset (tx : X → X → ℝ) (ty : Y → Y → ℝ)
    (tz : Z → Z → ℝ) (eps eta : ℝ) :
    (Prod.map (fun p : (X × Y) × Z => (p.1.1, p.2))
      (fun p => (p.1.1, p.2))) ⁻¹' timeBadPairs tx tz (eps + eta) ⊆
    (Prod.map Prod.fst Prod.fst) ⁻¹' timeBadPairs tx ty eps ∪
    (Prod.map (fun p => (p.1.2, p.2)) (fun p => (p.1.2, p.2))) ⁻¹' timeBadPairs ty tz eta := by
  intro z hz
  change eps + eta < |tx z.1.1.1 z.2.1.1 - tz z.1.2 z.2.2| at hz
  change eps < |tx z.1.1.1 z.2.1.1 - ty z.1.1.2 z.2.1.2| ∨
    eta < |ty z.1.1.2 z.2.1.2 - tz z.1.2 z.2.2|
  by_contra hn
  push Not at hn
  exact (not_lt_of_ge ((abs_sub_le _ _ _).trans (add_le_add hn.1 hn.2))) hz

theorem timeBadPairs_map_measure (gamma : Measure W) [SFinite gamma]
    {f : W → X × Y} (hf : Measurable f) {tx : X → X → ℝ} {ty : Y → Y → ℝ}
    (hx : Measurable (Function.uncurry tx)) (hy : Measurable (Function.uncurry ty)) (eps : ℝ) :
    ((gamma.map f).prod (gamma.map f)) (timeBadPairs tx ty eps) =
      (gamma.prod gamma) ((Prod.map f f) ⁻¹' timeBadPairs tx ty eps) := by
  rw [Measure.map_prod_map gamma gamma hf hf,
    Measure.map_apply (hf.prodMap hf) (measurableSet_timeBadPairs hx hy eps)]

theorem timeBadPairs_glued_bound (gamma : Measure ((X × Y) × Z)) [SFinite gamma]
    {tx : X → X → ℝ} {ty : Y → Y → ℝ} {tz : Z → Z → ℝ}
    (hx : Measurable (Function.uncurry tx)) (hy : Measurable (Function.uncurry ty))
    (hz : Measurable (Function.uncurry tz)) (eps eta : ℝ) :
    ((gamma.map (fun p => (p.1.1, p.2))).prod (gamma.map (fun p => (p.1.1, p.2))))
      (timeBadPairs tx tz (eps + eta)) ≤
    ((gamma.map Prod.fst).prod (gamma.map Prod.fst)) (timeBadPairs tx ty eps) +
    ((gamma.map (fun p => (p.1.2, p.2))).prod (gamma.map (fun p => (p.1.2, p.2))))
      (timeBadPairs ty tz eta) := by
  have hxz : Measurable (fun p : (X × Y) × Z => (p.1.1, p.2)) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hyz : Measurable (fun p : (X × Y) × Z => (p.1.2, p.2)) :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  rw [timeBadPairs_map_measure gamma hxz hx hz, timeBadPairs_map_measure gamma measurable_fst hx hy,
    timeBadPairs_map_measure gamma hyz hy hz]
  exact (measure_mono (timeBadPairs_triangle_subset tx ty tz eps eta)).trans (measure_union_le _ _)

variable [StandardBorelSpace Z]

theorem timeDistortionAdmissible_trans {mu : Measure X} {nu : Measure Y} {xi : Measure Z}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] [IsProbabilityMeasure xi]
    {tx : X → X → ℝ} {ty : Y → Y → ℝ} {tz : Z → Z → ℝ}
    (hx : Measurable (Function.uncurry tx)) (hy : Measurable (Function.uncurry ty))
    (hz : Measurable (Function.uncurry tz)) {eps eta : ℝ}
    (hXY : TimeDistortionAdmissible mu nu tx ty eps)
    (hYZ : TimeDistortionAdmissible nu xi ty tz eta) :
    TimeDistortionAdmissible mu xi tx tz (eps + eta) := by
  obtain ⟨he, piXY, hp, hpe⟩ := hXY
  obtain ⟨hf, piYZ, hq, hqf⟩ := hYZ
  obtain ⟨gamma, hprob, hgXY, hgYZ⟩ := exists_timeCoupling_gluing hp hq
  letI := hprob
  refine ⟨add_pos he hf, gamma.map (fun p => (p.1.1, p.2)),
    isTimeCoupling_glued_endpoints hp hq hgXY hgYZ, ?_⟩
  have hbound := timeBadPairs_glued_bound gamma hx hy hz eps eta
  rw [hgXY, hgYZ] at hbound
  exact (hbound.trans (add_le_add hpe hqf)).trans_eq (ENNReal.ofReal_add he.le hf.le).symm

theorem timeDistortionLoss_triangle (mu : Measure X) (nu : Measure Y) (xi : Measure Z)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] [IsProbabilityMeasure xi]
    {tx : X → X → ℝ} {ty : Y → Y → ℝ} {tz : Z → Z → ℝ}
    (hx : Measurable (Function.uncurry tx)) (hy : Measurable (Function.uncurry ty))
    (hz : Measurable (Function.uncurry tz)) :
    timeDistortionLoss mu xi tx tz ≤ timeDistortionLoss mu nu tx ty + timeDistortionLoss nu xi ty tz := by
  by_contra hn
  have hgap := lt_of_not_ge hn
  let delta := (timeDistortionLoss mu xi tx tz -
    (timeDistortionLoss mu nu tx ty + timeDistortionLoss nu xi ty tz)) / 3
  have hd : 0 < delta := by dsimp [delta]; linarith
  obtain ⟨eps, he, heLt⟩ := exists_lt_of_csInf_lt (timeDistortion_nonempty mu nu tx ty)
    (show sInf {e | TimeDistortionAdmissible mu nu tx ty e} <
      timeDistortionLoss mu nu tx ty + delta from lt_add_of_pos_right _ hd)
  obtain ⟨eta, hf, hfLt⟩ := exists_lt_of_csInf_lt (timeDistortion_nonempty nu xi ty tz)
    (show sInf {e | TimeDistortionAdmissible nu xi ty tz e} <
      timeDistortionLoss nu xi ty tz + delta from lt_add_of_pos_right _ hd)
  have h := timeDistortionLoss_le_of_admissible (timeDistortionAdmissible_trans hx hy hz he hf)
  dsimp [delta] at heLt hfLt
  linarith

#print axioms timeBadPairs_triangle_subset
#print axioms timeBadPairs_map_measure
#print axioms timeBadPairs_glued_bound
#print axioms timeDistortionAdmissible_trans
#print axioms timeDistortionLoss_triangle

end
end QuantyraNullCone
