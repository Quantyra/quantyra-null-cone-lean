import QuantyraNullCone.LorentzTimeQuotient
import QuantyraNullCone.LorentzGaugeClass
import Mathlib.MeasureTheory.Measure.OpenPos

/-! The original normalized density law, transported to the compact profile quotient.
All relative open sets have positive mass, including neighborhoods of the collapsed waist. -/

namespace QuantyraNullCone
open Set MeasureTheory Topology
noncomputable section

theorem closed_diamond_subset_closure_open3 : closedLorentzDiamond3 ⊆ closure lorentzDiamond3 := by
  intro p hp
  apply Metric.mem_closure_iff.mpr
  intro eps heps
  let d := min (eps / 2) (1 / 2 : ℝ)
  have hd : 0 < d := by dsimp [d]; positivity
  have hdhalf : d ≤ 1 / 2 := min_le_right _ _
  have hdeps : d ≤ eps / 2 := min_le_left _ _
  have ha : 0 ≤ 1 - d := by linarith
  refine ⟨(1 - d) • p, ?_, ?_⟩
  · change |((1 - d) • p) 0| + spatialRadius3 ((1 - d) • p) < 1
    rw [spatial_radius_smul3, abs_of_nonneg ha]
    change |(1 - d) * p 0| + (1 - d) * spatialRadius3 p < 1
    rw [abs_mul, abs_of_nonneg ha]
    have h := mul_le_mul_of_nonneg_left hp ha
    change (1 - d) * (|p 0| + spatialRadius3 p) ≤ (1 - d) * 1 at h
    nlinarith
  · have heq : p - (1 - d) • p = d • p := by
      rw [sub_smul, one_smul, sub_sub_cancel]
    rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, abs_of_pos hd]
    have hn := closed_diamond_norm_le_one3 hp
    have hmul := mul_le_mul_of_nonneg_left hn hd.le
    nlinarith

theorem closure_lorentzDiamond3 : closure lorentzDiamond3 = closedLorentzDiamond3 :=
  subset_antisymm (closure_minimal lorentz_diamond_subset_closed3 isClosed_closedLorentzDiamond3)
    closed_diamond_subset_closure_open3

def closedDensityMeasure3 (rho : LorentzPoint3 → ℝ) : Measure ClosedLorentzPoint3 :=
  (densityMeasure3 rho).comap Subtype.val

theorem closedDensityMeasure3_apply (rho : LorentzPoint3 → ℝ) (s : Set ClosedLorentzPoint3) :
    closedDensityMeasure3 rho s = densityMeasure3 rho (Subtype.val '' s) :=
  comap_subtype_coe_apply isClosed_closedLorentzDiamond3.measurableSet _ _

theorem closedDensityMeasure3_map_val (rho : LorentzPoint3 → ℝ) :
    (closedDensityMeasure3 rho).map Subtype.val = densityMeasure3 rho := by
  rw [closedDensityMeasure3, map_comap_subtype_coe
    isClosed_closedLorentzDiamond3.measurableSet]
  exact Measure.restrict_eq_self_of_ae_mem (density_measure3_ae_closed rho)

theorem InDensityClass3.closedDensityMeasure_univ {rho : LorentzPoint3 → ℝ}
    (hR : InDensityClass3 rho) : closedDensityMeasure3 rho univ = 1 := by
  rw [← hR.densityMeasure_univ, ← closedDensityMeasure3_map_val rho,
    Measure.map_apply measurable_subtype_coe MeasurableSet.univ, preimage_univ]

theorem InDensityClass3.closedDensity_isProbabilityMeasure {rho : LorentzPoint3 → ℝ}
    (hR : InDensityClass3 rho) : IsProbabilityMeasure (closedDensityMeasure3 rho) :=
  ⟨hR.closedDensityMeasure_univ⟩

theorem InDensityClass3.densityMeasure_dominates {rho : LorentzPoint3 → ℝ}
    (hR : InDensityClass3 rho) :
    ENNReal.ofReal (1 / 2 : ℝ) • flatDiamondMeasure3 ≤ densityMeasure3 rho := by
  rw [← withDensity_const]
  apply withDensity_mono
  exact flat_diamond3_ae_mem.mono (fun p hp => ENNReal.ofReal_le_ofReal (hR.bounds p hp).1)

theorem InDensityClass3.densityMeasure_open_pos {rho : LorentzPoint3 → ℝ}
    (hR : InDensityClass3 rho) {U : Set LorentzPoint3} (hU : IsOpen U)
    (hUC : (U ∩ closedLorentzDiamond3).Nonempty) : 0 < densityMeasure3 rho U := by
  obtain ⟨p, hpU, hpC⟩ := hUC
  have hne : (U ∩ lorentzDiamond3).Nonempty :=
    mem_closure_iff.mp (closed_diamond_subset_closure_open3 hpC) U hU hpU
  have hv : 0 < (volume : Measure LorentzPoint3) (U ∩ lorentzDiamond3) :=
    (hU.inter isOpen_lorentzDiamond3).measure_pos volume hne
  have hflat : 0 < flatDiamondMeasure3 U := by
    rw [flatDiamondMeasure3, Measure.smul_apply, Measure.restrict_apply hU.measurableSet]
    exact ENNReal.mul_pos (by simp) hv.ne'
  have hsmall : 0 < (ENNReal.ofReal (1 / 2 : ℝ) • flatDiamondMeasure3) U := by
    rw [Measure.smul_apply]
    exact ENNReal.mul_pos (by norm_num) hflat.ne'
  exact hsmall.trans_le (hR.densityMeasure_dominates U)

theorem InDensityClass3.closedDensity_isOpenPosMeasure {rho : LorentzPoint3 → ℝ}
    (hR : InDensityClass3 rho) : (closedDensityMeasure3 rho).IsOpenPosMeasure := by
  constructor
  intro U hU hne
  obtain ⟨V, hV, hVU⟩ := isOpen_induced_iff.mp hU
  obtain ⟨p, hp⟩ := hne
  have hpV : p.val ∈ V := by rw [← hVU] at hp; exact hp
  have hpos := hR.densityMeasure_open_pos hV ⟨p.val, hpV, p.property⟩
  have himage : Subtype.val '' U = V ∩ closedLorentzDiamond3 := by
    rw [← hVU, image_preimage_eq_inter_range, Subtype.range_coe]
  rw [closedDensityMeasure3_apply, himage]
  have heq : densityMeasure3 rho (V ∩ closedLorentzDiamond3) = densityMeasure3 rho V := by
    rw [← Measure.restrict_apply hV.measurableSet,
      Measure.restrict_eq_self_of_ae_mem (density_measure3_ae_closed rho)]
  rw [heq]
  exact hpos.ne'

variable {w : LorentzPoint3 → ℝ} {lo hi : ℝ} (hw : InTimeWeightClass3 w lo hi)

instance timeProfileSpace3MeasurableSpace : MeasurableSpace (TimeProfileSpace3 hw) := borel _
instance timeProfileSpace3BorelSpace : BorelSpace (TimeProfileSpace3 hw) := ⟨rfl⟩

def quotientDensityMeasure3 (rho : LorentzPoint3 → ℝ) : Measure (TimeProfileSpace3 hw) :=
  (closedDensityMeasure3 rho).map (timeProfileProjection3 hw)

theorem quotientDensityMeasure3_apply (rho : LorentzPoint3 → ℝ)
    {s : Set (TimeProfileSpace3 hw)} (hs : MeasurableSet s) :
    quotientDensityMeasure3 hw rho s =
      closedDensityMeasure3 rho (timeProfileProjection3 hw ⁻¹' s) :=
  Measure.map_apply (continuous_timeProfileProjection3 hw).measurable hs

theorem InDensityClass3.quotientDensity_isProbabilityMeasure {rho : LorentzPoint3 → ℝ}
    (hR : InDensityClass3 rho) : IsProbabilityMeasure (quotientDensityMeasure3 hw rho) := by
  letI := hR.closedDensity_isProbabilityMeasure
  exact Measure.isProbabilityMeasure_map (continuous_timeProfileProjection3 hw).measurable.aemeasurable

theorem InDensityClass3.quotientDensity_isOpenPosMeasure {rho : LorentzPoint3 → ℝ}
    (hR : InDensityClass3 rho) : (quotientDensityMeasure3 hw rho).IsOpenPosMeasure := by
  letI := hR.closedDensity_isOpenPosMeasure
  exact (continuous_timeProfileProjection3 hw).isOpenPosMeasure_map
    (surjective_timeProfileProjection3 hw)

theorem InDensityClass3.quotientDensity_open_pos {rho : LorentzPoint3 → ℝ}
    (hR : InDensityClass3 rho) {U : Set (TimeProfileSpace3 hw)} (hU : IsOpen U) (hne : U.Nonempty) :
    0 < quotientDensityMeasure3 hw rho U := by
  letI := hR.quotientDensity_isOpenPosMeasure hw
  exact hU.measure_pos _ hne

#print axioms closed_diamond_subset_closure_open3
#print axioms closure_lorentzDiamond3
#print axioms closedDensityMeasure3_apply
#print axioms closedDensityMeasure3_map_val
#print axioms InDensityClass3.closedDensityMeasure_univ
#print axioms InDensityClass3.closedDensity_isProbabilityMeasure
#print axioms InDensityClass3.densityMeasure_dominates
#print axioms InDensityClass3.densityMeasure_open_pos
#print axioms InDensityClass3.closedDensity_isOpenPosMeasure
#print axioms quotientDensityMeasure3_apply
#print axioms InDensityClass3.quotientDensity_isProbabilityMeasure
#print axioms InDensityClass3.quotientDensity_isOpenPosMeasure
#print axioms InDensityClass3.quotientDensity_open_pos

end
end QuantyraNullCone
