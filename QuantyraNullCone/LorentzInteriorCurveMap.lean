import QuantyraNullCone.LorentzCurveMap
import Mathlib.Analysis.Calculus.ContDiff.RCLike

namespace QuantyraNullCone
open MeasureTheory Set
noncomputable section
set_option maxHeartbeats 800000

theorem convex_causalDiamond3 (p q : LorentzPoint3) : Convex ℝ (causalDiamond3 p q) := by
  intro x hx y hy a b ha hb hab
  have hleft : a • (x - p) + b • (y - p) = a • x + b • y - p := by
    rw [smul_sub,smul_sub,sub_add_sub_comm,← add_smul,hab,one_smul]
  have hright : a • (q - x) + b • (q - y) = q - (a • x + b • y) := by
    rw [smul_sub,smul_sub,sub_add_sub_comm,← add_smul,hab,one_smul]
  constructor
  · have h := future_cone_add3 (future_cone_smul3 hx.1 ha) (future_cone_smul3 hy.1 hb)
    rw [hleft] at h
    exact h
  · have h := future_cone_add3 (future_cone_smul3 hx.2 ha) (future_cone_smul3 hy.2 hb)
    rw [hright] at h
    exact h

theorem FutureCurve3.point_mem_causalDiamond {p q : LorentzPoint3} (c : FutureCurve3 p q)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : c.point t ∈ causalDiamond3 p q := by
  have hl := c.causal_mono (by constructor <;> norm_num) ht ht.1
  have hr := c.causal_mono ht (by constructor <;> norm_num) ht.2
  rw [c.point_zero] at hl
  rw [c.point_one] at hr
  exact ⟨hl,hr⟩

theorem FutureCurve3.point_mem_open {p q : LorentzPoint3} (c : FutureCurve3 p q)
    (hp : p ∈ lorentzDiamond3) (hq : q ∈ lorentzDiamond3)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : c.point t ∈ lorentzDiamond3 :=
  causal_diamond_subset_open3 hp hq (c.point_mem_causalDiamond ht)

/-- Interior regularity suffices: no extension of the map or its derivative to the boundary. -/
structure IsInteriorCausalMap3 (F : LorentzPoint3 → LorentzPoint3)
    (D : LorentzPoint3 → LorentzPoint3 →L[ℝ] LorentzPoint3) : Prop where
  smooth : ContDiffOn ℝ 1 F lorentzDiamond3
  hasFDerivAt : ∀ p ∈ lorentzDiamond3, HasFDerivAt F (D p) p
  mapsTo : MapsTo F lorentzDiamond3 lorentzDiamond3
  future : ∀ p ∈ lorentzDiamond3, ∀ v, spatialRadius3 v ≤ v 0 →
    spatialRadius3 (D p v) ≤ D p v 0

variable {F : LorentzPoint3 → LorentzPoint3}
  {D : LorentzPoint3 → LorentzPoint3 →L[ℝ] LorentzPoint3}

theorem IsInteriorCausalMap3.lipschitz_causalDiamond (hF : IsInteriorCausalMap3 F D)
    {p q : LorentzPoint3} (hp : p ∈ lorentzDiamond3) (hq : q ∈ lorentzDiamond3) :
    ∃ K, LipschitzOnWith K F (causalDiamond3 p q) :=
  (hF.smooth.mono (causal_diamond_subset_open3 hp hq)).exists_lipschitzOnWith
    (by norm_num) (convex_causalDiamond3 p q)
    (isCompact_causalDiamond3 (lorentz_diamond_subset_closed3 hp) (lorentz_diamond_subset_closed3 hq))

theorem FutureCurve3.mapInterior_coord_AC {p q : LorentzPoint3} (c : FutureCurve3 p q)
    (hp : p ∈ lorentzDiamond3) (hq : q ∈ lorentzDiamond3)
    (hF : IsInteriorCausalMap3 F D) (i : Fin 3) :
    AbsolutelyContinuousOnInterval (fun t => F (c.point t) i) 0 1 := by
  obtain ⟨K,hK⟩ := hF.lipschitz_causalDiamond hp hq
  have h : AbsolutelyContinuousOnInterval (F ∘ c.point) 0 1 :=
    ac_comp_lipschitz3 c.point_AC hK (fun t ht => c.point_mem_causalDiamond (by
      simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht))
  exact ac_comp_lipschitz3 (g := lorentzCoordinateCLM3 i) (s := Set.univ) h
    (lorentzCoordinateCLM3 i).lipschitz.lipschitzOnWith (mapsTo_univ _ _)

theorem FutureCurve3.mapInterior_coord_deriv {p q : LorentzPoint3} (c : FutureCurve3 p q)
    (hp : p ∈ lorentzDiamond3) (hq : q ∈ lorentzDiamond3)
    (hF : IsInteriorCausalMap3 F D) (i : Fin 3) :
    ∀ᵐ t ∂curveMeasure, deriv (fun t => F (c.point t) i) t = D (c.point t) (c.velocity t) i := by
  filter_upwards [c.point_hasDerivAt,self_mem_ae_restrict measurableSet_Icc] with t ht hm
  exact ((lorentzCoordinateCLM3 i).hasFDerivAt.comp_hasDerivAt t
    ((hF.hasFDerivAt _ (c.point_mem_open hp hq hm)).comp_hasDerivAt t ht)).deriv

def FutureCurve3.mapInterior {p q : LorentzPoint3} (c : FutureCurve3 p q)
    (hp : p ∈ lorentzDiamond3) (hq : q ∈ lorentzDiamond3)
    (hF : IsInteriorCausalMap3 F D) : FutureCurve3 (F p) (F q) where
  coord i t := F (c.point t) i
  coordAC := c.mapInterior_coord_AC hp hq hF
  start i := by rw [c.point_zero]
  finish i := by rw [c.point_one]
  inDiamond t ht := lorentz_diamond_subset_closed3 (hF.mapsTo (c.point_mem_open hp hq ht))
  future := by
    have h := ae_all_iff.mpr (c.mapInterior_coord_deriv hp hq hF)
    filter_upwards [h,c.future,self_mem_ae_restrict measurableSet_Icc] with t ht hv hm
    have he : WithLp.toLp 2 (fun i => deriv (fun s => F (c.point s) i) t) =
        D (c.point t) (c.velocity t) := by ext i; exact ht i
    rw [he,ht 0]
    exact hF.future _ (c.point_mem_open hp hq hm) _ hv

theorem FutureCurve3.mapInterior_point {p q : LorentzPoint3} (c : FutureCurve3 p q)
    (hp : p ∈ lorentzDiamond3) (hq : q ∈ lorentzDiamond3)
    (hF : IsInteriorCausalMap3 F D) (t : ℝ) :
    (c.mapInterior hp hq hF).point t = F (c.point t) := rfl

theorem FutureCurve3.mapInterior_velocity {p q : LorentzPoint3} (c : FutureCurve3 p q)
    (hp : p ∈ lorentzDiamond3) (hq : q ∈ lorentzDiamond3)
    (hF : IsInteriorCausalMap3 F D) :
    ∀ᵐ t ∂curveMeasure, (c.mapInterior hp hq hF).velocity t = D (c.point t) (c.velocity t) := by
  have h := ae_all_iff.mpr (c.mapInterior_coord_deriv hp hq hF)
  filter_upwards [h] with t ht
  ext i
  exact ht i

theorem FutureCurve3.mapInterior_weightedLength {p q : LorentzPoint3} (c : FutureCurve3 p q)
    (hp : p ∈ lorentzDiamond3) (hq : q ∈ lorentzDiamond3)
    (hF : IsInteriorCausalMap3 F D) {w z : LorentzPoint3 → ℝ}
    (hw : ∀ p ∈ lorentzDiamond3, ∀ v, spatialRadius3 v ≤ v 0 →
      z (F p) * flatProperSpeed3 (D p v) = w p * flatProperSpeed3 v) :
    (c.mapInterior hp hq hF).weightedLength z = c.weightedLength w := by
  apply integral_congr_ae
  filter_upwards [c.mapInterior_velocity hp hq hF,c.future,self_mem_ae_restrict measurableSet_Icc] with t ht hv hm
  change z ((c.mapInterior hp hq hF).point t) * flatProperSpeed3 ((c.mapInterior hp hq hF).velocity t) = _
  rw [c.mapInterior_point hp hq hF,ht]
  exact hw _ (c.point_mem_open hp hq hm) _ hv

theorem weighted_time_le_of_interior_causal_map3 (hF : IsInteriorCausalMap3 F D)
    {w z : LorentzPoint3 → ℝ} {lo hi : ℝ} (hz : InTimeWeightClass3 z lo hi)
    (hw : ∀ p ∈ lorentzDiamond3, ∀ v, spatialRadius3 v ≤ v 0 →
      z (F p) * flatProperSpeed3 (D p v) = w p * flatProperSpeed3 v)
    {p q : LorentzPoint3} (hp : p ∈ lorentzDiamond3) (hq : q ∈ lorentzDiamond3) :
    weightedTimeSeparation3 w p q ≤ weightedTimeSeparation3 z (F p) (F q) := by
  apply csSup_le (by simp : (insert 0 (Set.range
    (fun c : FutureCurve3 p q => c.weightedLength w))).Nonempty)
  rintro x (hx | ⟨c,rfl⟩)
  · subst x; exact weighted_time_separation_nonneg3 hz _ _
  · change c.weightedLength w ≤ _
    rw [← c.mapInterior_weightedLength hp hq hF hw]
    exact (c.mapInterior hp hq hF).weightedLength_le_timeSeparation hz

theorem density_metric_speed_transport3 {rho sigma : LorentzPoint3 → ℝ}
    (hR : InDensityClass3 rho) (hS : InDensityClass3 sigma)
    (hF : IsInteriorCausalMap3 F D)
    (hm : ∀ p ∈ lorentzDiamond3, ∀ u v,
      densityMetric3 rho p u v = densityMetric3 sigma (F p) (D p u) (D p v))
    {p : LorentzPoint3} (hp : p ∈ lorentzDiamond3) {v : LorentzPoint3}
    (hv : spatialRadius3 v ≤ v 0) :
    densityTimeWeight3 sigma (F p) * flatProperSpeed3 (D p v) =
      densityTimeWeight3 rho p * flatProperSpeed3 v := by
  have hr : 0 ≤ rho p := by linarith [(hR.bounds p (lorentz_diamond_subset_closed3 hp)).1]
  have hs : 0 ≤ sigma (F p) := by
    linarith [(hS.bounds (F p) (lorentz_diamond_subset_closed3 (hF.mapsTo hp))).1]
  rw [← density_metric_proper_speed3 hs (hF.future p hp v hv),
    ← density_metric_proper_speed3 hr hv,hm p hp v v]

#print axioms convex_causalDiamond3
#print axioms FutureCurve3.point_mem_causalDiamond
#print axioms FutureCurve3.point_mem_open
#print axioms IsInteriorCausalMap3.lipschitz_causalDiamond
#print axioms FutureCurve3.mapInterior_coord_AC
#print axioms FutureCurve3.mapInterior_coord_deriv
#print axioms FutureCurve3.mapInterior_point
#print axioms FutureCurve3.mapInterior_velocity
#print axioms FutureCurve3.mapInterior_weightedLength
#print axioms weighted_time_le_of_interior_causal_map3
#print axioms density_metric_speed_transport3

end
end QuantyraNullCone
