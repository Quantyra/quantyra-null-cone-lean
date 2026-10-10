import QuantyraNullCone.LorentzCurvePerturbation
import QuantyraNullCone.LorentzDerivative
import Mathlib.Analysis.Calculus.Deriv.Prod

namespace QuantyraNullCone

open MeasureTheory Set Filter
open scoped Topology NNReal

noncomputable section

theorem ac_comp_lipschitz3 {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {f : ℝ → X} {g : X → Y} {a b : ℝ} {s : Set X} {K : ℝ≥0}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : LipschitzOnWith K g s)
    (hfs : MapsTo f (uIcc a b) s) : AbsolutelyContinuousOnInterval (g ∘ f) a b := by
  unfold AbsolutelyContinuousOnInterval at hf ⊢
  apply squeeze_zero' ?_ ?_ (by simpa using hf.const_mul (K : ℝ))
  · exact Eventually.of_forall fun _ => Finset.sum_nonneg fun _ _ => dist_nonneg
  rw [eventually_inf_principal]
  filter_upwards with E hE
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i hi => hg.dist_le_mul _
    (hfs (hE.1 i hi).1) _ (hfs (hE.1 i hi).2)

theorem lorentz_norm_le_sum_abs3 (v : LorentzPoint3) :
    ‖v‖ ≤ |v 0| + |v 1| + |v 2| := by
  have h := lorentz_norm_sq3 v
  unfold spatialSquared3 at h
  nlinarith [norm_nonneg v, abs_nonneg (v 0), abs_nonneg (v 1), abs_nonneg (v 2),
    sq_abs (v 0), sq_abs (v 1), sq_abs (v 2),
    mul_nonneg (abs_nonneg (v 0)) (abs_nonneg (v 1)),
    mul_nonneg (abs_nonneg (v 0)) (abs_nonneg (v 2)),
    mul_nonneg (abs_nonneg (v 1)) (abs_nonneg (v 2))]

theorem FutureCurve3.point_AC {p q : LorentzPoint3} (c : FutureCurve3 p q) :
    AbsolutelyContinuousOnInterval c.point 0 1 := by
  have h0 := c.coordAC 0
  have h1 := c.coordAC 1
  have h2 := c.coordAC 2
  unfold AbsolutelyContinuousOnInterval at h0 h1 h2 ⊢
  apply squeeze_zero (fun _ => Finset.sum_nonneg fun _ _ => dist_nonneg) ?_
    (by simpa using (h0.add h1).add h2)
  intro E
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  simpa [dist_eq_norm, Real.norm_eq_abs] using
    lorentz_norm_le_sum_abs3 (c.point (E.2 i).1 - c.point (E.2 i).2)

theorem FutureCurve3.point_hasDerivAt {p q : LorentzPoint3} (c : FutureCurve3 p q) :
    ∀ᵐ t ∂curveMeasure, HasDerivAt c.point (c.velocity t) t := by
  have h := ae_all_iff.mpr c.coord_hasDerivAt
  filter_upwards [h] with t ht
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_pi.mpr ht)

/-- Concrete regularity and causal assumptions used to transport the existing AC curve class. -/
structure IsCausalMap3 (F : LorentzPoint3 → LorentzPoint3)
    (D : LorentzPoint3 → LorentzPoint3 →L[ℝ] LorentzPoint3) : Prop where
  lipschitz : ∃ K, LipschitzOnWith K F closedLorentzDiamond3
  hasFDerivAt : ∀ p ∈ closedLorentzDiamond3, HasFDerivAt F (D p) p
  mapsTo : MapsTo F closedLorentzDiamond3 closedLorentzDiamond3
  future : ∀ p ∈ closedLorentzDiamond3, ∀ v, spatialRadius3 v ≤ v 0 →
    spatialRadius3 (D p v) ≤ D p v 0

variable {F : LorentzPoint3 → LorentzPoint3}
  {D : LorentzPoint3 → LorentzPoint3 →L[ℝ] LorentzPoint3}

set_option maxHeartbeats 800000 in
theorem FutureCurve3.map_coord_AC {p q : LorentzPoint3} (c : FutureCurve3 p q)
    (hF : IsCausalMap3 F D) (i : Fin 3) :
    AbsolutelyContinuousOnInterval (fun t => F (c.point t) i) 0 1 := by
  obtain ⟨K,hK⟩ := hF.lipschitz
  have h : AbsolutelyContinuousOnInterval (F ∘ c.point) 0 1 :=
    ac_comp_lipschitz3 c.point_AC hK (fun t ht => c.inDiamond t (by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht))
  exact ac_comp_lipschitz3 (g := lorentzCoordinateCLM3 i) (s := Set.univ) h
    (lorentzCoordinateCLM3 i).lipschitz.lipschitzOnWith (mapsTo_univ _ _)

theorem FutureCurve3.map_coord_deriv {p q : LorentzPoint3} (c : FutureCurve3 p q)
    (hF : IsCausalMap3 F D) (i : Fin 3) :
    ∀ᵐ t ∂curveMeasure, deriv (fun t => F (c.point t) i) t = D (c.point t) (c.velocity t) i := by
  filter_upwards [c.point_hasDerivAt, self_mem_ae_restrict measurableSet_Icc] with t ht hmem
  exact ((lorentzCoordinateCLM3 i).hasFDerivAt.comp_hasDerivAt t
    ((hF.hasFDerivAt _ (c.inDiamond t hmem)).comp_hasDerivAt t ht)).deriv

def FutureCurve3.map {p q : LorentzPoint3} (c : FutureCurve3 p q)
    (hF : IsCausalMap3 F D) : FutureCurve3 (F p) (F q) where
  coord i t := F (c.point t) i
  coordAC := c.map_coord_AC hF
  start i := by
    have h : c.point 0 = p := by ext j; exact c.start j
    rw [h]
  finish i := by
    have h : c.point 1 = q := by ext j; exact c.finish j
    rw [h]
  inDiamond t ht := hF.mapsTo (c.inDiamond t ht)
  future := by
    have h := ae_all_iff.mpr (c.map_coord_deriv hF)
    filter_upwards [h,c.future,self_mem_ae_restrict measurableSet_Icc] with t ht hv hm
    have he : WithLp.toLp 2 (fun i => deriv (fun s => F (c.point s) i) t) =
        D (c.point t) (c.velocity t) := by ext i; exact ht i
    rw [he, ht 0]
    exact hF.future _ (c.inDiamond t hm) _ hv

theorem FutureCurve3.map_point {p q : LorentzPoint3} (c : FutureCurve3 p q)
    (hF : IsCausalMap3 F D) (t : ℝ) : (c.map hF).point t = F (c.point t) := rfl

theorem FutureCurve3.map_velocity {p q : LorentzPoint3} (c : FutureCurve3 p q)
    (hF : IsCausalMap3 F D) :
    ∀ᵐ t ∂curveMeasure, (c.map hF).velocity t = D (c.point t) (c.velocity t) := by
  have h := ae_all_iff.mpr (c.map_coord_deriv hF)
  filter_upwards [h] with t ht
  ext i
  exact ht i

theorem FutureCurve3.map_weightedLength {p q : LorentzPoint3} (c : FutureCurve3 p q)
    (hF : IsCausalMap3 F D) {w z : LorentzPoint3 → ℝ}
    (hw : ∀ p ∈ closedLorentzDiamond3, ∀ v, spatialRadius3 v ≤ v 0 →
      z (F p) * flatProperSpeed3 (D p v) = w p * flatProperSpeed3 v) :
    (c.map hF).weightedLength z = c.weightedLength w := by
  apply integral_congr_ae
  filter_upwards [c.map_velocity hF,c.future,self_mem_ae_restrict measurableSet_Icc] with t ht hv hm
  change z ((c.map hF).point t) * flatProperSpeed3 ((c.map hF).velocity t) = _
  rw [c.map_point hF,ht]
  exact hw _ (c.inDiamond t hm) _ hv

theorem weighted_time_le_of_causal_map3 (hF : IsCausalMap3 F D)
    {w z : LorentzPoint3 → ℝ} {lo hi : ℝ} (hz : InTimeWeightClass3 z lo hi)
    (hw : ∀ p ∈ closedLorentzDiamond3, ∀ v, spatialRadius3 v ≤ v 0 →
      z (F p) * flatProperSpeed3 (D p v) = w p * flatProperSpeed3 v)
    (p q : LorentzPoint3) :
    weightedTimeSeparation3 w p q ≤ weightedTimeSeparation3 z (F p) (F q) := by
  apply csSup_le (by simp : (insert 0 (Set.range
    (fun c : FutureCurve3 p q => c.weightedLength w))).Nonempty)
  rintro x (hx | ⟨c,rfl⟩)
  · subst x; exact weighted_time_separation_nonneg3 hz _ _
  · change c.weightedLength w ≤ _
    rw [← c.map_weightedLength hF hw]
    exact (c.map hF).weightedLength_le_timeSeparation hz

#print axioms ac_comp_lipschitz3
#print axioms lorentz_norm_le_sum_abs3
#print axioms FutureCurve3.point_AC
#print axioms FutureCurve3.point_hasDerivAt
#print axioms FutureCurve3.map_coord_AC
#print axioms FutureCurve3.map_coord_deriv
#print axioms FutureCurve3.map_point
#print axioms FutureCurve3.map_velocity
#print axioms FutureCurve3.map_weightedLength
#print axioms weighted_time_le_of_causal_map3

end
end QuantyraNullCone
