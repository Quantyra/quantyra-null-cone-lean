import QuantyraNullCone.CommonMeasureCoupling
import QuantyraNullCone.TimeDistortionTriangle

namespace QuantyraNullCone
open MeasureTheory Set
noncomputable section
set_option maxHeartbeats 800000

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

theorem common_diagonal_bad_zero {omega : Measure X} [IsFiniteMeasure omega]
    {f : X → Y} {g : X → Z} (hf : Measurable f) (hg : Measurable g)
    {tx : Y → Y → ℝ} {ty : Z → Z → ℝ}
    (hx : Measurable (Function.uncurry tx)) (hy : Measurable (Function.uncurry ty))
    {delta eps : ℝ} (he : delta ≤ eps)
    (hb : ∀ x y, |tx (f x) (f y) - ty (g x) (g y)| ≤ delta) :
    ((graphTimeCoupling omega id).prod (graphTimeCoupling omega id))
      ((Prod.map (Prod.map f g) (Prod.map f g)) ⁻¹' timeBadPairs tx ty eps) = 0 := by
  have hdiag : Measurable (fun x : X => (x,x)) := measurable_id.prodMk measurable_id
  have hs := ((hf.prodMap hg).prodMap (hf.prodMap hg)) (measurableSet_timeBadPairs hx hy eps)
  simp only [graphTimeCoupling,id_eq]
  rw [Measure.map_prod_map omega omega hdiag hdiag,
    Measure.map_apply (hdiag.prodMap hdiag) hs]
  have hz : (Prod.map (fun x : X => (x,x)) (fun x => (x,x))) ⁻¹'
      ((Prod.map (Prod.map f g) (Prod.map f g)) ⁻¹' timeBadPairs tx ty eps) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact (not_lt_of_ge ((hb z.1 z.2).trans he)) hz
  rw [hz,measure_empty]

theorem common_coupling_bad_bound {mu nu omega : Measure X}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] [IsFiniteMeasure omega]
    (hm : omega ≤ mu) (hn : omega ≤ nu)
    {f : X → Y} {g : X → Z} (hf : Measurable f) (hg : Measurable g)
    {tx : Y → Y → ℝ} {ty : Z → Z → ℝ}
    (hx : Measurable (Function.uncurry tx)) (hy : Measurable (Function.uncurry ty))
    {delta eps : ℝ} (he : delta ≤ eps)
    (hb : ∀ x y, |tx (f x) (f y) - ty (g x) (g y)| ≤ delta) :
    (((commonMeasureCoupling mu nu omega).map (Prod.map f g)).prod
      ((commonMeasureCoupling mu nu omega).map (Prod.map f g))) (timeBadPairs tx ty eps) ≤
      (1 - omega univ) + (1 - omega univ) := by
  let pi := commonMeasureCoupling mu nu omega
  let d := graphTimeCoupling omega id
  let r := commonResidualCoupling mu nu omega
  letI : IsProbabilityMeasure pi := (isTimeCoupling_common hm hn).isProbabilityMeasure
  letI : IsFiniteMeasure r := common_residual_isFiniteMeasure hm hn
  have hdiag : Measurable (fun x : X => (x,x)) := measurable_id.prodMk measurable_id
  letI : IsFiniteMeasure d := Measure.isFiniteMeasure_map omega (fun x => (x,x))
  let E := (Prod.map (Prod.map f g) (Prod.map f g)) ⁻¹' timeBadPairs tx ty eps
  have hd : d univ ≤ 1 := by
    simpa [d,graphTimeCoupling,Measure.map_apply hdiag MeasurableSet.univ] using hm univ
  have hr : r univ = 1 - omega univ := common_residual_univ hm hn
  have h0 : (d.prod d) E = 0 := common_diagonal_bad_zero hf hg hx hy he hb
  have h1 : (d.prod r) E ≤ 1 - omega univ := by
    calc
      (d.prod r) E ≤ (d.prod r) univ := measure_mono (subset_univ E)
      _ = d univ * r univ := by
        simpa only [univ_prod_univ] using Measure.prod_prod (μ := d) (ν := r) univ univ
      _ ≤ 1 * r univ := mul_le_mul_left hd _
      _ = 1 - omega univ := by rw [one_mul,hr]
  have h2 : (r.prod pi) E ≤ 1 - omega univ := by
    calc
      (r.prod pi) E ≤ (r.prod pi) univ := measure_mono (subset_univ E)
      _ = r univ := by
        simpa only [univ_prod_univ,measure_univ (μ := pi),mul_one] using
          Measure.prod_prod (μ := r) (ν := pi) univ univ
      _ = 1 - omega univ := hr
  change ((pi.map (Prod.map f g)).prod (pi.map (Prod.map f g))) _ ≤ _
  rw [timeBadPairs_map_measure pi (hf.prodMap hg) hx hy]
  change (pi.prod pi) E ≤ _
  have heq : pi.prod pi = d.prod d + d.prod r + r.prod pi := by
    change (d + r).prod pi = _
    rw [Measure.add_prod]
    change d.prod (d + r) + r.prod pi = _
    rw [Measure.prod_add]
  rw [heq,Measure.add_apply,Measure.add_apply,h0,zero_add]
  exact add_le_add h1 h2

/-- A common submeasure and a uniform time bound control the actual infimum after two maps. -/
theorem timeDistortionLoss_le_of_common {mu nu omega : Measure X}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] [IsFiniteMeasure omega]
    (hm : omega ≤ mu) (hn : omega ≤ nu)
    {f : X → Y} {g : X → Z} (hf : Measurable f) (hg : Measurable g)
    {tx : Y → Y → ℝ} {ty : Z → Z → ℝ}
    (hx : Measurable (Function.uncurry tx)) (hy : Measurable (Function.uncurry ty))
    {delta : ℝ} (hd : 0 ≤ delta)
    (hmiss : (1 - omega univ) + (1 - omega univ) ≤ ENNReal.ofReal delta)
    (hb : ∀ x y, |tx (f x) (f y) - ty (g x) (g y)| ≤ delta) :
    timeDistortionLoss (mu.map f) (nu.map g) tx ty ≤ delta := by
  by_contra hnlt
  have hlt := lt_of_not_ge hnlt
  let eps := (delta + timeDistortionLoss (mu.map f) (nu.map g) tx ty) / 2
  have he : delta < eps := by dsimp [eps]; linarith
  have hbad := (common_coupling_bad_bound hm hn hf hg hx hy he.le hb).trans
    (hmiss.trans (ENNReal.ofReal_le_ofReal he.le))
  have h := timeDistortionLoss_le_of_admissible
    (show TimeDistortionAdmissible (mu.map f) (nu.map g) tx ty eps from
      ⟨hd.trans_lt he,(commonMeasureCoupling mu nu omega).map (Prod.map f g),
        (isTimeCoupling_common hm hn).map hf hg,hbad⟩)
  dsimp [eps] at h
  linarith

#print axioms common_diagonal_bad_zero
#print axioms common_coupling_bad_bound
#print axioms timeDistortionLoss_le_of_common

end
end QuantyraNullCone
