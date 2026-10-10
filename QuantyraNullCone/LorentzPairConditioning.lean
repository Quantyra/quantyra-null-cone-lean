import QuantyraNullCone.LorentzPairProbability
import QuantyraNullCone.LorentzTimeGeometry

namespace QuantyraNullCone
open MeasureTheory Set
noncomputable section
set_option maxHeartbeats 1200000

def timeComparableProbability3 (theta : ℝ) : ℝ := 2*timeOrderedPairProbability3 theta

theorem measurableSet_comparable_pairs3 : MeasurableSet {z : LorentzPoint3 × LorentzPoint3 |
    chronological3 z.1 z.2 ∨ chronological3 z.2 z.1} :=
  measurableSet_chronological_pairs3.union
    (measurableSet_chronological_pairs3.preimage measurable_swap)

theorem time_quadratic_comparable_pair_probability3 {theta : ℝ}
    (ht : theta ∈ Icc (0 : ℝ) (1/2)) :
    ((densityMeasure3 (timeQuadraticDensity3 theta)).prod
      (densityMeasure3 (timeQuadraticDensity3 theta))).real
        {z | chronological3 z.1 z.2 ∨ chronological3 z.2 z.1} = timeComparableProbability3 theta := by
  let mu := densityMeasure3 (timeQuadraticDensity3 theta)
  letI : IsProbabilityMeasure mu := (time_quadratic_density_class3 ht).isProbabilityMeasure
  have hd : Disjoint {z : LorentzPoint3 × LorentzPoint3 | chronological3 z.1 z.2}
      {z | chronological3 z.2 z.1} := by
    rw [disjoint_left]
    intro z h1 h2
    change spatialRadius3 (z.2-z.1) < z.2 0-z.1 0 at h1
    change spatialRadius3 (z.1-z.2) < z.1 0-z.2 0 at h2
    linarith [spatial_radius_nonneg3 (z.2-z.1),spatial_radius_nonneg3 (z.1-z.2)]
  have hs := measurableSet_chronological_pairs3.preimage measurable_swap
  have he := congrArg ENNReal.toReal
    ((Measure.measurePreserving_swap (μ := mu) (ν := mu)).measure_preimage
      measurableSet_chronological_pairs3.nullMeasurableSet)
  change (mu.prod mu).real {z | chronological3 z.2 z.1} =
    (mu.prod mu).real {z | chronological3 z.1 z.2} at he
  change (mu.prod mu).real ({z | chronological3 z.1 z.2} ∪ {z | chronological3 z.2 z.1}) = _
  rw [measureReal_union hd hs,he,time_quadratic_ordered_pair_probability3 ht]
  unfold timeComparableProbability3
  ring

theorem time_quadratic_order_law_comparable3 {theta : ℝ}
    (ht : theta ∈ Icc (0 : ℝ) (1/2)) :
    (orderLaw3 (timeQuadraticDensity3 theta) 2).real
      {code | code 0 1 = true ∨ code 1 0 = true} = timeComparableProbability3 theta := by
  letI := (time_quadratic_density_class3 ht).isProbabilityMeasure
  rw [Measure.real,orderLaw3,Measure.map_apply (sampledOrder3_measurable 2) (by measurability)]
  have he : sampledOrder3 ⁻¹' {code : OrderCode 2 | code 0 1 = true ∨ code 1 0 = true} =
      {w | chronological3 (w 0) (w 1) ∨ chronological3 (w 1) (w 0)} := by
    ext w
    simp [sampledOrder3]
  rw [he]
  have hm := congrArg ENNReal.toReal
    ((measurePreserving_finTwoArrow (densityMeasure3 (timeQuadraticDensity3 theta))).measure_preimage
      measurableSet_comparable_pairs3.nullMeasurableSet)
  exact hm.trans (time_quadratic_comparable_pair_probability3 ht)

theorem time_comparable_probability_difference3 (theta phi : ℝ) :
    timeComparableProbability3 theta-timeComparableProbability3 phi =
      (theta-phi)*(72/1925-(302/375375)*(theta+phi)) := by
  unfold timeComparableProbability3 timeOrderedPairProbability3
  ring

theorem time_comparable_probability_conditioning3 {theta phi : ℝ}
    (ht : theta ∈ Icc (0 : ℝ) (1/2)) (hf : phi ∈ Icc (0 : ℝ) (1/2)) :
    (13738/375375)*|theta-phi| ≤ |timeComparableProbability3 theta-timeComparableProbability3 phi| := by
  have hc : (13738/375375 : ℝ) ≤ 72/1925-(302/375375)*(theta+phi) := by
    linarith [ht.2,hf.2]
  rw [time_comparable_probability_difference3,abs_mul,
    abs_of_nonneg ((by norm_num : (0 : ℝ) ≤ 13738/375375).trans hc)]
  nlinarith [abs_nonneg (theta-phi)]

theorem time_comparable_probability_strictMono3 :
    StrictMonoOn timeComparableProbability3 (Icc (0 : ℝ) (1/2)) := by
  intro theta ht phi hf hlt
  have hc : (0 : ℝ) < 72/1925-(302/375375)*(phi+theta) := by
    linarith [ht.2,hf.2]
  have hd := mul_pos (sub_pos.mpr hlt) hc
  rw [← time_comparable_probability_difference3] at hd
  exact sub_pos.mp hd

/-- Restricted inverse conditioning for the accepted geometric quotient loss. -/
theorem time_quadratic_geometric_pair_inverse3 {theta phi : ℝ}
    (ht : theta ∈ Icc (0 : ℝ) (1/2)) (hf : phi ∈ Icc (0 : ℝ) (1/2)) :
    geometricDistortion3 (time_quadratic_density_class3 ht) (time_quadratic_density_class3 hf) ≤
      (225225/54952)*|timeComparableProbability3 theta-timeComparableProbability3 phi| := by
  have hg := time_quadratic_geometric_bound3 ht hf
  have hc := time_comparable_probability_conditioning3 ht hf
  linarith

/-- Equality of the original two-point order laws identifies this restricted parameter. -/
theorem time_quadratic_parameter_identifiable3 {theta phi : ℝ}
    (ht : theta ∈ Icc (0 : ℝ) (1/2)) (hf : phi ∈ Icc (0 : ℝ) (1/2))
    (he : orderLaw3 (timeQuadraticDensity3 theta) 2 = orderLaw3 (timeQuadraticDensity3 phi) 2) :
    theta = phi := by
  apply time_comparable_probability_strictMono3.injOn ht hf
  rw [← time_quadratic_order_law_comparable3 ht,he,time_quadratic_order_law_comparable3 hf]

#print axioms time_quadratic_comparable_pair_probability3
#print axioms time_quadratic_order_law_comparable3
#print axioms time_comparable_probability_conditioning3
#print axioms time_quadratic_geometric_pair_inverse3
#print axioms time_quadratic_parameter_identifiable3
end
end QuantyraNullCone
