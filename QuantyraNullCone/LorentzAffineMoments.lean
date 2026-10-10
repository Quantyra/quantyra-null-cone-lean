import QuantyraNullCone.LorentzSpatialMoments

namespace QuantyraNullCone
open MeasureTheory Set
noncomputable section
set_option maxHeartbeats 1000000

theorem flat_coordinate_product_moment3 (i j : Fin 3) :
    (∫ p : LorentzPoint3, p i*p j ∂flatDiamondMeasure3) =
      if i=j then (if i=0 then 1/10 else 3/20) else 0 := by
  by_cases h : i=j
  · subst j
    fin_cases i <;> simp only [ite_true,← pow_two]
    · exact flat_time_second_moment3
    · exact flat_spatial_coordinate_second_moment3.1
    · exact flat_spatial_coordinate_second_moment3.2
  · rw [if_neg h]
    exact flat_coordinate_cross_moment3 h

theorem flat_linear_mean3 (k : Fin 3 → ℝ) :
    (∫ p : LorentzPoint3, (∑ i : Fin 3, k i*p i) ∂flatDiamondMeasure3) = 0 := by
  rw [integral_finsetSum _ (fun i _ => continuous_integrable_flat3 (by fun_prop))]
  simp only [integral_const_mul,flat_coordinate_mean3,mul_zero,Finset.sum_const_zero]

theorem flat_linear_second_moment3 (k : Fin 3 → ℝ) :
    (∫ p : LorentzPoint3, (∑ i : Fin 3, k i*p i)^2 ∂flatDiamondMeasure3) =
      k 0^2/10+(3/20)*(k 1^2+k 2^2) := by
  have he : (fun p : LorentzPoint3 => (∑ i : Fin 3, k i*p i)^2) =
      (fun p => ∑ i : Fin 3, ∑ j : Fin 3, (k i*k j)*(p i*p j)) := by
    funext p
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
    ring
  rw [he,integral_finsetSum _ (fun i _ => continuous_integrable_flat3 (by fun_prop))]
  have hj (i : Fin 3) :
      (∫ p : LorentzPoint3, (∑ j : Fin 3, (k i*k j)*(p i*p j)) ∂flatDiamondMeasure3) =
        ∑ j : Fin 3, (k i*k j)*(∫ p : LorentzPoint3, p i*p j ∂flatDiamondMeasure3) := by
    rw [integral_finsetSum _ (fun j _ => continuous_integrable_flat3 (by fun_prop))]
    simp only [integral_const_mul]
  simp_rw [hj]
  simp [flat_coordinate_product_moment3,Fin.sum_univ_succ]
  ring

theorem flat_affine_second_moment3 (a : ℝ) (k : Fin 3 → ℝ) :
    (∫ p : LorentzPoint3, (a+∑ i : Fin 3, k i*p i)^2 ∂flatDiamondMeasure3) =
      a^2+k 0^2/10+(3/20)*(k 1^2+k 2^2) := by
  letI := flat_diamond_probability3
  have hi : Integrable (fun p : LorentzPoint3 => ∑ i : Fin 3, k i*p i) flatDiamondMeasure3 :=
    continuous_integrable_flat3 (by fun_prop)
  have hi2 : Integrable (fun p : LorentzPoint3 => (∑ i : Fin 3, k i*p i)^2) flatDiamondMeasure3 :=
    continuous_integrable_flat3 (by fun_prop)
  have hp : Integrable (fun p : LorentzPoint3 => a^2+(2*a)*(∑ i : Fin 3, k i*p i))
      flatDiamondMeasure3 := (integrable_const _).add (hi.const_mul _)
  have he : (fun p : LorentzPoint3 => (a+∑ i : Fin 3, k i*p i)^2) =
      (fun p => a^2+(2*a)*(∑ i : Fin 3, k i*p i)+(∑ i : Fin 3, k i*p i)^2) := by
    funext p
    ring
  rw [he,integral_add hp hi2,integral_add (integrable_const _) (hi.const_mul _),
    integral_const_mul,flat_linear_mean3,flat_linear_second_moment3]
  simp
  ring

#print axioms flat_coordinate_product_moment3
#print axioms flat_linear_mean3
#print axioms flat_linear_second_moment3
#print axioms flat_affine_second_moment3
end
end QuantyraNullCone
