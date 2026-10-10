import QuantyraNullCone.LorentzTriangleMoments
import QuantyraNullCone.LorentzIntervalMoments

namespace QuantyraNullCone
open MeasureTheory Set
noncomputable section
set_option maxHeartbeats 1600000

theorem integral_triangle_polynomial3 {m n : ℕ} (c : Fin m → Fin n → ℝ) :
    (∫ z in lightConeTriangle3, lightConeWeight3 z*
      (∑ i : Fin m, ∑ j : Fin n, c i j*z.1^(i : ℕ)*z.2^(j : ℕ))) =
      ∑ i : Fin m, ∑ j : Fin n,
        c i j/(((i : ℕ) + (5 : ℝ)/2)*((i : ℕ)+(7 : ℝ)/2)*((i : ℕ)+(j : ℕ)+(6 : ℝ))) := by
  have hi (i : Fin m) (j : Fin n) : IntegrableOn
      (fun z => c i j*(lightConeWeight3 z*z.1^(i : ℕ)*z.2^(j : ℕ))) lightConeTriangle3 volume :=
    integrableOn_triangle_continuous3 (continuous_const.mul
      ((continuous_lightConeWeight3.mul (continuous_fst.pow _)).mul (continuous_snd.pow _)))
  have he : (fun z => lightConeWeight3 z*
      (∑ i : Fin m, ∑ j : Fin n, c i j*z.1^(i : ℕ)*z.2^(j : ℕ))) =
      (fun z => ∑ i : Fin m, ∑ j : Fin n, c i j*(lightConeWeight3 z*z.1^(i : ℕ)*z.2^(j : ℕ))) := by
    funext z
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he,integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hi i j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul,integral_triangle_monomial3]
  ring

def timePairCoefficients3 (theta : ℝ) : Fin 5 → Fin 5 → ℝ :=
  ![![1+(9/5)*theta+(81/100)*theta^2,-3*theta-(27/10)*theta^2,
      (21/16)*theta+(509/160)*theta^2,-(13/8)*theta^2,(5/16)*theta^2],
    ![-3*theta-(27/10)*theta^2,(99/40)*theta+(2491/400)*theta^2,
      -(183/40)*theta^2,(11/10)*theta^2,0],
    ![(21/16)*theta+(509/160)*theta^2,-(183/40)*theta^2,(63/40)*theta^2,0,0],
    ![-(13/8)*theta^2,(11/10)*theta^2,0,0,0],
    ![(5/16)*theta^2,0,0,0,0]]

theorem time_pair_polynomial3 (theta a b : ℝ) :
    (1+theta*((1-a-b)^2-1/10))*
      (1+theta*((7+18*(1-a-b)+11*(1-a-b)^2)/40+(3/80)*(b-a)^2)) =
      ∑ i : Fin 5, ∑ j : Fin 5, timePairCoefficients3 theta i j*a^(i : ℕ)*b^(j : ℕ) := by
  simp [timePairCoefficients3,Fin.sum_univ_succ]
  ring

def radialFutureVolume3 (z : ℝ × ℝ) : ℝ := (Real.sqrt ((1-z.1)^2-z.2^2)/2)^3

theorem continuous_radialFutureVolume3 : Continuous radialFutureVolume3 := by
  unfold radialFutureVolume3
  fun_prop

theorem radial_future_volume_light_cone3 {z : ℝ × ℝ} (hz : z ∈ lightConeTriangle3) :
    radialFutureVolume3 (lightConeMap3 z) = (z.1*z.2)^((3 : ℝ)/2) := by
  have h : (1-(1-z.1-z.2))^2-(z.2-z.1)^2 = 4*(z.1*z.2) := by ring
  dsimp [radialFutureVolume3,lightConeMap3]
  rw [h,Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  have h4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num,Real.sqrt_sq (by norm_num)]
  rw [h4,show 2*Real.sqrt (z.1*z.2)/2 = Real.sqrt (z.1*z.2) by ring]
  rw [Real.sqrt_eq_rpow,← Real.rpow_natCast,← Real.rpow_mul (mul_pos hz.1 (hz.1.trans hz.2.1)).le]
  norm_num

theorem radial_future_volume_duration3 (p : LorentzPoint3) :
    radialFutureVolume3 (p 0,spatialRadius3 p) = (intervalDuration3 p lorentzTop3/2)^3 := by
  unfold radialFutureVolume3 intervalDuration3
  rw [spatial_radius_sq3]
  congr 3
  simp [lorentzSquare3,spatialSquared3,lorentzTop3,lorentzPoint3]
  ring

def timePairRadialIntegrand3 (theta : ℝ) (z : ℝ × ℝ) : ℝ :=
  radialFutureVolume3 z*(1+theta*(z.1^2-1/10))*
    (1+theta*((7+18*z.1+11*z.1^2)/40+(3/80)*z.2^2))

theorem time_pair_outer_integral3 (theta : ℝ) :
    (∫ p, (intervalDuration3 p lorentzTop3/2)^3*
      timeQuadraticDensity3 theta p*(1+theta*futureTimeShapeMean3 p) ∂flatDiamondMeasure3) =
      4/35+(36/1925)*theta-(151/375375)*theta^2 := by
  have he : (fun p => (intervalDuration3 p lorentzTop3/2)^3*
      timeQuadraticDensity3 theta p*(1+theta*futureTimeShapeMean3 p)) =
      (fun p => timePairRadialIntegrand3 theta (p 0,spatialRadius3 p)) := by
    funext p
    simp [timePairRadialIntegrand3,radial_future_volume_duration3,timeQuadraticDensity3,
      timeQuadraticShape3,futureTimeShapeMean3,spatial_radius_sq3]
  rw [he,integral_flat_light_cone_triangle3 (H := timePairRadialIntegrand3 theta)
    (by unfold timePairRadialIntegrand3; exact
      (continuous_radialFutureVolume3.mul (by fun_prop)).mul (by fun_prop))]
  have ht : (∫ z in lightConeTriangle3, (z.2-z.1)*timePairRadialIntegrand3 theta (lightConeMap3 z)) =
      ∫ z in lightConeTriangle3, lightConeWeight3 z*
        (∑ i : Fin 5, ∑ j : Fin 5, timePairCoefficients3 theta i j*z.1^(i : ℕ)*z.2^(j : ℕ)) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem isOpen_lightConeTriangle3.measurableSet] with z hz
    rw [← time_pair_polynomial3]
    unfold timePairRadialIntegrand3
    rw [radial_future_volume_light_cone3 hz]
    dsimp [lightConeMap3,lightConeWeight3]
    ring
  rw [ht,integral_triangle_polynomial3]
  norm_num [Fin.sum_univ_succ,timePairCoefficients3]
  ring

#print axioms integral_triangle_polynomial3
#print axioms time_pair_polynomial3
#print axioms radial_future_volume_light_cone3
#print axioms time_pair_outer_integral3
end
end QuantyraNullCone
