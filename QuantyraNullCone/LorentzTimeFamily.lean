import QuantyraNullCone.LorentzTimeMoments

namespace QuantyraNullCone
open MeasureTheory Set
noncomputable section
set_option maxHeartbeats 800000

def timeQuadraticShape3 (p : LorentzPoint3) : ℝ := p 0 ^ 2 - 1/10
def timeQuadraticDensity3 (theta : ℝ) (p : LorentzPoint3) : ℝ :=
  1 + theta * timeQuadraticShape3 p

theorem continuous_time_quadratic_shape3 : Continuous timeQuadraticShape3 := by
  unfold timeQuadraticShape3
  fun_prop

theorem time_quadratic_shape_mean3 :
    (∫ p, timeQuadraticShape3 p ∂flatDiamondMeasure3) = 0 := by
  letI := flat_diamond_probability3
  have hi : Integrable (fun p : LorentzPoint3 => p 0 ^ 2) flatDiamondMeasure3 :=
    continuous_integrable_flat3 (by fun_prop)
  change (∫ p : LorentzPoint3, p 0 ^ 2 - 1/10 ∂flatDiamondMeasure3) = 0
  rw [integral_sub hi (integrable_const (1/10)), flat_time_second_moment3]
  simp

theorem time_quadratic_shape_second_moment3 :
    (∫ p, timeQuadraticShape3 p ^ 2 ∂flatDiamondMeasure3) = 13/700 := by
  letI := flat_diamond_probability3
  have h2 : Integrable (fun p : LorentzPoint3 => p 0 ^ 2) flatDiamondMeasure3 :=
    continuous_integrable_flat3 (by fun_prop)
  have h4 : Integrable (fun p : LorentzPoint3 => p 0 ^ 4) flatDiamondMeasure3 :=
    continuous_integrable_flat3 (by fun_prop)
  have he : (fun p => timeQuadraticShape3 p ^ 2) =
      (fun p : LorentzPoint3 => p 0 ^ 4 - (1/5)*p 0 ^ 2 + 1/100) := by
    funext p
    unfold timeQuadraticShape3
    ring
  have hsub : Integrable (fun p : LorentzPoint3 => p 0 ^ 4 - (1/5)*p 0 ^ 2)
      flatDiamondMeasure3 := h4.sub (h2.const_mul (1/5))
  rw [he, integral_add hsub (integrable_const (1/100)),
    integral_sub h4 (h2.const_mul (1/5)), integral_const_mul,
    flat_time_second_moment3, flat_time_fourth_moment3]
  norm_num

theorem time_quadratic_density_bounds3 {theta : ℝ} (ht : theta ∈ Icc (0 : ℝ) (1/2))
    {p : LorentzPoint3} (hp : p ∈ closedLorentzDiamond3) :
    19/20 ≤ timeQuadraticDensity3 theta p ∧ timeQuadraticDensity3 theta p ≤ 29/20 := by
  have ha := (closed_lorentz_diamond_bounds3 hp).1
  have hsq : p 0 ^ 2 ≤ 1 := by nlinarith [sq_abs (p 0), abs_nonneg (p 0)]
  have h0 := mul_nonneg ht.1 (sq_nonneg (p 0))
  have h1 := mul_nonneg ht.1 (sub_nonneg.mpr hsq)
  dsimp [timeQuadraticDensity3, timeQuadraticShape3]
  constructor <;> nlinarith [ht.2]

theorem time_quadratic_density_class3 {theta : ℝ} (ht : theta ∈ Icc (0 : ℝ) (1/2)) :
    InDensityClass3 (timeQuadraticDensity3 theta) := by
  letI := flat_diamond_probability3
  constructor
  · refine ⟨univ, isOpen_univ, subset_univ _, ?_⟩
    apply ContDiff.contDiffOn
    unfold timeQuadraticDensity3 timeQuadraticShape3
    fun_prop
  · intro p hp
    have h := time_quadratic_density_bounds3 ht hp
    constructor <;> linarith
  · intro p hp q hq
    have hab : |p 0 + q 0| ≤ 2 :=
      (abs_add_le _ _).trans (by linarith [(closed_lorentz_diamond_bounds3 hp).1,
        (closed_lorentz_diamond_bounds3 hq).1])
    have hd := lorentz_coordinate_sub_bound3 p q 0
    have hsq : |p 0 ^ 2 - q 0 ^ 2| ≤ 2 * ‖p-q‖ := by
      rw [show p 0 ^ 2 - q 0 ^ 2 = (p 0-q 0)*(p 0+q 0) by ring, abs_mul]
      have h := mul_le_mul hd hab (abs_nonneg _) (norm_nonneg _)
      linarith
    have he : timeQuadraticDensity3 theta p - timeQuadraticDensity3 theta q =
        theta * (p 0 ^ 2 - q 0 ^ 2) := by
      unfold timeQuadraticDensity3 timeQuadraticShape3
      ring
    rw [he, abs_mul, abs_of_nonneg ht.1]
    have h := mul_le_mul_of_nonneg_left hsq ht.1
    nlinarith [ht.2, norm_nonneg (p-q)]
  · have hi := continuous_integrable_flat3 continuous_time_quadratic_shape3
    change (∫ p, 1 + theta * timeQuadraticShape3 p ∂flatDiamondMeasure3) = 1
    rw [integral_add (integrable_const _) (hi.const_mul _),
      integral_const_mul, time_quadratic_shape_mean3]
    simp

theorem time_quadratic_density_difference3 (theta phi : ℝ) (p : LorentzPoint3) :
    |timeQuadraticDensity3 theta p - timeQuadraticDensity3 phi p| =
      |theta-phi| * |timeQuadraticShape3 p| := by
  rw [show timeQuadraticDensity3 theta p - timeQuadraticDensity3 phi p =
    (theta-phi)*timeQuadraticShape3 p by unfold timeQuadraticDensity3; ring, abs_mul]

#print axioms time_quadratic_shape_mean3
#print axioms time_quadratic_shape_second_moment3
#print axioms time_quadratic_density_bounds3
#print axioms time_quadratic_density_class3
#print axioms time_quadratic_density_difference3
end
end QuantyraNullCone
