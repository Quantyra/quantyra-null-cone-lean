import QuantyraNullCone.OddGaussian

namespace QuantyraNullCone

open MeasureTheory

def lowerFlat (_ : DiamondPoint) : ℝ := 1

noncomputable def lowerAlternative (h : ℝ) (p : DiamondPoint) : ℝ :=
  1 + 2 * h * lowerProfile h p.1 * lowerProfile h p.2

theorem lower_alternative_smooth (h : ℝ) : ContDiff ℝ ⊤ (lowerAlternative h) := by
  unfold lowerAlternative lowerProfile oddGaussian
  fun_prop

theorem lower_alternative_deviation {h : ℝ} (hh : 0 ≤ h) (p : DiamondPoint) :
    |lowerAlternative h p - 1| ≤ h / 2 := by
  have hProd := mul_le_mul (lower_profile_abs_le h p.1) (lower_profile_abs_le h p.2)
    (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hMul := mul_le_mul_of_nonneg_left hProd (by positivity : 0 ≤ 2 * h)
  simp only [lowerAlternative, add_sub_cancel_left, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hh]
  nlinarith only [hMul]

theorem lower_alternative_bounds {h : ℝ} (hh : 0 ≤ h) (hSmall : h ≤ 1 / 2) (p : DiamondPoint) :
    (1 / 2 : ℝ) ≤ lowerAlternative h p ∧ lowerAlternative h p ≤ 3 / 2 := by
  obtain ⟨hLo, hHi⟩ := abs_le.mp (lower_alternative_deviation hh p)
  constructor <;> linarith

theorem lower_alternative_coordinate_lipschitz {h : ℝ} (hh : 0 < h) (p q : DiamondPoint) :
    |lowerAlternative h p - lowerAlternative h q| ≤ |p.1 - q.1| + |p.2 - q.2| := by
  have hOne := mul_le_mul (lower_profile_lipschitz hh p.1 q.1)
    (lower_profile_abs_le h p.2) (abs_nonneg _)
    (by positivity : 0 ≤ |p.1 - q.1| / h)
  have hTwo := mul_le_mul (lower_profile_abs_le h q.1)
    (lower_profile_lipschitz hh p.2 q.2) (abs_nonneg _)
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hDecomp : lowerAlternative h p - lowerAlternative h q =
      2 * h * ((lowerProfile h p.1 - lowerProfile h q.1) * lowerProfile h p.2 +
        lowerProfile h q.1 * (lowerProfile h p.2 - lowerProfile h q.2)) := by
    unfold lowerAlternative
    ring
  rw [hDecomp, abs_mul, abs_of_pos (by positivity : 0 < 2 * h)]
  calc
    _ ≤ 2 * h * (|(lowerProfile h p.1 - lowerProfile h q.1) * lowerProfile h p.2| +
        |lowerProfile h q.1 * (lowerProfile h p.2 - lowerProfile h q.2)|) := by
      exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (by positivity)
    _ ≤ 2 * h * ((|p.1 - q.1| / h) * (1 / 2) + (1 / 2) * (|p.2 - q.2| / h)) := by
      simp only [abs_mul]
      exact mul_le_mul_of_nonneg_left (add_le_add hOne hTwo) (by positivity)
    _ = _ := by field_simp [hh.ne']

theorem lower_alternative_euclidean_lipschitz {h : ℝ} (hh : 0 < h) (p q : DiamondPoint) :
    |lowerAlternative h p - lowerAlternative h q| ≤
      2 * Real.sqrt ((p.1 - q.1)^2 + (p.2 - q.2)^2) := by
  have hx : |p.1 - q.1| ≤ Real.sqrt ((p.1 - q.1)^2 + (p.2 - q.2)^2) := by
    apply Real.le_sqrt_of_sq_le
    rw [sq_abs]
    nlinarith only [sq_nonneg (p.2 - q.2)]
  have hy : |p.2 - q.2| ≤ Real.sqrt ((p.1 - q.1)^2 + (p.2 - q.2)^2) := by
    apply Real.le_sqrt_of_sq_le
    rw [sq_abs]
    nlinarith only [sq_nonneg (p.1 - q.1)]
  exact (lower_alternative_coordinate_lipschitz hh p q).trans (by linarith)

theorem lower_alternative_transpose (h : ℝ) (p : DiamondPoint) :
    lowerAlternative h (transposePoint p) = lowerAlternative h p := by
  unfold lowerAlternative transposePoint
  ring

theorem lower_alternative_marginal {h : ℝ} (hh : h ≠ 0) (u : ℝ) :
    (∫ v in (0 : ℝ)..1, lowerAlternative h (u, v)) = 1 := by
  change (∫ v in (0 : ℝ)..1, 1 + (2 * h * lowerProfile h u) * lowerProfile h v) = 1
  rw [intervalIntegral.integral_add ((continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).intervalIntegrable 0 1)
    (((lower_profile_smooth h).continuous.intervalIntegrable 0 1).const_mul _),
    intervalIntegral.integral_const_mul, lower_profile_integral_zero hh]
  simp

theorem lower_flat_in_class : InDensityClass lowerFlat := by
  refine ⟨⟨Set.univ, isOpen_univ, Set.subset_univ _, ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact contDiffOn_const
  · intro p _
    norm_num [lowerFlat]
  · intro p _ q _
    simp only [lowerFlat, sub_self, abs_zero]
    positivity
  · intro u _
    simp [lowerFlat]
  · intro v _
    simp [lowerFlat]

/-- The alternatives satisfy the full original smooth, uniformly marginal,
Euclidean-Lipschitz density class. No weaker closure class is substituted. -/
theorem lower_alternative_in_class {h : ℝ} (hh : 0 < h) (hSmall : h ≤ 1 / 2) :
    InDensityClass (lowerAlternative h) := by
  refine ⟨⟨Set.univ, isOpen_univ, Set.subset_univ _, (lower_alternative_smooth h).contDiffOn⟩,
    fun p _ => lower_alternative_bounds hh.le hSmall p,
    fun p _ q _ => lower_alternative_euclidean_lipschitz hh p q,
    fun u _ => lower_alternative_marginal hh.ne' u, ?_⟩
  intro v _
  have hEq : (fun u => lowerAlternative h (u, v)) = (fun u => lowerAlternative h (v, u)) := by
    funext u
    exact lower_alternative_transpose h (v, u)
  rw [hEq]
  exact lower_alternative_marginal hh.ne' v

#print axioms lower_alternative_smooth
#print axioms lower_alternative_deviation
#print axioms lower_alternative_bounds
#print axioms lower_alternative_coordinate_lipschitz
#print axioms lower_alternative_euclidean_lipschitz
#print axioms lower_alternative_transpose
#print axioms lower_alternative_marginal
#print axioms lower_flat_in_class
#print axioms lower_alternative_in_class

end QuantyraNullCone
