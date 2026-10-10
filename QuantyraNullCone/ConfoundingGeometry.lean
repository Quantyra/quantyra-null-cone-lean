import QuantyraNullCone.LowerAlternatives
import QuantyraNullCone.ThinningGenerating

namespace QuantyraNullCone

open MeasureTheory

def calibrationProfile (t : ℝ) : ℝ := 2 * t - 1

def calibrationDensity (epsilon : ℝ) (p : DiamondPoint) : ℝ :=
  1 + epsilon * calibrationProfile p.1 * calibrationProfile p.2

theorem calibration_density_zero : calibrationDensity 0 = lowerFlat := by
  funext p
  simp [calibrationDensity, lowerFlat]

theorem calibration_profile_smooth : ContDiff ℝ ⊤ calibrationProfile := by
  unfold calibrationProfile
  fun_prop

theorem calibration_profile_abs {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |calibrationProfile t| ≤ 1 := by
  rw [abs_le]
  simp only [calibrationProfile]
  constructor <;> linarith [ht.1, ht.2]

theorem calibration_profile_difference (s t : ℝ) :
    |calibrationProfile s - calibrationProfile t| = 2 * |s-t| := by
  have h : calibrationProfile s - calibrationProfile t = 2 * (s-t) := by
    unfold calibrationProfile
    ring
  rw [h, abs_mul]
  norm_num

theorem calibration_profile_integral (b : ℝ) :
    (∫ t in (0 : ℝ)..b, calibrationProfile t) = b^2-b := by
  unfold calibrationProfile
  rw [intervalIntegral.integral_sub
    ((show Continuous (fun t : ℝ => 2*t) by fun_prop).intervalIntegrable 0 b)
    (continuous_const.intervalIntegrable 0 b), intervalIntegral.integral_const_mul]
  simp
  ring

theorem calibration_density_smooth (epsilon : ℝ) :
    ContDiff ℝ ⊤ (calibrationDensity epsilon) := by
  unfold calibrationDensity calibrationProfile
  fun_prop

theorem calibration_density_deviation {epsilon : ℝ} (he : 0 ≤ epsilon)
    {p : DiamondPoint} (hp : p ∈ diamond) : |calibrationDensity epsilon p - 1| ≤ epsilon := by
  have h := mul_le_mul (calibration_profile_abs hp.1) (calibration_profile_abs hp.2)
    (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hm := mul_le_mul_of_nonneg_left h he
  simpa [calibrationDensity, abs_mul, abs_of_nonneg he, mul_assoc] using hm

theorem calibration_density_bounds {epsilon : ℝ} (he : 0 ≤ epsilon)
    {p : DiamondPoint} (hp : p ∈ diamond) :
    1-epsilon ≤ calibrationDensity epsilon p ∧ calibrationDensity epsilon p ≤ 1+epsilon := by
  obtain ⟨hl, hu⟩ := abs_le.mp (calibration_density_deviation he hp)
  constructor <;> linarith

theorem calibration_density_coordinate_lipschitz {epsilon : ℝ} (he : 0 ≤ epsilon)
    {p q : DiamondPoint} (hp : p ∈ diamond) (hq : q ∈ diamond) :
    |calibrationDensity epsilon p - calibrationDensity epsilon q| ≤
      2 * epsilon * (|p.1-q.1| + |p.2-q.2|) := by
  have h1 := mul_le_mul_of_nonneg_left (calibration_profile_abs hp.2)
    (abs_nonneg (calibrationProfile p.1-calibrationProfile q.1))
  have h2 := mul_le_mul_of_nonneg_right (calibration_profile_abs hq.1)
    (abs_nonneg (calibrationProfile p.2-calibrationProfile q.2))
  have hd : calibrationDensity epsilon p-calibrationDensity epsilon q =
      epsilon * ((calibrationProfile p.1-calibrationProfile q.1)*calibrationProfile p.2 +
        calibrationProfile q.1*(calibrationProfile p.2-calibrationProfile q.2)) := by
    unfold calibrationDensity
    ring
  rw [hd, abs_mul, abs_of_nonneg he]
  calc
    _ ≤ epsilon * (|(calibrationProfile p.1-calibrationProfile q.1)*calibrationProfile p.2| +
        |calibrationProfile q.1*(calibrationProfile p.2-calibrationProfile q.2)|) :=
      mul_le_mul_of_nonneg_left (abs_add_le _ _) he
    _ ≤ epsilon * (|calibrationProfile p.1-calibrationProfile q.1| +
        |calibrationProfile p.2-calibrationProfile q.2|) := by
      simp only [abs_mul]
      apply mul_le_mul_of_nonneg_left _ he
      simpa using add_le_add h1 h2
    _ = _ := by rw [calibration_profile_difference, calibration_profile_difference]; ring

theorem calibration_density_euclidean_lipschitz {epsilon : ℝ}
    (he : 0 ≤ epsilon) (heSmall : epsilon ≤ 1/2)
    {p q : DiamondPoint} (hp : p ∈ diamond) (hq : q ∈ diamond) :
    |calibrationDensity epsilon p-calibrationDensity epsilon q| ≤
      2 * Real.sqrt ((p.1-q.1)^2+(p.2-q.2)^2) := by
  have hx : |p.1-q.1| ≤ Real.sqrt ((p.1-q.1)^2+(p.2-q.2)^2) := by
    apply Real.le_sqrt_of_sq_le
    rw [sq_abs]
    nlinarith only [sq_nonneg (p.2-q.2)]
  have hy : |p.2-q.2| ≤ Real.sqrt ((p.1-q.1)^2+(p.2-q.2)^2) := by
    apply Real.le_sqrt_of_sq_le
    rw [sq_abs]
    nlinarith only [sq_nonneg (p.1-q.1)]
  apply (calibration_density_coordinate_lipschitz he hp hq).trans
  have hsum : 0 ≤ |p.1-q.1| + |p.2-q.2| := by positivity
  nlinarith

theorem calibration_density_transpose (epsilon : ℝ) (p : DiamondPoint) :
    calibrationDensity epsilon (transposePoint p) = calibrationDensity epsilon p := by
  unfold calibrationDensity transposePoint
  ring

theorem calibration_density_marginal (epsilon u : ℝ) :
    (∫ v in (0 : ℝ)..1, calibrationDensity epsilon (u,v)) = 1 := by
  change (∫ v in (0 : ℝ)..1, 1 + (epsilon * calibrationProfile u) * calibrationProfile v) = 1
  rw [intervalIntegral.integral_add (continuous_const.intervalIntegrable 0 1)
    ((calibration_profile_smooth.continuous.intervalIntegrable 0 1).const_mul _),
    intervalIntegral.integral_const_mul, calibration_profile_integral]
  norm_num

/-- The unchanged smooth, Euclidean-Lipschitz, uniform-marginal geometric class. -/
theorem calibration_density_in_class {epsilon : ℝ} (he : 0 ≤ epsilon)
    (heSmall : epsilon ≤ 1/2) : InDensityClass (calibrationDensity epsilon) := by
  refine ⟨⟨Set.univ, isOpen_univ, Set.subset_univ _, (calibration_density_smooth epsilon).contDiffOn⟩,
    ?_, fun _ hp _ hq => calibration_density_euclidean_lipschitz he heSmall hp hq,
    fun u _ => calibration_density_marginal epsilon u, ?_⟩
  · intro p hp
    obtain ⟨hl, hu⟩ := calibration_density_bounds he hp
    constructor <;> linarith
  · intro v _
    have h : (fun u => calibrationDensity epsilon (u,v)) =
        (fun u => calibrationDensity epsilon (v,u)) := by
      funext u
      exact calibration_density_transpose epsilon (v,u)
    rw [h]
    exact calibration_density_marginal epsilon v

end QuantyraNullCone
