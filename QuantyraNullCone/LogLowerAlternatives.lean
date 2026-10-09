import QuantyraNullCone.LogLowerMoments

namespace QuantyraNullCone

open MeasureTheory

noncomputable def logLowerAlternative (h c : ℝ) (p : DiamondPoint) : ℝ :=
  1 + (h/2) * logLowerProfile h c p.1 * logLowerProfile h c p.2

theorem log_lower_alternative_smooth (h c : ℝ) : ContDiff ℝ ⊤ (logLowerAlternative h c) := by
  unfold logLowerAlternative logLowerProfile logLowerRaw oddGaussian
  fun_prop

theorem log_lower_alternative_deviation {h : ℝ} (hh : 0 < h) (hSmall : h ≤ 1/16)
    (c : ℝ) (p : DiamondPoint) : |logLowerAlternative h c p - 1| ≤ h/2 := by
  have hp := mul_le_mul (log_lower_profile_abs_le_one hh hSmall c p.1)
    (log_lower_profile_abs_le_one hh hSmall c p.2) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  have hm := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ h/2)
  simp only [logLowerAlternative, add_sub_cancel_left, abs_mul,
    abs_of_pos (by positivity : 0 < h/2)]
  nlinarith only [hm]

theorem log_lower_alternative_bounds {h : ℝ} (hh : 0 < h) (hSmall : h ≤ 1/16)
    (c : ℝ) (p : DiamondPoint) :
    (1/2 : ℝ) ≤ logLowerAlternative h c p ∧ logLowerAlternative h c p ≤ 3/2 := by
  obtain ⟨hLo,hHi⟩ := abs_le.mp (log_lower_alternative_deviation hh hSmall c p)
  constructor <;> linarith

theorem log_lower_alternative_lipschitz {h : ℝ} (hh : 0 < h) (hSmall : h ≤ 1/16)
    (c : ℝ) (p q : DiamondPoint) :
    |logLowerAlternative h c p-logLowerAlternative h c q| ≤
      (|p.1-q.1|+|p.2-q.2|)/2 := by
  have hOne := mul_le_mul (log_lower_profile_lipschitz hh c p.1 q.1)
    (log_lower_profile_abs_le_one hh hSmall c p.2) (abs_nonneg _)
    (by positivity : 0 ≤ |p.1-q.1|/h)
  have hTwo := mul_le_mul (log_lower_profile_abs_le_one hh hSmall c q.1)
    (log_lower_profile_lipschitz hh c p.2 q.2) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  have hEq : logLowerAlternative h c p-logLowerAlternative h c q =
      (h/2) * ((logLowerProfile h c p.1-logLowerProfile h c q.1)*logLowerProfile h c p.2 +
        logLowerProfile h c q.1*(logLowerProfile h c p.2-logLowerProfile h c q.2)) := by
    unfold logLowerAlternative
    ring
  rw [hEq, abs_mul, abs_of_pos (by positivity : 0 < h/2)]
  calc
    _ ≤ (h/2) * (|(logLowerProfile h c p.1-logLowerProfile h c q.1)*logLowerProfile h c p.2| +
        |logLowerProfile h c q.1*(logLowerProfile h c p.2-logLowerProfile h c q.2)|) :=
      mul_le_mul_of_nonneg_left (abs_add_le _ _) (by positivity)
    _ ≤ (h/2) * ((|p.1-q.1|/h)*1 + 1*(|p.2-q.2|/h)) := by
      simp only [abs_mul]
      exact mul_le_mul_of_nonneg_left (add_le_add hOne hTwo) (by positivity)
    _ = _ := by field_simp [hh.ne']

theorem log_lower_alternative_transpose (h c : ℝ) (p : DiamondPoint) :
    logLowerAlternative h c (transposePoint p) = logLowerAlternative h c p := by
  unfold logLowerAlternative transposePoint
  ring

theorem log_lower_alternative_marginal (h c u : ℝ) :
    (∫ v in (0:ℝ)..1, logLowerAlternative h c (u,v)) = 1 := by
  change (∫ v in (0:ℝ)..1, 1 + ((h/2)*logLowerProfile h c u)*logLowerProfile h c v) = 1
  rw [intervalIntegral.integral_add intervalIntegrable_const
    (((log_lower_profile_smooth h c).continuous.intervalIntegrable 0 1).const_mul _),
    intervalIntegral.integral_const_mul, log_lower_profile_integral_zero]
  simp

theorem log_lower_alternative_in_class {h : ℝ} (hh : 0 < h) (hSmall : h ≤ 1/16)
    (c : ℝ) : InDensityClass (logLowerAlternative h c) := by
  refine ⟨⟨Set.univ,isOpen_univ,Set.subset_univ _,(log_lower_alternative_smooth h c).contDiffOn⟩,
    fun p _ => log_lower_alternative_bounds hh hSmall c p, ?_,
    fun u _ => log_lower_alternative_marginal h c u, ?_⟩
  · intro p _ q _
    have hx : |p.1-q.1| ≤ Real.sqrt ((p.1-q.1)^2+(p.2-q.2)^2) := by
      apply Real.le_sqrt_of_sq_le
      rw [sq_abs]
      nlinarith only [sq_nonneg (p.2-q.2)]
    have hy : |p.2-q.2| ≤ Real.sqrt ((p.1-q.1)^2+(p.2-q.2)^2) := by
      apply Real.le_sqrt_of_sq_le
      rw [sq_abs]
      nlinarith only [sq_nonneg (p.1-q.1)]
    have hb := log_lower_alternative_lipschitz hh hSmall c p q
    nlinarith [Real.sqrt_nonneg ((p.1-q.1)^2+(p.2-q.2)^2)]
  · intro v _
    have hEq : (fun u => logLowerAlternative h c (u,v)) =
        (fun u => logLowerAlternative h c (v,u)) := by
      funext u
      exact log_lower_alternative_transpose h c (v,u)
    rw [hEq]
    exact log_lower_alternative_marginal h c v

theorem log_lower_single_moment {h : ℝ} (hh : 0 < h) (c : ℝ) :
    (∫ p, (logLowerAlternative h c p - 1)^2 ∂diamondVolume) ≤ h^4/4 := by
  have hEq : (fun p : DiamondPoint => (logLowerAlternative h c p - 1)^2) =
      (fun p => (h^2/4)*(logLowerProfile h c p.1^2*logLowerProfile h c p.2^2)) := by
    funext p
    unfold logLowerAlternative
    ring
  rw [hEq, integral_const_mul]
  have hMeasure : diamondVolume =
      ((volume : Measure ℝ).restrict (Set.Icc 0 1)).prod (volume.restrict (Set.Icc 0 1)) := by
    rw [Measure.prod_restrict]
    rfl
  rw [hMeasure, integral_prod_mul (fun x : ℝ => logLowerProfile h c x^2)
    (fun x : ℝ => logLowerProfile h c x^2),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  obtain ⟨hNonneg,hBound⟩ := log_lower_profile_moment hh c
  have hSq := pow_le_pow_left₀ hNonneg hBound 2
  have hm := mul_le_mul_of_nonneg_left hSq (by positivity : 0 ≤ h^2/4)
  nlinarith only [hm]

#print axioms log_lower_alternative_smooth
#print axioms log_lower_alternative_deviation
#print axioms log_lower_alternative_bounds
#print axioms log_lower_alternative_lipschitz
#print axioms log_lower_alternative_transpose
#print axioms log_lower_alternative_marginal
#print axioms log_lower_alternative_in_class
#print axioms log_lower_single_moment

end QuantyraNullCone
