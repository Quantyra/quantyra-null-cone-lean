import QuantyraNullCone.LowerBound

namespace QuantyraNullCone

open MeasureTheory

noncomputable def logLowerRaw (h c x : ℝ) : ℝ := oddGaussian ((x - c) / h)

noncomputable def logLowerMean (h c : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, logLowerRaw h c x

noncomputable def logLowerProfile (h c x : ℝ) : ℝ :=
  logLowerRaw h c x - logLowerMean h c

theorem log_lower_raw_smooth (h c : ℝ) : ContDiff ℝ ⊤ (logLowerRaw h c) := by
  unfold logLowerRaw oddGaussian
  fun_prop

theorem log_lower_profile_smooth (h c : ℝ) : ContDiff ℝ ⊤ (logLowerProfile h c) := by
  exact (log_lower_raw_smooth h c).sub contDiff_const

theorem log_lower_raw_primitive {h : ℝ} (hh : h ≠ 0) (c x : ℝ) :
    HasDerivAt (fun t : ℝ => -(h / 2) * Real.exp (-(((t - c) / h) ^ 2)))
      (logLowerRaw h c x) x := by
  have hD := (((((hasDerivAt_id x).sub_const c).div_const h).pow 2).neg.exp).const_mul (-(h / 2))
  convert hD using 1
  dsimp [logLowerRaw, oddGaussian]
  field_simp [hh]

theorem log_lower_mean_formula {h : ℝ} (hh : h ≠ 0) (c : ℝ) :
    logLowerMean h c = (h / 2) *
      (Real.exp (-((c / h)^2)) - Real.exp (-(((1-c)/h)^2))) := by
  unfold logLowerMean
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => log_lower_raw_primitive hh c x)
    ((log_lower_raw_smooth h c).continuous.intervalIntegrable 0 1)]
  have hSq : ((0 - c) / h)^2 = (c / h)^2 := by ring
  rw [hSq]
  ring

theorem log_lower_mean_bound {h : ℝ} (hh : 0 < h) (c : ℝ) :
    |logLowerMean h c| ≤ h / 2 := by
  have hExp (t : ℝ) : 0 ≤ Real.exp (-(t^2)) ∧ Real.exp (-(t^2)) ≤ 1 := by
    refine ⟨(Real.exp_pos _).le, ?_⟩
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (neg_nonpos.mpr (sq_nonneg t))
  obtain ⟨ha, ha1⟩ := hExp (c/h)
  obtain ⟨hb, hb1⟩ := hExp ((1-c)/h)
  have hd : |Real.exp (-((c/h)^2)) - Real.exp (-(((1-c)/h)^2))| ≤ 1 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  rw [log_lower_mean_formula hh.ne', abs_mul, abs_of_pos (by positivity : 0 < h/2)]
  nlinarith [mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ h/2)]

theorem log_lower_profile_integral_zero (h c : ℝ) :
    (∫ x in (0 : ℝ)..1, logLowerProfile h c x) = 0 := by
  unfold logLowerProfile
  rw [intervalIntegral.integral_sub
    ((log_lower_raw_smooth h c).continuous.intervalIntegrable 0 1) intervalIntegrable_const]
  simp [logLowerMean]

theorem log_lower_profile_bound {h : ℝ} (hh : 0 < h) (c x : ℝ) :
    |logLowerProfile h c x| ≤ 1/2 + h/2 := by
  exact (abs_sub _ _).trans (add_le_add (odd_gaussian_abs_le _) (log_lower_mean_bound hh c))

theorem log_lower_profile_abs_le_one {h : ℝ} (hh : 0 < h) (hSmall : h ≤ 1/16)
    (c x : ℝ) : |logLowerProfile h c x| ≤ 1 := by
  have hp := log_lower_profile_bound hh c x
  linarith

theorem log_lower_profile_lipschitz {h : ℝ} (hh : 0 < h) (c x y : ℝ) :
    |logLowerProfile h c x - logLowerProfile h c y| ≤ |x-y|/h := by
  have hEq : logLowerProfile h c x - logLowerProfile h c y =
      oddGaussian ((x-c)/h) - oddGaussian ((y-c)/h) := by
    unfold logLowerProfile logLowerRaw
    ring
  rw [hEq]
  calc
    _ ≤ |(x-c)/h - (y-c)/h| := odd_gaussian_lipschitz _ _
    _ = _ := by rw [← sub_div, show x-c-(y-c)=x-y by ring, abs_div, abs_of_pos hh]

theorem log_lower_gaussian_peak : (3/8 : ℝ) ≤ oddGaussian (1/2) := by
  have hExp := Real.add_one_le_exp (-(1/4 : ℝ))
  norm_num [oddGaussian] at *
  linarith

theorem log_lower_gaussian_tail (t : ℝ) (ht : 4 ≤ |t|) :
    |oddGaussian t| ≤ 1/16 := by
  have hHalf := Real.add_one_le_exp (t^2/2)
  have hHalfSq := pow_le_pow_left₀ (by positivity : 0 ≤ t^2/2+1) hHalf 2
  have heq : Real.exp (t^2/2)^2 = Real.exp (t^2) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [heq] at hHalfSq
  have ha2 : 4 * |t| ≤ t^2 := by nlinarith [sq_abs t]
  have ht2 : 16 ≤ t^2 := by nlinarith [sq_abs t]
  have ha4 : 64 * |t| ≤ (t^2)^2 := by nlinarith
  have he : 16 * |t| ≤ Real.exp (t^2) := by nlinarith
  have hm := mul_le_mul_of_nonneg_right he (Real.exp_pos (-(t^2))).le
  have hi : Real.exp (t^2) * Real.exp (-(t^2)) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [hi] at hm
  simp only [oddGaussian, abs_mul, abs_of_pos (Real.exp_pos _)]
  linarith

theorem log_lower_profile_peak {h : ℝ} (hh : 0 < h) (hSmall : h ≤ 1/16) (c : ℝ) :
    (1/4 : ℝ) ≤ logLowerProfile h c (c+h/2) := by
  have hArg : ((c+h/2)-c)/h = (1/2 : ℝ) := by field_simp [hh.ne']; ring
  have hMean := (abs_le.mp (log_lower_mean_bound hh c)).2
  dsimp [logLowerProfile, logLowerRaw]
  rw [hArg]
  linarith [log_lower_gaussian_peak]

theorem log_lower_profile_tail {h : ℝ} (hh : 0 < h) (hSmall : h ≤ 1/16)
    (c x : ℝ) (hFar : 4 ≤ |(x-c)/h|) : |logLowerProfile h c x| ≤ 1/8 := by
  have hEst := (abs_sub (logLowerRaw h c x) (logLowerMean h c)).trans
    (add_le_add (log_lower_gaussian_tail _ hFar) (log_lower_mean_bound hh c))
  change |logLowerProfile h c x| ≤ 1/16+h/2 at hEst
  linarith

#print axioms log_lower_raw_smooth
#print axioms log_lower_profile_smooth
#print axioms log_lower_raw_primitive
#print axioms log_lower_mean_formula
#print axioms log_lower_mean_bound
#print axioms log_lower_profile_integral_zero
#print axioms log_lower_profile_bound
#print axioms log_lower_profile_abs_le_one
#print axioms log_lower_profile_lipschitz
#print axioms log_lower_gaussian_peak
#print axioms log_lower_gaussian_tail
#print axioms log_lower_profile_peak
#print axioms log_lower_profile_tail

end QuantyraNullCone
