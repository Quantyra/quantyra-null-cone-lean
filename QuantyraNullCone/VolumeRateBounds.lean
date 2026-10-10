import QuantyraNullCone.MarkedEstimator

namespace QuantyraNullCone

open MeasureTheory

noncomputable def calibrationBudget (R : ℝ) : ℝ := (R-1)/(R+1)
noncomputable def volumeSamplingScale (n : ℕ) : ℝ := 1 / Real.sqrt n
noncomputable def physicalVolumeRate (n : ℕ) (R : ℝ) : ℝ :=
  min 1 (volumeSamplingScale n + calibrationBudget R)

theorem calibration_budget_nonneg {R : ℝ} (hR : 1 ≤ R) : 0 ≤ calibrationBudget R := by
  unfold calibrationBudget
  exact div_nonneg (by linarith) (by linarith)

theorem retention_lower_bias {R x : ℝ} (hR : 1 ≤ R) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    x - retentionLower R x ≤ calibrationBudget R := by
  have hD := (retention_denominators hR hx).1
  have hR1 : 0 < R+1 := by linarith
  have hid : calibrationBudget R - (x-retentionLower R x) =
      (R-1)*(R*(1-x)^2+x^2)/((R+1)*(R-(R-1)*x)) := by
    unfold calibrationBudget retentionLower
    field_simp
    ring
  have hp : 0 ≤ (R-1)*(R*(1-x)^2+x^2)/((R+1)*(R-(R-1)*x)) :=
    div_nonneg (mul_nonneg (by linarith) (add_nonneg
      (mul_nonneg (by linarith) (sq_nonneg _)) (sq_nonneg _))) (mul_pos hR1 hD).le
  linarith

theorem retention_upper_bias {R x : ℝ} (hR : 1 ≤ R) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    retentionUpper R x - x ≤ calibrationBudget R := by
  have hD := (retention_denominators hR hx).2
  have hR1 : 0 < R+1 := by linarith
  have hid : calibrationBudget R - (retentionUpper R x-x) =
      (R-1)*((1-x)^2+R*x^2)/((R+1)*(1+(R-1)*x)) := by
    unfold calibrationBudget retentionUpper
    field_simp
    ring
  have hp : 0 ≤ (R-1)*((1-x)^2+R*x^2)/((R+1)*(1+(R-1)*x)) :=
    div_nonneg (mul_nonneg (by linarith) (add_nonneg (sq_nonneg _)
      (mul_nonneg (by linarith) (sq_nonneg _)))) (mul_pos hR1 hD).le
  linarith

theorem retained_volume_bias (mu : Measure DiamondPoint) [IsProbabilityMeasure mu]
    {pi : DiamondPoint → ℝ} (hpi : Integrable pi mu) {R : ℝ} (hR : 1 ≤ R)
    (hbounds : ∀ x, 1/R ≤ pi x ∧ pi x ≤ 1) {S : Set DiamondPoint} (hS : MeasurableSet S) :
    |(retainedMeasure mu pi).real S - mu.real S| ≤ calibrationBudget R := by
  have hRpos : 0 < R := by linarith
  have ha : 0 < 1/R := one_div_pos.mpr hRpos
  have hab : 1/R ≤ (1 : ℝ) := (div_le_iff₀ hRpos).mpr (by simpa using hR)
  letI := retained_measure_probability mu hpi ha hbounds
  have hident := retained_physical_identification mu hpi ha hab hbounds hS
  have hratio : (1 : ℝ)/(1/R) = R := by field_simp
  rw [hratio] at hident
  have htheta : (retainedMeasure mu pi).real S ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨measureReal_nonneg, measureReal_le_one⟩
  have hlo := retention_lower_bias hR htheta
  have hup := retention_upper_bias hR htheta
  exact abs_le.mpr ⟨by linarith [hident.2], by linarith [hident.1]⟩

theorem volume_sampling_scale_positive {n : ℕ} (hn : 0 < n) : 0 < volumeSamplingScale n := by
  unfold volumeSamplingScale
  positivity

theorem volume_sampling_budget {n : ℕ} (hn : 0 < n) :
    (n : ℝ)*(2*volumeSamplingScale n)^2 = 4 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hnR)
  unfold volumeSamplingScale
  field_simp
  nlinarith [Real.sq_sqrt hnR.le]

theorem volume_rate_error_inclusion {a b t theta v : ℝ} (hb : 0 ≤ b)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hv : v ∈ Set.Icc (0 : ℝ) 1)
    (hbias : |theta-v| ≤ b) (herr : 2*min 1 (a+b) < |t-v|) : 2*a ≤ |t-theta| := by
  have hunit : |t-v| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1, hv.2], by linarith [ht.2, hv.1]⟩
  have hsum : a+b < 1 := by
    by_contra h
    rw [min_eq_left (le_of_not_gt h)] at herr
    linarith
  rw [min_eq_right hsum.le] at herr
  have htriangle := abs_sub_le t theta v
  linarith

end QuantyraNullCone
