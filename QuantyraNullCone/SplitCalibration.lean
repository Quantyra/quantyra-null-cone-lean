import QuantyraNullCone.SplitProbability
import QuantyraNullCone.FiniteCalibration

namespace QuantyraNullCone

open MeasureTheory

def splitMarginRawQ (n : ℕ) (e : ℚ) : ℚ :=
  min 1 (4 * negativeExpUpperQ (2 * n * e ^ 2))

def splitJointRawQ (n q : ℕ) (e : ℚ) : ℚ :=
  min 1 (2 * (q + 1 : ℚ) ^ 2 * negativeExpUpperQ (2 * n * e ^ 2))

/-- Exact check of a fixed, pre-data split calibration. -/
def checkSplitCalibration (n q : ℕ) (eM eJ bM bJ delta : ℚ) : Bool :=
  decide (0 ≤ eM ∧ 0 ≤ eJ ∧ splitMarginRawQ n eM ≤ bM ∧
    splitJointRawQ n q eJ ≤ bJ ∧ bM + bJ = delta)

theorem split_exponential_upper (n : ℕ) (e : ℚ) :
    Real.exp (-2 * (n : ℝ) * (e : ℝ) ^ 2) ≤
      (negativeExpUpperQ (2 * n * e ^ 2) : ℝ) := by
  have ht : (0 : ℚ) ≤ 2 * n * e ^ 2 := by positivity
  have hBound := negative_exp_upper_rational ht
  have hCast : -((2 * n * e ^ 2 : ℚ) : ℝ) = -2 * (n : ℝ) * (e : ℝ) ^ 2 := by
    push_cast
    ring
  rw [hCast] at hBound
  exact hBound

theorem InDensityClass.split_margin_rational_failure {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) {n : ℕ} (hn : 0 < n) {e : ℚ} (he : 0 ≤ e) :
    (sampleMeasure rho n).real (sampleMarginalBad n e) ≤ (splitMarginRawQ n e : ℝ) := by
  letI : IsProbabilityMeasure (sampleMeasure rho n) := h.sample_isProbabilityMeasure n
  have heR : (0 : ℝ) ≤ e := by exact_mod_cast he
  have hBound := (h.split_marginal_failure hn heR).trans
    (mul_le_mul_of_nonneg_left (split_exponential_upper n e) (by norm_num : (0 : ℝ) ≤ 4))
  simpa [splitMarginRawQ] using le_min (measureReal_le_one (μ := sampleMeasure rho n)) hBound

theorem InDensityClass.split_joint_rational_failure {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) {n q : ℕ} (hn : 0 < n) {e : ℚ} (he : 0 ≤ e) :
    (sampleMeasure rho n).real (sampleJointGridBad rho n q e) ≤
      (splitJointRawQ n q e : ℝ) := by
  letI : IsProbabilityMeasure (sampleMeasure rho n) := h.sample_isProbabilityMeasure n
  have heR : (0 : ℝ) ≤ e := by exact_mod_cast he
  have hBound := (h.split_joint_grid_failure (q := q) hn heR).trans
    (mul_le_mul_of_nonneg_left (split_exponential_upper n e)
      (by positivity : (0 : ℝ) ≤ 2 * ((q : ℝ) + 1) ^ 2))
  simpa [splitJointRawQ] using le_min (measureReal_le_one (μ := sampleMeasure rho n)) hBound

/-- An accepted rational certificate bounds the actual original-K sample failure.
    The parameters are fixed before drawing the sample. -/
theorem InDensityClass.checked_split_calibration {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) {n q : ℕ} (hn : 0 < n) {eM eJ bM bJ delta : ℚ}
    (hCheck : checkSplitCalibration n q eM eJ bM bJ delta = true) :
    (sampleMeasure rho n).real (splitCalibrationBad rho n q eM eJ) ≤ (delta : ℝ) := by
  letI : IsProbabilityMeasure (sampleMeasure rho n) := h.sample_isProbabilityMeasure n
  have hc : 0 ≤ eM ∧ 0 ≤ eJ ∧ splitMarginRawQ n eM ≤ bM ∧
      splitJointRawQ n q eJ ≤ bJ ∧ bM + bJ = delta := of_decide_eq_true hCheck
  have hRound := rounded_split_failure_budget hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2
  have hm := roundFailureQ_upper (Nat.mul_pos (by norm_num : 0 < 10 ^ 12) bM.den_pos)
    (splitMarginRawQ n eM)
  have hj := roundFailureQ_upper (Nat.mul_pos (by norm_num : 0 < 10 ^ 12) bJ.den_pos)
    (splitJointRawQ n q eJ)
  have hRaw : splitMarginRawQ n eM + splitJointRawQ n q eJ ≤ delta :=
    (add_le_add hm hj).trans hRound
  have hRawR : (splitMarginRawQ n eM : ℝ) + (splitJointRawQ n q eJ : ℝ) ≤ delta := by
    exact_mod_cast hRaw
  exact (measureReal_union_le (μ := sampleMeasure rho n) _ _).trans
    ((add_le_add (h.split_margin_rational_failure hn hc.1)
      (h.split_joint_rational_failure hn hc.2.1)).trans hRawR)

theorem InDensityClass.checked_split_accuracy_probability {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) {n q : ℕ} (hn : 0 < n) {eM eJ bM bJ delta : ℚ}
    (hCheck : checkSplitCalibration n q eM eJ bM bJ delta = true) :
    1 - (delta : ℝ) ≤ (sampleMeasure rho n).real
      (splitCalibrationBad rho n q eM eJ)ᶜ := by
  letI : IsProbabilityMeasure (sampleMeasure rho n) := h.sample_isProbabilityMeasure n
  rw [probReal_compl_eq_one_sub (split_calibration_bad_measurable hn rho q eM eJ)]
  linarith only [h.checked_split_calibration hn hCheck]

#print axioms split_exponential_upper
#print axioms InDensityClass.checked_split_calibration
#print axioms InDensityClass.checked_split_accuracy_probability

end QuantyraNullCone
