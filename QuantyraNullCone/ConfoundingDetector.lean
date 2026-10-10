import QuantyraNullCone.ConfoundingGeometry

namespace QuantyraNullCone

open MeasureTheory

/-- A globally valid detector, agreeing with the ordinary quotient on the diamond. -/
noncomputable def calibrationDetector (epsilon : ℝ) (p : DiamondPoint) : ℝ :=
  (1-epsilon) / max (1-epsilon) (min (1+epsilon) (calibrationDensity epsilon p))

theorem calibration_detector_continuous {epsilon : ℝ} (heSmall : epsilon ≤ 1/2) :
    Continuous (calibrationDetector epsilon) := by
  apply Continuous.div continuous_const
    (continuous_const.max (continuous_const.min (calibration_density_smooth epsilon).continuous))
  intro p
  have h := le_max_left (1-epsilon) (min (1+epsilon) (calibrationDensity epsilon p))
  linarith

theorem calibration_detector_bounds {epsilon : ℝ} (he : 0 ≤ epsilon)
    (heSmall : epsilon ≤ 1/2) (p : DiamondPoint) :
    (1-epsilon)/(1+epsilon) ≤ calibrationDetector epsilon p ∧ calibrationDetector epsilon p ≤ 1 := by
  have hc : 0 < 1-epsilon := by linarith
  have hd : 0 < max (1-epsilon) (min (1+epsilon) (calibrationDensity epsilon p)) :=
    hc.trans_le (le_max_left _ _)
  have hu : max (1-epsilon) (min (1+epsilon) (calibrationDensity epsilon p)) ≤ 1+epsilon :=
    max_le (by linarith) (min_le_left _ _)
  constructor
  · exact div_le_div_of_nonneg_left hc.le hd hu
  · exact (div_le_one hd).mpr (le_max_left _ _)

theorem calibration_detector_unit {epsilon : ℝ} (he : 0 ≤ epsilon)
    (heSmall : epsilon ≤ 1/2) (p : DiamondPoint) :
    calibrationDetector epsilon p ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨hl, hu⟩ := calibration_detector_bounds he heSmall p
  exact ⟨(div_nonneg (by linarith) (by linarith)).trans hl, hu⟩

theorem calibration_detector_on_diamond {epsilon : ℝ} (he : 0 ≤ epsilon)
    {p : DiamondPoint} (hp : p ∈ diamond) :
    calibrationDetector epsilon p = (1-epsilon)/calibrationDensity epsilon p := by
  obtain ⟨hl, hu⟩ := calibration_density_bounds he hp
  simp only [calibrationDetector, min_eq_right hu, max_eq_right hl]

theorem calibration_detector_density {epsilon : ℝ} (he : 0 ≤ epsilon)
    (heSmall : epsilon ≤ 1/2) {p : DiamondPoint} (hp : p ∈ diamond) :
    calibrationDensity epsilon p * calibrationDetector epsilon p = 1-epsilon := by
  rw [calibration_detector_on_diamond he hp]
  have hp0 : 0 < calibrationDensity epsilon p := by
    have h := (calibration_density_bounds he hp).1
    linarith
  field_simp

end QuantyraNullCone
