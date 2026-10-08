import QuantyraNullCone.ProbabilityRate
import QuantyraNullCone.OrderSelector

namespace QuantyraNullCone

open MeasureTheory

theorem log_ratio_positive {n : ℕ} (hn : 2 ≤ n) :
    0 < Real.log (n : ℝ) / n := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  exact div_pos (Real.log_pos hnR) (by linarith)

theorem log_two_lower : (1 / 2 : ℝ) ≤ Real.log 2 := by
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at h
  exact h

theorem log_large_bounds {n : ℕ} (hn : 65536 ≤ n) :
    1 ≤ Real.log (n : ℝ) ∧ 2048 * Real.log (n : ℝ) ≤ n := by
  have hnR : (65536 : ℝ) ≤ n := by exact_mod_cast hn
  have hnPos : (0 : ℝ) < n := by linarith
  have hLog4 : 1 ≤ Real.log (4 : ℝ) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
    linarith [log_two_lower]
  have hLower := Real.log_le_log (by norm_num : (0 : ℝ) < 4)
    (by linarith : (4 : ℝ) ≤ n)
  have hLog2 : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hLog65536 : Real.log (65536 : ℝ) ≤ 16 := by
    rw [show (65536 : ℝ) = 2 ^ 16 by norm_num, Real.log_pow]
    norm_num
    linarith
  have hTangent := Real.log_le_sub_one_of_pos
    (div_pos hnPos (by norm_num : (0 : ℝ) < 65536))
  rw [Real.log_div (ne_of_gt hnPos) (by norm_num : (65536 : ℝ) ≠ 0)] at hTangent
  constructor
  · linarith
  · linarith

theorem logarithmic_grid_data {n : ℕ} (hn : 65536 ≤ n) :
    let x := Real.sqrt ((n : ℝ) / (8 * Real.log n))
    let m := Nat.floor x
    let r : ℝ := 1 / m
    16 ≤ m ∧ 0 < r ∧ (m : ℝ) * r = 1 ∧
      (m : ℝ) ^ 2 ≤ n / (8 * Real.log n) ∧
      87 * r ≤ 174 / x := by
  dsimp
  let x := Real.sqrt ((n : ℝ) / (8 * Real.log n))
  let m := Nat.floor x
  obtain ⟨hLog, hCutoff⟩ := log_large_bounds hn
  have hDen : 0 < 8 * Real.log (n : ℝ) := by linarith
  have hRatio : (256 : ℝ) ≤ n / (8 * Real.log n) := by
    apply (le_div_iff₀ hDen).mpr
    nlinarith
  have hx : 16 ≤ x := Real.le_sqrt_of_sq_le (by norm_num; exact hRatio)
  have hxPos : 0 < x := by linarith
  have hm : 16 ≤ m := (Nat.le_floor_iff' (by norm_num : (16 : ℕ) ≠ 0)).mpr hx
  have hmPos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hmr : (m : ℝ) * (1 / (m : ℝ)) = 1 := by
    simp [div_eq_mul_inv, ne_of_gt hmPos]
  have hmx : (m : ℝ) ≤ x := Nat.floor_le hxPos.le
  have hxSq : x ^ 2 = n / (8 * Real.log n) := Real.sq_sqrt (by positivity)
  have hmSq : (m : ℝ) ^ 2 ≤ n / (8 * Real.log n) := by
    rw [← hxSq]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hmx 2
  have hHalf : x ≤ 2 * (m : ℝ) := by
    have hf : x < (m : ℝ) + 1 := Nat.lt_floor_add_one x
    have hmR : (16 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hRecip : 1 / (m : ℝ) ≤ 2 / x := by
    apply (le_div_iff₀ hxPos).mpr
    have ht := mul_le_mul_of_nonneg_right hHalf (by positivity : 0 ≤ 1 / (m : ℝ))
    nlinarith [hmr]
  refine ⟨hm, by positivity, hmr, hmSq, ?_⟩
  calc
    _ ≤ 87 * (2 / x) := mul_le_mul_of_nonneg_left hRecip (by norm_num)
    _ = 174 / x := by ring

theorem exp_neg_nat_log {x : ℝ} (hx : 0 < x) (k : ℕ) :
    Real.exp (-((k : ℝ) * Real.log x)) = 1 / x ^ k := by
  rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log hx]
  simp only [one_div]

theorem logarithmic_grid_failure {n m : ℕ} (hn : 65536 ≤ n) (hm : 16 ≤ m)
    {r : ℝ} (hmr : (m : ℝ) * r = 1)
    (hmSq : (m : ℝ) ^ 2 ≤ n / (8 * Real.log n)) :
    (m : ℝ) ^ 2 * Real.exp (-(n : ℝ) * r ^ 2 / 2) +
      2 * ((m : ℝ) + 1) ^ 2 * Real.exp (-2 * (n : ℝ) * r ^ 2) ≤ 1 / 10 := by
  obtain ⟨hLog, _⟩ := log_large_bounds hn
  have hnR : (65536 : ℝ) ≤ n := by exact_mod_cast hn
  have hnPos : (0 : ℝ) < n := by linarith
  have hmR : (16 : ℝ) ≤ m := by exact_mod_cast hm
  have hBudget : (m : ℝ) ^ 2 * (8 * Real.log n) ≤ n :=
    (le_div_iff₀ (by linarith : 0 < 8 * Real.log (n : ℝ))).mp hmSq
  have hmEight : (m : ℝ) ^ 2 ≤ n / 8 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr
    have ht := mul_nonneg (sq_nonneg (m : ℝ)) (sub_nonneg.mpr hLog)
    nlinarith
  have hmrSq : (m : ℝ) ^ 2 * r ^ 2 = 1 := by
    calc
      _ = ((m : ℝ) * r) ^ 2 := by ring
      _ = 1 := by rw [hmr]; norm_num
  have hNR : 8 * Real.log (n : ℝ) ≤ (n : ℝ) * r ^ 2 := by
    calc
      _ = ((m : ℝ) ^ 2 * r ^ 2) * (8 * Real.log n) := by rw [hmrSq]; ring
      _ = ((m : ℝ) ^ 2 * (8 * Real.log n)) * r ^ 2 := by ring
      _ ≤ (n : ℝ) * r ^ 2 := mul_le_mul_of_nonneg_right hBudget (sq_nonneg r)
  have hOccExp : Real.exp (-(n : ℝ) * r ^ 2 / 2) ≤ 1 / (n : ℝ) ^ 4 := by
    calc
      _ ≤ Real.exp (-(4 * Real.log n)) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := exp_neg_nat_log hnPos 4
  have hJointExp : Real.exp (-2 * (n : ℝ) * r ^ 2) ≤ 1 / (n : ℝ) ^ 16 := by
    calc
      _ ≤ Real.exp (-(16 * Real.log n)) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := exp_neg_nat_log hnPos 16
  have hSucc : (m : ℝ) + 1 ≤ 2 * m := by linarith
  have hSuccSq := pow_le_pow_left₀ (by positivity : 0 ≤ (m : ℝ) + 1) hSucc 2
  have hCoeff : 2 * ((m : ℝ) + 1) ^ 2 ≤ 8 * (m : ℝ) ^ 2 := by
    nlinarith only [hSuccSq]
  have hOcc : (m : ℝ) ^ 2 * Real.exp (-(n : ℝ) * r ^ 2 / 2) ≤
      1 / (8 * (n : ℝ) ^ 3) := by
    calc
      _ ≤ (m : ℝ) ^ 2 * (1 / (n : ℝ) ^ 4) :=
        mul_le_mul_of_nonneg_left hOccExp (sq_nonneg _)
      _ ≤ ((n : ℝ) / 8) * (1 / (n : ℝ) ^ 4) :=
        mul_le_mul_of_nonneg_right hmEight (by positivity)
      _ = _ := by field_simp [ne_of_gt hnPos]
  have hJoint : 2 * ((m : ℝ) + 1) ^ 2 * Real.exp (-2 * (n : ℝ) * r ^ 2) ≤
      1 / (n : ℝ) ^ 15 := by
    calc
      _ ≤ 8 * (m : ℝ) ^ 2 * (1 / (n : ℝ) ^ 16) :=
        mul_le_mul hCoeff hJointExp (Real.exp_nonneg _) (by positivity)
      _ ≤ 8 * ((n : ℝ) / 8) * (1 / (n : ℝ) ^ 16) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmEight (by norm_num))
          (by positivity)
      _ = _ := by field_simp [ne_of_gt hnPos]
  have hnTwo : (2 : ℝ) ≤ n := by linarith
  have hCub := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hnTwo 3
  have hFifteen := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hnTwo 15
  norm_num at hCub hFifteen
  have hOccSmall : 1 / (8 * (n : ℝ) ^ 3) ≤ (1 / 64 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) (by nlinarith only [hCub])
  have hJointSmall : 1 / (n : ℝ) ^ 15 ≤ (1 / 32768 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) hFifteen
  linarith

theorem logarithmic_grid_reciprocal {n : ℕ} (hn : 2 ≤ n) :
    1 / Real.sqrt ((n : ℝ) / (8 * Real.log n)) =
      Real.sqrt 8 * Real.sqrt (Real.log (n : ℝ) / n) := by
  have hLog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg
    (by exact_mod_cast (show 1 ≤ n by omega))
  rw [Real.sqrt_div (Nat.cast_nonneg n), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8),
    Real.sqrt_div hLog, one_div_div]
  ring

theorem InDensityClass.logarithmic_reconstruction_probability {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) {n : ℕ} (hn : 65536 ≤ n) :
    (9 / 10 : ℝ) ≤ (sampleMeasure rho n).real
      {sample | SampleCDFReconstructed rho
        (174 * Real.sqrt 8 * Real.sqrt (Real.log (n : ℝ) / n)) sample} := by
  letI : IsProbabilityMeasure (sampleMeasure rho n) := h.sample_isProbabilityMeasure n
  let x := Real.sqrt ((n : ℝ) / (8 * Real.log n))
  let m := Nat.floor x
  let r : ℝ := 1 / m
  have hnPos : 0 < n := by omega
  obtain ⟨hm, hr, hmr, hmSq, hRate⟩ := logarithmic_grid_data hn
  have hFailure := logarithmic_grid_failure hn hm hmr hmSq
  have hSuccess := h.reconstruction_probability_grid hnPos hm hr hmr
  have hNine : (9 / 10 : ℝ) ≤ 1 - ((m : ℝ) ^ 2 * Real.exp (-(n : ℝ) * r ^ 2 / 2) +
      2 * ((m : ℝ) + 1) ^ 2 * Real.exp (-2 * (n : ℝ) * r ^ 2)) := by linarith
  have hRate' : 87 * r ≤ 174 * Real.sqrt 8 * Real.sqrt (Real.log (n : ℝ) / n) := by
    calc
      _ ≤ 174 / x := hRate
      _ = 174 * (1 / x) := by ring
      _ = _ := by
        rw [show 1 / x = Real.sqrt 8 * Real.sqrt (Real.log (n : ℝ) / n) from
          logarithmic_grid_reciprocal (by omega : 2 ≤ n)]
        ring
  refine (hNine.trans hSuccess).trans (measureReal_mono ?_)
  intro sample hs L
  obtain ⟨swap, hCDF⟩ := hs L
  exact ⟨swap, fun s t => (hCDF s t).trans hRate'⟩

theorem InDensityClass.logarithmic_orderCDFGood_probability {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) {n : ℕ} (hn : 65536 ≤ n) :
    (9 / 10 : ℝ) ≤ (orderLaw rho n).real
      {code | OrderCDFGood rho
        (174 * Real.sqrt 8 * Real.sqrt (Real.log (n : ℝ) / n)) code} := by
  letI : IsProbabilityMeasure (sampleMeasure rho n) := h.sample_isProbabilityMeasure n
  rw [orderLaw, map_measureReal_apply (sampledOrder_measurable n)
    (orderCDFGood_measurable _ _)]
  refine h.logarithmic_reconstruction_probability hn |>.trans ?_
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [h.sample_coordinates_injective n] with sample hInj
  exact fun hR => reconstructed_orderCDFGood hInj.1 hInj.2 hR

#print axioms log_large_bounds
#print axioms logarithmic_grid_data
#print axioms logarithmic_grid_failure
#print axioms InDensityClass.logarithmic_reconstruction_probability
#print axioms InDensityClass.logarithmic_orderCDFGood_probability

end QuantyraNullCone
