import QuantyraNullCone.GoodSamples
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace QuantyraNullCone

open MeasureTheory

theorem exp_neg_quadratic_bound {t : ℝ} (ht : 0 < t) :
    Real.exp (-t) ≤ 4 / t ^ 2 := by
  have hHalf : t / 2 ≤ Real.exp (t / 2) := by
    linarith [Real.add_one_le_exp (t / 2)]
  have hSquare := pow_le_pow_left₀ (by linarith : 0 ≤ t / 2) hHalf 2
  have hExpEq : Real.exp (t / 2) ^ 2 = Real.exp t := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hExpEq] at hSquare
  have hLower : t ^ 2 / 4 ≤ Real.exp t := by nlinarith
  calc
    Real.exp (-t) = 1 / Real.exp t := by simp only [Real.exp_neg, one_div]
    _ ≤ 1 / (t ^ 2 / 4) := one_div_le_one_div_of_le (by positivity) hLower
    _ = 4 / t ^ 2 := by field_simp

theorem grid_failure_bound {n m : ℕ} {x r : ℝ} (hx : 16 ≤ x)
    (hmx : (m : ℝ) ≤ x) (hmr : (m : ℝ) * r = 1) (hPower : x ^ 4 = n) :
    (m : ℝ) ^ 2 * Real.exp (-(n : ℝ) * r ^ 2 / 2) +
      2 * ((m : ℝ) + 1) ^ 2 * Real.exp (-2 * (n : ℝ) * r ^ 2) ≤ 3 / 32 := by
  have hxPos : 0 < x := by linarith
  have hxSqPos : 0 < x ^ 2 := sq_pos_of_pos hxPos
  have hmSq : (m : ℝ) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg m) hmx 2
  have hmrSq : (m : ℝ) ^ 2 * r ^ 2 = 1 := by
    calc
      _ = ((m : ℝ) * r) ^ 2 := by ring
      _ = 1 := by rw [hmr]; norm_num
  have hFactor : 1 ≤ x ^ 2 * r ^ 2 := by
    have ht := mul_le_mul_of_nonneg_right hmSq (sq_nonneg r)
    rwa [hmrSq] at ht
  have hNR : x ^ 2 ≤ (n : ℝ) * r ^ 2 := by
    calc
      _ = x ^ 2 * 1 := by ring
      _ ≤ x ^ 2 * (x ^ 2 * r ^ 2) := mul_le_mul_of_nonneg_left hFactor (sq_nonneg x)
      _ = (n : ℝ) * r ^ 2 := by rw [← hPower]; ring
  have hSucc : (m : ℝ) + 1 ≤ 2 * x := by linarith
  have hCoeff : 2 * ((m : ℝ) + 1) ^ 2 ≤ 8 * x ^ 2 := by
    have ht := pow_le_pow_left₀ (by positivity : 0 ≤ (m : ℝ) + 1) hSucc 2
    nlinarith
  have hOcc : (m : ℝ) ^ 2 * Real.exp (-(n : ℝ) * r ^ 2 / 2) ≤ 16 / x ^ 2 := by
    calc
      _ ≤ x ^ 2 * Real.exp (-(x ^ 2 / 2)) :=
        mul_le_mul hmSq (Real.exp_le_exp.mpr (by linarith)) (Real.exp_nonneg _) (sq_nonneg x)
      _ ≤ x ^ 2 * (4 / (x ^ 2 / 2) ^ 2) :=
        mul_le_mul_of_nonneg_left (exp_neg_quadratic_bound (by positivity)) (sq_nonneg x)
      _ = 16 / x ^ 2 := by field_simp [ne_of_gt hxPos]; ring
  have hVert : 2 * ((m : ℝ) + 1) ^ 2 * Real.exp (-2 * (n : ℝ) * r ^ 2) ≤
      8 / x ^ 2 := by
    calc
      _ ≤ 8 * x ^ 2 * Real.exp (-(2 * x ^ 2)) :=
        mul_le_mul hCoeff (Real.exp_le_exp.mpr (by linarith)) (Real.exp_nonneg _) (by positivity)
      _ ≤ 8 * x ^ 2 * (4 / (2 * x ^ 2) ^ 2) :=
        mul_le_mul_of_nonneg_left (exp_neg_quadratic_bound (by positivity)) (by positivity)
      _ = 8 / x ^ 2 := by field_simp [ne_of_gt hxPos]; ring
  have hxSq : 256 ≤ x ^ 2 := by nlinarith [sq_nonneg (x - 16)]
  have hRatio : 24 / x ^ 2 ≤ (3 / 32 : ℝ) := (div_le_iff₀ hxSqPos).mpr (by nlinarith)
  calc
    _ ≤ 16 / x ^ 2 + 8 / x ^ 2 := add_le_add hOcc hVert
    _ = 24 / x ^ 2 := by ring
    _ ≤ 3 / 32 := hRatio

theorem fourth_root_grid_data {n : ℕ} (hn : 65536 ≤ n) :
    let x := Real.sqrt (Real.sqrt (n : ℝ))
    let m := Nat.floor x
    let r : ℝ := 1 / m
    16 ≤ x ∧ 16 ≤ m ∧ 0 < r ∧ (m : ℝ) * r = 1 ∧
      (m : ℝ) ≤ x ∧ x ^ 4 = n ∧ 87 * r ≤ 174 / x := by
  dsimp
  let x := Real.sqrt (Real.sqrt (n : ℝ))
  let m := Nat.floor x
  have hInner : (256 : ℝ) ≤ Real.sqrt (n : ℝ) :=
    Real.le_sqrt_of_sq_le (by norm_num; exact hn)
  have hx : 16 ≤ x := Real.le_sqrt_of_sq_le (by norm_num; exact hInner)
  have hxPos : 0 < x := by linarith
  have hm : 16 ≤ m := (Nat.le_floor_iff' (by norm_num : (16 : ℕ) ≠ 0)).mpr hx
  have hmPos : 0 < m := by omega
  have hmRPos : (0 : ℝ) < m := by exact_mod_cast hmPos
  have hr : 0 < (1 / (m : ℝ)) := by positivity
  have hmr : (m : ℝ) * (1 / (m : ℝ)) = 1 := by simp [div_eq_mul_inv, ne_of_gt hmRPos]
  have hmx : (m : ℝ) ≤ x := Nat.floor_le hxPos.le
  have hPower : x ^ 4 = n := by
    have hx2 := Real.sq_sqrt (Real.sqrt_nonneg (n : ℝ))
    have hy2 := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    calc
      x ^ 4 = (x ^ 2) ^ 2 := by ring
      _ = (Real.sqrt (n : ℝ)) ^ 2 := by rw [show x ^ 2 = Real.sqrt (n : ℝ) from hx2]
      _ = n := hy2
  have hHalf : x ≤ 2 * (m : ℝ) := by
    have hf : x < (m : ℝ) + 1 := Nat.lt_floor_add_one x
    linarith
  have hRBound : 1 / (m : ℝ) ≤ 2 / x := by
    apply (le_div_iff₀ hxPos).mpr
    have ht := mul_le_mul_of_nonneg_right hHalf hr.le
    nlinarith [hmr]
  have hRate : 87 * (1 / (m : ℝ)) ≤ 174 / x := by
    calc
      _ ≤ 87 * (2 / x) := mul_le_mul_of_nonneg_left hRBound (by norm_num)
      _ = 174 / x := by ring
  exact ⟨hx, hm, hr, hmr, hmx, hPower, hRate⟩

theorem fourth_root_inverse {n : ℕ} :
    1 / Real.sqrt (Real.sqrt (n : ℝ)) = (n : ℝ) ^ (-1 / 4 : ℝ) := by
  have hRoot : Real.sqrt (Real.sqrt (n : ℝ)) = (n : ℝ) ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg n)]
    norm_num
  rw [hRoot, one_div, ← Real.rpow_neg (Nat.cast_nonneg n)]
  congr 1
  norm_num

theorem InDensityClass.reconstruction_probability {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) {n : ℕ} (hn : 65536 ≤ n) :
    (9 / 10 : ℝ) ≤ (sampleMeasure rho n).real
      {sample | SampleCDFReconstructed rho (174 * (n : ℝ) ^ (-1 / 4 : ℝ)) sample} := by
  letI : IsProbabilityMeasure (sampleMeasure rho n) := h.sample_isProbabilityMeasure n
  let x := Real.sqrt (Real.sqrt (n : ℝ))
  let m := Nat.floor x
  let r : ℝ := 1 / m
  have hnPos : 0 < n := by omega
  obtain ⟨hx, hm, hr, hmr, hmx, hPower, hRate⟩ := fourth_root_grid_data hn
  have hFailure := grid_failure_bound hx hmx hmr hPower
  have hSuccess := h.reconstruction_probability_grid hnPos hm hr hmr
  have hNine : (9 / 10 : ℝ) ≤ 1 - ((m : ℝ) ^ 2 * Real.exp (-(n : ℝ) * r ^ 2 / 2) +
      2 * ((m : ℝ) + 1) ^ 2 * Real.exp (-2 * (n : ℝ) * r ^ 2)) := by linarith
  have hRate' : 87 * r ≤ 174 * (n : ℝ) ^ (-1 / 4 : ℝ) := by
    calc
      _ ≤ 174 / x := hRate
      _ = 174 * (1 / x) := by ring
      _ = 174 * (n : ℝ) ^ (-1 / 4 : ℝ) := by
        rw [show 1 / x = (n : ℝ) ^ (-1 / 4 : ℝ) from fourth_root_inverse]
  refine (hNine.trans hSuccess).trans (measureReal_mono ?_)
  intro sample hs L
  obtain ⟨swap, hCDF⟩ := hs L
  exact ⟨swap, fun s t => (hCDF s t).trans hRate'⟩

#print axioms grid_failure_bound
#print axioms fourth_root_grid_data
#print axioms InDensityClass.reconstruction_probability

end QuantyraNullCone
