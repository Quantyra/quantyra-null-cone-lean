import QuantyraNullCone.DegreeHistogram

namespace QuantyraNullCone

open MeasureTheory

/-- The explicit inner mesh discharges width and floor assumptions without
altering the original degree threshold or density class. -/
theorem degree_inner_mesh_data {m : ℕ} (hm : 65536 ≤ m) :
    let r : ℝ := 1 / m
    let h := Real.sqrt r
    let k := Nat.floor (Real.sqrt (m : ℝ))
    let w := (1 - 16 * h) / k
    0 < r ∧ 0 < h ∧ h ^ 2 = r ∧ (m : ℝ) * r = 1 ∧ h ≤ 1 / 256 ∧
      0 < k ∧ (k : ℝ) ^ 2 ≤ m ∧ 0 < w ∧ (k : ℝ) * w = 1 - 16 * h ∧
        15 / 16 * h ≤ w ∧ w ≤ 2 * h := by
  dsimp
  let r : ℝ := 1 / m
  let h := Real.sqrt r
  let x := Real.sqrt (m : ℝ)
  let k := Nat.floor x
  have hmR : (65536 : ℝ) ≤ m := by exact_mod_cast hm
  have hmPos : (0 : ℝ) < m := by linarith
  have hr : 0 < r := by dsimp [r]; positivity
  have hh : 0 < h := Real.sqrt_pos.2 hr
  have hSquare : h ^ 2 = r := Real.sq_sqrt hr.le
  have hmr : (m : ℝ) * r = 1 := by dsimp [r]; field_simp [hmPos.ne']
  have hrSmall : r ≤ 1 / 65536 := one_div_le_one_div_of_le (by norm_num) hmR
  have hhSmall : h ≤ 1 / 256 := by nlinarith only [hrSmall, hSquare, hh.le]
  have hx : 256 ≤ x := Real.le_sqrt_of_sq_le (by norm_num; exact hm)
  have hkLarge : 256 ≤ k := (Nat.le_floor_iff' (by omega : (256 : ℕ) ≠ 0)).mpr hx
  have hk : 0 < k := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hkx : (k : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxSq : x ^ 2 = m := Real.sq_sqrt (Nat.cast_nonneg m)
  have hkSq : (k : ℝ) ^ 2 ≤ m := by nlinarith only [hkx, hxSq, hkR, hx]
  have hHalf : x ≤ 2 * k := by
    have hFloor := Nat.lt_floor_add_one x
    have hkOne : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
    linarith
  have hxh : x * h = 1 := by
    dsimp [x, h, r]
    rw [← Real.sqrt_mul (Nat.cast_nonneg m)]
    have hMul : (m : ℝ) * (1 / (m : ℝ)) = 1 := by field_simp [hmPos.ne']
    rw [hMul, Real.sqrt_one]
  have hKh : (k : ℝ) * h ≤ 1 := by nlinarith only [mul_le_mul_of_nonneg_right hkx hh.le, hxh]
  have hKhTwo : 1 ≤ 2 * (k : ℝ) * h := by
    nlinarith only [mul_le_mul_of_nonneg_right hHalf hh.le, hxh]
  have hNumerator : 0 < 1 - 16 * h := by linarith
  refine ⟨hr, hh, hSquare, hmr, hhSmall, hk, hkSq, div_pos hNumerator hkR, ?_, ?_, ?_⟩
  · change (k : ℝ) * ((1 - 16 * h) / k) = 1 - 16 * h
    field_simp [hkR.ne']
  · apply (le_div_iff₀ hkR).mpr
    nlinarith only [hKh, hhSmall]
  · apply (div_le_iff₀ hkR).mpr
    nlinarith only [hKhTwo, hh.le]

theorem degree_mesh_margins {h r w : ℝ} (hh : 0 < h) (hhSmall : h ≤ 1 / 256)
    (hSquare : h ^ 2 = r) (hWidth : 15 / 16 * h ≤ w) :
    0 ≤ 8 * h ∧ 8 * h ≤ 1 / 2 ∧ 0 < w ∧ 2 * (32 * r) ≤ w ∧
      7 * h ≤ 8 * h - 32 * r := by
  have hSqSmall := mul_le_mul_of_nonneg_left hhSmall hh.le
  refine ⟨by positivity, by linarith, by linarith, ?_, ?_⟩ <;>
    nlinarith only [hSquare, hSqSmall, hWidth, hh.le]

/-- The exact cell/extension constants of the selected estimator. -/
theorem degree_histogram_constant {h w : ℝ} (hh : 0 < h) (hhSmall : h ≤ 1 / 256)
    (hLow : 15 / 16 * h ≤ w) (hHigh : w ≤ 2 * h) :
    6 * (32 * h ^ 2) / w + 6 * ((32 * h ^ 2) / w) ^ 2 +
      (4 * h ^ 3) / w ^ 2 + 2 * w + 24 * h ≤ 270 * h := by
  have hw : 0 < w := by linarith
  have hRatio : 32 * h ^ 2 / w ≤ 512 / 15 * h := by
    apply (div_le_iff₀ hw).mpr
    have hm := mul_le_mul_of_nonneg_left hLow hh.le
    nlinarith only [hm]
  have hRatio0 : 0 ≤ 32 * h ^ 2 / w := by positivity
  have hRatioSq := pow_le_pow_left₀ hRatio0 hRatio 2
  have hSqSmall := mul_le_mul_of_nonneg_left hhSmall hh.le
  have hA : 6 * (32 * h ^ 2) / w ≤ 3072 / 15 * h := by
    calc
      _ = 6 * (32 * h ^ 2 / w) := by ring
      _ ≤ 6 * (512 / 15 * h) := mul_le_mul_of_nonneg_left hRatio (by norm_num)
      _ = _ := by ring
  have hB : 6 * ((32 * h ^ 2) / w) ^ 2 ≤ 6144 / 225 * h := by
    nlinarith only [hRatioSq, hSqSmall]
  have hWidthSq := pow_le_pow_left₀ (by positivity : 0 ≤ 15 / 16 * h) hLow 2
  have hC : 4 * h ^ 3 / w ^ 2 ≤ 1024 / 225 * h := by
    apply (div_le_iff₀ (sq_pos_of_pos hw)).mpr
    have hm := mul_le_mul_of_nonneg_left hWidthSq hh.le
    nlinarith only [hm]
  linarith

theorem InDensityClass.square_mass_upper {rho : DiamondPoint → ℝ} (hK : InDensityClass rho)
    {a c w : ℝ} (hw : 0 ≤ w) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (haw : a + w ≤ 1) (hcw : c + w ≤ 1) :
    (densityMeasure rho).real (squareCell a c w) ≤ (3 / 2 : ℝ) * w ^ 2 := by
  have hb := (hK.rectangle_mass_bounds ha (by linarith : a ≤ a + w) haw
    hc (by linarith : c ≤ c + w) hcw).2
  simpa only [add_sub_cancel_left, squareCell, pow_two, mul_assoc] using hb

theorem InDensityClass.shifted_inner_cell_mass {rho : DiamondPoint → ℝ}
    (hK : InDensityClass rho) {k : ℕ} (hk : 0 < k) {h r w : ℝ}
    (hh : 0 < h) (hhSmall : h ≤ 1 / 256) (hSquare : h ^ 2 = r)
    (hkw : (k : ℝ) * w = 1 - 16 * h) (hLow : 15 / 16 * h ≤ w) (hHigh : w ≤ 2 * h)
    (expand : Bool) {i j : ℕ} (hi : i < k) (hj : j < k) :
    (densityMeasure rho).real (shiftedInnerCell expand (8 * h) w (32 * r) i j) ≤ 8 * h ^ 2 := by
  obtain ⟨_, _, hw, hShift, hDeep⟩ := degree_mesh_margins hh hhSmall hSquare hLow
  have hI := inner_cell_location hk hw (by nlinarith only [hkw] : (k : ℝ) * w = 1 - 2 * (8 * h)) hi
  have hJ := inner_cell_location hk hw (by nlinarith only [hkw] : (k : ℝ) * w = 1 - 2 * (8 * h)) hj
  have hr : 0 ≤ r := by rw [← hSquare]; positivity
  have hSqSmall := mul_le_mul_of_nonneg_left hhSmall hh.le
  have hPlus : w + 2 * (32 * r) ≤ 9 / 4 * h := by nlinarith only [hSquare, hSqSmall, hHigh]
  cases expand with
  | false =>
    have hW : 0 ≤ w - 2 * (32 * r) := by linarith
    have hWU : w - 2 * (32 * r) ≤ 9 / 4 * h := by linarith
    have hb := hK.square_mass_upper hW
      (by linarith : 0 ≤ 8 * h + (i : ℝ) * w + 32 * r)
      (by linarith : 0 ≤ 8 * h + (j : ℝ) * w + 32 * r)
      (by linarith : 8 * h + (i : ℝ) * w + 32 * r + (w - 2 * (32 * r)) ≤ 1)
      (by linarith : 8 * h + (j : ℝ) * w + 32 * r + (w - 2 * (32 * r)) ≤ 1)
    have hs := pow_le_pow_left₀ hW hWU 2
    change (densityMeasure rho).real (squareCell _ _ _) ≤ _
    nlinarith only [hb, hs, sq_nonneg h]
  | true =>
    have hW : 0 ≤ w + 2 * (32 * r) := by positivity
    have hb := hK.square_mass_upper hW
      (by linarith : 0 ≤ 8 * h + (i : ℝ) * w - 32 * r)
      (by linarith : 0 ≤ 8 * h + (j : ℝ) * w - 32 * r)
      (by linarith : 8 * h + (i : ℝ) * w - 32 * r + (w + 2 * (32 * r)) ≤ 1)
      (by linarith : 8 * h + (j : ℝ) * w - 32 * r + (w + 2 * (32 * r)) ≤ 1)
    have hs := pow_le_pow_left₀ hW hPlus 2
    change (densityMeasure rho).real (squareCell _ _ _) ≤ _
    nlinarith only [hb, hs, sq_nonneg h]

#print axioms degree_inner_mesh_data
#print axioms degree_mesh_margins
#print axioms degree_histogram_constant
#print axioms InDensityClass.square_mass_upper
#print axioms InDensityClass.shifted_inner_cell_mass

end QuantyraNullCone
