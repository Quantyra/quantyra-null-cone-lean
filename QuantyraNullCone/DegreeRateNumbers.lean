import QuantyraNullCone.DegreeHistogramProbability

namespace QuantyraNullCone

noncomputable def degreeOuterMesh (n : ℕ) : ℕ :=
  Nat.floor (Real.sqrt ((n : ℝ) / (8 * Real.log n)))

noncomputable def degreeRadius (n : ℕ) : ℝ :=
  min (1 / 2 : ℝ) (650 * (Real.log (n : ℝ) / n) ^ (1 / 4 : ℝ))

def DegreeUseHistogram (n : ℕ) : Prop :=
  65536 ≤ degreeOuterMesh n ∧ 270 * Real.sqrt (1 / (degreeOuterMesh n : ℝ)) < 1 / 2

theorem degree_rate_fourth_power {n : ℕ} (hn : 2 ≤ n) :
    (650 * (Real.log (n : ℝ) / n) ^ (1 / 4 : ℝ)) ^ 4 =
      650 ^ 4 * (Real.log (n : ℝ) / n) := by
  rw [mul_pow, ← Real.rpow_natCast ((Real.log (n : ℝ) / n) ^ (1 / 4 : ℝ)) 4,
    ← Real.rpow_mul (log_ratio_positive hn).le]
  norm_num

theorem degree_large_mesh_rate {n : ℕ} (hn : 2 ≤ n) (hm : 65536 ≤ degreeOuterMesh n) :
    270 * Real.sqrt (1 / (degreeOuterMesh n : ℝ)) ≤
      650 * (Real.log (n : ℝ) / n) ^ (1 / 4 : ℝ) := by
  obtain ⟨hnLarge, _⟩ := degree_logarithmic_mesh_large hn hm
  obtain ⟨_, _, _, _, hRate⟩ := logarithmic_grid_data hnLarge
  let x := Real.sqrt ((n : ℝ) / (8 * Real.log n))
  let m := degreeOuterMesh n
  have hmPos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < degreeOuterMesh n)
  have hnPos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hLog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hRec : 1 / (m : ℝ) ≤ 2 / x := by
    change 87 * (1 / (m : ℝ)) ≤ 174 / x at hRate
    calc
      _ = (87 * (1 / (m : ℝ))) / 87 := by ring
      _ ≤ (174 / x) / 87 := div_le_div_of_nonneg_right hRate (by norm_num)
      _ = _ := by ring
  have hRecSq := pow_le_pow_left₀ (by positivity : 0 ≤ 1 / (m : ℝ)) hRec 2
  have hRecId : (2 / x) ^ 2 = 32 * (Real.log (n : ℝ) / n) := by
    dsimp [x]
    rw [div_pow, Real.sq_sqrt (by positivity)]
    field_simp [hnPos.ne', hLog.ne']
    norm_num
  rw [hRecId] at hRecSq
  have hFourth : (Real.sqrt (1 / (m : ℝ))) ^ 4 ≤ 32 * (Real.log (n : ℝ) / n) := by
    rw [show (Real.sqrt (1 / (m : ℝ))) ^ 4 = ((Real.sqrt (1 / (m : ℝ))) ^ 2) ^ 2 by ring,
      Real.sq_sqrt (by positivity)]
    exact hRecSq
  have hScaled := mul_le_mul_of_nonneg_left hFourth (by norm_num : (0 : ℝ) ≤ 270 ^ 4)
  have hConst := mul_le_mul_of_nonneg_right (by norm_num : (270 : ℝ) ^ 4 * 32 ≤ 650 ^ 4)
    (log_ratio_positive hn).le
  apply le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0)
    (mul_nonneg (by norm_num) (Real.rpow_nonneg (log_ratio_positive hn).le _))
  rw [degree_rate_fourth_power hn, mul_pow]
  nlinarith only [hScaled, hConst]

theorem degree_small_mesh_flat_radius {n : ℕ} (hn : 2 ≤ n)
    (hm : degreeOuterMesh n < 65536) :
    (1 / 2 : ℝ) ≤ 650 * (Real.log (n : ℝ) / n) ^ (1 / 4 : ℝ) := by
  let x := Real.sqrt ((n : ℝ) / (8 * Real.log n))
  have hnPos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hLog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hmR : (degreeOuterMesh n : ℝ) + 1 ≤ 65536 := by
    exact_mod_cast (by omega : degreeOuterMesh n + 1 ≤ 65536)
  have hx : x ≤ 65536 := (Nat.lt_floor_add_one x).le.trans hmR
  have hxSq : x ^ 2 = n / (8 * Real.log n) := Real.sq_sqrt (by positivity)
  have hBudget : (n : ℝ) ≤ 8 * 65536 ^ 2 * Real.log n := by
    have hs := pow_le_pow_left₀ (Real.sqrt_nonneg _) hx 2
    rw [hxSq] at hs
    have hh := (div_le_iff₀ (by positivity : 0 < 8 * Real.log (n : ℝ))).mp hs
    nlinarith only [hh]
  have hRatio : (1 / 1024 : ℝ) ^ 4 ≤ Real.log (n : ℝ) / n := by
    apply (le_div_iff₀ hnPos).mpr
    norm_num
    nlinarith only [hBudget, hLog.le]
  have hPow := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ (1 / 1024 : ℝ) ^ 4) hRatio
    (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hId : ((1 / 1024 : ℝ) ^ 4) ^ (1 / 4 : ℝ) = (1 / 1024 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 1024)]
    norm_num
  rw [hId] at hPow
  linarith

theorem degree_flat_radius {n : ℕ} (hn : 2 ≤ n) (hUse : ¬ DegreeUseHistogram n) :
    degreeRadius n = 1 / 2 := by
  apply min_eq_left
  by_cases hm : 65536 ≤ degreeOuterMesh n
  · have hFlat : (1 / 2 : ℝ) ≤ 270 * Real.sqrt (1 / (degreeOuterMesh n : ℝ)) := by
      by_contra hs
      exact hUse ⟨hm, lt_of_not_ge hs⟩
    exact hFlat.trans (degree_large_mesh_rate hn hm)
  · exact degree_small_mesh_flat_radius hn (by omega)

theorem degree_active_radius {n : ℕ} (hn : 2 ≤ n) (hUse : DegreeUseHistogram n) :
    270 * Real.sqrt (1 / (degreeOuterMesh n : ℝ)) ≤ degreeRadius n :=
  le_min hUse.2.le (degree_large_mesh_rate hn hUse.1)

#print axioms degree_rate_fourth_power
#print axioms degree_large_mesh_rate
#print axioms degree_small_mesh_flat_radius
#print axioms degree_flat_radius
#print axioms degree_active_radius

end QuantyraNullCone
