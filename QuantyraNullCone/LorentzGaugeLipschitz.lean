import QuantyraNullCone.LorentzGaugeBounds

namespace QuantyraNullCone

noncomputable section

theorem lorentz_coordinate_abs_le_norm3 (p : LorentzPoint3) (i : Fin 3) : |p i| ≤ ‖p‖ := by
  simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le p i

theorem closed_lorentz_coordinate_bound3 {p : LorentzPoint3} (hp : p ∈ closedLorentzDiamond3)
    (i : Fin 3) : |p i| ≤ 1 := by
  have hNorm := closed_lorentz_diamond_subset_ball3 hp
  change dist p 0 ≤ 1 at hNorm
  rw [dist_zero_right] at hNorm
  exact (lorentz_coordinate_abs_le_norm3 p i).trans hNorm

theorem lorentz_coordinate_sub_bound3 (p q : LorentzPoint3) (i : Fin 3) :
    |p i - q i| ≤ ‖p - q‖ := by
  simpa only [PiLp.sub_apply] using lorentz_coordinate_abs_le_norm3 (p - q) i

theorem closed_lorentz_coordinate_square_difference3 {p q : LorentzPoint3}
    (hp : p ∈ closedLorentzDiamond3) (hq : q ∈ closedLorentzDiamond3) (i : Fin 3) :
    |p i ^ 2 - q i ^ 2| ≤ 2 * ‖p - q‖ := by
  have hSum : |p i + q i| ≤ 2 := by
    exact (abs_add_le _ _).trans (by linarith [closed_lorentz_coordinate_bound3 hp i,
      closed_lorentz_coordinate_bound3 hq i])
  calc
    |p i ^ 2 - q i ^ 2| = |p i - q i| * |p i + q i| := by
      rw [← abs_mul]; congr 1; ring
    _ ≤ ‖p - q‖ * 2 := mul_le_mul (lorentz_coordinate_sub_bound3 p q i) hSum
      (abs_nonneg _) (norm_nonneg _)
    _ = 2 * ‖p - q‖ := mul_comm _ _

theorem gauge_denominator_lipschitz3 {p q : LorentzPoint3}
    (hp : p ∈ closedLorentzDiamond3) (hq : q ∈ closedLorentzDiamond3) :
    |flowDenominator3 (-gaugeParameter3) p - flowDenominator3 (-gaugeParameter3) q| ≤
      (3 / 100 : ℝ) * ‖p - q‖ := by
  have hIdentity : flowDenominator3 (-gaugeParameter3) p - flowDenominator3 (-gaugeParameter3) q =
      -(2 / 100 : ℝ) * (p 0 - q 0) + (1 / 10000 : ℝ) * (p 0 ^ 2 - q 0 ^ 2) +
        -(1 / 10000 : ℝ) * (p 1 ^ 2 - q 1 ^ 2) +
        -(1 / 10000 : ℝ) * (p 2 ^ 2 - q 2 ^ 2) := by
    unfold flowDenominator3 gaugeParameter3 spatialSquared3
    ring
  have hTriangle : ∀ u v w z : ℝ, |u + v + w + z| ≤ |u| + |v| + |w| + |z| := by
    intro u v w z
    linarith [abs_add_le (u + v + w) z, abs_add_le (u + v) w, abs_add_le u v]
  rw [hIdentity]
  have h := hTriangle (-(2 / 100 : ℝ) * (p 0 - q 0))
    ((1 / 10000 : ℝ) * (p 0 ^ 2 - q 0 ^ 2))
    (-(1 / 10000 : ℝ) * (p 1 ^ 2 - q 1 ^ 2))
    (-(1 / 10000 : ℝ) * (p 2 ^ 2 - q 2 ^ 2))
  simp only [abs_mul, abs_neg] at h
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2 / 100),
    abs_of_pos (by norm_num : (0 : ℝ) < 1 / 10000)] at h
  have h0 := lorentz_coordinate_sub_bound3 p q 0
  have h1 := closed_lorentz_coordinate_square_difference3 hp hq 0
  have h2 := closed_lorentz_coordinate_square_difference3 hp hq 1
  have h3 := closed_lorentz_coordinate_square_difference3 hp hq 2
  nlinarith [norm_nonneg (p - q)]

/-- Elementary reciprocal-cube bound with exact rational constants. -/
theorem reciprocal_cube_lipschitz3 {d e c : ℝ}
    (hd : (9 / 10 : ℝ) ≤ d ∧ d ≤ 11 / 10)
    (he : (9 / 10 : ℝ) ≤ e ∧ e ≤ 11 / 10) (hc : 0 ≤ c ∧ c ≤ 1) :
    |c / d ^ 3 - c / e ^ 3| ≤ 7 * |d - e| := by
  have hdPos : 0 < d := by linarith [hd.1]
  have hePos : 0 < e := by linarith [he.1]
  have hSumPos : 0 ≤ d ^ 2 + d * e + e ^ 2 := by positivity
  have hSum : d ^ 2 + d * e + e ^ 2 ≤ (363 / 100 : ℝ) := by
    have hdSq := pow_le_pow_left₀ hdPos.le hd.2 2
    have heSq := pow_le_pow_left₀ hePos.le he.2 2
    have hProd := mul_le_mul hd.2 he.2 hePos.le (by norm_num : (0 : ℝ) ≤ 11 / 10)
    nlinarith
  have hDenPos : 0 < d ^ 3 * e ^ 3 := by positivity
  have hDen : (9 / 10 : ℝ) ^ 6 ≤ d ^ 3 * e ^ 3 := by
    have hdCube := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 9 / 10) hd.1 3
    have heCube := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 9 / 10) he.1 3
    have h := mul_le_mul hdCube heCube (by norm_num : (0 : ℝ) ≤ (9 / 10) ^ 3)
      (le_of_lt (pow_pos hdPos 3))
    norm_num at h ⊢
    exact h
  have hFrac : c / d ^ 3 - c / e ^ 3 =
      c * (e - d) * (d ^ 2 + d * e + e ^ 2) / (d ^ 3 * e ^ 3) := by
    field_simp [hdPos.ne', hePos.ne']
    ring
  rw [hFrac, abs_div, abs_mul, abs_mul, abs_of_nonneg hc.1,
    abs_of_nonneg hSumPos, abs_of_pos hDenPos, abs_sub_comm e d]
  apply (div_le_iff₀ hDenPos).mpr
  have hNumerator : c * |d - e| * (d ^ 2 + d * e + e ^ 2) ≤
      |d - e| * (363 / 100 : ℝ) := by
    have hFirst : c * |d - e| ≤ |d - e| := by
      simpa using mul_le_mul_of_nonneg_right hc.2 (abs_nonneg (d - e))
    exact mul_le_mul hFirst hSum hSumPos (abs_nonneg _)
  have hDenMul := mul_le_mul_of_nonneg_left hDen (abs_nonneg (d - e))
  nlinarith [abs_nonneg (d - e)]

theorem gauge_density_lipschitz3 {p q : LorentzPoint3}
    (hp : p ∈ closedLorentzDiamond3) (hq : q ∈ closedLorentzDiamond3) :
    |gaugeDensity3 p - gaugeDensity3 q| ≤ 2 * ‖p - q‖ := by
  have hWeak : ∀ r ∈ closedLorentzDiamond3,
      (9 / 10 : ℝ) ≤ flowDenominator3 (-gaugeParameter3) r ∧
        flowDenominator3 (-gaugeParameter3) r ≤ 11 / 10 := by
    intro r hr
    obtain ⟨hLo, hHi⟩ := gauge_denominator_bounds3 hr
    constructor <;> nlinarith
  have hCube : (0 : ℝ) ≤ (1 - (-gaugeParameter3) ^ 2) ^ 3 ∧
      (1 - (-gaugeParameter3) ^ 2) ^ 3 ≤ 1 := by norm_num [gaugeParameter3]
  have hRecip := reciprocal_cube_lipschitz3 (hWeak p hp) (hWeak q hq) hCube
  have hRho (r : LorentzPoint3) : gaugeDensity3 r =
      (1 - (-gaugeParameter3) ^ 2) ^ 3 / flowDenominator3 (-gaugeParameter3) r ^ 3 := by
    simp only [gaugeDensity3, flowFactor3, div_pow]
  rw [hRho p, hRho q]
  have hDen := gauge_denominator_lipschitz3 hp hq
  nlinarith [norm_nonneg (p - q)]

#print axioms closed_lorentz_coordinate_square_difference3
#print axioms gauge_denominator_lipschitz3
#print axioms reciprocal_cube_lipschitz3
#print axioms gauge_density_lipschitz3

end

end QuantyraNullCone
