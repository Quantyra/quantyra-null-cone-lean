import QuantyraNullCone.DegreeCells
import QuantyraNullCone.DensityCellBias

namespace QuantyraNullCone

open MeasureTheory

theorem diamondVolume_probability : IsProbabilityMeasure diamondVolume := by
  constructor
  rw [diamondVolume, Measure.restrict_apply_univ]
  change ((volume : Measure ℝ).prod (volume : Measure ℝ))
    (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) = 1
  rw [Measure.prod_prod]
  norm_num

theorem InDensityClass.mass_gap_ceiling {rho : DiamondPoint → ℝ}
    (hK : InDensityClass rho) {A B : Set DiamondPoint}
    (hAB : A ⊆ B) (hA : MeasurableSet A) :
    (densityMeasure rho).real B - (densityMeasure rho).real A ≤
      (3 / 2 : ℝ) * (diamondVolume.real B - diamondVolume.real A) := by
  letI : IsProbabilityMeasure (densityMeasure rho) := hK.isProbabilityMeasure
  letI : IsProbabilityMeasure diamondVolume := diamondVolume_probability
  rw [← measureReal_diff hAB hA, ← measureReal_diff hAB hA]
  have hb := hK.densityMeasure_ceiling (B \ A)
  simp only [Measure.smul_apply, smul_eq_mul] at hb
  have hr := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) hb
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3 / 2)] using hr

theorem diamond_square_cell_real {a c w : ℝ} (hw : 0 ≤ w)
    (ha : 0 ≤ a) (hc : 0 ≤ c) (haw : a + w ≤ 1) (hcw : c + w ≤ 1) :
    diamondVolume.real (squareCell a c w) = w ^ 2 := by
  have hSub := (square_cell_subset_closed a c w).trans (closed_square_cell_subset ha hc haw hcw)
  rw [Measure.real, diamondVolume, Measure.restrict_apply (square_cell_measurable a c w),
    Set.inter_eq_left.mpr hSub, square_cell_volume hw, ENNReal.toReal_ofReal (sq_nonneg w)]

/-- Density bounded above controls both shifted shells by their area, keeping
the factor of cell width which the uniform marginal strip bound would lose. -/
theorem InDensityClass.shifted_square_mass_gaps {rho : DiamondPoint → ℝ}
    (hK : InDensityClass rho) {a c w s : ℝ} (hs : 0 ≤ s) (hws : 2 * s ≤ w)
    (ha : 0 ≤ a - s) (hc : 0 ≤ c - s)
    (haw : a + w + s ≤ 1) (hcw : c + w + s ≤ 1) :
    (densityMeasure rho).real (squareCell a c w) -
      (densityMeasure rho).real (squareCell (a + s) (c + s) (w - 2 * s)) ≤
        6 * w * s + 6 * s ^ 2 ∧
    (densityMeasure rho).real (squareCell (a - s) (c - s) (w + 2 * s)) -
      (densityMeasure rho).real (squareCell a c w) ≤ 6 * w * s + 6 * s ^ 2 := by
  have hw : 0 ≤ w := by linarith
  have hInner : squareCell (a + s) (c + s) (w - 2 * s) ⊆ squareCell a c w := by
    rintro p ⟨⟨hpa, hpb⟩, ⟨hpc, hpd⟩⟩
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hOuter : squareCell a c w ⊆ squareCell (a - s) (c - s) (w + 2 * s) := by
    rintro p ⟨⟨hpa, hpb⟩, ⟨hpc, hpd⟩⟩
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hV := diamond_square_cell_real hw (by linarith : 0 ≤ a) (by linarith : 0 ≤ c)
    (by linarith : a + w ≤ 1) (by linarith : c + w ≤ 1)
  have hVi := diamond_square_cell_real (by linarith : 0 ≤ w - 2 * s)
    (by linarith : 0 ≤ a + s) (by linarith : 0 ≤ c + s)
    (by linarith : a + s + (w - 2 * s) ≤ 1) (by linarith : c + s + (w - 2 * s) ≤ 1)
  have hVo := diamond_square_cell_real (by linarith : 0 ≤ w + 2 * s) ha hc
    (by linarith : a - s + (w + 2 * s) ≤ 1) (by linarith : c - s + (w + 2 * s) ≤ 1)
  have hI := hK.mass_gap_ceiling hInner (square_cell_measurable _ _ _)
  have hO := hK.mass_gap_ceiling hOuter (square_cell_measurable _ _ _)
  rw [hV, hVi] at hI
  rw [hVo, hV] at hO
  constructor <;> nlinarith only [hI, hO, sq_nonneg s]

theorem InDensityClass.shifted_cell_mean_error {rho : DiamondPoint → ℝ}
    (hK : InDensityClass rho) {a c w s recovered minus plus eps : ℝ}
    (hw : 0 < w) (hs : 0 ≤ s) (hws : 2 * s ≤ w)
    (ha : 0 ≤ a - s) (hc : 0 ≤ c - s)
    (haw : a + w + s ≤ 1) (hcw : c + w + s ≤ 1)
    (hSandwich : minus ≤ recovered ∧ recovered ≤ plus)
    (hMinus : |minus - (densityMeasure rho).real
      (squareCell (a + s) (c + s) (w - 2 * s))| ≤ eps)
    (hPlus : |plus - (densityMeasure rho).real
      (squareCell (a - s) (c - s) (w + 2 * s))| ≤ eps) :
    |recovered / w ^ 2 - densityCellMean rho a c w| ≤
      6 * s / w + 6 * (s / w) ^ 2 + eps / w ^ 2 := by
  obtain ⟨hI, hO⟩ := hK.shifted_square_mass_gaps hs hws ha hc haw hcw
  have hErr : |recovered - (densityMeasure rho).real (squareCell a c w)| ≤
      6 * w * s + 6 * s ^ 2 + eps := by
    rcases abs_le.mp hMinus with ⟨hM1, hM2⟩
    rcases abs_le.mp hPlus with ⟨hP1, hP2⟩
    exact abs_le.mpr ⟨by linarith [hSandwich.1], by linarith [hSandwich.2]⟩
  unfold densityCellMean
  rw [← sub_div, abs_div, abs_of_nonneg (sq_nonneg w)]
  calc
    _ ≤ (6 * w * s + 6 * s ^ 2 + eps) / w ^ 2 :=
      div_le_div_of_nonneg_right hErr (sq_nonneg w)
    _ = _ := by field_simp [hw.ne']

/-- Clipping to the known density range cannot increase pointwise error. -/
theorem density_clip_error {x y : ℝ} (hy : (1 / 2 : ℝ) ≤ y ∧ y ≤ 3 / 2) :
    |max (1 / 2 : ℝ) (min (3 / 2 : ℝ) x) - y| ≤ |x - y| := by
  by_cases hLo : x ≤ 1 / 2
  · rw [min_eq_right (by linarith : x ≤ 3 / 2), max_eq_left hLo,
      abs_of_nonpos (by linarith : (1 / 2 : ℝ) - y ≤ 0),
      abs_of_nonpos (by linarith : x - y ≤ 0)]
    linarith
  · by_cases hHi : 3 / 2 ≤ x
    · rw [min_eq_left hHi, max_eq_right (by norm_num : (1 / 2 : ℝ) ≤ 3 / 2),
        abs_of_nonneg (by linarith : 0 ≤ (3 / 2 : ℝ) - y),
        abs_of_nonneg (by linarith : 0 ≤ x - y)]
      linarith
    · rw [min_eq_right (le_of_not_ge hHi), max_eq_right (le_of_not_ge hLo)]

theorem InDensityClass.shifted_cell_point_error {rho : DiamondPoint → ℝ}
    (hK : InDensityClass rho) {a c w s recovered minus plus eps : ℝ}
    (hw : 0 < w) (hs : 0 ≤ s) (hws : 2 * s ≤ w)
    (ha : 0 ≤ a - s) (hc : 0 ≤ c - s)
    (haw : a + w + s ≤ 1) (hcw : c + w + s ≤ 1)
    (hSandwich : minus ≤ recovered ∧ recovered ≤ plus)
    (hMinus : |minus - (densityMeasure rho).real
      (squareCell (a + s) (c + s) (w - 2 * s))| ≤ eps)
    (hPlus : |plus - (densityMeasure rho).real
      (squareCell (a - s) (c - s) (w + 2 * s))| ≤ eps)
    {p : DiamondPoint} (hp : p ∈ closedSquareCell a c w) :
    |max (1 / 2 : ℝ) (min (3 / 2 : ℝ) (recovered / w ^ 2)) - rho p| ≤
      6 * s / w + 6 * (s / w) ^ 2 + eps / w ^ 2 + 2 * w := by
  have ha0 : 0 ≤ a := by linarith
  have hc0 : 0 ≤ c := by linarith
  have haw1 : a + w ≤ 1 := by linarith
  have hcw1 : c + w ≤ 1 := by linarith
  have hP := closed_square_cell_subset ha0 hc0 haw1 hcw1 hp
  have hCell := hK.shifted_cell_mean_error hw hs hws ha hc haw hcw hSandwich hMinus hPlus
  have hBias := hK.cell_mean_point_bias hw ha0 hc0 haw1 hcw1 hp
  exact (density_clip_error (hK.bounds p hP)).trans
    ((abs_sub_le (recovered / w ^ 2) (densityCellMean rho a c w) (rho p)).trans
      (add_le_add hCell hBias))

#print axioms diamondVolume_probability
#print axioms InDensityClass.mass_gap_ceiling
#print axioms diamond_square_cell_real
#print axioms InDensityClass.shifted_square_mass_gaps
#print axioms InDensityClass.shifted_cell_mean_error
#print axioms density_clip_error
#print axioms InDensityClass.shifted_cell_point_error

end QuantyraNullCone
