import QuantyraNullCone.DegreeCellBias
import Mathlib.MeasureTheory.Function.Floor

namespace QuantyraNullCone

open MeasureTheory

noncomputable def innerClamp (H x : ℝ) : ℝ := max H (min (1 - H) x)

noncomputable def innerClampPoint (H : ℝ) (p : DiamondPoint) : DiamondPoint :=
  (innerClamp H p.1, innerClamp H p.2)

/-- Queries on internal grid edges use the cell to their right; the uppermost
edge uses the last cell. Counts use Ioc cells, and error holds on their closures. -/
noncomputable def innerCellIndex (k : ℕ) (H w x : ℝ) : ℕ :=
  min (Nat.floor ((x - H) / w)) (k - 1)

def innerCell (H w : ℝ) (i j : ℕ) : Set DiamondPoint :=
  squareCell (H + (i : ℝ) * w) (H + (j : ℝ) * w) w

noncomputable def innerHistogram (k : ℕ) (H w : ℝ) (values : ℕ → ℕ → ℝ)
    (p : DiamondPoint) : ℝ :=
  values (innerCellIndex k H w (innerClamp H p.1))
    (innerCellIndex k H w (innerClamp H p.2))

theorem inner_clamp_bounds {H : ℝ} (hH : H ≤ 1 / 2) (x : ℝ) :
    H ≤ innerClamp H x ∧ innerClamp H x ≤ 1 - H := by
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem inner_clamp_displacement {H x : ℝ} (hH0 : 0 ≤ H) (hH : H ≤ 1 / 2)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) : |innerClamp H x - x| ≤ H := by
  by_cases hlo : x ≤ H
  · rw [innerClamp, min_eq_right (by linarith : x ≤ 1 - H), max_eq_left hlo,
      abs_of_nonneg (by linarith : 0 ≤ H - x)]
    linarith [hx.1]
  · by_cases hhi : 1 - H ≤ x
    · rw [innerClamp, min_eq_left hhi, max_eq_right (by linarith : H ≤ 1 - H),
        abs_of_nonpos (by linarith : 1 - H - x ≤ 0)]
      linarith [hx.2]
    · rw [innerClamp, min_eq_right (le_of_not_ge hhi), max_eq_right (le_of_not_ge hlo)]
      simpa using hH0

theorem inner_clamp_point_mem {H : ℝ} (hH0 : 0 ≤ H) (hH : H ≤ 1 / 2)
    (p : DiamondPoint) : innerClampPoint H p ∈ diamond := by
  have h1 := inner_clamp_bounds hH p.1
  have h2 := inner_clamp_bounds hH p.2
  exact ⟨⟨hH0.trans h1.1, by change innerClamp H p.1 ≤ 1; linarith [h1.2]⟩,
    ⟨hH0.trans h2.1, by change innerClamp H p.2 ≤ 1; linarith [h2.2]⟩⟩

theorem InDensityClass.inner_clamp_error {rho : DiamondPoint → ℝ}
    (hK : InDensityClass rho) {H : ℝ} (hH0 : 0 ≤ H) (hH : H ≤ 1 / 2)
    {p : DiamondPoint} (hp : p ∈ diamond) :
    |rho (innerClampPoint H p) - rho p| ≤ 3 * H := by
  have h1 := inner_clamp_displacement hH0 hH hp.1
  have h2 := inner_clamp_displacement hH0 hH hp.2
  have h1sq := pow_le_pow_left₀ (abs_nonneg _) h1 2
  have h2sq := pow_le_pow_left₀ (abs_nonneg _) h2 2
  simp only [sq_abs] at h1sq h2sq
  have hRoot : Real.sqrt ((innerClamp H p.1 - p.1) ^ 2 +
      (innerClamp H p.2 - p.2) ^ 2) ≤ 3 / 2 * H := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by positivity, by nlinarith [sq_nonneg H]⟩
  have hLip := hK.lipschitz (innerClampPoint H p) (inner_clamp_point_mem hH0 hH p) p hp
  change |rho (innerClampPoint H p) - rho p| ≤ _
  change |rho (innerClampPoint H p) - rho p| ≤
    2 * Real.sqrt ((innerClamp H p.1 - p.1) ^ 2 + (innerClamp H p.2 - p.2) ^ 2) at hLip
  linarith

theorem inner_cell_index_lt {k : ℕ} (hk : 0 < k) (H w x : ℝ) :
    innerCellIndex k H w x < k := by
  have hi := min_le_right (Nat.floor ((x - H) / w)) (k - 1)
  change min (Nat.floor ((x - H) / w)) (k - 1) < k
  omega

theorem inner_cell_location {k : ℕ} (_hk : 0 < k) {H w : ℝ}
    (hw : 0 < w) (hkw : (k : ℝ) * w = 1 - 2 * H) {i : ℕ} (hi : i < k) :
    H ≤ H + (i : ℝ) * w ∧ H + (i : ℝ) * w + w ≤ 1 - H := by
  have hiR : (i : ℝ) + 1 ≤ k := by exact_mod_cast (Nat.succ_le_of_lt hi)
  have hm := mul_le_mul_of_nonneg_right hiR hw.le
  exact ⟨by linarith [mul_nonneg (Nat.cast_nonneg i) hw.le], by nlinarith only [hm, hkw]⟩

theorem inner_cell_index_location {k : ℕ} (hk : 0 < k) {H w x : ℝ}
    (hw : 0 < w) (hkw : (k : ℝ) * w = 1 - 2 * H)
    (hx : x ∈ Set.Icc H (1 - H)) :
    H + (innerCellIndex k H w x : ℝ) * w ≤ x ∧
      x ≤ H + (innerCellIndex k H w x : ℝ) * w + w := by
  have hq : 0 ≤ (x - H) / w := div_nonneg (sub_nonneg.mpr hx.1) hw.le
  have hFloor := Nat.floor_le hq
  have hiFloor : (innerCellIndex k H w x : ℝ) ≤ Nat.floor ((x - H) / w) := by
    exact_mod_cast min_le_left (Nat.floor ((x - H) / w)) (k - 1)
  have hLower := (le_div_iff₀ hw).mp (hiFloor.trans hFloor)
  refine ⟨by linarith, ?_⟩
  by_cases hf : Nat.floor ((x - H) / w) < k
  · have hi : innerCellIndex k H w x = Nat.floor ((x - H) / w) :=
      min_eq_left (by omega)
    rw [hi]
    have hu := (div_lt_iff₀ hw).mp (Nat.lt_floor_add_one ((x - H) / w))
    nlinarith only [hu]
  · have hi : innerCellIndex k H w x = k - 1 := min_eq_right (by omega)
    rw [hi]
    have hkR : ((k - 1 : ℕ) : ℝ) + 1 = k := by
      exact_mod_cast Nat.sub_add_cancel (by omega : 1 ≤ k)
    have hkRw := congrArg (fun t : ℝ => t * w) hkR
    nlinarith only [hx.2, hkRw, hkw]

theorem inner_histogram_measurable (k : ℕ) (H w : ℝ) (values : ℕ → ℕ → ℝ) :
    Measurable (innerHistogram k H w values) := by
  have hClamp : Measurable (innerClamp H) :=
    (continuous_const.max (continuous_const.min continuous_id)).measurable
  have hIndex : Measurable (innerCellIndex k H w) :=
    (Nat.measurable_floor.comp ((measurable_id.sub_const H).div_const w)).min measurable_const
  have hPair : Measurable (fun p : DiamondPoint =>
      (innerCellIndex k H w (innerClamp H p.1), innerCellIndex k H w (innerClamp H p.2))) :=
    ((hIndex.comp hClamp).comp measurable_fst).prodMk ((hIndex.comp hClamp).comp measurable_snd)
  exact (measurable_of_countable (fun ij : ℕ × ℕ => values ij.1 ij.2)).comp hPair

theorem InDensityClass.inner_histogram_error {rho : DiamondPoint → ℝ}
    (hK : InDensityClass rho) {k : ℕ} (hk : 0 < k) {H w E : ℝ}
    (hH0 : 0 ≤ H) (hH : H ≤ 1 / 2) (hw : 0 < w) (hkw : (k : ℝ) * w = 1 - 2 * H)
    (values : ℕ → ℕ → ℝ)
    (hCell : ∀ i j : ℕ, i < k → j < k → ∀ q ∈
      closedSquareCell (H + (i : ℝ) * w) (H + (j : ℝ) * w) w,
        |values i j - rho q| ≤ E) {p : DiamondPoint} (hp : p ∈ diamond) :
    |innerHistogram k H w values p - rho p| ≤ E + 3 * H := by
  let i := innerCellIndex k H w (innerClamp H p.1)
  let j := innerCellIndex k H w (innerClamp H p.2)
  have hI := inner_cell_index_location hk hw hkw (inner_clamp_bounds hH p.1)
  have hJ := inner_cell_index_location hk hw hkw (inner_clamp_bounds hH p.2)
  have hPoint : innerClampPoint H p ∈
      closedSquareCell (H + (i : ℝ) * w) (H + (j : ℝ) * w) w := ⟨hI, hJ⟩
  have hLocal := hCell i j (inner_cell_index_lt hk _ _ _) (inner_cell_index_lt hk _ _ _) _ hPoint
  exact (abs_sub_le (values i j) (rho (innerClampPoint H p)) (rho p)).trans
    (add_le_add hLocal (hK.inner_clamp_error hH0 hH hp))

#print axioms inner_clamp_bounds
#print axioms inner_clamp_displacement
#print axioms inner_clamp_point_mem
#print axioms InDensityClass.inner_clamp_error
#print axioms inner_cell_index_lt
#print axioms inner_cell_location
#print axioms inner_cell_index_location
#print axioms inner_histogram_measurable
#print axioms InDensityClass.inner_histogram_error

end QuantyraNullCone
