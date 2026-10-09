import QuantyraNullCone.InnerHistogram
import QuantyraNullCone.DegreeProbability

namespace QuantyraNullCone

open MeasureTheory

def shiftedInnerCell (expand : Bool) (H w s : ℝ) (i j : ℕ) : Set DiamondPoint :=
  if expand then squareCell (H + (i : ℝ) * w - s) (H + (j : ℝ) * w - s) (w + 2 * s)
  else squareCell (H + (i : ℝ) * w + s) (H + (j : ℝ) * w + s) (w - 2 * s)

def InnerCountAccuracy {n : ℕ} (rho : DiamondPoint → ℝ) (k : ℕ) (H w s eps : ℝ)
    (sample : Fin n → DiamondPoint) : Prop :=
  ∀ expand : Bool, ∀ i j : ℕ, i < k → j < k →
    |(pointsIn sample (shiftedInnerCell expand H w s i j)).card / (n : ℝ) -
      (densityMeasure rho).real (shiftedInnerCell expand H w s i j)| ≤ eps

noncomputable def Realizer.degreeCellValue {n : ℕ} {R : Fin n → Fin n → Prop}
    (L : Realizer R) (r H w : ℝ) (i j : ℕ) : ℝ :=
  max (1 / 2 : ℝ) (min (3 / 2 : ℝ)
    (((retainedPointsIn (DegreeRetained R r) L.rankPoint (innerCell H w i j)).card : ℝ) / n / w ^ 2))

noncomputable def Realizer.degreeHistogram {n : ℕ} {R : Fin n → Fin n → Prop}
    (L : Realizer R) (r : ℝ) (k : ℕ) (H w : ℝ) : DiamondPoint → ℝ :=
  innerHistogram k H w (L.degreeCellValue r H w)

theorem Realizer.degreeHistogram_measurable {n : ℕ} {R : Fin n → Fin n → Prop}
    (L : Realizer R) (r : ℝ) (k : ℕ) (H w : ℝ) : Measurable (L.degreeHistogram r k H w) :=
  inner_histogram_measurable k H w _

theorem Realizer.degreeHistogram_bounds {n : ℕ} {R : Fin n → Fin n → Prop}
    (L : Realizer R) (r : ℝ) (k : ℕ) (H w : ℝ) (p : DiamondPoint) :
    (1 / 2 : ℝ) ≤ L.degreeHistogram r k H w p ∧ L.degreeHistogram r k H w p ≤ 3 / 2 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem Realizer.degreeCellValue_swap {n : ℕ} {R : Fin n → Fin n → Prop}
    (L : Realizer R) (r H w : ℝ) (i j : ℕ) :
    L.swap.degreeCellValue r H w i j = L.degreeCellValue r H w j i := by
  have hCounts : retainedPointsIn (DegreeRetained R r) L.swap.rankPoint (innerCell H w i j) =
      retainedPointsIn (DegreeRetained R r) L.rankPoint (innerCell H w j i) := by
    classical
    ext a
    simp only [retainedPointsIn, Finset.mem_filter, Finset.mem_univ, true_and,
      innerCell, squareCell, Set.mem_prod, Set.mem_Ioc, Realizer.rankPoint_swap, transposePoint]
    tauto
  simp only [Realizer.degreeCellValue, hCounts]

theorem Realizer.degreeHistogram_swap {n : ℕ} {R : Fin n → Fin n → Prop}
    (L : Realizer R) (r : ℝ) (k : ℕ) (H w : ℝ) (p : DiamondPoint) :
    L.swap.degreeHistogram r k H w p = L.degreeHistogram r k H w (transposePoint p) := by
  exact L.degreeCellValue_swap r H w _ _

/-- Deterministic whole-square reconstruction for the actual retained-rank
histogram. Every analytic premise is either the geometric event or fixed-cell
count accuracy; the concrete n-dependent parameter discharge follows separately. -/
theorem degree_histogram_error {n m k : ℕ} {rho : DiamondPoint → ℝ}
    (hK : InDensityClass rho) (hn : 0 < n) (hm : 16 ≤ m) (hk : 0 < k)
    {r h H w eps : ℝ} (hr : 0 < r) (hh : 0 ≤ h) (hSquare : h ^ 2 = r)
    (hmr : (m : ℝ) * r = 1) (hnr : 1 / (n : ℝ) ≤ r)
    (hH0 : 0 ≤ H) (hH : H ≤ 1 / 2) (hw : 0 < w) (hkw : (k : ℝ) * w = 1 - 2 * H)
    (hShift : 2 * (32 * r) ≤ w) (hDeep : 7 * h ≤ H - 32 * r)
    {sample : Fin n → DiamondPoint} (hg : SampleGood rho m r sample)
    (hAccuracy : InnerCountAccuracy rho k H w (32 * r) eps sample)
    (L : Realizer (Chronological (fun i => (sample i).1) (fun i => (sample i).2))) :
    ∃ swap : Bool, ∀ p ∈ diamond,
      |(L.aligned swap).degreeHistogram r k H w p - rho p| ≤
        6 * (32 * r) / w + 6 * ((32 * r) / w) ^ 2 + eps / w ^ 2 + 2 * w + 3 * H := by
  obtain ⟨swap, hCounts⟩ := degree_filtered_cell_counts hK hn hm hr hh hSquare hmr hnr hg L
  refine ⟨swap, ?_⟩
  intro p hp
  apply hK.inner_histogram_error hk hH0 hH hw hkw ((L.aligned swap).degreeCellValue r H w) _ hp
  intro i j hi hj q hq
  let a := H + (i : ℝ) * w
  let c := H + (j : ℝ) * w
  have hI := inner_cell_location hk hw hkw hi
  have hJ := inner_cell_location hk hw hkw hj
  change H ≤ a ∧ a + w ≤ 1 - H at hI
  change H ≤ c ∧ c + w ≤ 1 - H at hJ
  have hs : 0 ≤ 32 * r := by positivity
  have hRaw := hCounts a (a + w) c (c + w)
    (by linarith) (by linarith) (by linarith) (by linarith)
  have hMinusEq : countRectangle (a + 32 * r) (a + w - 32 * r)
      (c + 32 * r) (c + w - 32 * r) = squareCell (a + 32 * r) (c + 32 * r) (w - 2 * (32 * r)) := by
    simp only [countRectangle, squareCell,
      show a + 32 * r + (w - 2 * (32 * r)) = a + w - 32 * r by ring,
      show c + 32 * r + (w - 2 * (32 * r)) = c + w - 32 * r by ring]
  have hPlusEq : countRectangle (a - 32 * r) (a + w + 32 * r)
      (c - 32 * r) (c + w + 32 * r) = squareCell (a - 32 * r) (c - 32 * r) (w + 2 * (32 * r)) := by
    simp only [countRectangle, squareCell,
      show a - 32 * r + (w + 2 * (32 * r)) = a + w + 32 * r by ring,
      show c - 32 * r + (w + 2 * (32 * r)) = c + w + 32 * r by ring]
  rw [hMinusEq, hPlusEq] at hRaw
  have hMinus := hAccuracy false i j hi hj
  have hPlus := hAccuracy true i j hi hj
  simp only [shiftedInnerCell, Bool.false_eq_true, if_false, if_true] at hMinus hPlus
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply hK.shifted_cell_point_error hw hs hShift
    (by linarith) (by linarith) (by linarith) (by linarith) _ hMinus hPlus hq
  constructor
  · apply div_le_div_of_nonneg_right _ hnR.le
    exact_mod_cast hRaw.1
  · apply div_le_div_of_nonneg_right _ hnR.le
    exact_mod_cast hRaw.2

#print axioms Realizer.degreeHistogram_measurable
#print axioms Realizer.degreeHistogram_bounds
#print axioms Realizer.degreeCellValue_swap
#print axioms Realizer.degreeHistogram_swap
#print axioms degree_histogram_error

end QuantyraNullCone
