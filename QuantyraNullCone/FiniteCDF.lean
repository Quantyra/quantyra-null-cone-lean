import QuantyraNullCone.FiniteForcing
import QuantyraNullCone.GridAccuracy
import QuantyraNullCone.OrderSelector

namespace QuantyraNullCone

theorem finite_grid_CDF_unit {n q : ℕ} {u v : Fin n → ℝ}
    {rho : DiamondPoint → ℝ} {r eta : ℝ} (hK : InDensityClass rho)
    (hr : 0 < r) (hqr : (q : ℝ) * r = 1)
    (hGrid : ∀ j k : ℕ, j ≤ q → k ≤ q →
      |empiricalCDF u v ((j : ℝ) * r) ((k : ℝ) * r) -
        populationCDF rho ((j : ℝ) * r) ((k : ℝ) * r)| ≤ eta)
    (s t : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |empiricalCDF u v s t - populationCDF rho s t| ≤ eta + 2 * r := by
  obtain ⟨j, j', hj, hj', hslo, hshi, hsGap, hsGap'⟩ := grid_closed_bracket hr hqr hs0 hs1
  obtain ⟨k, k', hk, hk', htlo, hthi, htGap, htGap'⟩ := grid_closed_bracket hr hqr ht0 ht1
  have hLo := abs_le.mp (hGrid j k hj hk)
  have hHi := abs_le.mp (hGrid j' k' hj' hk')
  have hMonoLo := empiricalCDF_mono u v hslo htlo
  have hMonoHi := empiricalCDF_mono u v hshi hthi
  have hFLo : |populationCDF rho ((j : ℝ) * r) ((k : ℝ) * r) -
      populationCDF rho s t| ≤ 2 * r := by
    have h := hK.populationCDF_thresholdStability ((j : ℝ) * r) ((k : ℝ) * r) s t
    rw [abs_of_nonpos (sub_nonpos.mpr hslo), abs_of_nonpos (sub_nonpos.mpr htlo)] at h
    linarith
  have hFHi : |populationCDF rho ((j' : ℝ) * r) ((k' : ℝ) * r) -
      populationCDF rho s t| ≤ 2 * r := by
    have h := hK.populationCDF_thresholdStability ((j' : ℝ) * r) ((k' : ℝ) * r) s t
    rw [abs_of_nonneg (sub_nonneg.mpr hshi), abs_of_nonneg (sub_nonneg.mpr hthi)] at h
    linarith
  have hFL := abs_le.mp hFLo
  have hFH := abs_le.mp hFHi
  apply abs_le.mpr
  constructor <;> linarith

theorem finite_grid_CDF {n q : ℕ} {u v : Fin n → ℝ}
    {rho : DiamondPoint → ℝ} {r eta : ℝ} (hK : InDensityClass rho)
    (hr : 0 < r) (hqr : (q : ℝ) * r = 1) (hEta : 0 ≤ eta)
    (hU : ∀ i, 0 ≤ u i ∧ u i ≤ 1) (hV : ∀ i, 0 ≤ v i ∧ v i ≤ 1)
    (hGrid : ∀ j k : ℕ, j ≤ q → k ≤ q →
      |empiricalCDF u v ((j : ℝ) * r) ((k : ℝ) * r) -
        populationCDF rho ((j : ℝ) * r) ((k : ℝ) * r)| ≤ eta)
    (s t : ℝ) : |empiricalCDF u v s t - populationCDF rho s t| ≤ eta + 2 * r := by
  by_cases hs : s < 0
  · rw [empiricalCDF_negative u v (fun i => (hU i).1) (fun i => (hV i).1) (Or.inl hs),
      populationCDF_negative rho (Or.inl hs)]
    simp only [sub_self, abs_zero]
    positivity
  by_cases ht : t < 0
  · rw [empiricalCDF_negative u v (fun i => (hU i).1) (fun i => (hV i).1) (Or.inr ht),
      populationCDF_negative rho (Or.inr ht)]
    simp only [sub_self, abs_zero]
    positivity
  rw [empiricalCDF_cap u v (fun i => (hU i).2) (fun i => (hV i).2), populationCDF_cap]
  exact finite_grid_CDF_unit hK hr hqr hGrid (min s 1) (min t 1)
    (le_min (le_of_not_gt hs) (by norm_num)) (min_le_right _ _)
    (le_min (le_of_not_gt ht) (by norm_num)) (min_le_right _ _)

theorem normalized_rank_coordinate_error_general {n : ℕ} (hn : 0 < n)
    {w : Fin n → ℝ} (distinct : Function.Injective w)
    {L : Fin n → Fin n → Prop} {i : Fin n} {budget epsilon : ℝ}
    (hRank : |(rank L i : ℝ) - (rank (fun x y => w x < w y) i : ℝ)| ≤ budget)
    (hMargin : |marginalCDF w (w i) - w i| ≤ epsilon) :
    |(rank L i : ℝ) / n - w i| ≤ budget / n + epsilon := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hDiv : |((rank L i : ℝ) - (rank (fun x y => w x < w y) i : ℝ)) / n| ≤
      budget / n := by
    rw [abs_div, abs_of_pos hnR]
    exact div_le_div_of_nonneg_right hRank hnR.le
  have hCoordinate : |(rank (fun x y => w x < w y) i : ℝ) / n - w i| ≤ epsilon := by
    rw [normalized_coordinate_rank_eq_marginalCDF w distinct i]
    exact hMargin
  have hIdentity : (rank L i : ℝ) / n - w i =
      ((rank L i : ℝ) - (rank (fun x y => w x < w y) i : ℝ)) / n +
        ((rank (fun x y => w x < w y) i : ℝ) / n - w i) := by ring
  rw [hIdentity]
  exact (abs_add_le _ _).trans (add_le_add hDiv hCoordinate)

#print axioms finite_grid_CDF
#print axioms normalized_rank_coordinate_error_general

def coordinateRowRealizer {n : ℕ} (rows : Fin n → Fin n → Bool) (u v : Fin n → ℝ)
    (hu : Function.Injective u) (hv : Function.Injective v)
    (hRows : ∀ i j, rowRelation rows i j ↔ Chronological u v i j) :
    Realizer (rowRelation rows) where
  first := fun i j => u i < u j
  second := fun i j => v i < v j
  firstTotal := ⟨fun i => lt_irrefl (u i), fun h₁ h₂ => lt_trans h₁ h₂,
    fun hij => lt_or_gt_of_ne (hu.ne hij)⟩
  secondTotal := ⟨fun i => lt_irrefl (v i), fun h₁ h₂ => lt_trans h₁ h₂,
    fun hij => lt_or_gt_of_ne (hv.ne hij)⟩
  intersection := hRows

def trimTailCount {n : ℕ} (rows : Fin n → Fin n → Bool) (trace : List (ForcingEntry n))
    (cutoff : ℕ) : ℕ :=
  (Finset.univ.filter (fun i => cutoff < unresolvedDegree rows trace i)).card

/-- One checked orientation works simultaneously for every data-dependent trim cutoff.
Concentration inputs are kept separate here and supplied by the probability campaign. -/
theorem checked_trimmed_CDF {n q : ℕ} {rho : DiamondPoint → ℝ}
    (hK : InDensityClass rho) (hn : 0 < n) (rows : Fin n → Fin n → Bool)
    (u v : Fin n → ℝ) (hu : Function.Injective u) (hv : Function.Injective v)
    (hRows : ∀ i j, rowRelation rows i j ↔ Chronological u v i j)
    (hU : ∀ i, 0 ≤ u i ∧ u i ≤ 1) (hV : ∀ i, 0 ≤ v i ∧ v i ≤ 1)
    (L : Realizer (rowRelation rows)) (anchor : FiniteArc n) (trace : List (ForcingEntry n))
    (hAccept : checkForcingTrace rows anchor trace = true)
    {epsilonM epsilonJ r : ℝ} (hM : 0 ≤ epsilonM) (hJ : 0 ≤ epsilonJ)
    (hr : 0 < r) (hqr : (q : ℝ) * r = 1)
    (hMU : ∀ i, |marginalCDF u (u i) - u i| ≤ epsilonM)
    (hMV : ∀ i, |marginalCDF v (v i) - v i| ≤ epsilonM)
    (hGrid : ∀ j k : ℕ, j ≤ q → k ≤ q →
      |empiricalCDF u v ((j : ℝ) * r) ((k : ℝ) * r) -
        populationCDF rho ((j : ℝ) * r) ((k : ℝ) * r)| ≤ epsilonJ) :
    ∃ swap : Bool, ∀ cutoff : ℕ, ∀ s t : ℝ,
      |(L.aligned swap).rankCDF s t - populationCDF rho s t| ≤
        (trimTailCount rows trace cutoff : ℝ) / n + 2 * cutoff / n +
          2 * epsilonM + epsilonJ + 2 * r := by
  classical
  let R := coordinateRowRealizer rows u v hu hv hRows
  obtain ⟨swap, hRanks⟩ := L.checked_forcing_rank_bounds R anchor trace hAccept
  refine ⟨swap, ?_⟩
  intro cutoff s t
  let bad := Finset.univ.filter (fun i => cutoff < unresolvedDegree rows trace i)
  have hGood : ∀ i, i ∉ bad →
      |(rank (L.aligned swap).first i : ℝ) / n - u i| ≤ (cutoff : ℝ) / n + epsilonM ∧
      |(rank (L.aligned swap).second i : ℝ) / n - v i| ≤ (cutoff : ℝ) / n + epsilonM := by
    intro i hi
    have hDegree : unresolvedDegree rows trace i ≤ cutoff := by
      apply le_of_not_gt
      intro hGt
      exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hGt⟩)
    have hDegreeReal : (unresolvedDegree rows trace i : ℝ) ≤ cutoff := by exact_mod_cast hDegree
    have hRU : |(rank (L.aligned swap).first i : ℝ) -
        (rank (fun x y => u x < u y) i : ℝ)| ≤ cutoff := (hRanks i).1.trans hDegreeReal
    have hRV : |(rank (L.aligned swap).second i : ℝ) -
        (rank (fun x y => v x < v y) i : ℝ)| ≤ cutoff := (hRanks i).2.trans hDegreeReal
    exact ⟨normalized_rank_coordinate_error_general hn hu hRU (hMU i),
      normalized_rank_coordinate_error_general hn hv hRV (hMV i)⟩
  have hd : 0 ≤ (cutoff : ℝ) / n + epsilonM := by positivity
  have hCDF := empiricalCDF_error_of_coordinate_error hn u v
    (fun i => (rank (L.aligned swap).first i : ℝ) / n)
    (fun i => (rank (L.aligned swap).second i : ℝ) / n) bad hd hGood
    (populationCDF rho) hK.populationCDF_thresholdStability
    (finite_grid_CDF hK hr hqr hJ hU hV hGrid) s t
  have hExpression : (bad.card : ℝ) / n + 2 * ((cutoff : ℝ) / n + epsilonM) +
      (epsilonJ + 2 * r) = (trimTailCount rows trace cutoff : ℝ) / n +
        2 * cutoff / n + 2 * epsilonM + epsilonJ + 2 * r := by
    dsimp [bad, trimTailCount]
    ring
  exact hCDF.trans_eq hExpression

#print axioms checked_trimmed_CDF

end QuantyraNullCone
