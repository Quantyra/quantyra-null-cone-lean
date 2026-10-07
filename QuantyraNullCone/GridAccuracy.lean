import QuantyraNullCone.Cumulative
import QuantyraNullCone.DensityCDF

namespace QuantyraNullCone

def GridMarginalAccuracy {n : ℕ} (w : Fin n → ℝ) (m : ℕ) (r : ℝ) : Prop :=
  ∀ k : ℕ, k ≤ m → |marginalCDF w ((k : ℝ) * r) - (k : ℝ) * r| ≤ r

def GridVertexAccuracy {n : ℕ} (u v : Fin n → ℝ) (rho : DiamondPoint → ℝ)
    (m : ℕ) (r : ℝ) : Prop :=
  ∀ j k : ℕ, j ≤ m → k ≤ m →
    |empiricalCDF u v ((j : ℝ) * r) ((k : ℝ) * r) -
      populationCDF rho ((j : ℝ) * r) ((k : ℝ) * r)| ≤ r

theorem marginalCDF_mono {n : ℕ} (w : Fin n → ℝ) {a b : ℝ} (hab : a ≤ b) :
    marginalCDF w a ≤ marginalCDF w b := by
  classical
  have hSub : cumulativeCount w a ⊆ cumulativeCount w b := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,
      (Finset.mem_filter.mp hi).2.trans hab⟩
  exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card hSub)
    (Nat.cast_nonneg n)

theorem grid_bracket {m : ℕ} {r t : ℝ} (hr : 0 < r) (hmr : (m : ℝ) * r = 1)
    (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ∃ k : ℕ, k < m ∧ (k : ℝ) * r ≤ t ∧ t < ((k : ℝ) + 1) * r := by
  let k := Nat.floor (t / r)
  have hlo : (k : ℝ) * r ≤ t :=
    (le_div_iff₀ hr).mp (Nat.floor_le (div_nonneg ht0 hr.le))
  have hhi : t < ((k : ℝ) + 1) * r :=
    (div_lt_iff₀ hr).mp (Nat.lt_floor_add_one (t / r))
  have hk : (k : ℝ) < m := lt_of_mul_lt_mul_right
    (by linarith : (k : ℝ) * r < (m : ℝ) * r) hr.le
  exact ⟨k, by exact_mod_cast hk, hlo, hhi⟩

theorem grid_marginal_accuracy_uniform {n m : ℕ} {w : Fin n → ℝ} {r : ℝ}
    (hr : 0 < r) (hmr : (m : ℝ) * r = 1) (hGrid : GridMarginalAccuracy w m r)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : |marginalCDF w t - t| ≤ 2 * r := by
  rcases lt_or_eq_of_le ht1 with ht | ht
  · obtain ⟨k, hk, hlo, hhi⟩ := grid_bracket hr hmr ht0 ht
    have hLow := abs_le.mp (hGrid k hk.le)
    have hHigh := abs_le.mp (hGrid (k + 1) (Nat.succ_le_of_lt hk))
    have hMonoLow := marginalCDF_mono w hlo
    have hMonoHigh := marginalCDF_mono w hhi.le
    push_cast at hHigh
    apply abs_le.mpr
    constructor <;> nlinarith
  · subst t
    have h := hGrid m le_rfl
    rw [hmr] at h
    exact h.trans (by linarith)

theorem empiricalCDF_u_one {n : ℕ} (u v : Fin n → ℝ) (hV : ∀ i, v i ≤ 1) (s : ℝ) :
    empiricalCDF u v s 1 = marginalCDF u s := by
  classical
  have hSet : rectangleCount u v s 1 = cumulativeCount u s := by
    ext i
    simp [rectangleCount, cumulativeCount, hV i]
  unfold empiricalCDF marginalCDF
  rw [hSet]

theorem empiricalCDF_one_v {n : ℕ} (u v : Fin n → ℝ) (hU : ∀ i, u i ≤ 1) (t : ℝ) :
    empiricalCDF u v 1 t = marginalCDF v t := by
  classical
  have hSet : rectangleCount u v 1 t = cumulativeCount v t := by
    ext i
    simp [rectangleCount, cumulativeCount, hU i]
  unfold empiricalCDF marginalCDF
  rw [hSet]

theorem grid_vertices_marginalU {n m : ℕ} {u v : Fin n → ℝ}
    {rho : DiamondPoint → ℝ} {r : ℝ} (hK : InDensityClass rho)
    (hr : 0 < r) (hmr : (m : ℝ) * r = 1) (hV : ∀ i, v i ≤ 1)
    (hGrid : GridVertexAccuracy u v rho m r) : GridMarginalAccuracy u m r := by
  intro k hk
  have hk0 : 0 ≤ (k : ℝ) * r := mul_nonneg (Nat.cast_nonneg k) hr.le
  have hk1 : (k : ℝ) * r ≤ 1 := by
    rw [← hmr]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hr.le
  have h := hGrid k m hk le_rfl
  rw [hmr, empiricalCDF_u_one u v hV, hK.populationCDF_u_one hk0 hk1] at h
  exact h

theorem grid_vertices_marginalV {n m : ℕ} {u v : Fin n → ℝ}
    {rho : DiamondPoint → ℝ} {r : ℝ} (hK : InDensityClass rho)
    (hr : 0 < r) (hmr : (m : ℝ) * r = 1) (hU : ∀ i, u i ≤ 1)
    (hGrid : GridVertexAccuracy u v rho m r) : GridMarginalAccuracy v m r := by
  intro k hk
  have hk0 : 0 ≤ (k : ℝ) * r := mul_nonneg (Nat.cast_nonneg k) hr.le
  have hk1 : (k : ℝ) * r ≤ 1 := by
    rw [← hmr]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hr.le
  have h := hGrid m k le_rfl hk
  rw [hmr, empiricalCDF_one_v u v hU, hK.populationCDF_one_v hk0 hk1] at h
  exact h

theorem coordinate_boundary_count_le {n : ℕ} (hn : 0 < n) (w : Fin n → ℝ) {r : ℝ}
    (hLow : |marginalCDF w (4 * r) - 4 * r| ≤ r)
    (hHigh : |marginalCDF w (1 - 4 * r) - (1 - 4 * r)| ≤ r) :
    ((cumulativeCount w (4 * r)).card : ℝ) +
      ((Finset.univ \ cumulativeCount w (1 - 4 * r)).card : ℝ) ≤ 10 * r * n := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlo := (abs_le.mp hLow).2
  have hhi := (abs_le.mp hHigh).1
  have hLowCount : ((cumulativeCount w (4 * r)).card : ℝ) ≤ 5 * r * n := by
    apply (div_le_iff₀ hnR).mp
    change marginalCDF w (4 * r) ≤ 5 * r
    linarith
  have hHighCount : (1 - 5 * r) * n ≤ ((cumulativeCount w (1 - 4 * r)).card : ℝ) := by
    apply (le_div_iff₀ hnR).mp
    change 1 - 5 * r ≤ marginalCDF w (1 - 4 * r)
    linarith
  have hComplement : ((Finset.univ \ cumulativeCount w (1 - 4 * r)).card : ℝ) +
      ((cumulativeCount w (1 - 4 * r)).card : ℝ) = n := by
    have hNat := Finset.card_sdiff_add_card_eq_card
      (Finset.subset_univ (cumulativeCount w (1 - 4 * r)))
    simp only [Finset.card_univ, Fintype.card_fin] at hNat
    exact_mod_cast hNat
  nlinarith

theorem boundary_card_le_of_endpoint_accuracy {n : ℕ} (hn : 0 < n)
    (u v : Fin n → ℝ) {r : ℝ}
    (huLow : |marginalCDF u (4 * r) - 4 * r| ≤ r)
    (huHigh : |marginalCDF u (1 - 4 * r) - (1 - 4 * r)| ≤ r)
    (hvLow : |marginalCDF v (4 * r) - 4 * r| ≤ r)
    (hvHigh : |marginalCDF v (1 - 4 * r) - (1 - 4 * r)| ≤ r) :
    ((boundary u v r).card : ℝ) ≤ 20 * r * n := by
  classical
  let lowU := cumulativeCount u (4 * r)
  let highU := Finset.univ \ cumulativeCount u (1 - 4 * r)
  let lowV := cumulativeCount v (4 * r)
  let highV := Finset.univ \ cumulativeCount v (1 - 4 * r)
  have hSub : boundary u v r ⊆ (lowU ∪ highU) ∪ (lowV ∪ highV) := by
    intro i hi
    have hNot : ¬ Interior u v r i := (Finset.mem_filter.mp hi).2
    by_cases hu0 : u i ≤ 4 * r
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hu0⟩))
    by_cases hu1 : u i ≤ 1 - 4 * r
    · by_cases hv0 : v i ≤ 4 * r
      · exact Finset.mem_union_right _ (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hv0⟩))
      · by_cases hv1 : v i ≤ 1 - 4 * r
        · exact False.elim (hNot ⟨(not_le.mp hu0).le, hu1, (not_le.mp hv0).le, hv1⟩)
        · exact Finset.mem_union_right _ (Finset.mem_union_right _
            (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, by
              intro hm
              exact hv1 (Finset.mem_filter.mp hm).2⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, by
          intro hm
          exact hu1 (Finset.mem_filter.mp hm).2⟩))
  have hCard : (boundary u v r).card ≤ lowU.card + highU.card + (lowV.card + highV.card) :=
    (Finset.card_le_card hSub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add (Finset.card_union_le _ _) (Finset.card_union_le _ _)))
  have hCardR : ((boundary u v r).card : ℝ) ≤
      (lowU.card : ℝ) + highU.card + ((lowV.card : ℝ) + highV.card) := by
    exact_mod_cast hCard
  have hU := coordinate_boundary_count_le hn u huLow huHigh
  have hV := coordinate_boundary_count_le hn v hvLow hvHigh
  dsimp [lowU, highU, lowV, highV] at hCardR
  nlinarith

theorem boundary_card_le_of_grid_marginals {n m : ℕ} (hn : 0 < n) (hm : 16 ≤ m)
    (u v : Fin n → ℝ) {r : ℝ} (hmr : (m : ℝ) * r = 1)
    (hU : GridMarginalAccuracy u m r) (hV : GridMarginalAccuracy v m r) :
    ((boundary u v r).card : ℝ) ≤ 20 * r * n := by
  have h4 : 4 ≤ m := by omega
  have hUpper : ((m - 4 : ℕ) : ℝ) * r = 1 - 4 * r := by
    rw [Nat.cast_sub h4]
    push_cast
    nlinarith [hmr]
  have huLow := hU 4 h4
  have hvLow := hV 4 h4
  have huHigh := hU (m - 4) (Nat.sub_le m 4)
  have hvHigh := hV (m - 4) (Nat.sub_le m 4)
  norm_num only [Nat.cast_ofNat] at huLow hvLow
  rw [hUpper] at huHigh hvHigh
  exact boundary_card_le_of_endpoint_accuracy hn u v huLow huHigh hvLow hvHigh

theorem grid_closed_bracket {m : ℕ} {r t : ℝ} (hr : 0 < r)
    (hmr : (m : ℝ) * r = 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ j k : ℕ, j ≤ m ∧ k ≤ m ∧ (j : ℝ) * r ≤ t ∧ t ≤ (k : ℝ) * r ∧
      t - (j : ℝ) * r ≤ r ∧ (k : ℝ) * r - t ≤ r := by
  rcases lt_or_eq_of_le ht1 with ht | ht
  · obtain ⟨j, hj, hlo, hhi⟩ := grid_bracket hr hmr ht0 ht
    refine ⟨j, j + 1, hj.le, Nat.succ_le_of_lt hj, hlo, ?_, ?_, ?_⟩
    all_goals push_cast; nlinarith
  · subst t
    exact ⟨m, m, le_rfl, le_rfl, hmr.le, hmr.ge,
      by rw [hmr]; linarith, by rw [hmr]; linarith⟩

theorem empiricalCDF_mono {n : ℕ} (u v : Fin n → ℝ) {s t s' t' : ℝ}
    (hs : s ≤ s') (ht : t ≤ t') : empiricalCDF u v s t ≤ empiricalCDF u v s' t' := by
  classical
  have hSub : rectangleCount u v s t ⊆ rectangleCount u v s' t' := by
    intro i hi
    have h := (Finset.mem_filter.mp hi).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, h.1.trans hs, h.2.trans ht⟩
  exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card hSub)
    (Nat.cast_nonneg n)

theorem grid_vertices_empiricalCDF_unit {n m : ℕ} {u v : Fin n → ℝ}
    {rho : DiamondPoint → ℝ} {r : ℝ} (hK : InDensityClass rho)
    (hr : 0 < r) (hmr : (m : ℝ) * r = 1)
    (hGrid : GridVertexAccuracy u v rho m r) (s t : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |empiricalCDF u v s t - populationCDF rho s t| ≤ 3 * r := by
  obtain ⟨j, j', hj, hj', hslo, hshi, hsGap, hsGap'⟩ := grid_closed_bracket hr hmr hs0 hs1
  obtain ⟨k, k', hk, hk', htlo, hthi, htGap, htGap'⟩ := grid_closed_bracket hr hmr ht0 ht1
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

theorem empiricalCDF_cap {n : ℕ} (u v : Fin n → ℝ)
    (hU : ∀ i, u i ≤ 1) (hV : ∀ i, v i ≤ 1) (s t : ℝ) :
    empiricalCDF u v s t = empiricalCDF u v (min s 1) (min t 1) := by
  classical
  have hSet : rectangleCount u v s t = rectangleCount u v (min s 1) (min t 1) := by
    ext i
    simp [rectangleCount, hU i, hV i]
  unfold empiricalCDF
  rw [hSet]

theorem populationCDF_cap (rho : DiamondPoint → ℝ) (s t : ℝ) :
    populationCDF rho s t = populationCDF rho (min s 1) (min t 1) := by
  have hSet : cdfRegion s t ∩ diamond = cdfRegion (min s 1) (min t 1) ∩ diamond := by
    ext p
    change ((p.1 ≤ s ∧ p.2 ≤ t) ∧ ((0 ≤ p.1 ∧ p.1 ≤ 1) ∧ (0 ≤ p.2 ∧ p.2 ≤ 1))) ↔
      ((p.1 ≤ min s 1 ∧ p.2 ≤ min t 1) ∧
        ((0 ≤ p.1 ∧ p.1 ≤ 1) ∧ (0 ≤ p.2 ∧ p.2 ≤ 1)))
    simp only [le_min_iff]
    tauto
  change (densityMeasure rho (cdfRegion s t)).toReal =
    (densityMeasure rho (cdfRegion (min s 1) (min t 1))).toReal
  rw [densityMeasure_inter_diamond rho (cdfRegion_measurableSet s t),
    densityMeasure_inter_diamond rho (cdfRegion_measurableSet (min s 1) (min t 1)), hSet]

theorem populationCDF_negative (rho : DiamondPoint → ℝ) {s t : ℝ}
    (hNeg : s < 0 ∨ t < 0) : populationCDF rho s t = 0 := by
  have hSet : cdfRegion s t ∩ diamond = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro p ⟨hp, hd⟩
    change (0 ≤ p.1 ∧ p.1 ≤ 1) ∧ (0 ≤ p.2 ∧ p.2 ≤ 1) at hd
    rcases hNeg with hs | ht
    · linarith [hp.1, hd.1.1]
    · linarith [hp.2, hd.2.1]
  change (densityMeasure rho (cdfRegion s t)).toReal = 0
  rw [densityMeasure_inter_diamond rho (cdfRegion_measurableSet s t), hSet]
  simp

theorem empiricalCDF_negative {n : ℕ} (u v : Fin n → ℝ)
    (hU : ∀ i, 0 ≤ u i) (hV : ∀ i, 0 ≤ v i) {s t : ℝ}
    (hNeg : s < 0 ∨ t < 0) : empiricalCDF u v s t = 0 := by
  classical
  have hSet : rectangleCount u v s t = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hp := (Finset.mem_filter.mp hi).2
    rcases hNeg with hs | ht
    · linarith [hp.1, hU i]
    · linarith [hp.2, hV i]
  simp [empiricalCDF, hSet]

theorem grid_vertices_empiricalCDF {n m : ℕ} {u v : Fin n → ℝ}
    {rho : DiamondPoint → ℝ} {r : ℝ} (hK : InDensityClass rho)
    (hr : 0 < r) (hmr : (m : ℝ) * r = 1)
    (hU : ∀ i, 0 ≤ u i ∧ u i ≤ 1) (hV : ∀ i, 0 ≤ v i ∧ v i ≤ 1)
    (hGrid : GridVertexAccuracy u v rho m r) (s t : ℝ) :
    |empiricalCDF u v s t - populationCDF rho s t| ≤ 3 * r := by
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
  exact grid_vertices_empiricalCDF_unit hK hr hmr hGrid (min s 1) (min t 1)
    (le_min (le_of_not_gt hs) (by norm_num)) (min_le_right _ _)
    (le_min (le_of_not_gt ht) (by norm_num)) (min_le_right _ _)

theorem finite_realizer_cumulative_error_of_grid_vertices {n m : ℕ}
    {u v : Fin n → ℝ} {rho : DiamondPoint → ℝ} {r : ℝ}
    (hK : InDensityClass rho) (hn : 0 < n) (hm : 16 ≤ m) (hr : 0 < r)
    (hmr : (m : ℝ) * r = 1)
    (hU : ∀ i, 0 ≤ u i ∧ u i ≤ 1) (hV : ∀ i, 0 ≤ v i ∧ v i ≤ 1)
    (uDistinct : Function.Injective u) (vDistinct : Function.Injective v)
    (occ : GridOccupied u v m r) (L : Realizer (Chronological u v))
    (hGrid : GridVertexAccuracy u v rho m r) :
    ∃ swap : Bool, ∀ s t : ℝ,
      |empiricalCDF (fun i => (rank (L.aligned swap).first i : ℝ) / n)
        (fun i => (rank (L.aligned swap).second i : ℝ) / n) s t -
        populationCDF rho s t| ≤ 87 * r := by
  have hGU := grid_vertices_marginalU hK hr hmr (fun i => (hV i).2) hGrid
  have hGV := grid_vertices_marginalV hK hr hmr (fun i => (hU i).2) hGrid
  exact finite_realizer_cumulative_error hn hm hr hmr uDistinct vDistinct occ L
    (grid_marginal_accuracy_uniform hr hmr hGU)
    (grid_marginal_accuracy_uniform hr hmr hGV)
    (boundary_card_le_of_grid_marginals hn hm u v hmr hGU hGV)
    (populationCDF rho) hK.populationCDF_thresholdStability
    (grid_vertices_empiricalCDF hK hr hmr hU hV hGrid)

#print axioms grid_marginal_accuracy_uniform
#print axioms boundary_card_le_of_grid_marginals
#print axioms grid_vertices_empiricalCDF
#print axioms finite_realizer_cumulative_error_of_grid_vertices

end QuantyraNullCone
