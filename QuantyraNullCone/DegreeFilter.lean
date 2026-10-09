import QuantyraNullCone.GoodSamples
import QuantyraNullCone.OrderSelector

namespace QuantyraNullCone

/-- A filter using only strict degrees in the observed directed relation. -/
def DegreeRetained {n : ℕ} (R : Fin n → Fin n → Prop) (r : ℝ) (i : Fin n) : Prop :=
  6 * r * n < (predecessors R i).card ∧
    6 * r * n < (predecessors (fun x y => R y x) i).card

/-- The joint inclusive count includes the sample point exactly once. -/
theorem chronological_predecessor_count {n : ℕ} {u v : Fin n → ℝ}
    (hu : Function.Injective u) (hv : Function.Injective v) (i : Fin n) :
    (rectangleCount u v (u i) (v i)).card =
      (predecessors (Chronological u v) i).card + 1 := by
  classical
  have hset : rectangleCount u v (u i) (v i) =
      insert i (predecessors (Chronological u v) i) := by
    ext j
    simp only [rectangleCount, predecessors, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_insert, Chronological]
    constructor
    · rintro ⟨hju, hjv⟩
      by_cases hji : j = i
      · exact Or.inl hji
      · exact Or.inr ⟨lt_of_le_of_ne hju (fun h => hji (hu h)),
          lt_of_le_of_ne hjv (fun h => hji (hv h))⟩
    · rintro (hji | ⟨hju, hjv⟩)
      · subst j
        exact ⟨le_rfl, le_rfl⟩
      · exact ⟨hju.le, hjv.le⟩
  have hnot : i ∉ predecessors (Chronological u v) i := by
    simp [predecessors, Chronological]
  rw [hset, Finset.card_insert_of_notMem hnot]

theorem chronological_predecessor_fraction {n : ℕ}
    {u v : Fin n → ℝ} (hu : Function.Injective u) (hv : Function.Injective v)
    (i : Fin n) :
    ((predecessors (Chronological u v) i).card : ℝ) / n =
      empiricalCDF u v (u i) (v i) - 1 / n := by
  have heq : ((rectangleCount u v (u i) (v i)).card : ℝ) =
      ((predecessors (Chronological u v) i).card : ℝ) + 1 := by
    exact_mod_cast chronological_predecessor_count hu hv i
  unfold empiricalCDF
  rw [heq, add_div]
  ring

/-- Strict successors are the complement of the union of two inclusive tails.
No self-count correction remains in this inclusion-exclusion identity. -/
theorem chronological_successor_count {n : ℕ} (u v : Fin n → ℝ) (i : Fin n) :
    (predecessors (fun x y => Chronological u v y x) i).card +
      (cumulativeCount u (u i)).card + (cumulativeCount v (v i)).card =
      n + (rectangleCount u v (u i) (v i)).card := by
  classical
  let A := cumulativeCount u (u i)
  let B := cumulativeCount v (v i)
  have hsucc : predecessors (fun x y => Chronological u v y x) i =
      Finset.univ \ (A ∪ B) := by
    ext j
    simp [predecessors, Chronological, A, B, cumulativeCount, not_le]
  have hinter : A ∩ B = rectangleCount u v (u i) (v i) := by
    ext j
    simp [A, B, cumulativeCount, rectangleCount]
  have hcomp := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (A ∪ B))
  have hunion := Finset.card_union_add_card_inter A B
  rw [Finset.card_univ, Fintype.card_fin] at hcomp
  rw [hsucc, ← hinter]
  change (Finset.univ \ (A ∪ B)).card + A.card + B.card = n + (A ∩ B).card
  omega

theorem chronological_successor_fraction {n : ℕ} (hn : 0 < n)
    (u v : Fin n → ℝ) (i : Fin n) :
    ((predecessors (fun x y => Chronological u v y x) i).card : ℝ) / n =
      1 - marginalCDF u (u i) - marginalCDF v (v i) +
        empiricalCDF u v (u i) (v i) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have heq : ((predecessors (fun x y => Chronological u v y x) i).card : ℝ) +
      (cumulativeCount u (u i)).card + (cumulativeCount v (v i)).card =
      n + (rectangleCount u v (u i) (v i)).card := by
    exact_mod_cast chronological_successor_count u v i
  unfold marginalCDF empiricalCDF
  field_simp
  nlinarith

theorem degree_retained_interior {n : ℕ} (hn : 0 < n) {u v : Fin n → ℝ}
    {r : ℝ} (hr : 0 < r)
    (huLow : marginalCDF u (4 * r) ≤ 5 * r)
    (hvLow : marginalCDF v (4 * r) ≤ 5 * r)
    (huHigh : 1 - marginalCDF u (1 - 4 * r) ≤ 5 * r)
    (hvHigh : 1 - marginalCDF v (1 - 4 * r) ≤ 5 * r)
    {i : Fin n} (hi : DegreeRetained (Chronological u v) r i) :
    Interior u v r i := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hrn : 0 < r * n := mul_pos hr hnR
  have lowBound (w : Fin n → ℝ)
      (hTail : marginalCDF w (4 * r) ≤ 5 * r)
      (hSub : predecessors (Chronological u v) i ⊆ cumulativeCount w (4 * r)) :
      False := by
    have hc : ((predecessors (Chronological u v) i).card : ℝ) ≤
        (cumulativeCount w (4 * r)).card := by
      exact_mod_cast Finset.card_le_card hSub
    have ht : ((cumulativeCount w (4 * r)).card : ℝ) ≤ 5 * r * n :=
      (div_le_iff₀ hnR).mp hTail
    have hp := hi.1
    nlinarith
  have highBound (w : Fin n → ℝ)
      (hTail : 1 - marginalCDF w (1 - 4 * r) ≤ 5 * r)
      (hSub : predecessors (fun x y => Chronological u v y x) i ⊆
        Finset.univ \ cumulativeCount w (1 - 4 * r)) : False := by
    have hc : ((predecessors (fun x y => Chronological u v y x) i).card : ℝ) ≤
        (Finset.univ \ cumulativeCount w (1 - 4 * r)).card := by
      exact_mod_cast Finset.card_le_card hSub
    have hsum : ((Finset.univ \ cumulativeCount w (1 - 4 * r)).card : ℝ) +
        (cumulativeCount w (1 - 4 * r)).card = n := by
      have hNat := Finset.card_sdiff_add_card_eq_card
        (Finset.subset_univ (cumulativeCount w (1 - 4 * r)))
      simp only [Finset.card_univ, Fintype.card_fin] at hNat
      exact_mod_cast hNat
    have ht := (mul_le_mul_of_nonneg_right hTail hnR.le)
    have hcancel : marginalCDF w (1 - 4 * r) * n =
        (cumulativeCount w (1 - 4 * r)).card := by
      unfold marginalCDF
      exact div_mul_cancel₀ _ (ne_of_gt hnR)
    rw [sub_mul, one_mul, hcancel] at ht
    have hp := hi.2
    nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_contra h
    have hui : u i < 4 * r := lt_of_not_ge h
    exact lowBound u huLow (by
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ j,
        ((Finset.mem_filter.mp hj).2.1.trans hui).le⟩)
  · by_contra h
    have hui : 1 - 4 * r < u i := lt_of_not_ge h
    exact highBound u huHigh (by
      intro j hj
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ j, ?_⟩
      intro hle
      exact not_lt_of_ge (Finset.mem_filter.mp hle).2
        (hui.trans (Finset.mem_filter.mp hj).2.1))
  · by_contra h
    have hvi : v i < 4 * r := lt_of_not_ge h
    exact lowBound v hvLow (by
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ j,
        ((Finset.mem_filter.mp hj).2.2.trans hvi).le⟩)
  · by_contra h
    have hvi : 1 - 4 * r < v i := lt_of_not_ge h
    exact highBound v hvHigh (by
      intro j hj
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ j, ?_⟩
      intro hle
      exact not_lt_of_ge (Finset.mem_filter.mp hle).2
        (hvi.trans (Finset.mem_filter.mp hj).2.2))

theorem degree_retained_coordinate_rigidity {n m : ℕ} {rho : DiamondPoint → ℝ}
    (hK : InDensityClass rho) (hn : 0 < n) (hm : 16 ≤ m) {r : ℝ}
    (hr : 0 < r) (hmr : (m : ℝ) * r = 1)
    {sample : Fin n → DiamondPoint} (hg : SampleGood rho m r sample)
    (L : Realizer (Chronological (fun i => (sample i).1) (fun i => (sample i).2))) :
    ∃ swap : Bool, ∀ i,
      DegreeRetained (Chronological (fun j => (sample j).1) (fun j => (sample j).2)) r i →
      |(rank (L.aligned swap).first i : ℝ) / n - (sample i).1| ≤ 32 * r ∧
      |(rank (L.aligned swap).second i : ℝ) / n - (sample i).2| ≤ 32 * r := by
  obtain ⟨hSquare, hu, hv, hOcc, hGrid⟩ := hg
  have hGU := grid_vertices_marginalU hK hr hmr (fun i => (hSquare i).2.2) hGrid
  have hGV := grid_vertices_marginalV hK hr hmr (fun i => (hSquare i).1.2) hGrid
  obtain ⟨swap, hswap⟩ := finite_realizer_coordinate_rigidity hn hm hr hmr hu hv hOcc L
    (grid_marginal_accuracy_uniform hr hmr hGU)
    (grid_marginal_accuracy_uniform hr hmr hGV)
    (boundary_card_le_of_grid_marginals hn hm _ _ hmr hGU hGV)
  have h4 : 4 ≤ m := by omega
  have heq : ((m - 4 : ℕ) : ℝ) * r = 1 - 4 * r := by
    rw [Nat.cast_sub h4]
    push_cast
    nlinarith
  have ends (w : Fin n → ℝ) (hw : GridMarginalAccuracy w m r) :
      marginalCDF w (4 * r) ≤ 5 * r ∧
        1 - marginalCDF w (1 - 4 * r) ≤ 5 * r := by
    have hlo := abs_le.mp (hw 4 h4)
    have hhi := abs_le.mp (hw (m - 4) (Nat.sub_le m 4))
    norm_num only [Nat.cast_ofNat] at hlo
    rw [heq] at hhi
    constructor <;> linarith
  have hU := ends _ hGU
  have hV := ends _ hGV
  exact ⟨swap, fun i hi => hswap i
    (degree_retained_interior hn hr hU.1 hV.1 hU.2 hV.2 hi)⟩

#print axioms chronological_predecessor_count
#print axioms chronological_predecessor_fraction
#print axioms chronological_successor_count
#print axioms chronological_successor_fraction
#print axioms degree_retained_interior
#print axioms degree_retained_coordinate_rigidity

end QuantyraNullCone
