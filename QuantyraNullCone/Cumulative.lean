import QuantyraNullCone.Bridges
import Mathlib.Tactic.Ring

namespace QuantyraNullCone

/-- Inclusive marginal counts at an event are exactly its coordinate rank.
There is no additional one-over-sample-size offset. -/
theorem coordinate_rank_eq_cumulativeCount {n : ℕ} (w : Fin n → ℝ)
    (distinct : Function.Injective w) (i : Fin n) :
    rank (fun x y => w x < w y) i = (cumulativeCount w (w i)).card := by
  classical
  have hset : cumulativeCount w (w i) =
      insert i (predecessors (fun x y => w x < w y) i) := by
    ext j
    simp only [cumulativeCount, predecessors, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_insert]
    constructor
    · intro h
      rcases lt_or_eq_of_le h with hlt | heq
      · exact Or.inr hlt
      · exact Or.inl (distinct heq)
    · rintro (h | h)
      · subst j
        exact le_rfl
      · exact h.le
  have hnot : i ∉ predecessors (fun x y => w x < w y) i := by
    simp [predecessors]
  rw [hset, Finset.card_insert_of_notMem hnot]
  simp [rank, Nat.add_comm]

theorem normalized_coordinate_rank_eq_marginalCDF {n : ℕ} (w : Fin n → ℝ)
    (distinct : Function.Injective w) (i : Fin n) :
    (rank (fun x y => w x < w y) i : ℝ) / n = marginalCDF w (w i) := by
  rw [coordinate_rank_eq_cumulativeCount w distinct i]
  rfl

/-- A finite rank discrepancy and an empirical marginal error imply a true
coordinate discrepancy after normalization. This is an algebraic bridge;
the finite rank theorem and concentration supply its two separate inputs. -/
theorem normalized_rank_coordinate_error {n : ℕ} (hn : 0 < n)
    {w : Fin n → ℝ} (distinct : Function.Injective w)
    {L : Fin n → Fin n → Prop} {i : Fin n} {r : ℝ}
    (rankError : |(rank L i : ℝ) -
      (rank (fun x y => w x < w y) i : ℝ)| ≤ 30 * r * n)
    (marginError : |marginalCDF w (w i) - w i| ≤ 2 * r) :
    |(rank L i : ℝ) / n - w i| ≤ 32 * r := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdiv : |((rank L i : ℝ) -
      (rank (fun x y => w x < w y) i : ℝ)) / n| ≤ 30 * r := by
    rw [abs_div, abs_of_pos hnR]
    apply (div_le_iff₀ hnR).mpr
    exact rankError
  have hmargin : |(rank (fun x y => w x < w y) i : ℝ) / n - w i| ≤ 2 * r := by
    rw [normalized_coordinate_rank_eq_marginalCDF w distinct i]
    exact marginError
  have hdecomp : (rank L i : ℝ) / n - w i =
      ((rank L i : ℝ) - (rank (fun x y => w x < w y) i : ℝ)) / n +
        ((rank (fun x y => w x < w y) i : ℝ) / n - w i) := by
    rw [sub_div]
    ring
  rw [hdecomp]
  have htriangle := abs_add_le
    (((rank L i : ℝ) - (rank (fun x y => w x < w y) i : ℝ)) / n)
    ((rank (fun x y => w x < w y) i : ℝ) / n - w i)
  linarith

/-- The existing finite theorem yields true-coordinate accuracy for every
interior event after one globally shared swap of an arbitrary realizer. -/
theorem finite_realizer_coordinate_rigidity {n m : ℕ} {u v : Fin n → ℝ} {r : ℝ}
    (hn : 0 < n) (hm : 16 ≤ m) (hr : 0 < r) (hmr : (m : ℝ) * r = 1)
    (uDistinct : Function.Injective u) (vDistinct : Function.Injective v)
    (occ : GridOccupied u v m r) (L : Realizer (Chronological u v))
    (marginU : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → |marginalCDF u t - t| ≤ 2 * r)
    (marginV : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → |marginalCDF v t - t| ≤ 2 * r)
    (boundaryBound : ((boundary u v r).card : ℝ) ≤ 20 * r * n) :
    ∃ swap : Bool, ∀ i : Fin n, Interior u v r i →
      |(rank (L.aligned swap).first i : ℝ) / n - u i| ≤ 32 * r ∧
      |(rank (L.aligned swap).second i : ℝ) / n - v i| ≤ 32 * r := by
  rcases finite_realizer_rank_rigidity hn hm hr hmr uDistinct vDistinct occ L
    marginV boundaryBound with ⟨swap, hswap⟩
  refine ⟨swap, ?_⟩
  intro i hi
  have hu0 : 0 ≤ u i := by linarith [hi.1]
  have hu1 : u i ≤ 1 := by linarith [hi.2.1]
  have hv0 : 0 ≤ v i := by linarith [hi.2.2.1]
  have hv1 : v i ≤ 1 := by linarith [hi.2.2.2]
  exact ⟨normalized_rank_coordinate_error hn uDistinct (hswap i hi).1
      (marginU (u i) hu0 hu1),
    normalized_rank_coordinate_error hn vDistinct (hswap i hi).2
      (marginV (v i) hv0 hv1)⟩

noncomputable def rectangleCount {n : ℕ} (u v : Fin n → ℝ) (s t : ℝ) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => u i ≤ s ∧ v i ≤ t)

noncomputable def empiricalCDF {n : ℕ} (u v : Fin n → ℝ) (s t : ℝ) : ℝ :=
  ((rectangleCount u v s t).card : ℝ) / n

/-- The rectangle sandwich discards the bad set once in each direction.
It is valid at all real thresholds, so clipping can be treated separately. -/
theorem empiricalCDF_sandwich {n : ℕ} (hn : 0 < n)
    (u v qu qv : Fin n → ℝ) (bad : Finset (Fin n)) {d : ℝ}
    (good : ∀ i, i ∉ bad → |qu i - u i| ≤ d ∧ |qv i - v i| ≤ d)
    (s t : ℝ) :
    empiricalCDF u v (s - d) (t - d) - (bad.card : ℝ) / n ≤
      empiricalCDF qu qv s t ∧
    empiricalCDF qu qv s t ≤ empiricalCDF u v (s + d) (t + d) +
      (bad.card : ℝ) / n := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have lowerSub : rectangleCount u v (s - d) (t - d) ⊆
      rectangleCount qu qv s t ∪ bad := by
    intro i hi
    by_cases hbad : i ∈ bad
    · exact Finset.mem_union.mpr (Or.inr hbad)
    · have hpoint : u i ≤ s - d ∧ v i ≤ t - d := by
        simpa [rectangleCount] using hi
      have hu := (abs_le.mp (good i hbad).1).2
      have hv := (abs_le.mp (good i hbad).2).2
      apply Finset.mem_union.mpr
      left
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, by constructor <;> linarith⟩
  have upperSub : rectangleCount qu qv s t ⊆
      rectangleCount u v (s + d) (t + d) ∪ bad := by
    intro i hi
    by_cases hbad : i ∈ bad
    · exact Finset.mem_union.mpr (Or.inr hbad)
    · have hpoint : qu i ≤ s ∧ qv i ≤ t := by
        simpa [rectangleCount] using hi
      have hu := (abs_le.mp (good i hbad).1).1
      have hv := (abs_le.mp (good i hbad).2).1
      apply Finset.mem_union.mpr
      left
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, by constructor <;> linarith⟩
  have lowerCard : ((rectangleCount u v (s - d) (t - d)).card : ℝ) ≤
      ((rectangleCount qu qv s t).card : ℝ) + (bad.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card lowerSub).trans
      (Finset.card_union_le _ _)
  have upperCard : ((rectangleCount qu qv s t).card : ℝ) ≤
      ((rectangleCount u v (s + d) (t + d)).card : ℝ) + (bad.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card upperSub).trans
      (Finset.card_union_le _ _)
  have lowerDiv := div_le_div_of_nonneg_right lowerCard hnR.le
  have upperDiv := div_le_div_of_nonneg_right upperCard hnR.le
  rw [add_div] at lowerDiv upperDiv
  dsimp [empiricalCDF]
  constructor <;> linarith only [lowerDiv, upperDiv]

/-- Population threshold stability and latent empirical accuracy turn the
deterministic sandwich into a cumulative error. These analytic inputs are
separate from, and weaker than, the reconstructed-CDF conclusion. -/
theorem empiricalCDF_error_of_coordinate_error {n : ℕ} (hn : 0 < n)
    (u v qu qv : Fin n → ℝ) (bad : Finset (Fin n))
    {d η : ℝ} (hd : 0 ≤ d)
    (good : ∀ i, i ∉ bad → |qu i - u i| ≤ d ∧ |qv i - v i| ≤ d)
    (F : ℝ → ℝ → ℝ)
    (thresholdStability : ∀ s t s' t',
      |F s t - F s' t'| ≤ |s - s'| + |t - t'|)
    (latentAccuracy : ∀ s t, |empiricalCDF u v s t - F s t| ≤ η)
    (s t : ℝ) :
    |empiricalCDF qu qv s t - F s t| ≤ (bad.card : ℝ) / n + 2 * d + η := by
  have hsandwich := empiricalCDF_sandwich hn u v qu qv bad good s t
  have hdown : |F (s - d) (t - d) - F s t| ≤ 2 * d := by
    have h := thresholdStability (s - d) (t - d) s t
    have hs : (s - d) - s = -d := by ring
    have ht : (t - d) - t = -d := by ring
    rw [hs, ht, abs_neg, abs_of_nonneg hd] at h
    linarith only [h]
  have hup : |F (s + d) (t + d) - F s t| ≤ 2 * d := by
    have h := thresholdStability (s + d) (t + d) s t
    simp only [add_sub_cancel_left, abs_of_nonneg hd] at h
    linarith only [h]
  have hlatentDown := abs_le.mp (latentAccuracy (s - d) (t - d))
  have hlatentUp := abs_le.mp (latentAccuracy (s + d) (t + d))
  have hpopDown := abs_le.mp hdown
  have hpopUp := abs_le.mp hup
  apply abs_le.mpr
  constructor <;> linarith only [hsandwich.1, hsandwich.2,
    hlatentDown.1, hlatentDown.2, hlatentUp.1, hlatentUp.2,
    hpopDown.1, hpopDown.2, hpopUp.1, hpopUp.2]

/-- The full deterministic rank-to-cumulative bridge. Uniform-marginal
stability and latent empirical error are explicit analytic premises to be
proved from the concrete model and grid concentration in the next stages. -/
theorem finite_realizer_cumulative_error {n m : ℕ} {u v : Fin n → ℝ} {r : ℝ}
    (hn : 0 < n) (hm : 16 ≤ m) (hr : 0 < r) (hmr : (m : ℝ) * r = 1)
    (uDistinct : Function.Injective u) (vDistinct : Function.Injective v)
    (occ : GridOccupied u v m r) (L : Realizer (Chronological u v))
    (marginU : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → |marginalCDF u t - t| ≤ 2 * r)
    (marginV : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → |marginalCDF v t - t| ≤ 2 * r)
    (boundaryBound : ((boundary u v r).card : ℝ) ≤ 20 * r * n)
    (F : ℝ → ℝ → ℝ)
    (thresholdStability : ∀ s t s' t',
      |F s t - F s' t'| ≤ |s - s'| + |t - t'|)
    (latentAccuracy : ∀ s t, |empiricalCDF u v s t - F s t| ≤ 3 * r) :
    ∃ swap : Bool, ∀ s t : ℝ,
      |empiricalCDF (fun i => (rank (L.aligned swap).first i : ℝ) / n)
        (fun i => (rank (L.aligned swap).second i : ℝ) / n) s t - F s t| ≤ 87 * r := by
  classical
  rcases finite_realizer_coordinate_rigidity hn hm hr hmr uDistinct vDistinct
    occ L marginU marginV boundaryBound with ⟨swap, aligned⟩
  refine ⟨swap, ?_⟩
  intro s t
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hboundary : ((boundary u v r).card : ℝ) / n ≤ 20 * r :=
    (div_le_iff₀ hnR).mpr boundaryBound
  have good : ∀ i, i ∉ boundary u v r →
      |(rank (L.aligned swap).first i : ℝ) / n - u i| ≤ 32 * r ∧
      |(rank (L.aligned swap).second i : ℝ) / n - v i| ≤ 32 * r := by
    intro i hi
    exact aligned i (by simpa [boundary] using hi)
  have h := empiricalCDF_error_of_coordinate_error hn u v
    (fun i => (rank (L.aligned swap).first i : ℝ) / n)
    (fun i => (rank (L.aligned swap).second i : ℝ) / n)
    (boundary u v r) (by positivity : 0 ≤ 32 * r) good F
    thresholdStability latentAccuracy s t
  linarith only [h, hboundary]

end QuantyraNullCone

#print axioms QuantyraNullCone.finite_realizer_coordinate_rigidity
#print axioms QuantyraNullCone.finite_realizer_cumulative_error
