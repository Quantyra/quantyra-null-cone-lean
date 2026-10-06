import QuantyraNullCone.Grid
import QuantyraNullCone.Counts

namespace QuantyraNullCone

noncomputable def cumulativeCount {n : ℕ} (w : Fin n → ℝ) (t : ℝ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun j => w j ≤ t)

noncomputable def marginalCDF {n : ℕ} (w : Fin n → ℝ) (t : ℝ) : ℝ :=
  (cumulativeCount w t).card / (n : ℝ)

noncomputable def verticalStrip {n : ℕ} (v : Fin n → ℝ) (r : ℝ) (i : Fin n) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun j => |v j - v i| < 3 * r)

noncomputable def boundary {n : ℕ} (u v : Fin n → ℝ) (r : ℝ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun j => ¬ Interior u v r j)

/-- The uniform marginal error gives the required strip count for interior events. -/
theorem verticalStrip_card_le {n : ℕ} {u v : Fin n → ℝ} {r : ℝ}
    (hn : 0 < n) (hr : 0 < r)
    (margin : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → |marginalCDF v t - t| ≤ 2 * r)
    {i : Fin n} (hi : Interior u v r i) :
    ((verticalStrip v r i).card : ℝ) ≤ 10 * r * n := by
  classical
  let a := v i - 3 * r
  let b := v i + 3 * r
  let A := cumulativeCount v a
  let B := cumulativeCount v b
  have ha0 : 0 ≤ a := by dsimp [a]; linarith [hi.2.2.1]
  have ha1 : a ≤ 1 := by dsimp [a]; linarith [hi.2.2.2]
  have hb0 : 0 ≤ b := by dsimp [b]; linarith [hi.2.2.1]
  have hb1 : b ≤ 1 := by dsimp [b]; linarith [hi.2.2.2]
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have subAB : A ⊆ B := by
    intro j hj
    have hja : v j ≤ a := by simpa [A, cumulativeCount] using hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hja.trans hab⟩
  have stripSub : verticalStrip v r i ⊆ B \ A := by
    intro j hj
    have hstrip : |v j - v i| < 3 * r := by simpa [verticalStrip] using hj
    have hbounds := abs_lt.mp hstrip
    apply Finset.mem_sdiff.mpr
    constructor
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ j, by dsimp [b]; linarith [hbounds.2]⟩
    · intro hja
      have hle : v j ≤ a := by simpa [A, cumulativeCount] using hja
      dsimp [a] at hle
      linarith [hbounds.1]
  have hcountNat := Finset.card_sdiff_add_card_eq_card subAB
  have hcount : ((B \ A).card : ℝ) + (A.card : ℝ) = (B.card : ℝ) := by
    exact_mod_cast hcountNat
  have hstripCount : ((verticalStrip v r i).card : ℝ) ≤ ((B \ A).card : ℝ) := by
    exact_mod_cast Finset.card_le_card stripSub
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hma := (abs_le.mp (margin a ha0 ha1)).1
  have hmb := (abs_le.mp (margin b hb0 hb1)).2
  have hlo : (a - 2 * r) * n ≤ (A.card : ℝ) := by
    apply (le_div_iff₀ hnR).mp
    change a - 2 * r ≤ marginalCDF v a
    linarith only [hma]
  have hhi : (B.card : ℝ) ≤ (b + 2 * r) * n := by
    apply (div_le_iff₀ hnR).mp
    change marginalCDF v b ≤ b + 2 * r
    linarith only [hmb]
  dsimp [a, b] at hlo hhi
  nlinarith only [hlo, hhi, hcount, hstripCount]

/-- Outside the boundary and narrow vertical strip, the two comparisons agree. -/
theorem comparisons_agree {n : ℕ} {u v : Fin n → ℝ} {r : ℝ}
    (uDistinct : Function.Injective u) (vDistinct : Function.Injective v)
    (L : Realizer (Chronological u v))
    (good : ∀ x y, Interior u v r x → Interior u v r y →
      u x < u y → 3 * r ≤ v x - v y → L.opposite x y)
    {i j : Fin n} (hi : Interior u v r i) (hj : Interior u v r j)
    (separated : 3 * r ≤ |v j - v i|) :
    (L.first j i ↔ u j < u i) ∧ (L.second j i ↔ v j < v i) := by
  by_cases hji : j = i
  · subst j
    exact ⟨iff_of_false (L.firstTotal.irrefl i) (lt_irrefl _),
      iff_of_false (L.secondTotal.irrefl i) (lt_irrefl _)⟩
  have huNe : u j ≠ u i := fun h => hji (uDistinct h)
  have hvNe : v j ≠ v i := fun h => hji (vDistinct h)
  rcases lt_or_gt_of_ne huNe with hu | hu
  · rcases lt_or_gt_of_ne hvNe with hv | hv
    · have p := (L.intersection j i).mp (show Chronological u v j i from ⟨hu, hv⟩)
      exact ⟨iff_of_true p.1 hu, iff_of_true p.2 hv⟩
    · have gap : 3 * r ≤ v j - v i := by
        simpa only [abs_of_pos (sub_pos.mpr hv)] using separated
      have q := good j i hj hi hu gap
      exact ⟨iff_of_true q.1 hu,
        iff_of_false (L.secondTotal.asymm q.2) (not_lt_of_ge hv.le)⟩
  · rcases lt_or_gt_of_ne hvNe with hv | hv
    · have gap : 3 * r ≤ v i - v j := by
        rw [abs_of_neg (sub_neg.mpr hv)] at separated
        linarith only [separated]
      have q := good i j hi hj hu gap
      exact ⟨iff_of_false (L.firstTotal.asymm q.1) (not_lt_of_ge hu.le),
        iff_of_true q.2 hv⟩
    · have p := (L.intersection i j).mp (show Chronological u v i j from ⟨hu, hv⟩)
      exact ⟨iff_of_false (L.firstTotal.asymm p.1) (not_lt_of_ge hu.le),
        iff_of_false (L.secondTotal.asymm p.2) (not_lt_of_ge hv.le)⟩

def Realizer.swap {α : Type} {P : α → α → Prop} (L : Realizer P) : Realizer P where
  first := L.second
  second := L.first
  firstTotal := L.secondTotal
  secondTotal := L.firstTotal
  intersection := by
    intro x y
    constructor
    · intro h
      have hp := (L.intersection x y).mp h
      exact ⟨hp.2, hp.1⟩
    · intro h
      exact (L.intersection x y).mpr ⟨h.2, h.1⟩

def Realizer.aligned {α : Type} {P : α → α → Prop} (L : Realizer P) : Bool → Realizer P
  | false => L
  | true => L.swap

theorem oriented_rank_error {n : ℕ} {u v : Fin n → ℝ} {r : ℝ}
    (hn : 0 < n) (hr : 0 < r)
    (uDistinct : Function.Injective u) (vDistinct : Function.Injective v)
    (L : Realizer (Chronological u v))
    (good : ∀ x y, Interior u v r x → Interior u v r y →
      u x < u y → 3 * r ≤ v x - v y → L.opposite x y)
    (margin : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → |marginalCDF v t - t| ≤ 2 * r)
    (boundaryBound : ((boundary u v r).card : ℝ) ≤ 20 * r * n)
    {i : Fin n} (hi : Interior u v r i) :
    |(rank L.first i : ℝ) - (rank (fun x y => u x < u y) i : ℝ)| ≤ 30 * r * n ∧
    |(rank L.second i : ℝ) - (rank (fun x y => v x < v y) i : ℝ)| ≤ 30 * r * n := by
  classical
  let bad := boundary u v r ∪ verticalStrip v r i
  have outsideAgree : ∀ j, j ∉ bad →
      (L.first j i ↔ u j < u i) ∧ (L.second j i ↔ v j < v i) := by
    intro j hj
    have notBoundary : j ∉ boundary u v r :=
      fun h => hj (Finset.mem_union.mpr (Or.inl h))
    have hjInterior : Interior u v r j := by simpa [boundary] using notBoundary
    have sep : 3 * r ≤ |v j - v i| := by
      apply le_of_not_gt
      intro h
      apply hj
      apply Finset.mem_union.mpr
      right
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩
    exact comparisons_agree uDistinct vDistinct L good hi hjInterior sep
  have subsetFor (R T : Fin n → Fin n → Prop)
      (agree : ∀ j, j ∉ bad → (R j i ↔ T j i)) : disagreements R T i ⊆ bad := by
    intro j hj
    by_contra hnot
    have hdis : ¬ (R j i ↔ T j i) := by simpa [disagreements] using hj
    exact hdis (agree j hnot)
  have cardUnion : (bad.card : ℝ) ≤ ((boundary u v r).card : ℝ) +
      ((verticalStrip v r i).card : ℝ) := by
    exact_mod_cast Finset.card_union_le (boundary u v r) (verticalStrip v r i)
  have stripBound := verticalStrip_card_le hn hr margin hi
  have badBound : (bad.card : ℝ) ≤ 30 * r * n := by
    linarith only [cardUnion, stripBound, boundaryBound]
  have firstCard : ((disagreements L.first (fun x y => u x < u y) i).card : ℝ) ≤
      (bad.card : ℝ) := by
    exact_mod_cast Finset.card_le_card (subsetFor L.first (fun x y => u x < u y)
      (fun j h => (outsideAgree j h).1))
  have secondCard : ((disagreements L.second (fun x y => v x < v y) i).card : ℝ) ≤
      (bad.card : ℝ) := by
    exact_mod_cast Finset.card_le_card (subsetFor L.second (fun x y => v x < v y)
      (fun j h => (outsideAgree j h).2))
  exact ⟨(abs_rank_sub_le_disagreements L.first (fun x y => u x < u y) i).trans
      (firstCard.trans badBound),
    (abs_rank_sub_le_disagreements L.second (fun x y => v x < v y) i).trans
      (secondCard.trans badBound)⟩

/-- The selected substantive finite rank theorem: one global swap, both ranks,
and every interior event. Witness existence and comparison error are derived. -/
theorem finite_realizer_rank_rigidity {n m : ℕ} {u v : Fin n → ℝ} {r : ℝ}
    (hn : 0 < n) (hm : 16 ≤ m) (hr : 0 < r) (hmr : (m : ℝ) * r = 1)
    (uDistinct : Function.Injective u) (vDistinct : Function.Injective v)
    (occ : GridOccupied u v m r) (L : Realizer (Chronological u v))
    (margin : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → |marginalCDF v t - t| ≤ 2 * r)
    (boundaryBound : ((boundary u v r).card : ℝ) ≤ 20 * r * n) :
    ∃ swap : Bool, ∀ i : Fin n, Interior u v r i →
      |(rank (L.aligned swap).first i : ℝ) -
        (rank (fun x y => u x < u y) i : ℝ)| ≤ 30 * r * n ∧
      |(rank (L.aligned swap).second i : ℝ) -
        (rank (fun x y => v x < v y) i : ℝ)| ≤ 30 * r * n := by
  rcases occupied_grid_global_orientation hm hr hmr occ L with good | reverse
  · refine ⟨false, ?_⟩
    intro i hi
    exact oriented_rank_error hn hr uDistinct vDistinct L good margin boundaryBound hi
  · refine ⟨true, ?_⟩
    have good : ∀ x y, Interior u v r x → Interior u v r y →
        u x < u y → 3 * r ≤ v x - v y → L.swap.opposite x y := by
      intro x y hx hy hu hv
      have h := reverse x y hx hy hu hv
      exact ⟨h.2, h.1⟩
    intro i hi
    exact oriented_rank_error hn hr uDistinct vDistinct L.swap good margin boundaryBound hi

/-- Specialization matching the original selected statement, including normalized
boundary mass, both marginal errors, unit-square coordinates, and no grid-line ties.
The general theorem above shows three of those hypotheses are unnecessary. -/
theorem finite_realizer_rank_rigidity_specified {n m : ℕ} {u v : Fin n → ℝ} {r : ℝ}
    (hn : 1 ≤ n) (hm : 16 ≤ m) (rValue : r = 1 / (m : ℝ))
    (_inUnit : ∀ i, 0 < u i ∧ u i < 1 ∧ 0 < v i ∧ v i < 1)
    (uDistinct : Function.Injective u) (vDistinct : Function.Injective v)
    (_noGridLines : ∀ i (k : ℕ), u i ≠ (k : ℝ) * r ∧ v i ≠ (k : ℝ) * r)
    (occ : GridOccupied u v m r) (L : Realizer (Chronological u v))
    (_marginU : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → |marginalCDF u t - t| ≤ 2 * r)
    (marginV : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → |marginalCDF v t - t| ≤ 2 * r)
    (boundaryFraction : ((boundary u v r).card : ℝ) / n ≤ 20 * r) :
    ∃ swap : Bool, ∀ i : Fin n, Interior u v r i →
      |(rank (L.aligned swap).first i : ℝ) -
        (rank (fun x y => u x < u y) i : ℝ)| ≤ 30 * r * n ∧
      |(rank (L.aligned swap).second i : ℝ) -
        (rank (fun x y => v x < v y) i : ℝ)| ≤ 30 * r * n := by
  have hnPos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnPos
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hr : 0 < r := by rw [rValue]; positivity
  have hmr : (m : ℝ) * r = 1 := by
    have h := (eq_div_iff (ne_of_gt hmR)).mp rValue
    simpa only [mul_comm] using h
  exact finite_realizer_rank_rigidity hnPos hm hr hmr uDistinct vDistinct occ L
    marginV ((div_le_iff₀ hnR).mp boundaryFraction)

end QuantyraNullCone

#print axioms QuantyraNullCone.verticalStrip_card_le
#print axioms QuantyraNullCone.comparisons_agree
#print axioms QuantyraNullCone.finite_realizer_rank_rigidity
#print axioms QuantyraNullCone.finite_realizer_rank_rigidity_specified
