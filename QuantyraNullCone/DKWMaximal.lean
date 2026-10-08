import QuantyraNullCone.DKWBins
import Mathlib.Data.Finset.Max

namespace QuantyraNullCone

theorem finite_bin_reveal_count {n q k j : ℕ} {x y : BinProfile n q}
    (h : finiteBinReveal k x = finiteBinReveal k y) (hkj : k ≤ j) :
    finiteBinCount x j = finiteBinCount y j := by
  unfold finiteBinCount
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hi := congrFun h i
  change max ((x i).val + 1) k = max ((y i).val + 1) k at hi
  have hx : (x i).val < j ↔ max ((x i).val + 1) k ≤ j := by
    rw [max_le_iff]
    omega
  have hy : (y i).val < j ↔ max ((y i).val + 1) k ≤ j := by
    rw [max_le_iff]
    omega
  rw [hx, hi, ← hy]

theorem finite_bin_likelihood_reveal {n q k j : ℕ} {x y : BinProfile n q}
    (h : finiteBinReveal k x = finiteBinReveal k y) (hkj : k ≤ j) (lambda : ℝ) :
    finiteBinLikelihood lambda j x = finiteBinLikelihood lambda j y := by
  unfold finiteBinLikelihood
  rw [finite_bin_reveal_count h hkj]

theorem finite_bin_likelihood_nonneg {n q k : ℕ} {lambda : ℝ} (hL : 0 < lambda)
    (x : BinProfile n q) : 0 ≤ finiteBinLikelihood lambda k x := by
  unfold finiteBinLikelihood
  positivity

/-- Finite fiber summation; the actual-bin application derives the atom identity. -/
theorem finite_fiber_sum_invariant {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    (r : α → β) (T M : α → ℝ) (E : Finset α)
    (hAtom : ∀ x, (∑ y ∈ Finset.univ.filter (fun y => r y = r x), T y) =
      (Finset.univ.filter (fun y => r y = r x)).card * M x)
    (hM : ∀ x y, r x = r y → M x = M y)
    (hE : ∀ x y, r x = r y → (x ∈ E ↔ y ∈ E)) :
    (∑ x ∈ E, T x) = ∑ x ∈ E, M x := by
  have hFibre : ∀ z ∈ E.image r,
      (∑ y ∈ E.filter (fun y => r y = z), T y) =
        ∑ y ∈ E.filter (fun y => r y = z), M y := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    have hSet : E.filter (fun y => r y = r x) =
        Finset.univ.filter (fun y => r y = r x) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact And.right
      · intro hy
        exact ⟨(hE y x hy).mpr hx, hy⟩
    rw [hSet, hAtom]
    have hSum : (∑ y ∈ Finset.univ.filter (fun y => r y = r x), M y) =
        ∑ _y ∈ Finset.univ.filter (fun y => r y = r x), M x := by
      apply Finset.sum_congr rfl
      intro y hy
      exact hM y x (Finset.mem_filter.mp hy).2
    rw [hSum]
    simp
  have hMaps : ∀ x ∈ E, r x ∈ E.image r := fun x hx => Finset.mem_image_of_mem r hx
  rw [← Finset.sum_fiberwise_of_maps_to hMaps T, ← Finset.sum_fiberwise_of_maps_to hMaps M]
  exact Finset.sum_congr rfl hFibre

theorem finite_bin_invariant_terminal_sum {n q k : ℕ} (hk : 0 < k) (hkq : k ≤ q)
    (lambda : ℝ) (E : Finset (BinProfile n q))
    (hE : ∀ x y, finiteBinReveal k x = finiteBinReveal k y → (x ∈ E ↔ y ∈ E)) :
    (∑ x ∈ E, finiteBinLikelihood lambda 1 x) =
      ∑ x ∈ E, finiteBinLikelihood lambda k x := by
  apply finite_fiber_sum_invariant (finiteBinReveal k)
  · exact finite_bin_atom_likelihood_identity hk hkq lambda
  · intro x y h
    exact finite_bin_likelihood_reveal h le_rfl lambda
  · exact hE

noncomputable def finiteBinFirstCross {n q : ℕ} (lambda B : ℝ) (k : ℕ) :
    Finset (BinProfile n q) := by
  classical
  exact Finset.univ.filter (fun x => B ≤ finiteBinLikelihood lambda k x ∧
    ∀ j ∈ Finset.Ioc k q, finiteBinLikelihood lambda j x < B)

noncomputable def finiteBinCrossing {n q : ℕ} (lambda B : ℝ) : Finset (BinProfile n q) := by
  classical
  exact (Finset.Icc 1 q).biUnion (finiteBinFirstCross (n := n) lambda B)

theorem finite_bin_first_cross_invariant {n q k : ℕ} (lambda B : ℝ) :
    ∀ x y : BinProfile n q, finiteBinReveal k x = finiteBinReveal k y →
      (x ∈ finiteBinFirstCross lambda B k ↔ y ∈ finiteBinFirstCross lambda B k) := by
  classical
  intro x y h
  have hAt : ∀ j, k ≤ j → finiteBinLikelihood lambda j x = finiteBinLikelihood lambda j y :=
    fun j hj => finite_bin_likelihood_reveal h hj lambda
  simp only [finiteBinFirstCross, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hBase, hHigh⟩
    constructor
    · rwa [← hAt k le_rfl]
    · intro j hj
      rw [← hAt j (Finset.mem_Ioc.mp hj).1.le]
      exact hHigh j hj
  · rintro ⟨hBase, hHigh⟩
    constructor
    · rwa [hAt k le_rfl]
    · intro j hj
      rw [hAt j (Finset.mem_Ioc.mp hj).1.le]
      exact hHigh j hj

theorem finite_bin_first_cross_disjoint {n q : ℕ} (lambda B : ℝ) :
    Set.PairwiseDisjoint (↑(Finset.Icc 1 q)) (finiteBinFirstCross (n := n) (q := q) lambda B) := by
  classical
  intro k hk j hj hkj
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hX := (Finset.mem_filter.mp hx).2
  have hY := (Finset.mem_filter.mp hy).2
  rcases lt_or_gt_of_ne hkj with hlt | hgt
  · have hLess := hX.2 j (Finset.mem_Ioc.mpr ⟨hlt, (Finset.mem_Icc.mp hj).2⟩)
    exact (not_le_of_gt hLess) hY.1
  · have hLess := hY.2 k (Finset.mem_Ioc.mpr ⟨hgt, (Finset.mem_Icc.mp hk).2⟩)
    exact (not_le_of_gt hLess) hX.1

theorem finite_bin_crossing_of_threshold {n q k : ℕ} (lambda B : ℝ) (x : BinProfile n q)
    (hk : k ∈ Finset.Icc 1 q) (hCross : B ≤ finiteBinLikelihood lambda k x) :
    x ∈ finiteBinCrossing lambda B := by
  classical
  let S := (Finset.Icc 1 q).filter (fun j => B ≤ finiteBinLikelihood lambda j x)
  have hS : S.Nonempty := ⟨k, Finset.mem_filter.mpr ⟨hk, hCross⟩⟩
  let j := S.max' hS
  have hj : j ∈ S := Finset.max'_mem S hS
  have hjRange := (Finset.mem_filter.mp hj).1
  have hjCross := (Finset.mem_filter.mp hj).2
  apply Finset.mem_biUnion.mpr
  refine ⟨j, hjRange, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hjCross, ?_⟩⟩
  intro l hl
  apply lt_of_not_ge
  intro hL
  have hjBounds := Finset.mem_Icc.mp hjRange
  have hlBounds := Finset.mem_Ioc.mp hl
  have hlRange : l ∈ Finset.Icc 1 q := Finset.mem_Icc.mpr
    ⟨by omega, hlBounds.2⟩
  have hlS : l ∈ S := Finset.mem_filter.mpr ⟨hlRange, hL⟩
  have hLe := Finset.le_max' S l hlS
  have hLt := (Finset.mem_Ioc.mp hl).1
  exact (not_le_of_gt hLt) hLe

/-- Direct finite Ville bound, with the revealed-atom identity derived from bins. -/
theorem finite_bin_likelihood_maximal {n q : ℕ} {lambda B : ℝ}
    (hq : 0 < q) (hL : 0 < lambda) (hB : 0 < B) :
    ((finiteBinCrossing (n := n) (q := q) lambda B).card : ℝ) / (q : ℝ) ^ n ≤ 1 / B := by
  classical
  let E := finiteBinCrossing (n := n) (q := q) lambda B
  let P := finiteBinFirstCross (n := n) (q := q) lambda B
  have hDis := finite_bin_first_cross_disjoint (n := n) (q := q) lambda B
  have hCompare : B * E.card ≤ ∑ x ∈ E, finiteBinLikelihood lambda 1 x := by
    calc
      B * E.card = ∑ _x ∈ E, B := by simp [mul_comm]
      _ = ∑ k ∈ Finset.Icc 1 q, ∑ _x ∈ P k, B :=
        Finset.sum_biUnion hDis
      _ ≤ ∑ k ∈ Finset.Icc 1 q, ∑ x ∈ P k, finiteBinLikelihood lambda k x := by
        apply Finset.sum_le_sum
        intro k hk
        apply Finset.sum_le_sum
        intro x hx
        exact (Finset.mem_filter.mp hx).2.1
      _ = ∑ k ∈ Finset.Icc 1 q, ∑ x ∈ P k, finiteBinLikelihood lambda 1 x := by
        apply Finset.sum_congr rfl
        intro k hk
        have hk' := Finset.mem_Icc.mp hk
        exact (finite_bin_invariant_terminal_sum (by omega : 0 < k) hk'.2 lambda (P k)
          (finite_bin_first_cross_invariant lambda B)).symm
      _ = ∑ x ∈ E, finiteBinLikelihood lambda 1 x := (Finset.sum_biUnion hDis).symm
  have hAll : (∑ x ∈ E, finiteBinLikelihood lambda 1 x) ≤
      ∑ x : BinProfile n q, finiteBinLikelihood lambda 1 x :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ E)
      (fun x _ _ => finite_bin_likelihood_nonneg hL x)
  rw [finite_bin_terminal_sum hq hL] at hAll
  have hBound := hCompare.trans hAll
  apply (div_le_div_iff₀ (pow_pos (by exact_mod_cast hq) n) hB).mpr
  simpa [E, mul_comm] using hBound

#print axioms finite_bin_likelihood_maximal

end QuantyraNullCone
