import QuantyraNullCone.DegreeMass

namespace QuantyraNullCone

def countRectangle (a b c d : ℝ) : Set DiamondPoint := Set.Ioc a b ×ˢ Set.Ioc c d

noncomputable def pointsIn {n : ℕ} (points : Fin n → DiamondPoint)
    (R : Set DiamondPoint) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => points i ∈ R)

noncomputable def retainedPointsIn {n : ℕ} (keep : Fin n → Prop)
    (points : Fin n → DiamondPoint) (R : Set DiamondPoint) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => keep i ∧ points i ∈ R)

def CoordinateError (s : ℝ) (p q : DiamondPoint) : Prop :=
  |p.1 - q.1| ≤ s ∧ |p.2 - q.2| ≤ s

theorem eroded_rectangle_recovered {a b c d s : ℝ} {p q : DiamondPoint}
    (he : CoordinateError s p q)
    (hq : q ∈ countRectangle (a + s) (b - s) (c + s) (d - s)) :
    p ∈ countRectangle a b c d := by
  have hx := abs_le.mp he.1
  have hy := abs_le.mp he.2
  rcases hq with ⟨⟨hqa, hqb⟩, ⟨hqc, hqd⟩⟩
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

theorem recovered_rectangle_expanded {a b c d s : ℝ} {p q : DiamondPoint}
    (he : CoordinateError s p q) (hp : p ∈ countRectangle a b c d) :
    q ∈ countRectangle (a - s) (b + s) (c - s) (d + s) := by
  have hx := abs_le.mp he.1
  have hy := abs_le.mp he.2
  rcases hp with ⟨⟨hpa, hpb⟩, ⟨hpc, hpd⟩⟩
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- All true points in the eroded cell are retained, so neither bound needs
the number of globally discarded points. -/
theorem retained_rectangle_count_sandwich {n : ℕ} {keep : Fin n → Prop}
    {recovered truth : Fin n → DiamondPoint} {a b c d s : ℝ}
    (hAcc : ∀ i, keep i → CoordinateError s (recovered i) (truth i))
    (hKeep : ∀ i, truth i ∈ countRectangle (a + s) (b - s) (c + s) (d - s) → keep i) :
    (pointsIn truth (countRectangle (a + s) (b - s) (c + s) (d - s))).card ≤
      (retainedPointsIn keep recovered (countRectangle a b c d)).card ∧
    (retainedPointsIn keep recovered (countRectangle a b c d)).card ≤
      (pointsIn truth (countRectangle (a - s) (b + s) (c - s) (d + s))).card := by
  classical
  constructor
  · apply Finset.card_le_card
    intro i hi
    have ht : truth i ∈ countRectangle (a + s) (b - s) (c + s) (d - s) :=
      (Finset.mem_filter.mp hi).2
    have hk := hKeep i ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hk,
      eroded_rectangle_recovered (hAcc i hk) ht⟩
  · apply Finset.card_le_card
    intro i hi
    have hk : keep i ∧ recovered i ∈ countRectangle a b c d :=
      (Finset.mem_filter.mp hi).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,
      recovered_rectangle_expanded (hAcc i hk.1) hk.2⟩

noncomputable def Realizer.rankPoint {n : ℕ} {R : Fin n → Fin n → Prop}
    (L : Realizer R) (i : Fin n) : DiamondPoint :=
  ((rank L.first i : ℝ) / n, (rank L.second i : ℝ) / n)

theorem Realizer.rankPoint_swap {n : ℕ} {R : Fin n → Fin n → Prop}
    (L : Realizer R) (i : Fin n) : L.swap.rankPoint i = transposePoint (L.rankPoint i) := rfl

/-- A single orientation works for every admissible rectangle simultaneously.
The only sample event is the already accepted geometric grid event. -/
theorem degree_filtered_cell_counts {n m : ℕ} {rho : DiamondPoint → ℝ}
    (hK : InDensityClass rho) (hn : 0 < n) (hm : 16 ≤ m) {r h : ℝ}
    (hr : 0 < r) (hh : 0 ≤ h) (hSquare : h ^ 2 = r)
    (hmr : (m : ℝ) * r = 1) (hnr : 1 / (n : ℝ) ≤ r)
    {sample : Fin n → DiamondPoint} (hg : SampleGood rho m r sample)
    (L : Realizer (Chronological (fun i => (sample i).1) (fun i => (sample i).2))) :
    ∃ swap : Bool, ∀ a b c d : ℝ,
      7 * h ≤ a + 32 * r → b - 32 * r ≤ 1 - 7 * h →
      7 * h ≤ c + 32 * r → d - 32 * r ≤ 1 - 7 * h →
      (pointsIn sample
        (countRectangle (a + 32 * r) (b - 32 * r) (c + 32 * r) (d - 32 * r))).card ≤
        (retainedPointsIn
          (DegreeRetained (Chronological (fun i => (sample i).1) (fun i => (sample i).2)) r)
          (L.aligned swap).rankPoint (countRectangle a b c d)).card ∧
      (retainedPointsIn
          (DegreeRetained (Chronological (fun i => (sample i).1) (fun i => (sample i).2)) r)
          (L.aligned swap).rankPoint (countRectangle a b c d)).card ≤
        (pointsIn sample
          (countRectangle (a - 32 * r) (b + 32 * r) (c - 32 * r) (d + 32 * r))).card := by
  obtain ⟨swap, hAcc⟩ := degree_retained_coordinate_rigidity hK hn hm hr hmr hg L
  refine ⟨swap, ?_⟩
  intro a b c d ha hb hc hd
  apply retained_rectangle_count_sandwich
  · exact hAcc
  · intro i hi
    apply deep_point_degree_retained hK hn hr hh hSquare hmr hnr hg i
    exact ⟨ha.trans hi.1.1.le, hi.1.2.trans hb,
      hc.trans hi.2.1.le, hi.2.2.trans hd⟩

#print axioms eroded_rectangle_recovered
#print axioms recovered_rectangle_expanded
#print axioms retained_rectangle_count_sandwich
#print axioms Realizer.rankPoint_swap
#print axioms degree_filtered_cell_counts

end QuantyraNullCone
