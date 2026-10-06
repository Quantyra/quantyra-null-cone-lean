import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import QuantyraNullCone.Realizer

namespace QuantyraNullCone

def Chronological {α : Type} (u v : α → ℝ) (x y : α) : Prop :=
  u x < u y ∧ v x < v y

def Interior {α : Type} (u v : α → ℝ) (r : ℝ) (x : α) : Prop :=
  4 * r ≤ u x ∧ u x ≤ 1 - 4 * r ∧ 4 * r ≤ v x ∧ v x ≤ 1 - 4 * r

def GridOccupied {α : Type} (u v : α → ℝ) (m : ℕ) (r : ℝ) : Prop :=
  ∀ j k : ℕ, j < m → k < m → ∃ z,
    (j : ℝ) * r < u z ∧ u z < ((j : ℝ) + 1) * r ∧
    (k : ℝ) * r < v z ∧ v z < ((k : ℝ) + 1) * r

theorem crossed_incomparable {α : Type} {u v : α → ℝ} {x y : α}
    (hu : u x < u y) (hv : v y < v x) : Incomparable (Chronological u v) x y := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    subst y
    exact lt_irrefl _ hu
  · intro h
    exact (not_lt_of_ge hv.le) h.2
  · intro h
    exact (not_lt_of_ge hu.le) h.1

/-- A gap of three cells contains a full open grid interval. -/
theorem grid_interval {m : ℕ} {r a b : ℝ} (hr : 0 < r)
    (hmr : (m : ℝ) * r = 1) (ha : 0 ≤ a) (hb : b ≤ 1)
    (hgap : 3 * r ≤ b - a) :
    ∃ k : ℕ, k < m ∧ a < (k : ℝ) * r ∧ ((k : ℝ) + 1) * r < b := by
  let k := Nat.floor (a / r) + 1
  have hlo : (Nat.floor (a / r) : ℝ) * r ≤ a :=
    (le_div_iff₀ hr).mp (Nat.floor_le (div_nonneg ha hr.le))
  have hhi : a < ((Nat.floor (a / r) : ℝ) + 1) * r :=
    (div_lt_iff₀ hr).mp (Nat.lt_floor_add_one (a / r))
  have hkcast : (k : ℝ) = (Nat.floor (a / r) : ℝ) + 1 := by
    simp [k]
  have hkl : a < (k : ℝ) * r := by rw [hkcast]; exact hhi
  have hku : ((k : ℝ) + 1) * r < b := by rw [hkcast]; nlinarith
  have hkreal : (k : ℝ) < (m : ℝ) := by
    have hmul : (k : ℝ) * r < (m : ℝ) * r := by nlinarith
    exact lt_of_mul_lt_mul_right hmul hr.le
  exact ⟨k, by exact_mod_cast hkreal, hkl, hku⟩

/-- Occupancy supplies actual geometric witnesses, without a prime-graph assumption. -/
theorem occupied_grid_global_orientation {α : Type} {u v : α → ℝ}
    {m : ℕ} {r : ℝ} (hm : 16 ≤ m) (hr : 0 < r)
    (hmr : (m : ℝ) * r = 1) (occ : GridOccupied u v m r)
    (L : Realizer (Chronological u v)) :
    (∀ x y, Interior u v r x → Interior u v r y →
      u x < u y → 3 * r ≤ v x - v y → L.opposite x y) ∨
    (∀ x y, Interior u v r x → Interior u v r y →
      u x < u y → 3 * r ≤ v x - v y → L.opposite y x) := by
  have hmreal : (16 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hsmall : 16 * r ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hmreal hr.le
    nlinarith
  have cm1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  have cm2 : ((m - 2 : ℕ) : ℝ) = (m : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  have cm3 : ((m - 3 : ℕ) : ℝ) = (m : ℝ) - 3 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  obtain ⟨A, au0, au1, av0, av1⟩ := occ 1 (m - 2) (by omega) (by omega)
  obtain ⟨B, bu0, bu1, bv0, bv1⟩ := occ (m - 2) 1 (by omega) (by omega)
  obtain ⟨W, wu0, wu1, wv0, wv1⟩ := occ (m - 1) (m - 3) (by omega) (by omega)
  simp only [Nat.cast_one, cm1, cm2, cm3] at au0 au1 av0 av1 bu0 bu1 bv0 bv1 wu0 wu1 wv0 wv1
  have Au0 : r < u A := by nlinarith
  have Au1 : u A < 2 * r := by nlinarith
  have Av0 : 1 - 2 * r < v A := by nlinarith
  have Bu0 : 1 - 2 * r < u B := by nlinarith
  have Bu1 : u B < 1 - r := by nlinarith
  have Bv1 : v B < 2 * r := by nlinarith
  have Wu0 : 1 - r < u W := by nlinarith
  have Wv0 : 1 - 3 * r < v W := by nlinarith
  have Wv1 : v W < 1 - 2 * r := by nlinarith
  have hAB : Incomparable (Chronological u v) A B :=
    crossed_incomparable (by linarith) (by linarith)
  have hAW : Incomparable (Chronological u v) A W :=
    crossed_incomparable (by linarith) (by linarith)
  have hBW : Chronological u v B W := ⟨by linarith, by linarith⟩
  let E := fun x y => Interior u v r x ∧ Interior u v r y ∧
    u x < u y ∧ 3 * r ≤ v x - v y
  have witnesses : ∀ x y, E x y →
      Incomparable (Chronological u v) x y ∧
      Incomparable (Chronological u v) A y ∧ Chronological u v y W ∧
      ∃ z, Incomparable (Chronological u v) z y ∧
        Chronological u v z x ∧ Chronological u v z A := by
    intro x y hE
    rcases hE with ⟨hx, hy, huxy, hgap⟩
    obtain ⟨k, hkm, hkl, hku⟩ := grid_interval hr hmr
      (by linarith [hy.2.2.1]) (by linarith [hx.2.2.2]) hgap
    obtain ⟨z, zu0, zu1, zv0, zv1⟩ := occ 0 k (by omega) hkm
    simp only [Nat.cast_zero, zero_mul, zero_add, one_mul] at zu0 zu1
    have hzv0 : v y < v z := lt_trans hkl zv0
    have hzv1 : v z < v x := lt_trans zv1 hku
    refine ⟨crossed_incomparable huxy (by linarith),
      crossed_incomparable (by linarith [hy.1]) (by linarith [hy.2.2.2]),
      ⟨by linarith [hy.2.1], by linarith [hy.2.2.2]⟩, z,
      crossed_incomparable (by linarith [hy.1]) hzv0,
      ⟨by linarith [hx.1], hzv1⟩,
      ⟨by linarith, by linarith [hx.2.2.2]⟩⟩
  rcases L.global_orientation E hAB hAW hBW witnesses with h | h
  · left
    intro x y hx hy hu hv
    exact h x y ⟨hx, hy, hu, hv⟩
  · right
    intro x y hx hy hu hv
    exact h x y ⟨hx, hy, hu, hv⟩

end QuantyraNullCone

#print axioms QuantyraNullCone.occupied_grid_global_orientation
