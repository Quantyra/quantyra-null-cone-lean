import Std

namespace QuantyraNullCone

structure StrictTotal {α : Type} (R : α → α → Prop) : Prop where
  irrefl : ∀ x, ¬ R x x
  trans : ∀ {x y z}, R x y → R y z → R x z
  total : ∀ {x y}, x ≠ y → R x y ∨ R y x

theorem StrictTotal.asymm {α : Type} {R : α → α → Prop}
    (h : StrictTotal R) {x y : α} (hxy : R x y) : ¬ R y x := by
  intro hyx
  exact h.irrefl x (h.trans hxy hyx)

def Incomparable {α : Type} (P : α → α → Prop) (x y : α) : Prop :=
  x ≠ y ∧ ¬ P x y ∧ ¬ P y x

def Comparable {α : Type} (P : α → α → Prop) (x y : α) : Prop :=
  P x y ∨ P y x

structure Realizer {α : Type} (P : α → α → Prop) where
  first : α → α → Prop
  second : α → α → Prop
  firstTotal : StrictTotal first
  secondTotal : StrictTotal second
  intersection : ∀ x y, P x y ↔ first x y ∧ second x y

def Realizer.opposite {α : Type} {P : α → α → Prop}
    (L : Realizer P) (x y : α) : Prop := L.first x y ∧ L.second y x

theorem Realizer.opposite_trans {α : Type} {P : α → α → Prop}
    (L : Realizer P) {x y z : α}
    (hxy : L.opposite x y) (hyz : L.opposite y z) : L.opposite x z :=
  ⟨L.firstTotal.trans hxy.1 hyz.1, L.secondTotal.trans hyz.2 hxy.2⟩

theorem Realizer.opposite_asymm {α : Type} {P : α → α → Prop}
    (L : Realizer P) {x y : α} (hxy : L.opposite x y) : ¬ L.opposite y x := by
  intro hyx
  exact L.firstTotal.asymm hxy.1 hyx.1

theorem Realizer.opposite_not_comparable {α : Type} {P : α → α → Prop}
    (L : Realizer P) {x y : α} (hxy : L.opposite x y) : ¬ Comparable P x y := by
  intro h
  rcases h with h | h
  · exact L.secondTotal.asymm hxy.2 ((L.intersection x y).mp h).2
  · exact L.firstTotal.asymm hxy.1 ((L.intersection y x).mp h).1

theorem Realizer.orient_incomparable {α : Type} {P : α → α → Prop}
    (L : Realizer P) {x y : α} (h : Incomparable P x y) :
    L.opposite x y ∨ L.opposite y x := by
  rcases L.firstTotal.total h.1 with hxy | hyx
  · left
    refine ⟨hxy, ?_⟩
    rcases L.secondTotal.total h.1 with sxy | syx
    · exact False.elim (h.2.1 ((L.intersection x y).mpr ⟨hxy, sxy⟩))
    · exact syx
  · right
    refine ⟨hyx, ?_⟩
    rcases L.secondTotal.total h.1 with sxy | syx
    · exact sxy
    · exact False.elim (h.2.2 ((L.intersection y x).mpr ⟨hyx, syx⟩))

theorem Realizer.forcing_at_right {α : Type} {P : α → α → Prop}
    (L : Realizer P) {x y z : α} (hxy : Incomparable P x y)
    (hzy : Incomparable P z y) (hxz : Comparable P x z) :
    L.opposite x y ↔ L.opposite z y := by
  constructor
  · intro qxy
    rcases L.orient_incomparable hzy with qzy | qyz
    · exact qzy
    · exact False.elim (L.opposite_not_comparable (L.opposite_trans qxy qyz) hxz)
  · intro qzy
    rcases L.orient_incomparable hxy with qxy | qyx
    · exact qxy
    · have hzx : Comparable P z x := hxz.elim Or.inr Or.inl
      exact False.elim (L.opposite_not_comparable (L.opposite_trans qzy qyx) hzx)

theorem Realizer.forcing_at_left {α : Type} {P : α → α → Prop}
    (L : Realizer P) {x y z : α} (hxy : Incomparable P x y)
    (hxz : Incomparable P x z) (hyz : Comparable P y z) :
    L.opposite x y ↔ L.opposite x z := by
  constructor
  · intro qxy
    rcases L.orient_incomparable hxz with qxz | qzx
    · exact qxz
    · have hzy : Comparable P z y := hyz.elim Or.inr Or.inl
      exact False.elim (L.opposite_not_comparable (L.opposite_trans qzx qxy) hzy)
  · intro qxz
    rcases L.orient_incomparable hxy with qxy | qyx
    · exact qxy
    · exact False.elim (L.opposite_not_comparable (L.opposite_trans qyx qxz) hyz)

/-- The five-edge orientation path used by the occupied-grid reconstruction. -/
theorem Realizer.five_edge_forcing {α : Type} {P : α → α → Prop}
    (L : Realizer P) {x y z A B W : α}
    (hxy : Incomparable P x y) (hzy : Incomparable P z y)
    (hAy : Incomparable P A y) (hAW : Incomparable P A W)
    (hAB : Incomparable P A B)
    (hzx : P z x) (hzA : P z A) (hyW : P y W) (hBW : P B W) :
    L.opposite x y ↔ L.opposite A B := by
  calc
    L.opposite x y ↔ L.opposite z y := L.forcing_at_right hxy hzy (Or.inr hzx)
    _ ↔ L.opposite A y := L.forcing_at_right hzy hAy (Or.inl hzA)
    _ ↔ L.opposite A W := L.forcing_at_left hAy hAW (Or.inl hyW)
    _ ↔ L.opposite A B := L.forcing_at_left hAW hAB (Or.inr hBW)

/-- A single anchor orientation governs the whole eligible relation.
The geometric existence of witnesses is a separate required component. -/
theorem Realizer.global_orientation {α : Type} {P : α → α → Prop}
    (L : Realizer P) (E : α → α → Prop) {A B W : α}
    (hAB : Incomparable P A B) (hAW : Incomparable P A W) (hBW : P B W)
    (witness : ∀ x y, E x y → Incomparable P x y ∧ Incomparable P A y ∧
      P y W ∧ ∃ z, Incomparable P z y ∧ P z x ∧ P z A) :
    (∀ x y, E x y → L.opposite x y) ∨
      (∀ x y, E x y → L.opposite y x) := by
  have linked : ∀ x y, E x y → (L.opposite x y ↔ L.opposite A B) := by
    intro x y hE
    rcases witness x y hE with ⟨hxy, hAy, hyW, z, hzy, hzx, hzA⟩
    exact L.five_edge_forcing hxy hzy hAy hAW hAB hzx hzA hyW hBW
  rcases L.orient_incomparable hAB with qAB | qBA
  · exact Or.inl (fun x y hE => (linked x y hE).mpr qAB)
  · right
    intro x y hE
    rcases L.orient_incomparable (witness x y hE).1 with qxy | qyx
    · exact False.elim (L.opposite_asymm qBA ((linked x y hE).mp qxy))
    · exact qyx

end QuantyraNullCone

#print axioms QuantyraNullCone.Realizer.five_edge_forcing
#print axioms QuantyraNullCone.Realizer.global_orientation
