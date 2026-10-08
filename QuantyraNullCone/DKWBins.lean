import QuantyraNullCone.DKWLikelihood
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.BigOperators

namespace QuantyraNullCone

abbrev BinProfile (n q : ℕ) := Fin n → Fin q

def finiteBinCount {n q : ℕ} (x : BinProfile n q) (k : ℕ) : ℕ :=
  (Finset.univ.filter (fun i => (x i).val < k)).card

def finiteBinReveal {n q : ℕ} (k : ℕ) (x : BinProfile n q) : Fin n → ℕ :=
  fun i => max ((x i).val + 1) k

def finiteBinAtom {n q : ℕ} (k : ℕ) (x : BinProfile n q) : Finset (BinProfile n q) :=
  Finset.univ.filter (fun y => finiteBinReveal k y = finiteBinReveal k x)

def finiteBinCoordinateSet {q : ℕ} (k : ℕ) (a : Fin q) : Finset (Fin q) :=
  if a.val < k then Finset.univ.filter (fun b => b.val < k) else {a}

def finiteBinWeight (lambda : ℝ) {q : ℕ} (b : Fin q) : ℝ :=
  if b.val = 0 then 1 + lambda * q else 1

noncomputable def finiteBinLikelihood (lambda : ℝ) {n q : ℕ}
    (k : ℕ) (x : BinProfile n q) : ℝ :=
  (1 + lambda * q / k) ^ finiteBinCount x k / (1 + lambda) ^ n

theorem finite_bin_coordinate_mem {q k : ℕ} (a b : Fin q) :
    max (b.val + 1) k = max (a.val + 1) k ↔ b ∈ finiteBinCoordinateSet k a := by
  by_cases ha : a.val < k
  · simp only [finiteBinCoordinateSet, ha, if_true, Finset.mem_filter, Finset.mem_univ,
      true_and]
    rw [max_eq_right (show a.val + 1 ≤ k by omega)]
    constructor
    · intro h
      have : b.val + 1 ≤ k := (le_max_left _ _).trans_eq h
      omega
    · intro hb
      exact max_eq_right (by omega)
  · simp only [finiteBinCoordinateSet, ha, if_false, Finset.mem_singleton]
    rw [max_eq_left (show k ≤ a.val + 1 by omega)]
    constructor
    · intro h
      by_cases hb : b.val + 1 ≤ k
      · rw [max_eq_right hb] at h
        omega
      · rw [max_eq_left (show k ≤ b.val + 1 by omega)] at h
        exact Fin.ext (by omega)
    · intro h
      subst b
      exact max_eq_left (by omega)

theorem finite_bin_atom_pi {n q k : ℕ} (x : BinProfile n q) :
    finiteBinAtom k x = Fintype.piFinset (fun i => finiteBinCoordinateSet k (x i)) := by
  ext y
  simp only [finiteBinAtom, Finset.mem_filter, Finset.mem_univ, true_and,
    Fintype.mem_piFinset, finiteBinReveal, funext_iff]
  exact forall_congr' (fun i => finite_bin_coordinate_mem (x i) (y i))

theorem finite_bin_coordinate_card {q k : ℕ} (hkq : k ≤ q) (a : Fin q) :
    (finiteBinCoordinateSet k a).card = if a.val < k then k else 1 := by
  by_cases ha : a.val < k
  · simp only [finiteBinCoordinateSet, ha, if_true]
    exact Fin.card_filter_val_lt.trans (Nat.min_eq_right hkq)
  · simp [finiteBinCoordinateSet, ha]

theorem finite_bin_atom_card {n q k : ℕ} (hkq : k ≤ q) (x : BinProfile n q) :
    (finiteBinAtom k x).card = k ^ finiteBinCount x k := by
  rw [finite_bin_atom_pi, Fintype.card_piFinset]
  simp_rw [finite_bin_coordinate_card hkq]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  rfl

theorem finite_bin_coordinate_weight_sum {q k : ℕ} (hk : 0 < k) (hkq : k ≤ q)
    (lambda : ℝ) (a : Fin q) :
    (∑ b ∈ finiteBinCoordinateSet k a, finiteBinWeight lambda b) =
      if a.val < k then (k : ℝ) + lambda * q else 1 := by
  classical
  by_cases ha : a.val < k
  · simp only [finiteBinCoordinateSet, ha, if_true]
    let S : Finset (Fin q) := Finset.univ.filter (fun b => b.val < k)
    let z : Fin q := ⟨0, hk.trans_le hkq⟩
    have hz : z ∈ S := by simp [S, z, hk]
    have hCard : S.card = k := Fin.card_filter_val_lt.trans (Nat.min_eq_right hkq)
    have hWeight : ∀ b : Fin q, finiteBinWeight lambda b =
        1 + if b = z then lambda * q else 0 := by
      intro b
      by_cases hb : b = z
      · subst b
        simp [finiteBinWeight, z]
      · have hb0 : b.val ≠ 0 := by
          intro h
          exact hb (Fin.ext h)
        simp [finiteBinWeight, hb, hb0]
    change (∑ b ∈ S, finiteBinWeight lambda b) = _
    simp_rw [hWeight]
    rw [Finset.sum_add_distrib]
    simp [hz, hCard]
  · have ha0 : a.val ≠ 0 := by omega
    simp [finiteBinCoordinateSet, ha, finiteBinWeight, ha0]

theorem finite_bin_terminal_product {n q : ℕ} (lambda : ℝ) (x : BinProfile n q) :
    finiteBinLikelihood lambda 1 x =
      (∏ i, finiteBinWeight lambda (x i)) / (1 + lambda) ^ n := by
  unfold finiteBinLikelihood
  simp only [Nat.cast_one, div_one]
  congr 1
  unfold finiteBinWeight finiteBinCount
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  simp only [Nat.lt_one_iff]

theorem finite_bin_atom_terminal_sum {n q k : ℕ} (hk : 0 < k) (hkq : k ≤ q)
    (lambda : ℝ) (x : BinProfile n q) :
    (∑ y ∈ finiteBinAtom k x, finiteBinLikelihood lambda 1 y) =
      ((k : ℝ) + lambda * q) ^ finiteBinCount x k / (1 + lambda) ^ n := by
  simp_rw [finite_bin_terminal_product]
  rw [← Finset.sum_div, finite_bin_atom_pi, ← Finset.prod_univ_sum]
  simp_rw [finite_bin_coordinate_weight_sum hk hkq]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  rfl

/-- Exact terminal conditional-mean identity on each actual revealed atom.
No martingale or concentration conclusion is an assumption. -/
theorem finite_bin_atom_likelihood_identity {n q k : ℕ} (hk : 0 < k) (hkq : k ≤ q)
    (lambda : ℝ) (x : BinProfile n q) :
    (∑ y ∈ finiteBinAtom k x, finiteBinLikelihood lambda 1 y) =
      (finiteBinAtom k x).card * finiteBinLikelihood lambda k x := by
  rw [finite_bin_atom_terminal_sum hk hkq, finite_bin_atom_card hkq]
  simp only [Nat.cast_pow, finiteBinLikelihood]
  have hkR : (k : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hk)
  have hFactor : (k : ℝ) * (1 + lambda * q / k) = (k : ℝ) + lambda * q := by
    calc
      (k : ℝ) * (1 + lambda * q / k) = (k : ℝ) + (lambda * q / k) * k := by ring
      _ = (k : ℝ) + lambda * q := by rw [div_mul_cancel₀ _ hkR]
  rw [← mul_div_assoc, ← mul_pow, hFactor]

theorem finite_bin_count_top {n q : ℕ} (x : BinProfile n q) : finiteBinCount x q = n := by
  unfold finiteBinCount
  rw [Finset.filter_eq_self.mpr (fun i _ => (x i).isLt)]
  simp

theorem finite_bin_atom_top {n q : ℕ} (x : BinProfile n q) :
    finiteBinAtom q x = Finset.univ := by
  ext y
  simp only [finiteBinAtom, Finset.mem_filter, Finset.mem_univ, true_and]
  apply iff_true_intro
  funext i
  simp only [finiteBinReveal]
  rw [max_eq_right (show (y i).val + 1 ≤ q by omega),
    max_eq_right (show (x i).val + 1 ≤ q by omega)]

theorem finite_bin_likelihood_top {n q : ℕ} {lambda : ℝ} (hq : 0 < q) (hL : 0 < lambda)
    (x : BinProfile n q) : finiteBinLikelihood lambda q x = 1 := by
  rw [finiteBinLikelihood, finite_bin_count_top, mul_div_cancel_right₀]
  · exact div_self (ne_of_gt (pow_pos (by linarith) n))
  · exact_mod_cast hq.ne'

theorem finite_bin_terminal_sum {n q : ℕ} {lambda : ℝ} (hq : 0 < q) (hL : 0 < lambda) :
    (∑ x : BinProfile n q, finiteBinLikelihood lambda 1 x) = (q : ℝ) ^ n := by
  let x : BinProfile n q := fun _ => ⟨0, hq⟩
  have h := finite_bin_atom_likelihood_identity hq le_rfl lambda x
  rw [finite_bin_atom_top, finite_bin_likelihood_top hq hL, mul_one] at h
  simpa [Fintype.card_pi_const] using h

#print axioms finite_bin_atom_likelihood_identity
#print axioms finite_bin_terminal_sum

end QuantyraNullCone
