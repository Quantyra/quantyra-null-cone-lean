import QuantyraNullCone.DKWFiniteCDF
import Mathlib.Data.Fin.Rev

namespace QuantyraNullCone

def finiteBinReflect {n q : ℕ} (x : BinProfile n q) : BinProfile n q :=
  fun i => Fin.rev (x i)

theorem finite_bin_reflect_injective {n q : ℕ} :
    Function.Injective (finiteBinReflect : BinProfile n q → BinProfile n q) := by
  intro x y h
  funext i
  exact Fin.rev_injective (congrFun h i)

theorem finite_bin_reflect_count {n q k : ℕ} (hkq : k ≤ q) (x : BinProfile n q) :
    finiteBinCount x k + finiteBinCount (finiteBinReflect x) (q - k) = n := by
  have hFilter : Finset.univ.filter (fun i => ((finiteBinReflect x) i).val < q - k) =
      Finset.univ.filter (fun i => ¬ (x i).val < k) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, finiteBinReflect, Fin.val_rev]
    have hi := (x i).isLt
    omega
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun i : Fin n => (x i).val < k)
  rw [← hFilter] at h
  simpa [finiteBinCount] using h

theorem finite_bin_reflect_CDF {n q k : ℕ} (hn : 0 < n) (hq : 0 < q)
    (hkq : k ≤ q) (x : BinProfile n q) :
    finiteBinCDF (finiteBinReflect x) (q - k) - ((q - k : ℕ) : ℝ) / q =
      (k : ℝ) / q - finiteBinCDF x k := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hCount : (finiteBinCount x k : ℝ) +
      (finiteBinCount (finiteBinReflect x) (q - k) : ℝ) = n := by
    exact_mod_cast finite_bin_reflect_count hkq x
  have hComplement : (finiteBinCount (finiteBinReflect x) (q - k) : ℝ) =
      (n : ℝ) - finiteBinCount x k := by linarith only [hCount]
  unfold finiteBinCDF
  rw [hComplement, Nat.cast_sub hkq]
  field_simp [hnR, hqR]
  ring

noncomputable def finiteBinLowerDeviation {n q : ℕ} (e : ℝ) : Finset (BinProfile n q) := by
  classical
  exact Finset.univ.filter (fun x => ∃ k ∈ Finset.Icc 0 q,
    e < (k : ℝ) / q - finiteBinCDF x k)

noncomputable def finiteBinAbsDeviation {n q : ℕ} (e : ℝ) : Finset (BinProfile n q) := by
  classical
  exact Finset.univ.filter (fun x => ∃ k ∈ Finset.Icc 0 q,
    e < |finiteBinCDF x k - (k : ℝ) / q|)

theorem finite_bin_lower_card_le_upper {n q : ℕ} (hn : 0 < n) (hq : 0 < q) (e : ℝ) :
    (finiteBinLowerDeviation (n := n) (q := q) e).card ≤
      (finiteBinUpperDeviation (n := n) (q := q) e).card := by
  classical
  have hSub : (finiteBinLowerDeviation (n := n) (q := q) e).image finiteBinReflect ⊆
      finiteBinUpperDeviation e := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    simp only [finiteBinLowerDeviation, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨k, hk, hBad⟩ := hx
    simp only [finiteBinUpperDeviation, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨q - k, Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.sub_le _ _⟩, ?_⟩
    rw [finite_bin_reflect_CDF hn hq (Finset.mem_Icc.mp hk).2]
    exact hBad
  calc
    (finiteBinLowerDeviation (n := n) (q := q) e).card =
        ((finiteBinLowerDeviation (n := n) (q := q) e).image finiteBinReflect).card :=
      (Finset.card_image_of_injective _ finite_bin_reflect_injective).symm
    _ ≤ (finiteBinUpperDeviation e).card := Finset.card_le_card hSub

theorem finite_bin_abs_card_le_sum {n q : ℕ} (e : ℝ) :
    (finiteBinAbsDeviation (n := n) (q := q) e).card ≤
      (finiteBinUpperDeviation (n := n) (q := q) e).card +
        (finiteBinLowerDeviation (n := n) (q := q) e).card := by
  classical
  have hSub : finiteBinAbsDeviation (n := n) (q := q) e ⊆
      finiteBinUpperDeviation e ∪ finiteBinLowerDeviation e := by
    intro x hx
    simp only [finiteBinAbsDeviation, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨k, hk, hBad⟩ := hx
    by_cases hSign : 0 ≤ finiteBinCDF x k - (k : ℝ) / q
    · rw [abs_of_nonneg hSign] at hBad
      apply Finset.mem_union.mpr
      apply Or.inl
      simp only [finiteBinUpperDeviation, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨k, hk, hBad⟩
    · rw [abs_of_nonpos (le_of_not_ge hSign)] at hBad
      apply Finset.mem_union.mpr
      apply Or.inr
      simp only [finiteBinLowerDeviation, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨k, hk, ?_⟩
      linarith only [hBad]
  exact (Finset.card_le_card hSub).trans (Finset.card_union_le _ _)

theorem finite_bin_two_sided_DKW_small {n q : ℕ} {e : ℝ} (hn : 0 < n) (hq : 0 < q)
    (he : 0 < e) (he1 : e < 1) :
    ((finiteBinAbsDeviation (n := n) (q := q) e).card : ℝ) / (q : ℝ) ^ n ≤
      2 * Real.exp (-2 * (n : ℝ) * e ^ 2) := by
  have hCard : ((finiteBinAbsDeviation (n := n) (q := q) e).card : ℝ) ≤
      (finiteBinUpperDeviation (n := n) (q := q) e).card +
        (finiteBinLowerDeviation (n := n) (q := q) e).card := by
    exact_mod_cast finite_bin_abs_card_le_sum (n := n) (q := q) e
  have hNegCard : ((finiteBinLowerDeviation (n := n) (q := q) e).card : ℝ) ≤
      (finiteBinUpperDeviation (n := n) (q := q) e).card := by
    exact_mod_cast finite_bin_lower_card_le_upper hn hq e
  have hPos := finite_bin_upper_DKW hn hq he he1
  have hNeg := (div_le_div_of_nonneg_right hNegCard
    (show 0 ≤ (q : ℝ) ^ n by positivity)).trans hPos
  have hRatio := div_le_div_of_nonneg_right hCard (show 0 ≤ (q : ℝ) ^ n by positivity)
  rw [add_div] at hRatio
  have h := hRatio.trans (add_le_add hPos hNeg)
  linarith only [h]

theorem finite_bin_abs_deviation_empty {n q : ℕ} {e : ℝ} (hn : 0 < n) (hq : 0 < q)
    (he : 1 ≤ e) : finiteBinAbsDeviation (n := n) (q := q) e = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  simp only [finiteBinAbsDeviation, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  obtain ⟨k, hk, hBad⟩ := hx
  have hCDF := finite_bin_CDF_bounds (k := k) hn x
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have ht0 : 0 ≤ (k : ℝ) / q := by positivity
  have ht1 : (k : ℝ) / q ≤ 1 := by
    apply (div_le_one hqR).mpr
    exact_mod_cast (Finset.mem_Icc.mp hk).2
  have hAbs : |finiteBinCDF x k - (k : ℝ) / q| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith only [hCDF.1, hCDF.2, ht0, ht1]
  exact (not_lt_of_ge (hAbs.trans he)) hBad

/-- Sharp two-sided finite-grid DKW for every nonnegative tolerance.
The left side is the exact iid uniform profile probability, not an n-fold union bound. -/
theorem finite_bin_two_sided_DKW {n q : ℕ} {e : ℝ} (hn : 0 < n) (hq : 0 < q)
    (he : 0 ≤ e) :
    ((finiteBinAbsDeviation (n := n) (q := q) e).card : ℝ) / (q : ℝ) ^ n ≤
      2 * Real.exp (-2 * (n : ℝ) * e ^ 2) := by
  by_cases he1 : e < 1
  · by_cases he0 : e = 0
    · subst e
      have hNat := Finset.card_le_univ (finiteBinAbsDeviation (n := n) (q := q) 0)
      have hCard : ((finiteBinAbsDeviation (n := n) (q := q) 0).card : ℝ) ≤ (q : ℝ) ^ n := by
        exact_mod_cast (show (finiteBinAbsDeviation (n := n) (q := q) 0).card ≤ q ^ n by
          simpa [Fintype.card_pi_const] using hNat)
      have hRatio := (div_le_one (pow_pos (by exact_mod_cast hq) n)).mpr hCard
      norm_num
      linarith only [hRatio]
    · exact finite_bin_two_sided_DKW_small hn hq (lt_of_le_of_ne he (Ne.symm he0)) he1
  · rw [finite_bin_abs_deviation_empty hn hq (le_of_not_gt he1)]
    simp only [Finset.card_empty, Nat.cast_zero, zero_div]
    positivity

#print axioms finite_bin_reflect_CDF
#print axioms finite_bin_two_sided_DKW

end QuantyraNullCone
