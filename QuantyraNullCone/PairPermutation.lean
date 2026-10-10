import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Fintype.Perm
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace QuantyraNullCone
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000

abbrev DistinctPair (ι : Type*) := {p : ι × ι // p.1 ≠ p.2}

def permuteDistinctPair {ι : Type*} (e : Equiv.Perm ι) : DistinctPair ι ≃ DistinctPair ι where
  toFun p := ⟨(e p.val.1,e p.val.2),fun h => p.property (e.injective h)⟩
  invFun p := ⟨(e.symm p.val.1,e.symm p.val.2),fun h => p.property (e.symm.injective h)⟩
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp

def pairMean {ι : Type*} [Fintype ι] [DecidableEq ι] (h : ι → ι → ℝ) : ℝ :=
  𝔼 p : DistinctPair ι, h p.val.1 p.val.2

def pairBlockMean {ι : Type*} {m : ℕ} (a b : Fin m → ι) (h : ι → ι → ℝ) : ℝ :=
  𝔼 k : Fin m, h (a k) (b k)

theorem pairMean_permute {ι : Type*} [Fintype ι] [DecidableEq ι] (e : Equiv.Perm ι) (h : ι → ι → ℝ) :
    pairMean (fun i j => h (e i) (e j)) = pairMean h := by
  exact Fintype.expect_equiv (permuteDistinctPair e) _ _ (fun _ => rfl)

theorem exists_perm_distinct_pair {ι : Type*} (p q : DistinctPair ι) :
    ∃ e : Equiv.Perm ι, e p.val.1 = q.val.1 ∧ e p.val.2 = q.val.2 := by
  have hi (z : DistinctPair ι) : Function.Injective ![z.val.1,z.val.2] := by
    have hz := z.property
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  obtain ⟨e,he⟩ := Equiv.Perm.exists_extending_pair ![p.val.1,p.val.2] ![q.val.1,q.val.2]
    (hi p) (hi q)
  exact ⟨e,he 0,he 1⟩

theorem permutation_pair_expect_constant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → ι → ℝ) (p q : DistinctPair ι) :
    (𝔼 e : Equiv.Perm ι, h (e p.val.1) (e p.val.2)) =
      𝔼 e : Equiv.Perm ι, h (e q.val.1) (e q.val.2) := by
  classical
  obtain ⟨s,hs0,hs1⟩ := exists_perm_distinct_pair q p
  apply Fintype.expect_equiv (Equiv.mulRight s)
  intro e
  simp only [Equiv.coe_mulRight,Equiv.Perm.mul_apply,hs0,hs1]

/-- A uniform permutation sends any fixed distinct pair uniformly over all distinct pairs. -/
theorem permutation_pair_expect {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → ι → ℝ) (p : DistinctPair ι) :
    (𝔼 e : Equiv.Perm ι, h (e p.val.1) (e p.val.2)) = pairMean h := by
  classical
  letI : Nonempty (DistinctPair ι) := ⟨p⟩
  calc
    _ = 𝔼 q : DistinctPair ι, 𝔼 e : Equiv.Perm ι, h (e q.val.1) (e q.val.2) := by
      rw [← Fintype.expect_const (ι := DistinctPair ι)
        (𝔼 e : Equiv.Perm ι, h (e p.val.1) (e p.val.2))]
      apply Finset.expect_congr rfl
      intro q _
      exact permutation_pair_expect_constant h p q
    _ = 𝔼 e : Equiv.Perm ι, 𝔼 q : DistinctPair ι, h (e q.val.1) (e q.val.2) :=
      Finset.expect_comm _ _ _
    _ = 𝔼 _e : Equiv.Perm ι, pairMean h := by
      apply Finset.expect_congr rfl
      intro e _
      exact pairMean_permute e h
    _ = pairMean h := Fintype.expect_const _

/-- The permutation average of block averages equals the all-pairs statistic pointwise. -/
theorem pairMean_eq_permutation_blocks {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ} (hm : 0 < m)
    (a b : Fin m → ι) (hab : ∀ k, a k ≠ b k) (h : ι → ι → ℝ) :
    pairMean h = 𝔼 e : Equiv.Perm ι, pairBlockMean a b (fun i j => h (e i) (e j)) := by
  classical
  letI : NeZero m := ⟨hm.ne'⟩
  symm
  unfold pairBlockMean
  rw [Finset.expect_comm]
  have he (k : Fin m) : (𝔼 e : Equiv.Perm ι, h (e (a k)) (e (b k))) = pairMean h :=
    permutation_pair_expect h ⟨(a k,b k),hab k⟩
  simp_rw [he]
  exact Fintype.expect_const _

theorem exp_expect_le {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) :
    Real.exp (𝔼 i, f i) ≤ 𝔼 i, Real.exp (f i) := by
  have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hw : (∑ _i : ι, (Fintype.card ι : ℝ)⁻¹) = 1 := by
    simp [hc.ne']
  have he := convexOn_exp.map_sum_le (t := Finset.univ)
    (w := fun _ : ι => (Fintype.card ι : ℝ)⁻¹) (p := f)
    (fun _ _ => inv_nonneg.mpr hc.le) hw (fun _ _ => Set.mem_univ _)
  simpa only [Fintype.expect_eq_sum_div_card,smul_eq_mul,← Finset.mul_sum,
    div_eq_mul_inv,mul_comm,← Finset.sum_mul] using he

theorem pairMean_exp_le_permutation_blocks {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ} (hm : 0 < m)
    (a b : Fin m → ι) (hab : ∀ k, a k ≠ b k) (h : ι → ι → ℝ) (t c : ℝ) :
    Real.exp (t*(pairMean h-c)) ≤
      𝔼 e : Equiv.Perm ι, Real.exp (t*(pairBlockMean a b (fun i j => h (e i) (e j))-c)) := by
  classical
  rw [pairMean_eq_permutation_blocks hm a b hab h]
  have he : t*((𝔼 e : Equiv.Perm ι, pairBlockMean a b (fun i j => h (e i) (e j)))-c) =
      𝔼 e : Equiv.Perm ι, t*(pairBlockMean a b (fun i j => h (e i) (e j))-c) := by
    rw [← Finset.mul_expect,Finset.expect_sub_distrib,Fintype.expect_const]
  rw [he]
  exact exp_expect_le _

#print axioms permutation_pair_expect
#print axioms pairMean_eq_permutation_blocks
#print axioms pairMean_exp_le_permutation_blocks
end
end QuantyraNullCone
