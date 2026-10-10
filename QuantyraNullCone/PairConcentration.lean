import QuantyraNullCone.PairPermutation
import QuantyraNullCone.DisjointPairSample
import QuantyraNullCone.BernsteinSample

namespace QuantyraNullCone
open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000

def pairIndicatorMean {Ω : Type*} (S : Set (Ω × Ω)) {n : ℕ} (x : Fin n → Ω) : ℝ :=
  pairMean (fun i j => S.indicator (fun _ => (1 : ℝ)) (x i,x j))

def disjointPairs {Ω : Type*} {n : ℕ} (e : Equiv.Perm (Fin n)) (x : Fin n → Ω)
    (k : Fin (n/2)) : Ω × Ω := (x (e (disjointPairLeft n k)),x (e (disjointPairRight n k)))

theorem pairIndicatorMean_measurable {Ω : Type*} [MeasurableSpace Ω]
    {S : Set (Ω × Ω)} (hS : MeasurableSet S) (n : ℕ) :
    Measurable (pairIndicatorMean S (n := n)) := by
  unfold pairIndicatorMean pairMean
  simp only [Fintype.expect_eq_sum_div_card]
  exact (Finset.measurable_sum _ (fun p _ => (measurable_const.indicator hS).comp
    ((measurable_pi_apply p.val.1).prodMk (measurable_pi_apply p.val.2)))).div_const _

theorem pairBlockMean_scaled {ι : Type*} {m : ℕ} (a b : Fin m → ι)
    (h : ι → ι → ℝ) (p : ℝ) :
    (m : ℝ)*(pairBlockMean a b h-p) = ∑ k : Fin m, (h (a k) (b k)-p) := by
  rw [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    mul_sub]
  congr 1
  simpa only [Fintype.card_fin,pairBlockMean] using
    Fintype.card_mul_expect (fun k : Fin m => h (a k) (b k))

theorem pairIndicator_exp_le_blocks {Ω : Type*} {n : ℕ} (hn : 2 ≤ n)
    (S : Set (Ω × Ω)) (x : Fin n → Ω) (p t : ℝ) :
    Real.exp (t*((n/2 : ℕ) : ℝ)*(pairIndicatorMean S x-p)) ≤
      𝔼 e : Equiv.Perm (Fin n), Real.exp (t*centeredIndicatorSum S p (disjointPairs e x)) := by
  have hm : 0 < n/2 := by omega
  have h := pairMean_exp_le_permutation_blocks hm (disjointPairLeft n) (disjointPairRight n)
    (disjointPair_ne n) (fun i j => S.indicator (fun _ => (1 : ℝ)) (x i,x j))
    (t*(n/2 : ℕ)) p
  simpa only [mul_assoc,pairBlockMean_scaled,centeredIndicatorSum,disjointPairs,
    pairIndicatorMean] using h

theorem integral_fintype_expect {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} (f : ι → Ω → ℝ) (hf : ∀ i, Integrable (f i) μ) :
    (∫ x, 𝔼 i : ι, f i x ∂μ) = 𝔼 i : ι, ∫ x, f i x ∂μ := by
  simp only [Fintype.expect_eq_sum_div_card]
  rw [integral_div,integral_finsetSum _ (fun i _ => hf i)]

theorem integrable_fintype_expect {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} (f : ι → Ω → ℝ) (hf : ∀ i, Integrable (f i) μ) :
    Integrable (fun x => 𝔼 i : ι, f i x) μ := by
  simp only [Fintype.expect_eq_sum_div_card]
  exact (integrable_finsetSum _ (fun i _ => hf i)).div_const _

theorem pairIndicator_exp_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {S : Set (Ω × Ω)} (hS : MeasurableSet S)
    {n : ℕ} (hn : 2 ≤ n) (p t : ℝ) :
    Integrable (fun x : Fin n → Ω => Real.exp (t*((n/2 : ℕ) : ℝ)*(pairIndicatorMean S x-p)))
      (Measure.pi (fun _ : Fin n => μ)) := by
  have hi (e : Equiv.Perm (Fin n)) : Integrable
      (fun x : Fin n → Ω => Real.exp (t*centeredIndicatorSum S p (disjointPairs e x)))
      (Measure.pi (fun _ : Fin n => μ)) :=
    (permuted_disjoint_pairs_preserving μ n e).integrable_comp_of_integrable
      (iid_indicator_sum_exp_integrable hS p t (n/2))
  refine (integrable_fintype_expect _ hi).mono'
    (((pairIndicatorMean_measurable hS n).sub_const p).const_mul (t*(n/2 : ℕ))).exp.aestronglyMeasurable ?_
  exact ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact pairIndicator_exp_le_blocks hn S x p t)

/-- Dependence-aware exponential bound for the actual all-pairs statistic. -/
theorem pairIndicator_bernstein_mgf {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {S : Set (Ω × Ω)} (hS : MeasurableSet S)
    {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : |t| < 3) :
    mgf (fun x : Fin n → Ω => ((n/2 : ℕ) : ℝ)*(pairIndicatorMean S x-(μ.prod μ).real S))
      (Measure.pi (fun _ : Fin n => μ)) t ≤
      Real.exp (((n/2 : ℕ) : ℝ)*(μ.prod μ).real S*(1-(μ.prod μ).real S)*t^2/(2*(1-|t|/3))) := by
  let p := (μ.prod μ).real S
  let P := Measure.pi (fun _ : Fin n => μ)
  let Q := Measure.pi (fun _ : Fin (n/2) => μ.prod μ)
  let f (e : Equiv.Perm (Fin n)) (x : Fin n → Ω) :=
    Real.exp (t*centeredIndicatorSum S p (disjointPairs e x))
  have hi (e : Equiv.Perm (Fin n)) : Integrable (f e) P :=
    (permuted_disjoint_pairs_preserving μ n e).integrable_comp_of_integrable
      (iid_indicator_sum_exp_integrable hS p t (n/2))
  have he (e : Equiv.Perm (Fin n)) : (∫ x, f e x ∂P) =
      mgf (centeredIndicatorSum S p (m := n/2)) Q t := by
    have hp := permuted_disjoint_pairs_preserving μ n e
    have hmap := integral_map_of_stronglyMeasurable (μ := P) hp.measurable
      (((centeredIndicatorSum_measurable hS p (n/2)).const_mul t).exp.stronglyMeasurable)
    rw [hp.map_eq] at hmap
    exact hmap.symm
  calc
    _ ≤ ∫ x, 𝔼 e : Equiv.Perm (Fin n), f e x ∂P := by
      apply integral_mono_of_nonneg (ae_of_all _ (fun _ => (Real.exp_pos _).le))
        (integrable_fintype_expect f hi)
      exact ae_of_all _ (fun x => by
        simpa only [mul_assoc] using pairIndicator_exp_le_blocks hn S x p t)
    _ = mgf (centeredIndicatorSum S p (m := n/2)) Q t := by
      rw [integral_fintype_expect f hi]
      simp_rw [he]
      exact Fintype.expect_const _
    _ ≤ _ := iid_indicator_sum_bernstein_mgf hS (n/2) ht

#print axioms pairIndicator_exp_le_blocks
#print axioms pairIndicator_exp_integrable
#print axioms pairIndicator_bernstein_mgf
end
end QuantyraNullCone
