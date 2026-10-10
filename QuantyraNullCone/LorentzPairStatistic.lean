import QuantyraNullCone.LorentzPairConditioning
import QuantyraNullCone.PairBernsteinTail

namespace QuantyraNullCone
open MeasureTheory Set
open scoped BigOperators
noncomputable section

/-- Fraction of distinct pairs comparable in the full order code. -/
def orderPairMean {n : ℕ} (code : OrderCode n) : ℝ :=
  pairMean (fun i j => if code i j = true ∨ code j i = true then 1 else 0)

theorem orderPairMean_relabel {n : ℕ} (e : Equiv.Perm (Fin n)) (code : OrderCode n) :
    orderPairMean (relabelOrder e code) = orderPairMean code := by
  simpa only [orderPairMean,relabelOrder] using
    pairMean_permute e (fun i j => if code i j = true ∨ code j i = true then (1 : ℝ) else 0)

def unlabeledPairMean {n : ℕ} : UnlabeledOrderCode n → ℝ :=
  Quotient.lift orderPairMean (by
    intro a b h
    obtain ⟨e,rfl⟩ := h
    exact (orderPairMean_relabel e a).symm)

theorem unlabeledPairMean_forget {n : ℕ} (code : OrderCode n) :
    unlabeledPairMean (forgetOrderLabels code) = orderPairMean code := rfl

theorem unlabeledPairMean_measurable (n : ℕ) :
    Measurable (unlabeledPairMean (n := n)) := measurable_of_countable _

theorem sampled_order_pair_mean3 {n : ℕ} (x : Fin n → LorentzPoint3) :
    orderPairMean (sampledOrder3 x) =
      pairIndicatorMean {z : LorentzPoint3 × LorentzPoint3 |
        chronological3 z.1 z.2 ∨ chronological3 z.2 z.1} x := by
  classical
  unfold orderPairMean pairIndicatorMean pairMean
  apply Finset.expect_congr rfl
  intro p _
  simp [sampledOrder3,Set.indicator_apply]

def timePairVarianceBound3 : ℝ := 104849697629/563625562500

theorem time_comparable_probability_range3 {theta : ℝ} (ht : theta ∈ Icc (0 : ℝ) (1/2)) :
    8/35 ≤ timeComparableProbability3 theta ∧ timeComparableProbability3 theta ≤ 185489/750750 := by
  constructor
  · have h := time_comparable_probability_strictMono3.monotoneOn
      (show (0 : ℝ) ∈ Icc (0 : ℝ) (1/2) by norm_num) ht ht.1
    norm_num [timeComparableProbability3,timeOrderedPairProbability3] at h ⊢
    exact h
  · have h := time_comparable_probability_strictMono3.monotoneOn ht
      (show (1/2 : ℝ) ∈ Icc (0 : ℝ) (1/2) by norm_num) ht.2
    norm_num [timeComparableProbability3,timeOrderedPairProbability3] at h ⊢
    exact h

theorem time_pair_variance_bound3 {theta : ℝ} (ht : theta ∈ Icc (0 : ℝ) (1/2)) :
    timeComparableProbability3 theta*(1-timeComparableProbability3 theta) ≤ timePairVarianceBound3 := by
  have h := time_comparable_probability_range3 ht
  have hb : 0 ≤ 1-185489/750750-timeComparableProbability3 theta := by linarith [h.2]
  have hm := mul_nonneg (sub_nonneg.mpr h.2) hb
  unfold timePairVarianceBound3
  nlinarith only [hm]

theorem time_pair_sample_bernstein3 {theta r : ℝ} (ht : theta ∈ Icc (0 : ℝ) (1/2))
    {n : ℕ} (hn : 2 ≤ n) (hr : 0 < r) :
    (sampleMeasure3 (timeQuadraticDensity3 theta) n).real
      {x | r ≤ |orderPairMean (sampledOrder3 x)-timeComparableProbability3 theta|} ≤
      2*Real.exp (-((n/2 : ℕ) : ℝ)*r^2/(2*(timePairVarianceBound3+r/3))) := by
  letI := (time_quadratic_density_class3 ht).isProbabilityMeasure
  have h := pairIndicator_bernstein_tail (μ := densityMeasure3 (timeQuadraticDensity3 theta))
    measurableSet_comparable_pairs3 hn (v := timePairVarianceBound3)
    (by norm_num [timePairVarianceBound3]) hr
    (by rw [time_quadratic_comparable_pair_probability3 ht]; exact time_pair_variance_bound3 ht)
  simpa only [sampled_order_pair_mean3,time_quadratic_comparable_pair_probability3 ht] using h

/-- Finite-confidence bound for an observable of the original unlabeled order alone. -/
theorem time_pair_unlabeled_bernstein3 {theta r : ℝ} (ht : theta ∈ Icc (0 : ℝ) (1/2))
    {n : ℕ} (hn : 2 ≤ n) (hr : 0 < r) :
    (unlabeledOrderLaw3 (timeQuadraticDensity3 theta) n).real
      {code | r ≤ |unlabeledPairMean code-timeComparableProbability3 theta|} ≤
      2*Real.exp (-((n/2 : ℕ) : ℝ)*r^2/(2*(timePairVarianceBound3+r/3))) := by
  rw [Measure.real,unlabeledOrderLaw3,Measure.map_apply (measurable_of_countable _)
    (measurableSet_le measurable_const (((unlabeledPairMean_measurable n).sub_const _).abs)),
    orderLaw3,Measure.map_apply (sampledOrder3_measurable n) (by measurability)]
  exact time_pair_sample_bernstein3 ht hn hr

#print axioms orderPairMean_relabel
#print axioms sampled_order_pair_mean3
#print axioms time_pair_variance_bound3
#print axioms time_pair_sample_bernstein3
#print axioms time_pair_unlabeled_bernstein3
end
end QuantyraNullCone
