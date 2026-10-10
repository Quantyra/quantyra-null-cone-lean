import QuantyraNullCone.LorentzPairStatistic

namespace QuantyraNullCone
open MeasureTheory Set
noncomputable section
set_option maxHeartbeats 1000000

def timePairClip3 (u : ℝ) : ℝ := max (8/35) (min (185489/750750) u)

theorem time_pair_clip_range3 (u : ℝ) : timePairClip3 u ∈ Icc (8/35 : ℝ) (185489/750750) := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

theorem time_pair_clip_error3 {p : ℝ} (hp : p ∈ Icc (8/35 : ℝ) (185489/750750)) (u : ℝ) :
    |timePairClip3 u-p| ≤ |u-p| := by
  unfold timePairClip3
  by_cases hl : u ≤ 8/35
  · rw [min_eq_right (by linarith [hp.1,hp.2]),max_eq_left hl,
      abs_of_nonpos (by linarith [hp.1]),abs_of_nonpos (by linarith [hp.1])]
    linarith
  · by_cases hu : 185489/750750 ≤ u
    · rw [min_eq_left hu,max_eq_right (by norm_num),
        abs_of_nonneg (by linarith [hp.2]),abs_of_nonneg (by linarith [hp.2])]
      linarith
    · rw [min_eq_right (le_of_not_ge hu),max_eq_right (le_of_not_ge hl)]

theorem time_pair_clipped_inverse_exists3 (u : ℝ) :
    ∃ theta ∈ Icc (0 : ℝ) (1/2), timeComparableProbability3 theta = timePairClip3 u := by
  have hc : Continuous timeComparableProbability3 := by
    unfold timeComparableProbability3 timeOrderedPairProbability3
    fun_prop
  have h := intermediate_value_Icc (show (0 : ℝ) ≤ 1/2 by norm_num) hc.continuousOn
  have hr : timePairClip3 u ∈ Icc (timeComparableProbability3 0) (timeComparableProbability3 (1/2)) := by
    norm_num [timeComparableProbability3,timeOrderedPairProbability3]
    exact time_pair_clip_range3 u
  exact h hr

def timePairInverse3 (u : ℝ) : ℝ := Classical.choose (time_pair_clipped_inverse_exists3 u)

theorem time_pair_inverse_mem3 (u : ℝ) : timePairInverse3 u ∈ Icc (0 : ℝ) (1/2) :=
  (Classical.choose_spec (time_pair_clipped_inverse_exists3 u)).1

theorem time_pair_inverse_eq3 (u : ℝ) : timeComparableProbability3 (timePairInverse3 u) = timePairClip3 u :=
  (Classical.choose_spec (time_pair_clipped_inverse_exists3 u)).2

def timePairEstimator3 {n : ℕ} (code : UnlabeledOrderCode n) : ℝ :=
  timePairInverse3 (unlabeledPairMean code)

theorem time_pair_estimator_mem3 {n : ℕ} (code : UnlabeledOrderCode n) :
    timePairEstimator3 code ∈ Icc (0 : ℝ) (1/2) := time_pair_inverse_mem3 _

theorem time_pair_estimator_measurable3 (n : ℕ) :
    Measurable (timePairEstimator3 (n := n)) := measurable_of_countable _

/-- Pointwise transport from the observable error to the original geometric quotient loss. -/
theorem time_pair_estimator_geometric_error3 {theta : ℝ} (ht : theta ∈ Icc (0 : ℝ) (1/2))
    {n : ℕ} (code : UnlabeledOrderCode n) :
    geometricDistortion3 (time_quadratic_density_class3 (time_pair_estimator_mem3 code))
      (time_quadratic_density_class3 ht) ≤
      (225225/54952)*|unlabeledPairMean code-timeComparableProbability3 theta| := by
  have h := time_quadratic_geometric_pair_inverse3 (time_pair_estimator_mem3 code) ht
  have he : timeComparableProbability3 (timePairEstimator3 code) = timePairClip3 (unlabeledPairMean code) :=
    time_pair_inverse_eq3 _
  rw [he] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (time_pair_clip_error3 (time_comparable_probability_range3 ht) _)
    (by norm_num : (0 : ℝ) ≤ 225225/54952))

/-- Geometric confidence from the original unlabeled order law, with explicit tail radius. -/
theorem time_pair_estimator_geometric_tail3 {theta r : ℝ} (ht : theta ∈ Icc (0 : ℝ) (1/2))
    {n : ℕ} (hn : 2 ≤ n) (hr : 0 < r) :
    (unlabeledOrderLaw3 (timeQuadraticDensity3 theta) n).real
      {code | (225225/54952)*r <
        geometricDistortion3 (time_quadratic_density_class3 (time_pair_estimator_mem3 code))
          (time_quadratic_density_class3 ht)} ≤
      2*Real.exp (-((n/2 : ℕ) : ℝ)*r^2/(2*(timePairVarianceBound3+r/3))) := by
  letI := (time_quadratic_density_class3 ht).isProbabilityMeasure
  letI : IsFiniteMeasure (unlabeledOrderLaw3 (timeQuadraticDensity3 theta) n) := by
    unfold unlabeledOrderLaw3 orderLaw3 sampleMeasure3
    infer_instance
  have hsub : {code : UnlabeledOrderCode n | (225225/54952)*r <
      geometricDistortion3 (time_quadratic_density_class3 (time_pair_estimator_mem3 code))
        (time_quadratic_density_class3 ht)} ⊆
      {code | r ≤ |unlabeledPairMean code-timeComparableProbability3 theta|} := by
    intro code hc
    have hg := time_pair_estimator_geometric_error3 ht code
    change (225225/54952)*r < _ at hc
    change r ≤ _
    linarith
  exact (measureReal_mono hsub).trans (time_pair_unlabeled_bernstein3 ht hn hr)

theorem time_pair_midpoint_geometric_bound3 {theta : ℝ} (ht : theta ∈ Icc (0 : ℝ) (1/2)) :
    geometricDistortion3 (time_quadratic_density_class3 (by norm_num : (1/4 : ℝ) ∈ Icc (0 : ℝ) (1/2)))
      (time_quadratic_density_class3 ht) ≤ 3/80 := by
  have h := time_quadratic_geometric_bound3
    (show (1/4 : ℝ) ∈ Icc (0 : ℝ) (1/2) by norm_num) ht
  have hb : |(1/4 : ℝ)-theta| ≤ 1/4 := abs_le.mpr ⟨by linarith [ht.2],by linarith [ht.1]⟩
  linarith

#print axioms time_pair_clipped_inverse_exists3
#print axioms time_pair_estimator_geometric_error3
#print axioms time_pair_estimator_geometric_tail3
#print axioms time_pair_midpoint_geometric_bound3
end
end QuantyraNullCone
