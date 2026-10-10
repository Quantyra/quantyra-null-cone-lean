import QuantyraNullCone.LorentzPairEstimator
import QuantyraNullCone.BernsteinRadius

namespace QuantyraNullCone
open MeasureTheory Set
noncomputable section
set_option maxHeartbeats 1000000

def timePairStatisticalRadius3 (n : ℕ) (alpha : ℝ) : ℝ :=
  bernsteinRadius (n/2 : ℕ) timePairVarianceBound3 (Real.log (2/alpha))

def timePairRawGeometricRadius3 (n : ℕ) (alpha : ℝ) : ℝ :=
  (225225/54952)*timePairStatisticalRadius3 n alpha

/-- The estimator choice depends only on sample size and the requested confidence level. -/
def timePairConfidenceEstimator3 {n : ℕ} (alpha : ℝ) (code : UnlabeledOrderCode n) : ℝ :=
  if 2 ≤ n ∧ timePairRawGeometricRadius3 n alpha ≤ 3/80 then timePairEstimator3 code else 1/4

def timePairConfidenceRadius3 (n : ℕ) (alpha : ℝ) : ℝ :=
  if 2 ≤ n then min (3/80) (timePairRawGeometricRadius3 n alpha) else 3/80

theorem time_pair_confidence_estimator_mem3 {n : ℕ} (alpha : ℝ) (code : UnlabeledOrderCode n) :
    timePairConfidenceEstimator3 alpha code ∈ Icc (0 : ℝ) (1/2) := by
  unfold timePairConfidenceEstimator3
  split_ifs
  · exact time_pair_estimator_mem3 code
  · norm_num

theorem time_pair_confidence_estimator_measurable3 (n : ℕ) (alpha : ℝ) :
    Measurable (timePairConfidenceEstimator3 (n := n) alpha) := measurable_of_countable _

theorem time_pair_statistical_radius_pos3 {n : ℕ} (hn : 2 ≤ n) {alpha : ℝ}
    (ha0 : 0 < alpha) (ha1 : alpha < 1) : 0 < timePairStatisticalRadius3 n alpha := by
  apply bernsteinRadius_pos
  · have : 0 < n/2 := by omega
    exact_mod_cast this
  · norm_num [timePairVarianceBound3]
  · exact Real.log_pos ((lt_div_iff₀ ha0).mpr (by linarith))

theorem time_pair_raw_geometric_confidence3 {theta alpha : ℝ} (ht : theta ∈ Icc (0 : ℝ) (1/2))
    {n : ℕ} (hn : 2 ≤ n) (ha0 : 0 < alpha) (ha1 : alpha < 1) :
    (unlabeledOrderLaw3 (timeQuadraticDensity3 theta) n).real
      {code | timePairRawGeometricRadius3 n alpha <
        geometricDistortion3 (time_quadratic_density_class3 (time_pair_estimator_mem3 code))
          (time_quadratic_density_class3 ht)} ≤ alpha := by
  have h := time_pair_estimator_geometric_tail3 ht hn (time_pair_statistical_radius_pos3 hn ha0 ha1)
  have hm : (0 : ℝ) < (n/2 : ℕ) := by
    have : 0 < n/2 := by omega
    exact_mod_cast this
  have he := bernstein_log_radius_tail hm
    (show (0 : ℝ) < timePairVarianceBound3 by norm_num [timePairVarianceBound3]) ha0 ha1
  exact h.trans_eq he

/-- Complete finite-confidence theorem for the original geometric loss and unlabeled observation.
For n<2 the deterministic midpoint is used. For n>=2 the radius is the better of the
midpoint radius 3/80 and the dependence-aware statistical radius. -/
theorem time_pair_geometric_confidence3 {theta alpha : ℝ} (ht : theta ∈ Icc (0 : ℝ) (1/2))
    (n : ℕ) (ha0 : 0 < alpha) (ha1 : alpha < 1) :
    (unlabeledOrderLaw3 (timeQuadraticDensity3 theta) n).real
      {code | timePairConfidenceRadius3 n alpha <
        geometricDistortion3 (time_quadratic_density_class3 (time_pair_confidence_estimator_mem3 alpha code))
          (time_quadratic_density_class3 ht)} ≤ alpha := by
  by_cases hchoose : 2 ≤ n ∧ timePairRawGeometricRadius3 n alpha ≤ 3/80
  · simpa only [timePairConfidenceRadius3,if_pos hchoose.1,min_eq_right hchoose.2,
      timePairConfidenceEstimator3,if_pos hchoose] using
      time_pair_raw_geometric_confidence3 ht hchoose.1 ha0 ha1
  · have hr : timePairConfidenceRadius3 n alpha = 3/80 := by
      unfold timePairConfidenceRadius3
      by_cases hn : 2 ≤ n
      · rw [if_pos hn,min_eq_left (le_of_not_ge (fun h => hchoose ⟨hn,h⟩))]
      · rw [if_neg hn]
    have hempty : {code : UnlabeledOrderCode n | timePairConfidenceRadius3 n alpha <
        geometricDistortion3 (time_quadratic_density_class3 (time_pair_confidence_estimator_mem3 alpha code))
          (time_quadratic_density_class3 ht)} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro code
      simp only [Set.mem_setOf_eq,hr,timePairConfidenceEstimator3,if_neg hchoose,not_lt]
      exact time_pair_midpoint_geometric_bound3 ht
    rw [hempty,measureReal_empty]
    exact ha0.le

#print axioms time_pair_confidence_estimator_measurable3
#print axioms time_pair_raw_geometric_confidence3
#print axioms time_pair_geometric_confidence3
end
end QuantyraNullCone
