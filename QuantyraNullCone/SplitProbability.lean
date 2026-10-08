import QuantyraNullCone.DKWClass
import QuantyraNullCone.Concentration

namespace QuantyraNullCone

open MeasureTheory

theorem sample_empirical_CDF_measurable (n : ℕ) (s t : ℝ) :
    Measurable (fun w : Fin n → DiamondPoint =>
      empiricalCDF (fun i => (w i).1) (fun i => (w i).2) s t) := by
  classical
  have hMeas : Measurable (fun w : Fin n → DiamondPoint =>
      ∑ i : Fin n, (cdfRegion s t).indicator (fun _ : DiamondPoint => (1 : ℝ)) (w i)) :=
    Finset.measurable_sum _ (fun i _ =>
      (measurable_const.indicator (cdfRegion_measurableSet s t)).comp (measurable_pi_apply i))
  convert hMeas.div_const (n : ℝ) using 1
  funext w
  simp [empiricalCDF, rectangleCount, Set.indicator_apply, cdfRegion, Finset.sum_boole]

def jointGridPointBad (rho : DiamondPoint → ℝ) (n q : ℕ) (e : ℝ)
    (jk : Fin (q + 1) × Fin (q + 1)) : Set (Fin n → DiamondPoint) :=
  {w | e < |empiricalCDF (fun i => (w i).1) (fun i => (w i).2)
    ((jk.1.val : ℝ) / q) ((jk.2.val : ℝ) / q) -
      populationCDF rho ((jk.1.val : ℝ) / q) ((jk.2.val : ℝ) / q)|}

def sampleJointGridBad (rho : DiamondPoint → ℝ) (n q : ℕ) (e : ℝ) :
    Set (Fin n → DiamondPoint) := ⋃ jk, jointGridPointBad rho n q e jk

theorem sample_joint_grid_bad_measurable (rho : DiamondPoint → ℝ) (n q : ℕ) (e : ℝ) :
    MeasurableSet (sampleJointGridBad rho n q e) :=
  MeasurableSet.iUnion (fun jk => measurableSet_lt measurable_const
    (((sample_empirical_CDF_measurable n ((jk.1.val : ℝ) / q) ((jk.2.val : ℝ) / q)).sub_const
      (populationCDF rho ((jk.1.val : ℝ) / q) ((jk.2.val : ℝ) / q))).abs))

theorem InDensityClass.split_joint_grid_failure {rho : DiamondPoint → ℝ} (h : InDensityClass rho)
    {n q : ℕ} {e : ℝ} (hn : 0 < n) (he : 0 ≤ e) :
    (sampleMeasure rho n).real (sampleJointGridBad rho n q e) ≤
      2 * ((q : ℝ) + 1) ^ 2 * Real.exp (-2 * (n : ℝ) * e ^ 2) := by
  letI : IsProbabilityMeasure (sampleMeasure rho n) := h.sample_isProbabilityMeasure n
  have hEach : ∀ jk : Fin (q + 1) × Fin (q + 1),
      (sampleMeasure rho n).real (jointGridPointBad rho n q e jk) ≤
        2 * Real.exp (-2 * (n : ℝ) * e ^ 2) := by
    intro jk
    have hSub : jointGridPointBad rho n q e jk ⊆ {w : Fin n → DiamondPoint |
        e ≤ |empiricalCDF (fun i => (w i).1) (fun i => (w i).2)
          ((jk.1.val : ℝ) / q) ((jk.2.val : ℝ) / q) -
            populationCDF rho ((jk.1.val : ℝ) / q) ((jk.2.val : ℝ) / q)|} := by
      intro w hBad
      change e < |empiricalCDF (fun i => (w i).1) (fun i => (w i).2)
        ((jk.1.val : ℝ) / q) ((jk.2.val : ℝ) / q) -
          populationCDF rho ((jk.1.val : ℝ) / q) ((jk.2.val : ℝ) / q)| at hBad
      exact le_of_lt hBad
    exact (measureReal_mono hSub).trans
      (h.empiricalCDF_concentration hn ((jk.1.val : ℝ) / q) ((jk.2.val : ℝ) / q) he)
  calc
    (sampleMeasure rho n).real (sampleJointGridBad rho n q e) ≤
        ∑ jk : Fin (q + 1) × Fin (q + 1), (sampleMeasure rho n).real (jointGridPointBad rho n q e jk) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _jk : Fin (q + 1) × Fin (q + 1), 2 * Real.exp (-2 * (n : ℝ) * e ^ 2) :=
      Finset.sum_le_sum (fun jk _ => hEach jk)
    _ = 2 * ((q : ℝ) + 1) ^ 2 * Real.exp (-2 * (n : ℝ) * e ^ 2) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      ring

def splitCalibrationBad (rho : DiamondPoint → ℝ) (n q : ℕ) (epsilonM epsilonJ : ℝ) :
    Set (Fin n → DiamondPoint) := sampleMarginalBad n epsilonM ∪ sampleJointGridBad rho n q epsilonJ

theorem split_calibration_bad_measurable {n : ℕ} (hn : 0 < n)
    (rho : DiamondPoint → ℝ) (q : ℕ) (epsilonM epsilonJ : ℝ) :
    MeasurableSet (splitCalibrationBad rho n q epsilonM epsilonJ) :=
  (sample_marginal_bad_measurable hn epsilonM).union
    (sample_joint_grid_bad_measurable rho n q epsilonJ)

/-- Actual split-DKW/Hoeffding failure expression for original K. -/
theorem InDensityClass.split_confidence_failure {rho : DiamondPoint → ℝ} (h : InDensityClass rho)
    {n q : ℕ} {epsilonM epsilonJ : ℝ} (hn : 0 < n) (hM : 0 ≤ epsilonM) (hJ : 0 ≤ epsilonJ) :
    (sampleMeasure rho n).real (splitCalibrationBad rho n q epsilonM epsilonJ) ≤
      4 * Real.exp (-2 * (n : ℝ) * epsilonM ^ 2) +
        2 * ((q : ℝ) + 1) ^ 2 * Real.exp (-2 * (n : ℝ) * epsilonJ ^ 2) := by
  letI : IsProbabilityMeasure (sampleMeasure rho n) := h.sample_isProbabilityMeasure n
  have hUnion := measureReal_union_le (μ := sampleMeasure rho n)
    (sampleMarginalBad n epsilonM) (sampleJointGridBad rho n q epsilonJ)
  exact hUnion.trans (add_le_add (h.split_marginal_failure hn hM) (h.split_joint_grid_failure hn hJ))

theorem InDensityClass.split_accuracy_probability {rho : DiamondPoint → ℝ} (h : InDensityClass rho)
    {n q : ℕ} {epsilonM epsilonJ : ℝ} (hn : 0 < n) (hM : 0 ≤ epsilonM) (hJ : 0 ≤ epsilonJ) :
    1 - (4 * Real.exp (-2 * (n : ℝ) * epsilonM ^ 2) +
      2 * ((q : ℝ) + 1) ^ 2 * Real.exp (-2 * (n : ℝ) * epsilonJ ^ 2)) ≤
        (sampleMeasure rho n).real (splitCalibrationBad rho n q epsilonM epsilonJ)ᶜ := by
  letI : IsProbabilityMeasure (sampleMeasure rho n) := h.sample_isProbabilityMeasure n
  rw [probReal_compl_eq_one_sub (split_calibration_bad_measurable hn rho q epsilonM epsilonJ)]
  linarith only [h.split_confidence_failure (q := q) hn hM hJ]

#print axioms InDensityClass.split_joint_grid_failure
#print axioms InDensityClass.split_confidence_failure
#print axioms InDensityClass.split_accuracy_probability

end QuantyraNullCone
