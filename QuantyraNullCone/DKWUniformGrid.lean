import QuantyraNullCone.DKWQuantization
import Mathlib.MeasureTheory.Order.Group.Lattice

namespace QuantyraNullCone

open MeasureTheory

theorem marginal_CDF_measurable (n : ℕ) (t : ℝ) :
    Measurable (fun w : Fin n → ℝ => marginalCDF w t) := by
  classical
  have hMeas : Measurable (fun w : Fin n → ℝ =>
      ∑ i : Fin n, (Set.Iic t).indicator (fun _ : ℝ => (1 : ℝ)) (w i)) :=
    Finset.measurable_sum _ (fun i _ =>
      (measurable_const.indicator measurableSet_Iic).comp (measurable_pi_apply i))
  convert hMeas.div_const (n : ℝ) using 1
  funext w
  simp [marginalCDF, cumulativeCount, Set.indicator_apply, Finset.sum_boole]

def uniformGridBad (n q : ℕ) (e : ℝ) : Set (Fin n → ℝ) :=
  {w | ∃ k ∈ Finset.Icc 0 q, e < |marginalCDF w ((k : ℝ) / q) - (k : ℝ) / q|}

theorem uniform_grid_bad_measurable (n q : ℕ) (e : ℝ) : MeasurableSet (uniformGridBad n q e) := by
  have hSet : uniformGridBad n q e = ⋃ k : Fin (q + 1),
      {w : Fin n → ℝ | e < |marginalCDF w ((k.val : ℝ) / q) - (k.val : ℝ) / q|} := by
    ext w
    simp only [uniformGridBad, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨k, hk, hBad⟩
      exact ⟨⟨k, Nat.lt_succ_of_le (Finset.mem_Icc.mp hk).2⟩, hBad⟩
    · rintro ⟨k, hBad⟩
      exact ⟨k.val, Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.le_of_lt_succ k.isLt⟩, hBad⟩
  rw [hSet]
  exact MeasurableSet.iUnion (fun k => measurableSet_lt measurable_const
    (((marginal_CDF_measurable n ((k.val : ℝ) / q)).sub_const ((k.val : ℝ) / q)).abs))

theorem uniform_sample_supported (n : ℕ) :
    ∀ᵐ w ∂uniformSampleMeasure n, ∀ i, w i ∈ Set.Ioc (0 : ℝ) 1 := by
  apply Filter.eventually_all.mpr
  intro i
  exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => uniform01Measure) (i := i)).eventually
    (ae_restrict_mem measurableSet_Ioc)

/-- Sharp finite-grid concentration for the actual iid continuous uniform law. -/
theorem uniform_grid_DKW {n q : ℕ} {e : ℝ} (hn : 0 < n) (hq : 0 < q) (he : 0 ≤ e) :
    (uniformSampleMeasure n).real (uniformGridBad n q e) ≤
      2 * Real.exp (-2 * (n : ℝ) * e ^ 2) := by
  classical
  let E := finiteBinAbsDeviation (n := n) (q := q) e
  let Q := uniformQuantizedProfile (n := n) q hq
  have hSub : ∀ᵐ w ∂uniformSampleMeasure n, w ∈ uniformGridBad n q e → Q w ∈ E := by
    filter_upwards [uniform_sample_supported n] with w hw
    intro hBad
    obtain ⟨k, hk, hError⟩ := hBad
    simp only [E, Q, finiteBinAbsDeviation, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨k, hk, ?_⟩
    rw [uniform_quantized_CDF hq w hw]
    exact hError
  have hAE : uniformGridBad n q e ≤ᶠ[ae (uniformSampleMeasure n)] Q ⁻¹' (E : Set _) := hSub
  have hMass := ENNReal.toReal_mono (measure_ne_top (uniformSampleMeasure n) (Q ⁻¹' (E : Set _)))
    (measure_mono_ae hAE)
  have hQ : Measurable Q := uniform_quantized_profile_measurable q hq
  calc
    (uniformSampleMeasure n).real (uniformGridBad n q e) ≤
        (uniformSampleMeasure n).real (Q ⁻¹' (E : Set _)) := hMass
    _ = ((uniformSampleMeasure n).map Q).real E :=
      congrArg ENNReal.toReal (Measure.map_apply hQ E.measurableSet).symm
    _ = (E.card : ℝ) / (q : ℝ) ^ n := uniform_quantized_profile_real_mass hq E
    _ ≤ 2 * Real.exp (-2 * (n : ℝ) * e ^ 2) := finite_bin_two_sided_DKW hn hq he

#print axioms uniform_grid_bad_measurable
#print axioms uniform_grid_DKW

end QuantyraNullCone
