import QuantyraNullCone.DKWUniformGrid
import Mathlib.Algebra.Order.Archimedean.Basic

namespace QuantyraNullCone

open MeasureTheory

def uniformPopulationCDF (t : ℝ) : ℝ := max 0 (min t 1)

theorem uniform_population_CDF (t : ℝ) :
    uniform01Measure.real (Set.Iic t) = uniformPopulationCDF t := by
  have hSet : Set.Iic t ∩ Set.Ioc (0 : ℝ) 1 = Set.Ioc 0 (min t 1) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioc, le_min_iff]
    tauto
  rw [Measure.real, uniform01Measure, Measure.restrict_apply measurableSet_Iic,
    hSet, Real.volume_Ioc, sub_zero]
  unfold uniformPopulationCDF
  by_cases h : 0 ≤ min t 1
  · rw [ENNReal.toReal_ofReal h, max_eq_right h]
  · rw [ENNReal.ofReal_of_nonpos (le_of_not_ge h), ENNReal.toReal_zero,
      max_eq_left (le_of_not_ge h)]

theorem uniform_population_CDF_unit {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    uniformPopulationCDF t = t := by
  simp only [uniformPopulationCDF, min_eq_left ht.2, max_eq_right ht.1]

theorem marginal_CDF_bounds {n : ℕ} (hn : 0 < n) (w : Fin n → ℝ) (t : ℝ) :
    0 ≤ marginalCDF w t ∧ marginalCDF w t ≤ 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · unfold marginalCDF
    positivity
  · apply (div_le_one hnR).mpr
    have h := Finset.card_le_univ (cumulativeCount w t)
    exact_mod_cast (show (cumulativeCount w t).card ≤ n by simpa using h)

def uniformBad (n : ℕ) (e : ℝ) : Set (Fin n → ℝ) :=
  {w | ∃ t : ℝ, e < |marginalCDF w t - uniformPopulationCDF t|}

theorem uniform_grid_bad_double {n q : ℕ} (e : ℝ) :
    uniformGridBad n q e ⊆ uniformGridBad n (2 * q) e := by
  intro w h
  obtain ⟨k, hk, hError⟩ := h
  refine ⟨2 * k, Finset.mem_Icc.mpr
    ⟨Nat.zero_le _, Nat.mul_le_mul_left 2 (Finset.mem_Icc.mp hk).2⟩, ?_⟩
  have hRatio : ((2 * k : ℕ) : ℝ) / ((2 * q : ℕ) : ℝ) = (k : ℝ) / q := by
    push_cast
    exact mul_div_mul_left (k : ℝ) (q : ℝ) (by norm_num : (2 : ℝ) ≠ 0)
  rwa [hRatio]

theorem uniform_dyadic_bad_monotone (n : ℕ) (e : ℝ) :
    Monotone (fun m : ℕ => uniformGridBad n (2 ^ m) e) := by
  apply monotone_nat_of_le_succ
  intro m
  simpa only [pow_succ, Nat.mul_comm] using uniform_grid_bad_double (n := n) (q := 2 ^ m) e

/-- Real-threshold strict deviations equal a countable nested grid union.
The identity holds for every sample, not merely on supported samples. -/
theorem uniform_bad_dyadic_union {n : ℕ} (hn : 0 < n) (e : ℝ) :
    uniformBad n e = ⋃ m : ℕ, uniformGridBad n (2 ^ m) e := by
  ext w
  constructor
  · rintro ⟨t, hError⟩
    by_cases htNeg : t < 0
    · have hPop : uniformPopulationCDF t = 0 := by
        simp [uniformPopulationCDF, min_eq_left (by linarith : t ≤ 1),
          max_eq_left htNeg.le]
      rw [hPop, sub_zero, abs_of_nonneg (marginal_CDF_bounds hn w t).1] at hError
      have hMono := marginalCDF_mono w htNeg.le
      apply Set.mem_iUnion.mpr
      refine ⟨0, 0, by simp, ?_⟩
      simp only [pow_zero, Nat.cast_zero, Nat.cast_one, zero_div, sub_zero]
      rw [abs_of_nonneg (marginal_CDF_bounds hn w 0).1]
      exact hError.trans_le hMono
    by_cases htHigh : 1 < t
    · have hPop : uniformPopulationCDF t = 1 := by
        simp [uniformPopulationCDF, min_eq_right htHigh.le]
      rw [hPop, abs_of_nonpos (sub_nonpos.mpr (marginal_CDF_bounds hn w t).2)] at hError
      have hMono := marginalCDF_mono w htHigh.le
      apply Set.mem_iUnion.mpr
      refine ⟨0, 1, by simp, ?_⟩
      simp only [pow_zero, Nat.cast_one, div_one]
      rw [abs_of_nonpos (sub_nonpos.mpr (marginal_CDF_bounds hn w 1).2)]
      linarith only [hError, hMono]
    have ht0 : 0 ≤ t := le_of_not_gt htNeg
    have ht1 : t ≤ 1 := le_of_not_gt htHigh
    rw [uniform_population_CDF_unit ⟨ht0, ht1⟩] at hError
    let gap : ℝ := |marginalCDF w t - t| - e
    have hGap : 0 < gap := by dsimp [gap]; linarith only [hError]
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hGap (by norm_num : (1 / 2 : ℝ) < 1)
    let q : ℕ := 2 ^ m
    let r : ℝ := 1 / (q : ℝ)
    have hq : 0 < q := pow_pos (by norm_num) m
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hr : 0 < r := div_pos (by norm_num) hqR
    have hqr : (q : ℝ) * r = 1 := by dsimp [r]; exact mul_one_div_cancel (ne_of_gt hqR)
    have hRadius : r = (1 / 2 : ℝ) ^ m := by
      dsimp [r, q]
      rw [Nat.cast_pow, one_div, ← inv_pow]
      norm_num
    have hSmall : r < gap := by rwa [hRadius]
    obtain ⟨j, k, hj, hk, hLo, hHi, hGapLo, hGapHi⟩ := grid_closed_bracket hr hqr ht0 ht1
    by_cases hSign : 0 ≤ marginalCDF w t - t
    · dsimp [gap] at hSmall
      rw [abs_of_nonneg hSign] at hSmall
      have hMono := marginalCDF_mono w hHi
      have hStrict : e < marginalCDF w ((k : ℝ) * r) - (k : ℝ) * r := by
        linarith only [hSmall, hMono, hGapHi]
      apply Set.mem_iUnion.mpr
      refine ⟨m, k, Finset.mem_Icc.mpr ⟨Nat.zero_le _, hk⟩, ?_⟩
      change e < |marginalCDF w ((k : ℝ) / q) - (k : ℝ) / q|
      have hRatio : (k : ℝ) / q = (k : ℝ) * r := by dsimp [r]; ring
      rw [hRatio]
      exact hStrict.trans_le (le_abs_self _)
    · dsimp [gap] at hSmall
      rw [abs_of_nonpos (le_of_not_ge hSign)] at hSmall
      have hMono := marginalCDF_mono w hLo
      have hStrict : e < (j : ℝ) * r - marginalCDF w ((j : ℝ) * r) := by
        linarith only [hSmall, hMono, hGapLo]
      apply Set.mem_iUnion.mpr
      refine ⟨m, j, Finset.mem_Icc.mpr ⟨Nat.zero_le _, hj⟩, ?_⟩
      change e < |marginalCDF w ((j : ℝ) / q) - (j : ℝ) / q|
      have hRatio : (j : ℝ) / q = (j : ℝ) * r := by dsimp [r]; ring
      rw [hRatio]
      have hAbs : (j : ℝ) * r - marginalCDF w ((j : ℝ) * r) ≤
          |marginalCDF w ((j : ℝ) * r) - (j : ℝ) * r| := by
        linarith only [neg_le_abs (marginalCDF w ((j : ℝ) * r) - (j : ℝ) * r)]
      exact hStrict.trans_le hAbs
  · intro h
    obtain ⟨m, k, hk, hError⟩ := Set.mem_iUnion.mp h
    have hqR : (0 : ℝ) < (2 ^ m : ℕ) := by positivity
    have ht0 : 0 ≤ (k : ℝ) / (2 ^ m : ℕ) := by positivity
    have ht1 : (k : ℝ) / (2 ^ m : ℕ) ≤ 1 := by
      apply (div_le_one hqR).mpr
      exact_mod_cast (Finset.mem_Icc.mp hk).2
    refine ⟨(k : ℝ) / (2 ^ m : ℕ), ?_⟩
    rwa [uniform_population_CDF_unit ⟨ht0, ht1⟩]

theorem uniform_bad_measurable {n : ℕ} (hn : 0 < n) (e : ℝ) : MeasurableSet (uniformBad n e) := by
  rw [uniform_bad_dyadic_union hn e]
  exact MeasurableSet.iUnion (fun m => uniform_grid_bad_measurable n (2 ^ m) e)

/-- Sharp two-sided DKW for the actual continuous iid uniform law and every real threshold. -/
theorem uniform_DKW {n : ℕ} {e : ℝ} (hn : 0 < n) (he : 0 ≤ e) :
    (uniformSampleMeasure n).real (uniformBad n e) ≤
      2 * Real.exp (-2 * (n : ℝ) * e ^ 2) := by
  let C := 2 * Real.exp (-2 * (n : ℝ) * e ^ 2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hBound : ∀ m : ℕ, uniformSampleMeasure n (uniformGridBad n (2 ^ m) e) ≤
      ENNReal.ofReal C := by
    intro m
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal (uniform_grid_DKW hn (by positivity : 0 < 2 ^ m) he)
  have hMass : uniformSampleMeasure n (uniformBad n e) ≤ ENNReal.ofReal C := by
    rw [uniform_bad_dyadic_union hn e, (uniform_dyadic_bad_monotone n e).measure_iUnion]
    exact iSup_le hBound
  have hReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hMass
  rw [ENNReal.toReal_ofReal hC] at hReal
  exact hReal

theorem uniform_DKW_actual_population {n : ℕ} {e : ℝ} (hn : 0 < n) (he : 0 ≤ e) :
    (uniformSampleMeasure n).real {w | ∃ t : ℝ,
      e < |marginalCDF w t - uniform01Measure.real (Set.Iic t)|} ≤
      2 * Real.exp (-2 * (n : ℝ) * e ^ 2) := by
  simp_rw [uniform_population_CDF]
  exact uniform_DKW hn he

#print axioms uniform_bad_dyadic_union
#print axioms uniform_DKW
#print axioms uniform_DKW_actual_population

end QuantyraNullCone
