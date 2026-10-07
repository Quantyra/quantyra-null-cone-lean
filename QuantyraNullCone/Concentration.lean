import QuantyraNullCone.Sampling
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Independence.Basic

namespace QuantyraNullCone

open MeasureTheory ProbabilityTheory

theorem InDensityClass.indicator_concentration {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) {n : ℕ} (hn : 0 < n) {S : Set DiamondPoint}
    (hS : MeasurableSet S) {r : ℝ} (hr : 0 ≤ r) :
    (sampleMeasure rho n).real {sample |
      r ≤ |(∑ i : Fin n, S.indicator (fun _ => (1 : ℝ)) (sample i)) / n -
        (densityMeasure rho S).toReal|} ≤
      2 * Real.exp (-2 * (n : ℝ) * r ^ 2) := by
  classical
  letI : IsProbabilityMeasure (densityMeasure rho) := h.isProbabilityMeasure
  letI : IsProbabilityMeasure (sampleMeasure rho n) := h.sample_isProbabilityMeasure n
  let Y : DiamondPoint → ℝ := S.indicator (fun _ => 1)
  let p : ℝ := (densityMeasure rho S).toReal
  let X (i : Fin n) (sample : Fin n → DiamondPoint) : ℝ := Y (sample i) - p
  have hMeas : Measurable Y := measurable_const.indicator hS
  have hBound : ∀ q, Y q ∈ Set.Icc (0 : ℝ) 1 := by
    intro q
    by_cases hq : q ∈ S <;> simp [Y, hq]
  have hMean : (∫ q, Y q ∂densityMeasure rho) = p := by
    simp [Y, p, integral_indicator hS, Measure.real]
  have hSG : HasSubgaussianMGF (fun q => Y q - p) (1 / 4) (densityMeasure rho) := by
    have hSG' := hasSubgaussianMGF_of_mem_Icc (μ := densityMeasure rho)
      hMeas.aemeasurable (ae_of_all _ hBound)
    rw [hMean] at hSG'
    norm_num at hSG'
    exact hSG'
  have hIndep : iIndepFun X (sampleMeasure rho n) :=
    iIndepFun_pi (X := fun _ : Fin n => fun q => Y q - p)
      (fun _ => (hMeas.sub_const p).aemeasurable)
  have hEach (i : Fin n) : HasSubgaussianMGF (X i) (1 / 4) (sampleMeasure rho n) := by
    have hMap : (sampleMeasure rho n).map (Function.eval i) = densityMeasure rho :=
      (measurePreserving_eval (fun _ : Fin n => densityMeasure rho) i).map_eq
    have hSGMap : HasSubgaussianMGF (fun q => Y q - p) (1 / 4)
        ((sampleMeasure rho n).map (Function.eval i)) := by
      rw [hMap]
      exact hSG
    exact HasSubgaussianMGF.of_map (μ := sampleMeasure rho n) (Y := Function.eval i)
      (measurable_pi_apply i).aemeasurable hSGMap
  have hNegIndep : iIndepFun (fun i sample => -X i sample) (sampleMeasure rho n) :=
    hIndep.comp (fun _ => fun x : ℝ => -x) (fun _ => measurable_neg)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hThreshold : 0 ≤ (n : ℝ) * r := mul_nonneg hnR.le hr
  have hUpper := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hIndep
    (s := Finset.univ) (c := fun _ => (1 / 4 : NNReal)) (ε := (n : ℝ) * r)
    (fun i _ => hEach i) hThreshold
  have hLower := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hNegIndep
    (s := Finset.univ) (c := fun _ => (1 / 4 : NNReal)) (ε := (n : ℝ) * r)
    (fun i _ => (hEach i).neg) hThreshold
  have hExponent : -((n : ℝ) * r) ^ 2 / (2 * (∑ _i : Fin n, (1 / 4 : NNReal) : NNReal)) =
      -2 * (n : ℝ) * r ^ 2 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
    field_simp [ne_of_gt hnR]
    ring
  rw [hExponent] at hUpper hLower
  have hSum (sample : Fin n → DiamondPoint) :
      ∑ i : Fin n, X i sample = (n : ℝ) * ((∑ i : Fin n, Y (sample i)) / n - p) := by
    simp only [X, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp [ne_of_gt hnR]
  have hSub : {sample : Fin n → DiamondPoint |
      r ≤ |(∑ i, Y (sample i)) / n - p|} ⊆
      {sample | (n : ℝ) * r ≤ ∑ i, X i sample} ∪
      {sample | (n : ℝ) * r ≤ ∑ i, -X i sample} := by
    intro sample hs
    have hAbs : (n : ℝ) * r ≤ |∑ i, X i sample| := by
      rw [hSum, abs_mul, abs_of_nonneg hnR.le]
      exact mul_le_mul_of_nonneg_left hs hnR.le
    by_cases hSign : 0 ≤ ∑ i, X i sample
    · left
      rwa [abs_of_nonneg hSign] at hAbs
    · right
      change (n : ℝ) * r ≤ ∑ i : Fin n, -X i sample
      rw [Finset.sum_neg_distrib]
      rwa [abs_of_neg (lt_of_not_ge hSign)] at hAbs
  calc
    _ ≤ (sampleMeasure rho n).real
        ({sample | (n : ℝ) * r ≤ ∑ i, X i sample} ∪
          {sample | (n : ℝ) * r ≤ ∑ i, -X i sample}) := measureReal_mono hSub
    _ ≤ (sampleMeasure rho n).real {sample | (n : ℝ) * r ≤ ∑ i, X i sample} +
        (sampleMeasure rho n).real {sample | (n : ℝ) * r ≤ ∑ i, -X i sample} :=
      measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-2 * (n : ℝ) * r ^ 2) := by linarith

theorem InDensityClass.empiricalCDF_concentration {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) {n : ℕ} (hn : 0 < n) (s t : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    (sampleMeasure rho n).real {sample |
      r ≤ |empiricalCDF (fun i => (sample i).1) (fun i => (sample i).2) s t -
        populationCDF rho s t|} ≤ 2 * Real.exp (-2 * (n : ℝ) * r ^ 2) := by
  classical
  have hCount (sample : Fin n → DiamondPoint) :
      (∑ i : Fin n, (cdfRegion s t).indicator (fun _ => (1 : ℝ)) (sample i)) =
        (rectangleCount (fun i => (sample i).1) (fun i => (sample i).2) s t).card := by
    simp [Set.indicator_apply, cdfRegion, rectangleCount, Finset.sum_boole]
  convert h.indicator_concentration hn (cdfRegion_measurableSet s t) hr using 1
  congr 1
  ext sample
  simp only [Set.mem_setOf_eq]
  rw [hCount]
  rfl

theorem InDensityClass.grid_vertices_failure {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) {n : ℕ} (hn : 0 < n) (m : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (sampleMeasure rho n).real {sample | ¬ GridVertexAccuracy
      (fun i => (sample i).1) (fun i => (sample i).2) rho m r} ≤
      2 * ((m : ℝ) + 1) ^ 2 * Real.exp (-2 * (n : ℝ) * r ^ 2) := by
  classical
  letI : IsProbabilityMeasure (sampleMeasure rho n) := h.sample_isProbabilityMeasure n
  let bad (jk : Fin (m + 1) × Fin (m + 1)) : Set (Fin n → DiamondPoint) :=
    {sample | r ≤ |empiricalCDF (fun i => (sample i).1) (fun i => (sample i).2)
      ((jk.1 : ℝ) * r) ((jk.2 : ℝ) * r) -
      populationCDF rho ((jk.1 : ℝ) * r) ((jk.2 : ℝ) * r)|}
  have hSub : {sample : Fin n → DiamondPoint | ¬ GridVertexAccuracy
      (fun i => (sample i).1) (fun i => (sample i).2) rho m r} ⊆ ⋃ jk, bad jk := by
    intro sample hs
    by_contra hUnion
    apply hs
    intro j k hj hk
    by_contra hBad
    apply hUnion
    exact Set.mem_iUnion.mpr ⟨(⟨j, Nat.lt_succ_of_le hj⟩, ⟨k, Nat.lt_succ_of_le hk⟩),
      (lt_of_not_ge hBad).le⟩
  calc
    _ ≤ (sampleMeasure rho n).real (⋃ jk, bad jk) := measureReal_mono hSub
    _ ≤ ∑ jk : Fin (m + 1) × Fin (m + 1), (sampleMeasure rho n).real (bad jk) :=
      measureReal_iUnion_fintype_le bad
    _ ≤ ∑ _jk : Fin (m + 1) × Fin (m + 1), 2 * Real.exp (-2 * (n : ℝ) * r ^ 2) :=
      Finset.sum_le_sum fun jk _ => h.empiricalCDF_concentration hn _ _ hr
    _ = 2 * ((m : ℝ) + 1) ^ 2 * Real.exp (-2 * (n : ℝ) * r ^ 2) := by
      simp [Fintype.card_prod, sq]
      ring

#print axioms InDensityClass.indicator_concentration
#print axioms InDensityClass.empiricalCDF_concentration
#print axioms InDensityClass.grid_vertices_failure

end QuantyraNullCone
