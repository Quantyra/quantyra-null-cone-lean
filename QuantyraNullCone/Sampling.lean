import QuantyraNullCone.GridAccuracy
import Mathlib.Analysis.SpecialFunctions.Exp

namespace QuantyraNullCone

open MeasureTheory

theorem densityMeasure_ae_mem_diamond (rho : DiamondPoint → ℝ) :
    ∀ᵐ p ∂densityMeasure rho, p ∈ diamond := by
  apply ae_iff.mpr
  change densityMeasure rho diamondᶜ = 0
  rw [densityMeasure_inter_diamond rho diamond_measurableSet.compl]
  simp

theorem InDensityClass.sample_ae_mem_diamond {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) (n : ℕ) :
    ∀ᵐ sample ∂sampleMeasure rho n, ∀ i, sample i ∈ diamond := by
  letI : IsProbabilityMeasure (densityMeasure rho) := h.isProbabilityMeasure
  exact Filter.eventually_all.mpr fun i =>
    (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => densityMeasure rho) (i := i)).eventually
      (densityMeasure_ae_mem_diamond rho)

theorem InDensityClass.coordinate_ne_ae {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) (a : ℝ) :
    ∀ᵐ p ∂densityMeasure rho, p.1 ≠ a ∧ p.2 ≠ a := by
  have hU : densityMeasure rho {p | p.1 = a} = 0 := by
    rw [show {p : DiamondPoint | p.1 = a} = Prod.fst ⁻¹' {a} by rfl,
      h.uMarginal_mass (measurableSet_singleton a)]
    exact measure_mono_null Set.inter_subset_left (measure_singleton a)
  have hV : densityMeasure rho {p | p.2 = a} = 0 := by
    rw [show {p : DiamondPoint | p.2 = a} = Prod.snd ⁻¹' {a} by rfl,
      h.vMarginal_mass (measurableSet_singleton a)]
    exact measure_mono_null Set.inter_subset_left (measure_singleton a)
  have hu : ∀ᵐ p ∂densityMeasure rho, p.1 ≠ a := by
    apply ae_iff.mpr
    simpa only [not_not] using hU
  have hv : ∀ᵐ p ∂densityMeasure rho, p.2 ≠ a := by
    apply ae_iff.mpr
    simpa only [not_not] using hV
  exact hu.and hv

theorem InDensityClass.sample_ae_no_grid_lines {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) (n m : ℕ) (r : ℝ) :
    ∀ᵐ sample ∂sampleMeasure rho n, ∀ i, ∀ k : Fin (m + 1),
      (sample i).1 ≠ (k : ℝ) * r ∧ (sample i).2 ≠ (k : ℝ) * r := by
  letI : IsProbabilityMeasure (densityMeasure rho) := h.isProbabilityMeasure
  apply Filter.eventually_all.mpr
  intro i
  apply Filter.eventually_all.mpr
  intro k
  exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n => densityMeasure rho) (i := i)).eventually
    (h.coordinate_ne_ae ((k : ℝ) * r))

def openGridCell (j k : ℕ) (r : ℝ) : Set DiamondPoint :=
  (Set.Ioo ((j : ℝ) * r) (((j : ℝ) + 1) * r)).prod
    (Set.Ioo ((k : ℝ) * r) (((k : ℝ) + 1) * r))

theorem openGridCell_measurable (j k : ℕ) (r : ℝ) : MeasurableSet (openGridCell j k r) :=
  measurableSet_Ioo.prod measurableSet_Ioo

theorem openGridCell_subset {j k m : ℕ} {r : ℝ} (hj : j < m) (hk : k < m)
    (hr : 0 < r) (hmr : (m : ℝ) * r = 1) : openGridCell j k r ⊆ diamond := by
  intro p hp
  have hj0 : 0 ≤ (j : ℝ) * r := mul_nonneg (Nat.cast_nonneg j) hr.le
  have hk0 : 0 ≤ (k : ℝ) * r := mul_nonneg (Nat.cast_nonneg k) hr.le
  have hj1 : ((j : ℝ) + 1) * r ≤ 1 := by
    calc
      _ ≤ (m : ℝ) * r :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hj) hr.le
      _ = 1 := hmr
  have hk1 : ((k : ℝ) + 1) * r ≤ 1 := by
    calc
      _ ≤ (m : ℝ) * r :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hk) hr.le
      _ = 1 := hmr
  exact ⟨⟨hj0.trans hp.1.1.le, hp.1.2.le.trans hj1⟩,
    ⟨hk0.trans hp.2.1.le, hp.2.2.le.trans hk1⟩⟩

theorem InDensityClass.densityMeasure_floor {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) : (ENNReal.ofReal (1 / 2 : ℝ)) • diamondVolume ≤
      densityMeasure rho := by
  rw [← withDensity_const]
  apply withDensity_mono
  exact (ae_restrict_mem diamond_measurableSet).mono fun p hp =>
    ENNReal.ofReal_le_ofReal (h.bounds p hp).1

theorem InDensityClass.gridCell_mass_lower {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) {j k m : ℕ} {r : ℝ} (hj : j < m) (hk : k < m)
    (hr : 0 < r) (hmr : (m : ℝ) * r = 1) :
    r ^ 2 / 2 ≤ (densityMeasure rho (openGridCell j k r)).toReal := by
  letI : IsProbabilityMeasure (densityMeasure rho) := h.isProbabilityMeasure
  have hVol : diamondVolume (openGridCell j k r) = ENNReal.ofReal (r ^ 2) := by
    rw [diamondVolume, Measure.restrict_apply (openGridCell_measurable j k r),
      Set.inter_eq_left.mpr (openGridCell_subset hj hk hr hmr)]
    rw [show openGridCell j k r =
      Set.Ioo ((j : ℝ) * r) (((j : ℝ) + 1) * r) ×ˢ
        Set.Ioo ((k : ℝ) * r) (((k : ℝ) + 1) * r) from rfl]
    rw [Measure.prod_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)),
      Real.volume_Ioo, Real.volume_Ioo]
    have hWidth (i : ℕ) : (((i : ℝ) + 1) * r - (i : ℝ) * r) = r := by ring
    rw [hWidth j, hWidth k, ← ENNReal.ofReal_mul hr.le]
    congr 1
    ring
  have hLow := h.densityMeasure_floor (openGridCell j k r)
  simp only [Measure.smul_apply, smul_eq_mul, hVol] at hLow
  have hLowReal := ENNReal.toReal_mono (measure_ne_top _ _) hLow
  simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal, hr.le, sq_nonneg,
    div_eq_mul_inv, mul_comm] using hLowReal

theorem InDensityClass.sample_misses_mass {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) (n : ℕ) {S : Set DiamondPoint} (hS : MeasurableSet S) :
    (sampleMeasure rho n {sample | ∀ i, sample i ∉ S}).toReal =
      (1 - (densityMeasure rho S).toReal) ^ n := by
  letI : IsProbabilityMeasure (densityMeasure rho) := h.isProbabilityMeasure
  have hSet : {sample : Fin n → DiamondPoint | ∀ i, sample i ∉ S} =
      Set.univ.pi (fun _ : Fin n => Sᶜ) := by
    ext sample
    simp
  rw [hSet, sampleMeasure, Measure.pi_pi]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.toReal_pow]
  rw [show (densityMeasure rho Sᶜ).toReal = 1 - (densityMeasure rho S).toReal from
    probReal_compl_eq_one_sub hS]

theorem InDensityClass.sample_misses_le_exp {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) (n : ℕ) {S : Set DiamondPoint} (hS : MeasurableSet S) :
    (sampleMeasure rho n {sample | ∀ i, sample i ∉ S}).toReal ≤
      Real.exp (-(n : ℝ) * (densityMeasure rho S).toReal) := by
  letI : IsProbabilityMeasure (densityMeasure rho) := h.isProbabilityMeasure
  have h0 : 0 ≤ 1 - (densityMeasure rho S).toReal := by
    change 0 ≤ 1 - (densityMeasure rho).real S
    rw [← probReal_compl_eq_one_sub hS]
    exact ENNReal.toReal_nonneg
  rw [h.sample_misses_mass n hS]
  calc
    _ ≤ Real.exp (-(densityMeasure rho S).toReal) ^ n :=
      pow_le_pow_left₀ h0 (by linarith [Real.add_one_le_exp (-(densityMeasure rho S).toReal)]) n
    _ = Real.exp (-(n : ℝ) * (densityMeasure rho S).toReal) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

theorem InDensityClass.grid_occupancy_failure {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) (n m : ℕ) {r : ℝ} (hr : 0 < r) (hmr : (m : ℝ) * r = 1) :
    (sampleMeasure rho n {sample | ¬ GridOccupied (fun i => (sample i).1)
      (fun i => (sample i).2) m r}).toReal ≤
      (m : ℝ) ^ 2 * Real.exp (-(n : ℝ) * r ^ 2 / 2) := by
  classical
  letI : IsProbabilityMeasure (sampleMeasure rho n) := h.sample_isProbabilityMeasure n
  let misses (jk : Fin m × Fin m) : Set (Fin n → DiamondPoint) :=
    {sample | ∀ i, sample i ∉ openGridCell jk.1 jk.2 r}
  have hSub : {sample : Fin n → DiamondPoint | ¬ GridOccupied (fun i => (sample i).1)
      (fun i => (sample i).2) m r} ⊆ ⋃ jk, misses jk := by
    intro sample hs
    by_contra hUnion
    apply hs
    intro j k hj hk
    by_contra hMissing
    apply hUnion
    apply Set.mem_iUnion.mpr
    refine ⟨(⟨j, hj⟩, ⟨k, hk⟩), ?_⟩
    intro i hi
    exact hMissing ⟨i, hi.1.1, hi.1.2, hi.2.1, hi.2.2⟩
  have hEach (jk : Fin m × Fin m) : (sampleMeasure rho n).real (misses jk) ≤
      Real.exp (-(n : ℝ) * r ^ 2 / 2) := by
    refine (h.sample_misses_le_exp n (openGridCell_measurable jk.1 jk.2 r)).trans ?_
    apply Real.exp_le_exp.mpr
    have hMass := h.gridCell_mass_lower jk.1.isLt jk.2.isLt hr hmr
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  calc
    _ ≤ (sampleMeasure rho n).real (⋃ jk, misses jk) := measureReal_mono hSub
    _ ≤ ∑ jk : Fin m × Fin m, (sampleMeasure rho n).real (misses jk) :=
      measureReal_iUnion_fintype_le misses
    _ ≤ ∑ _jk : Fin m × Fin m, Real.exp (-(n : ℝ) * r ^ 2 / 2) :=
      Finset.sum_le_sum fun jk _ => hEach jk
    _ = (m : ℝ) ^ 2 * Real.exp (-(n : ℝ) * r ^ 2 / 2) := by
      simp [Fintype.card_prod, sq]

#print axioms InDensityClass.sample_ae_mem_diamond
#print axioms InDensityClass.sample_ae_no_grid_lines
#print axioms InDensityClass.gridCell_mass_lower
#print axioms InDensityClass.sample_misses_le_exp
#print axioms InDensityClass.grid_occupancy_failure

end QuantyraNullCone
