import QuantyraNullCone.SmallMassConcentration
import QuantyraNullCone.LogGridRate

namespace QuantyraNullCone

open MeasureTheory

/-- A union argument for the actual sample, with no independence assumption
between grid recovery and rectangle counts. -/
theorem InDensityClass.sample_good_and_small_mass_probability {rho : DiamondPoint → ℝ}
    (hK : InDensityClass rho) {n m : ℕ} (hn : 0 < n) {r h : ℝ}
    (hr : 0 < r) (hmr : (m : ℝ) * r = 1)
    {ι : Type*} [Fintype ι] (sets : ι → Set DiamondPoint)
    (hSets : ∀ i, MeasurableSet (sets i)) (hh0 : 0 ≤ h) (hh4 : h ≤ 4)
    (hp : ∀ i, (densityMeasure rho).real (sets i) ≤ 8 * h ^ 2) :
    1 - ((m : ℝ) ^ 2 * Real.exp (-(n : ℝ) * r ^ 2 / 2) +
      2 * ((m : ℝ) + 1) ^ 2 * Real.exp (-2 * (n : ℝ) * r ^ 2) +
      2 * Fintype.card ι * Real.exp (-(n : ℝ) * h ^ 4 / 2)) ≤
      (sampleMeasure rho n).real {sample | SampleGood rho m r sample ∧ ∀ i,
        |(pointsIn sample (sets i)).card / (n : ℝ) - (densityMeasure rho).real (sets i)| ≤
          4 * h ^ 3} := by
  letI : IsProbabilityMeasure (sampleMeasure rho n) := hK.sample_isProbabilityMeasure n
  let good := {sample : Fin n → DiamondPoint | SampleGood rho m r sample ∧ ∀ i,
    |(pointsIn sample (sets i)).card / (n : ℝ) - (densityMeasure rho).real (sets i)| ≤ 4 * h ^ 3}
  let bad := {sample : Fin n → DiamondPoint | ∃ i,
    4 * h ^ 3 ≤ |(pointsIn sample (sets i)).card / (n : ℝ) - (densityMeasure rho).real (sets i)|}
  have hSub : {sample | SampleGood rho m r sample} ⊆ good ∪ bad := by
    intro sample hs
    by_cases hAll : ∀ i, |(pointsIn sample (sets i)).card / (n : ℝ) -
        (densityMeasure rho).real (sets i)| ≤ 4 * h ^ 3
    · exact Or.inl ⟨hs, hAll⟩
    · right
      obtain ⟨i, hi⟩ := not_forall.mp hAll
      exact ⟨i, (lt_of_not_ge hi).le⟩
  have hCover := (measureReal_mono (μ := sampleMeasure rho n) hSub).trans
    (measureReal_union_le good bad)
  have hGrid := hK.sample_good_probability hn hr hmr
  have hMass := hK.small_mass_family_failure hn sets hSets hh0 hh4 hp
  change _ ≤ (sampleMeasure rho n).real good
  change (sampleMeasure rho n).real bad ≤ _ at hMass
  linarith

/-- The weaker MGF tail still leaves ample room in the 1/20 budget. Up to
4n rectangles allow both shifts and both orientations without extra symmetry
assumptions; actual grid cardinalities are discharged in the estimator stage. -/
theorem degree_event_failure_budget {n m q : ℕ} (hn : 65536 ≤ n) (hm : 16 ≤ m)
    {r : ℝ} (hmr : (m : ℝ) * r = 1)
    (hmSq : (m : ℝ) ^ 2 ≤ n / (8 * Real.log n)) (hq : (q : ℝ) ≤ 4 * n) :
    (m : ℝ) ^ 2 * Real.exp (-(n : ℝ) * r ^ 2 / 2) +
      2 * ((m : ℝ) + 1) ^ 2 * Real.exp (-2 * (n : ℝ) * r ^ 2) +
      2 * q * Real.exp (-(n : ℝ) * r ^ 2 / 2) ≤ 1 / 20 := by
  obtain ⟨hLog, _⟩ := log_large_bounds hn
  have hnR : (65536 : ℝ) ≤ n := by exact_mod_cast hn
  have hnPos : (0 : ℝ) < n := by linarith
  have hmR : (16 : ℝ) ≤ m := by exact_mod_cast hm
  have hBudget : (m : ℝ) ^ 2 * (8 * Real.log n) ≤ n :=
    (le_div_iff₀ (by linarith : 0 < 8 * Real.log (n : ℝ))).mp hmSq
  have hmEight : (m : ℝ) ^ 2 ≤ n / 8 := by
    have ht := mul_nonneg (sq_nonneg (m : ℝ)) (sub_nonneg.mpr hLog)
    nlinarith
  have hmrSq : (m : ℝ) ^ 2 * r ^ 2 = 1 := by
    calc
      _ = ((m : ℝ) * r) ^ 2 := by ring
      _ = 1 := by rw [hmr]; norm_num
  have hNR : 8 * Real.log (n : ℝ) ≤ (n : ℝ) * r ^ 2 := by
    calc
      _ = ((m : ℝ) ^ 2 * r ^ 2) * (8 * Real.log n) := by rw [hmrSq]; ring
      _ = ((m : ℝ) ^ 2 * (8 * Real.log n)) * r ^ 2 := by ring
      _ ≤ (n : ℝ) * r ^ 2 := mul_le_mul_of_nonneg_right hBudget (sq_nonneg r)
  have hOccExp : Real.exp (-(n : ℝ) * r ^ 2 / 2) ≤ 1 / (n : ℝ) ^ 4 := by
    calc
      _ ≤ Real.exp (-(4 * Real.log n)) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := exp_neg_nat_log hnPos 4
  have hJointExp : Real.exp (-2 * (n : ℝ) * r ^ 2) ≤ 1 / (n : ℝ) ^ 16 := by
    calc
      _ ≤ Real.exp (-(16 * Real.log n)) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := exp_neg_nat_log hnPos 16
  have hSucc : (m : ℝ) + 1 ≤ 2 * m := by linarith
  have hSuccSq := pow_le_pow_left₀ (by positivity : 0 ≤ (m : ℝ) + 1) hSucc 2
  have hCoeff : 2 * ((m : ℝ) + 1) ^ 2 ≤ 8 * (m : ℝ) ^ 2 := by nlinarith only [hSuccSq]
  have hOcc : (m : ℝ) ^ 2 * Real.exp (-(n : ℝ) * r ^ 2 / 2) ≤ 1 / (8 * (n : ℝ) ^ 3) := by
    calc
      _ ≤ (m : ℝ) ^ 2 * (1 / (n : ℝ) ^ 4) := mul_le_mul_of_nonneg_left hOccExp (sq_nonneg _)
      _ ≤ ((n : ℝ) / 8) * (1 / (n : ℝ) ^ 4) := mul_le_mul_of_nonneg_right hmEight (by positivity)
      _ = _ := by field_simp [hnPos.ne']
  have hJoint : 2 * ((m : ℝ) + 1) ^ 2 * Real.exp (-2 * (n : ℝ) * r ^ 2) ≤
      1 / (n : ℝ) ^ 15 := by
    calc
      _ ≤ 8 * (m : ℝ) ^ 2 * (1 / (n : ℝ) ^ 16) :=
        mul_le_mul hCoeff hJointExp (Real.exp_nonneg _) (by positivity)
      _ ≤ 8 * ((n : ℝ) / 8) * (1 / (n : ℝ) ^ 16) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmEight (by norm_num)) (by positivity)
      _ = _ := by field_simp [hnPos.ne']
  have hMass : 2 * q * Real.exp (-(n : ℝ) * r ^ 2 / 2) ≤ 8 / (n : ℝ) ^ 3 := by
    calc
      _ ≤ 2 * (4 * n) * (1 / (n : ℝ) ^ 4) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hq (by norm_num)) hOccExp
          (Real.exp_nonneg _) (by positivity)
      _ = _ := by field_simp [hnPos.ne']; ring
  have hnEight : (8 : ℝ) ≤ n := by linarith
  have hCub := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 8) hnEight 3
  have hnTwo : (2 : ℝ) ≤ n := by linarith
  have hFifteen := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hnTwo 15
  norm_num at hCub hFifteen
  have hOccSmall : 1 / (8 * (n : ℝ) ^ 3) ≤ (1 / 4096 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) (by nlinarith only [hCub])
  have hJointSmall : 1 / (n : ℝ) ^ 15 ≤ (1 / 32768 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) hFifteen
  have hMassSmall : 8 / (n : ℝ) ^ 3 ≤ (1 / 64 : ℝ) :=
    (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) ^ 3)).mpr (by linarith only [hCub])
  linarith

theorem InDensityClass.degree_event_probability {rho : DiamondPoint → ℝ}
    (hK : InDensityClass rho) {n m : ℕ} (hn : 65536 ≤ n) (hm : 16 ≤ m) {r h : ℝ}
    (hr : 0 < r) (hmr : (m : ℝ) * r = 1) (hh0 : 0 ≤ h) (hh4 : h ≤ 4) (hSquare : h ^ 2 = r)
    (hmSq : (m : ℝ) ^ 2 ≤ n / (8 * Real.log n))
    {ι : Type*} [Fintype ι] (sets : ι → Set DiamondPoint)
    (hSets : ∀ i, MeasurableSet (sets i))
    (hp : ∀ i, (densityMeasure rho).real (sets i) ≤ 8 * h ^ 2)
    (hq : (Fintype.card ι : ℝ) ≤ 4 * n) :
    (19 / 20 : ℝ) ≤ (sampleMeasure rho n).real
      {sample | SampleGood rho m r sample ∧ ∀ i,
        |(pointsIn sample (sets i)).card / (n : ℝ) - (densityMeasure rho).real (sets i)| ≤
          4 * h ^ 3} := by
  have hProb := hK.sample_good_and_small_mass_probability (by omega : 0 < n)
    hr hmr sets hSets hh0 hh4 hp
  have hPow : h ^ 4 = r ^ 2 := by rw [show h ^ 4 = (h ^ 2) ^ 2 by ring, hSquare]
  rw [hPow] at hProb
  have hBudget := degree_event_failure_budget hn hm hmr hmSq hq
  linarith

#print axioms InDensityClass.sample_good_and_small_mass_probability
#print axioms degree_event_failure_budget
#print axioms InDensityClass.degree_event_probability

end QuantyraNullCone
