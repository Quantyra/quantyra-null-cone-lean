import QuantyraNullCone.BernoulliMGF
import QuantyraNullCone.DegreeCells
import Mathlib.MeasureTheory.Integral.Pi

namespace QuantyraNullCone

open MeasureTheory ProbabilityTheory

/-- A two-sided finite-sample bound using the actual event mass. Its small-t
quadratic MGF bound is weaker than sharp Bernstein but keeps the final S032
rate and constants: the selected rectangle parameters give exponent -nr²/2. -/
theorem iid_indicator_chernoff {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ} (hn : 0 < n)
    {S : Set Ω} (hS : MeasurableSet S) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (eps : ℝ) :
    (Measure.pi (fun _ : Fin n => μ)).real {sample |
      eps ≤ |(∑ i : Fin n, S.indicator (fun _ => (1 : ℝ)) (sample i)) / n - μ.real S|} ≤
      2 * Real.exp ((n : ℝ) * μ.real S * t ^ 2 - (n : ℝ) * t * eps) := by
  classical
  let P := Measure.pi (fun _ : Fin n => μ)
  let Y : Ω → ℝ := S.indicator (fun _ => 1)
  let p := μ.real S
  let X (i : Fin n) (sample : Fin n → Ω) : ℝ := Y (sample i) - p
  have hY : Measurable Y := measurable_const.indicator hS
  have hMeas (i : Fin n) : Measurable (X i) := (hY.comp (measurable_pi_apply i)).sub_const p
  have hIndep : iIndepFun X P := iIndepFun_pi
    (X := fun _ : Fin n => fun q => Y q - p) (fun _ => (hY.sub_const p).aemeasurable)
  have hIntBase (z : ℝ) : Integrable (fun q => Real.exp (z * (Y q - p))) μ :=
    centered_indicator_exp_integrable hS p z
  have hInt (z : ℝ) : Integrable (fun sample => Real.exp (z * (∑ i : Fin n, X i sample))) P := by
    simpa only [Finset.sum_apply] using hIndep.integrable_exp_mul_sum (t := z) hMeas
      (s := Finset.univ) (fun i _ => integrable_comp_eval
        (μ := fun _ : Fin n => μ) (i := i) (hIntBase z))
  have hMGF (z : ℝ) (hz : |z| ≤ 1) :
      mgf (fun sample => ∑ i : Fin n, X i sample) P z ≤ Real.exp ((n : ℝ) * p * z ^ 2) := by
    have hEach (i : Fin n) : mgf (X i) P z ≤ Real.exp (p * z ^ 2) := by
      have hEq : mgf (X i) P z = mgf (fun q => Y q - p) μ z :=
        integral_comp_eval (μ := fun _ : Fin n => μ) (i := i) (hIntBase z).aestronglyMeasurable
      rw [hEq]
      exact centered_indicator_mgf_le hS hz
    rw [show (fun sample => ∑ i : Fin n, X i sample) = ∑ i : Fin n, X i by
      funext sample; simp only [Finset.sum_apply], hIndep.mgf_sum hMeas Finset.univ]
    calc
      _ ≤ ∏ _i : Fin n, Real.exp (p * z ^ 2) :=
        Finset.prod_le_prod (fun _ _ => mgf_nonneg) (fun i _ => hEach i)
      _ = Real.exp ((n : ℝ) * p * z ^ 2) := by
        rw [← Real.exp_sum]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        congr 1
        ring
  have htAbs : |t| ≤ 1 := by rwa [abs_of_nonneg ht0]
  have hUpper := (measure_ge_le_exp_mul_mgf (μ := P) ((n : ℝ) * eps) ht0 (hInt t)).trans
    (mul_le_mul_of_nonneg_left (hMGF t htAbs) (Real.exp_pos _).le)
  have hLower := (measure_le_le_exp_mul_mgf (μ := P) (-((n : ℝ) * eps))
    (neg_nonpos.mpr ht0) (hInt (-t))).trans
    (mul_le_mul_of_nonneg_left (hMGF (-t) (by simpa using htAbs)) (Real.exp_pos _).le)
  rw [← Real.exp_add] at hUpper hLower
  have hUExp : -t * ((n : ℝ) * eps) + (n : ℝ) * p * t ^ 2 =
      (n : ℝ) * p * t ^ 2 - (n : ℝ) * t * eps := by ring
  have hLExp : -(-t) * (-((n : ℝ) * eps)) + (n : ℝ) * p * (-t) ^ 2 =
      (n : ℝ) * p * t ^ 2 - (n : ℝ) * t * eps := by ring
  rw [hUExp] at hUpper
  rw [hLExp] at hLower
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hSum (sample : Fin n → Ω) :
      ∑ i : Fin n, X i sample = (n : ℝ) * ((∑ i : Fin n, Y (sample i)) / n - p) := by
    simp only [X, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp [hnR.ne']
  have hSub : {sample : Fin n → Ω | eps ≤ |(∑ i, Y (sample i)) / n - p|} ⊆
      {sample | (n : ℝ) * eps ≤ ∑ i, X i sample} ∪
      {sample | (∑ i, X i sample) ≤ -((n : ℝ) * eps)} := by
    intro sample hs
    have hAbs : (n : ℝ) * eps ≤ |∑ i, X i sample| := by
      rw [hSum, abs_mul, abs_of_nonneg hnR.le]
      exact mul_le_mul_of_nonneg_left hs hnR.le
    by_cases hSign : 0 ≤ ∑ i, X i sample
    · left
      rwa [abs_of_nonneg hSign] at hAbs
    · right
      change (∑ i, X i sample) ≤ -((n : ℝ) * eps)
      rw [abs_of_neg (lt_of_not_ge hSign)] at hAbs
      linarith
  calc
    _ ≤ P.real ({sample | (n : ℝ) * eps ≤ ∑ i, X i sample} ∪
        {sample | (∑ i, X i sample) ≤ -((n : ℝ) * eps)}) := measureReal_mono hSub
    _ ≤ P.real {sample | (n : ℝ) * eps ≤ ∑ i, X i sample} +
        P.real {sample | (∑ i, X i sample) ≤ -((n : ℝ) * eps)} := measureReal_union_le _ _
    _ ≤ 2 * Real.exp ((n : ℝ) * p * t ^ 2 - (n : ℝ) * t * eps) := by linarith

theorem InDensityClass.small_mass_count_concentration {rho : DiamondPoint → ℝ}
    (hK : InDensityClass rho) {n : ℕ} (hn : 0 < n)
    {S : Set DiamondPoint} (hS : MeasurableSet S) {h : ℝ}
    (hh0 : 0 ≤ h) (hh4 : h ≤ 4)
    (hp : (densityMeasure rho).real S ≤ 8 * h ^ 2) :
    (sampleMeasure rho n).real {sample |
      4 * h ^ 3 ≤ |(pointsIn sample S).card / (n : ℝ) - (densityMeasure rho).real S|} ≤
      2 * Real.exp (-(n : ℝ) * h ^ 4 / 2) := by
  classical
  letI : IsProbabilityMeasure (densityMeasure rho) := hK.isProbabilityMeasure
  have hc := iid_indicator_chernoff (μ := densityMeasure rho) hn hS
    (t := h / 4) (by positivity) (by linarith) (4 * h ^ 3)
  have hCount (sample : Fin n → DiamondPoint) :
      (∑ i : Fin n, S.indicator (fun _ => (1 : ℝ)) (sample i)) = (pointsIn sample S).card := by
    simp [pointsIn, Set.indicator_apply, Finset.sum_boole]
  simp_rw [hCount] at hc
  apply hc.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Real.exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ (n : ℝ) * (h / 4) ^ 2)
  nlinarith only [hm]

theorem InDensityClass.small_mass_family_failure {rho : DiamondPoint → ℝ}
    (hK : InDensityClass rho) {n : ℕ} (hn : 0 < n)
    {ι : Type*} [Fintype ι] (sets : ι → Set DiamondPoint)
    (hSets : ∀ i, MeasurableSet (sets i)) {h : ℝ} (hh0 : 0 ≤ h) (hh4 : h ≤ 4)
    (hp : ∀ i, (densityMeasure rho).real (sets i) ≤ 8 * h ^ 2) :
    (sampleMeasure rho n).real {sample | ∃ i,
      4 * h ^ 3 ≤ |(pointsIn sample (sets i)).card / (n : ℝ) -
        (densityMeasure rho).real (sets i)|} ≤
      2 * Fintype.card ι * Real.exp (-(n : ℝ) * h ^ 4 / 2) := by
  classical
  letI : IsProbabilityMeasure (sampleMeasure rho n) := hK.sample_isProbabilityMeasure n
  let bad (i : ι) := {sample : Fin n → DiamondPoint |
    4 * h ^ 3 ≤ |(pointsIn sample (sets i)).card / (n : ℝ) - (densityMeasure rho).real (sets i)|}
  calc
    _ = (sampleMeasure rho n).real (⋃ i, bad i) := by congr 1; ext sample; simp [bad]
    _ ≤ ∑ i : ι, (sampleMeasure rho n).real (bad i) := measureReal_iUnion_fintype_le bad
    _ ≤ ∑ _i : ι, 2 * Real.exp (-(n : ℝ) * h ^ 4 / 2) :=
      Finset.sum_le_sum fun i _ => hK.small_mass_count_concentration hn (hSets i) hh0 hh4 (hp i)
    _ = _ := by simp; ring

#print axioms iid_indicator_chernoff
#print axioms InDensityClass.small_mass_count_concentration
#print axioms InDensityClass.small_mass_family_failure

end QuantyraNullCone
