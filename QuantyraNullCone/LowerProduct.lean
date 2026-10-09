import QuantyraNullCone.LowerScale
import Mathlib.MeasureTheory.Integral.Pi

namespace QuantyraNullCone

open MeasureTheory

local instance : IsProbabilityMeasure diamondVolume := diamondVolume_probability

noncomputable def lowerBaseSample (n : ℕ) : Measure (Fin n → DiamondPoint) :=
  Measure.pi (fun _ => diamondVolume)

noncomputable def lowerLikelihood (h : ℝ) {n : ℕ} (x : Fin n → DiamondPoint) : ℝ :=
  ∏ i, lowerAlternative h (x i)

instance lowerBaseSample_probability (n : ℕ) : IsProbabilityMeasure (lowerBaseSample n) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => diamondVolume)))

theorem lower_flat_sample (n : ℕ) : sampleMeasure lowerFlat n = lowerBaseSample n := by
  have hFlat : densityMeasure lowerFlat = diamondVolume := by
    simp only [densityMeasure, lowerFlat, ENNReal.ofReal_one]
    exact withDensity_one
  simp only [sampleMeasure, hFlat, lowerBaseSample]

theorem lower_likelihood_nonneg {h : ℝ} (hh : 0 < h) (hSmall : h ≤ 1 / 2)
    {n : ℕ} (x : Fin n → DiamondPoint) : 0 ≤ lowerLikelihood h x := by
  apply Finset.prod_nonneg
  intro i _
  exact le_trans (by norm_num : (0 : ℝ) ≤ 1 / 2) (lower_alternative_bounds hh.le hSmall (x i)).1

theorem lower_likelihood_integrable {h : ℝ} (hh : 0 < h) (hSmall : h ≤ 1 / 2) (n : ℕ) :
    Integrable (lowerLikelihood h) (lowerBaseSample n) :=
  Integrable.fintype_prod (fun _ => (lower_alternative_in_class hh hSmall).integrable)

theorem lower_sample_withDensity {h : ℝ} (hh : 0 < h) (hSmall : h ≤ 1 / 2) (n : ℕ) :
    sampleMeasure (lowerAlternative h) n =
      (lowerBaseSample n).withDensity (fun x => ENNReal.ofReal (lowerLikelihood h x)) := by
  let hK := lower_alternative_in_class hh hSmall
  letI := hK.isProbabilityMeasure
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← ofReal_integral_eq_lintegral_ofReal (lower_likelihood_integrable hh hSmall n).restrict
      (Filter.Eventually.of_forall (lower_likelihood_nonneg hh hSmall))]
  change ENNReal.ofReal (∫ x, (∏ i, lowerAlternative h (x i))
    ∂(Measure.pi (fun _ : Fin n => diamondVolume)).restrict (Set.univ.pi s)) = _
  rw [Measure.restrict_pi_pi, integral_fintype_prod_eq_prod]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg_of_ae
    (ae_restrict_of_ae hK.nonneg_ae))]
  exact Finset.prod_congr rfl (fun i _ => (hK.densityMeasure_apply (hs i)).symm)

theorem lower_likelihood_integral {h : ℝ} (hh : 0 < h) (hSmall : h ≤ 1 / 2) (n : ℕ) :
    (∫ x, lowerLikelihood h x ∂lowerBaseSample n) = 1 := by
  unfold lowerLikelihood lowerBaseSample
  rw [integral_fintype_prod_eq_pow (lowerAlternative h),
    (lower_alternative_in_class hh hSmall).integral_eq_one, one_pow]

theorem lower_alternative_square_integrable (h : ℝ) :
    Integrable (fun p => lowerAlternative h p ^ 2) diamondVolume :=
  ((lower_alternative_smooth h).continuous.pow 2).continuousOn.integrableOn_compact diamond_isCompact

theorem lower_likelihood_square_integrable (h : ℝ) (n : ℕ) :
    Integrable (fun x => lowerLikelihood h x ^ 2) (lowerBaseSample n) := by
  simp only [lowerLikelihood, ← Finset.prod_pow]
  exact Integrable.fintype_prod (fun _ => lower_alternative_square_integrable h)

theorem normalized_square_integral {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ] {f : X → ℝ} (hf : Integrable f μ)
    (hf2 : Integrable (fun x => f x ^ 2) μ) (hMean : (∫ x, f x ∂μ) = 1) :
    (∫ x, (f x - 1) ^ 2 ∂μ) = (∫ x, f x ^ 2 ∂μ) - 1 := by
  have hEq : (fun x => (f x - 1) ^ 2) = (fun x => (f x ^ 2 - 2 * f x) + 1) := by
    funext x
    ring
  have hDiff : Integrable (fun x => f x ^ 2 - 2 * f x) μ := hf2.sub (hf.const_mul 2)
  rw [hEq, integral_add hDiff (integrable_const 1),
    integral_sub hf2 (hf.const_mul 2), integral_const_mul, hMean]
  simp only [integral_const, probReal_univ, one_smul, mul_one]
  ring

theorem lower_product_divergence_identity {h : ℝ} (hh : 0 < h) (hSmall : h ≤ 1 / 2) (n : ℕ) :
    (∫ x, (lowerLikelihood h x - 1) ^ 2 ∂lowerBaseSample n) =
      (1 + ∫ p, (lowerAlternative h p - 1) ^ 2 ∂diamondVolume) ^ n - 1 := by
  rw [normalized_square_integral (lower_likelihood_integrable hh hSmall n)
    (lower_likelihood_square_integrable h n) (lower_likelihood_integral hh hSmall n)]
  simp only [lowerLikelihood, ← Finset.prod_pow, lowerBaseSample]
  rw [integral_fintype_prod_eq_pow (fun p => lowerAlternative h p ^ 2), Fintype.card_fin]
  rw [normalized_square_integral (lower_alternative_in_class hh hSmall).integrable
    (lower_alternative_square_integrable h) (lower_alternative_in_class hh hSmall).integral_eq_one]
  congr 2
  ring

theorem lower_product_divergence_bound {h : ℝ} (hh : 0 < h) (hSmall : h ≤ 1 / 2) (n : ℕ) :
    (∫ x, (lowerLikelihood h x - 1) ^ 2 ∂lowerBaseSample n) ≤
      Real.exp ((n : ℝ) * Real.pi * h ^ 4 / 8) - 1 := by
  rw [lower_product_divergence_identity hh hSmall]
  have hNonneg : 0 ≤ ∫ p, (lowerAlternative h p - 1) ^ 2 ∂diamondVolume :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hSingle := lower_single_point_divergence_bound hh
  have hExp := Real.add_one_le_exp ((Real.pi / 8) * h ^ 4)
  have hBase : 1 + (∫ p, (lowerAlternative h p - 1) ^ 2 ∂diamondVolume) ≤
      Real.exp ((Real.pi / 8) * h ^ 4) := by linarith
  have hPow := pow_le_pow_left₀ (by linarith : 0 ≤ 1 +
    ∫ p, (lowerAlternative h p - 1) ^ 2 ∂diamondVolume) hBase n
  rw [← Real.exp_nat_mul] at hPow
  convert sub_le_sub_right hPow 1 using 1
  congr 2
  ring

#print axioms lower_flat_sample
#print axioms lower_likelihood_nonneg
#print axioms lower_likelihood_integrable
#print axioms lower_sample_withDensity
#print axioms lower_likelihood_integral
#print axioms lower_alternative_square_integrable
#print axioms lower_likelihood_square_integrable
#print axioms normalized_square_integral
#print axioms lower_product_divergence_identity
#print axioms lower_product_divergence_bound

end QuantyraNullCone
