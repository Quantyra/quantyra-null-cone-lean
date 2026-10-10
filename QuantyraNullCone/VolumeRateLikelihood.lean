import QuantyraNullCone.VolumeRateExperiment
import QuantyraNullCone.ConfoundingTime
import QuantyraNullCone.LowerDataProcessing

namespace QuantyraNullCone

open MeasureTheory

local instance : IsProbabilityMeasure diamondVolume := diamondVolume_probability

theorem retained_measure_one {X : Type*} [MeasurableSpace X] (mu : Measure X)
    [IsProbabilityMeasure mu] : retainedMeasure mu (fun _ => 1) = mu := by
  simp only [retainedMeasure, integral_const, probReal_univ, one_smul, div_one, ENNReal.ofReal_one]
  exact withDensity_one

noncomputable def calibrationLikelihood (epsilon : ℝ) {n : ℕ} (sample : Fin n → DiamondPoint) : ℝ :=
  ∏ i, calibrationDensity epsilon (sample i)

/-- Positivity is required only on the actual product support, not outside the diamond. -/
theorem calibration_likelihood_nonneg_ae {epsilon : ℝ} (he : 0 ≤ epsilon)
    (heSmall : epsilon ≤ 1/2) (n : ℕ) :
    0 ≤ᵐ[lowerBaseSample n] calibrationLikelihood epsilon := by
  have h := lower_flat_in_class.sample_ae_mem_diamond n
  rw [lower_flat_sample] at h
  filter_upwards [h] with sample hs
  apply Finset.prod_nonneg
  intro i _
  have hb := (calibration_density_bounds he (hs i)).1
  linarith

theorem calibration_likelihood_integrable {epsilon : ℝ} (he : 0 ≤ epsilon)
    (heSmall : epsilon ≤ 1/2) (n : ℕ) :
    Integrable (calibrationLikelihood epsilon) (lowerBaseSample n) :=
  Integrable.fintype_prod (fun _ => (calibration_density_in_class he heSmall).integrable)

theorem calibration_sample_withDensity {epsilon : ℝ} (he : 0 ≤ epsilon)
    (heSmall : epsilon ≤ 1/2) (n : ℕ) :
    sampleMeasure (calibrationDensity epsilon) n =
      (lowerBaseSample n).withDensity (fun sample => ENNReal.ofReal (calibrationLikelihood epsilon sample)) := by
  let hK := calibration_density_in_class he heSmall
  letI := hK.isProbabilityMeasure
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← ofReal_integral_eq_lintegral_ofReal (calibration_likelihood_integrable he heSmall n).restrict
      (ae_restrict_of_ae (calibration_likelihood_nonneg_ae he heSmall n))]
  change ENNReal.ofReal (∫ x, (∏ i, calibrationDensity epsilon (x i))
    ∂(Measure.pi (fun _ : Fin n => diamondVolume)).restrict (Set.univ.pi s)) = _
  rw [Measure.restrict_pi_pi, integral_fintype_prod_eq_prod]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg_of_ae
    (ae_restrict_of_ae hK.nonneg_ae))]
  exact Finset.prod_congr rfl (fun i _ => (hK.densityMeasure_apply (hs i)).symm)

theorem calibration_likelihood_integral {epsilon : ℝ} (he : 0 ≤ epsilon)
    (heSmall : epsilon ≤ 1/2) (n : ℕ) :
    (∫ x, calibrationLikelihood epsilon x ∂lowerBaseSample n) = 1 := by
  unfold calibrationLikelihood lowerBaseSample
  rw [integral_fintype_prod_eq_pow (calibrationDensity epsilon),
    (calibration_density_in_class he heSmall).integral_eq_one, one_pow]

theorem calibration_density_square_integrable (epsilon : ℝ) :
    Integrable (fun p => calibrationDensity epsilon p ^ 2) diamondVolume :=
  ((calibration_density_smooth epsilon).continuous.pow 2).continuousOn.integrableOn_compact diamond_isCompact

theorem calibration_likelihood_square_integrable (epsilon : ℝ) (n : ℕ) :
    Integrable (fun x => calibrationLikelihood epsilon x ^ 2) (lowerBaseSample n) := by
  simp only [calibrationLikelihood, ← Finset.prod_pow]
  exact Integrable.fintype_prod (fun _ => calibration_density_square_integrable epsilon)

theorem calibration_single_point_divergence (epsilon : ℝ) :
    (∫ p, (calibrationDensity epsilon p - 1)^2 ∂diamondVolume) = epsilon^2/9 := by
  have hf : (fun p : DiamondPoint => (calibrationDensity epsilon p-1)^2) =
      (fun p => epsilon^2 * (calibrationProfile p.1^2 * calibrationProfile p.2^2)) := by
    funext p
    unfold calibrationDensity
    ring
  have hm : diamondVolume =
      ((volume : Measure ℝ).restrict (Set.Icc 0 1)).prod (volume.restrict (Set.Icc 0 1)) := by
    rw [Measure.prod_restrict]
    rfl
  rw [hf, integral_const_mul, hm,
    integral_prod_mul (fun x : ℝ => calibrationProfile x^2) (fun x : ℝ => calibrationProfile x^2),
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), calibration_profile_square_integral]
  ring

theorem calibration_product_divergence {epsilon : ℝ} (he : 0 ≤ epsilon)
    (heSmall : epsilon ≤ 1/2) (n : ℕ) :
    (∫ x, (calibrationLikelihood epsilon x-1)^2 ∂lowerBaseSample n) =
      (1+epsilon^2/9)^n-1 := by
  rw [normalized_square_integral (calibration_likelihood_integrable he heSmall n)
    (calibration_likelihood_square_integrable epsilon n) (calibration_likelihood_integral he heSmall n)]
  simp only [calibrationLikelihood, ← Finset.prod_pow, lowerBaseSample]
  rw [integral_fintype_prod_eq_pow (fun p => calibrationDensity epsilon p^2), Fintype.card_fin]
  have h := normalized_square_integral (calibration_density_in_class he heSmall).integrable
    (calibration_density_square_integrable epsilon) (calibration_density_in_class he heSmall).integral_eq_one
  rw [calibration_single_point_divergence] at h
  have hs : (∫ p, calibrationDensity epsilon p^2 ∂diamondVolume) = 1+epsilon^2/9 := by linarith
  rw [hs]

theorem calibration_central_square_integrable {epsilon : ℝ} (he : 0 ≤ epsilon)
    (heSmall : epsilon ≤ 1/2) (n : ℕ) :
    Integrable (fun x => (calibrationLikelihood epsilon x-1)^2) (lowerBaseSample n) := by
  have hf : (fun x : Fin n → DiamondPoint => (calibrationLikelihood epsilon x-1)^2) =
      (fun x => (calibrationLikelihood epsilon x^2 - 2*calibrationLikelihood epsilon x)+1) := by
    funext x
    ring
  rw [hf]
  exact ((calibration_likelihood_square_integrable epsilon n).sub
    ((calibration_likelihood_integrable he heSmall n).const_mul 2)).add (integrable_const 1)

theorem calibration_sample_real_apply {epsilon : ℝ} (he : 0 ≤ epsilon)
    (heSmall : epsilon ≤ 1/2) (n : ℕ) {S : Set (Fin n → DiamondPoint)} (hS : MeasurableSet S) :
    (sampleMeasure (calibrationDensity epsilon) n).real S =
      ∫ x in S, calibrationLikelihood epsilon x ∂lowerBaseSample n := by
  rw [measureReal_def, calibration_sample_withDensity he heSmall n, withDensity_apply _ hS,
    ← ofReal_integral_eq_lintegral_ofReal (calibration_likelihood_integrable he heSmall n).restrict
      (ae_restrict_of_ae (calibration_likelihood_nonneg_ae he heSmall n)), ENNReal.toReal_ofReal]
  exact integral_nonneg_of_ae (ae_restrict_of_ae (calibration_likelihood_nonneg_ae he heSmall n))

end QuantyraNullCone
