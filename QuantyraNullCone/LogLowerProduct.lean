import QuantyraNullCone.LogLowerTesting

namespace QuantyraNullCone

open MeasureTheory

local instance : IsProbabilityMeasure diamondVolume := diamondVolume_probability

noncomputable def logLowerLikelihood (h c : ℝ) {n : ℕ} (x : Fin n → DiamondPoint) : ℝ :=
  ∏ i, logLowerAlternative h c (x i)

theorem log_lower_likelihood_nonneg {h : ℝ} (hh : 0 < h) (hSmall : h ≤ 1/16)
    (c : ℝ) {n : ℕ} (x : Fin n → DiamondPoint) : 0 ≤ logLowerLikelihood h c x := by
  apply Finset.prod_nonneg
  intro i _
  exact le_trans (by norm_num : (0:ℝ) ≤ 1/2) (log_lower_alternative_bounds hh hSmall c (x i)).1

theorem log_lower_likelihood_integrable {h : ℝ} (hh : 0 < h) (hSmall : h ≤ 1/16)
    (c : ℝ) (n : ℕ) : Integrable (logLowerLikelihood h c) (lowerBaseSample n) :=
  Integrable.fintype_prod (fun _ => (log_lower_alternative_in_class hh hSmall c).integrable)

theorem log_lower_alternative_square_integrable (h c : ℝ) :
    Integrable (fun p => logLowerAlternative h c p^2) diamondVolume :=
  ((log_lower_alternative_smooth h c).continuous.pow 2).continuousOn.integrableOn_compact diamond_isCompact

theorem log_lower_likelihood_square_integrable (h c : ℝ) (n : ℕ) :
    Integrable (fun x => logLowerLikelihood h c x^2) (lowerBaseSample n) := by
  simp only [logLowerLikelihood,← Finset.prod_pow]
  exact Integrable.fintype_prod (fun _ => log_lower_alternative_square_integrable h c)

theorem log_lower_sample_withDensity {h : ℝ} (hh : 0 < h) (hSmall : h ≤ 1/16)
    (c : ℝ) (n : ℕ) : sampleMeasure (logLowerAlternative h c) n =
      (lowerBaseSample n).withDensity (fun x => ENNReal.ofReal (logLowerLikelihood h c x)) := by
  let hK := log_lower_alternative_in_class hh hSmall c
  letI := hK.isProbabilityMeasure
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← ofReal_integral_eq_lintegral_ofReal (log_lower_likelihood_integrable hh hSmall c n).restrict
      (Filter.Eventually.of_forall (log_lower_likelihood_nonneg hh hSmall c))]
  change ENNReal.ofReal (∫ x, (∏ i, logLowerAlternative h c (x i))
    ∂(Measure.pi (fun _ : Fin n => diamondVolume)).restrict (Set.univ.pi s)) = _
  rw [Measure.restrict_pi_pi,integral_fintype_prod_eq_prod]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg_of_ae
    (ae_restrict_of_ae hK.nonneg_ae))]
  exact Finset.prod_congr rfl (fun i _ => (hK.densityMeasure_apply (hs i)).symm)

theorem log_lower_product_second_moment {h : ℝ} (hh : 0 < h) (hSmall : h ≤ 1/16)
    (c : ℝ) (n : ℕ) :
    (∫ x, logLowerLikelihood h c x^2 ∂lowerBaseSample n) ≤ Real.exp ((n:ℝ)*h^4/4) := by
  have hK := log_lower_alternative_in_class hh hSmall c
  have hVariance := normalized_square_integral hK.integrable
    (log_lower_alternative_square_integrable h c) hK.integral_eq_one
  have hMoment := log_lower_single_moment hh c
  have hBase : (∫ p, logLowerAlternative h c p^2 ∂diamondVolume) ≤ Real.exp (h^4/4) := by
    linarith [Real.add_one_le_exp (h^4/4)]
  have hPow := pow_le_pow_left₀ (integral_nonneg (fun _ => sq_nonneg _)) hBase n
  simp only [logLowerLikelihood,← Finset.prod_pow,lowerBaseSample]
  rw [integral_fintype_prod_eq_pow (fun p => logLowerAlternative h c p^2),Fintype.card_fin]
  rw [← Real.exp_nat_mul] at hPow
  convert hPow using 1
  congr 1
  ring

theorem log_lower_seed_real_apply {h : ℝ} (hh : 0 < h) (hSmall : h ≤ 1/16)
    (c : ℝ) (n : ℕ) {Ω : Type*} [MeasurableSpace Ω]
    (ξ : Measure Ω) [IsProbabilityMeasure ξ]
    {S : Set ((Fin n → DiamondPoint) × Ω)} (hS : MeasurableSet S) :
    ((sampleMeasure (logLowerAlternative h c) n).prod ξ).real S =
      ∫ z in S, logLowerLikelihood h c z.1 ∂((lowerBaseSample n).prod ξ) := by
  have hi := log_lower_likelihood_integrable hh hSmall c n
  rw [measureReal_def,log_lower_sample_withDensity hh hSmall c n,
    prod_withDensity_left₀ hi.aestronglyMeasurable.aemeasurable.ennreal_ofReal,
    withDensity_apply _ hS,
    ← ofReal_integral_eq_lintegral_ofReal (hi.comp_fst ξ).restrict
      (Filter.Eventually.of_forall (fun z => log_lower_likelihood_nonneg hh hSmall c z.1)),
    ENNReal.toReal_ofReal]
  exact integral_nonneg (fun z => log_lower_likelihood_nonneg hh hSmall c z.1)

theorem log_lower_seed_second_moment {h : ℝ} (hh : 0 < h) (hSmall : h ≤ 1/16)
    (c : ℝ) (n : ℕ) {Ω : Type*} [MeasurableSpace Ω]
    (ξ : Measure Ω) [IsProbabilityMeasure ξ] :
    (∫ z, logLowerLikelihood h c z.1^2 ∂((lowerBaseSample n).prod ξ)) ≤
      Real.exp ((n:ℝ)*h^4/4) := by
  rw [integral_fun_fst (fun x : Fin n → DiamondPoint => logLowerLikelihood h c x^2),
    probReal_univ,one_smul]
  exact log_lower_product_second_moment hh hSmall c n

#print axioms log_lower_likelihood_nonneg
#print axioms log_lower_likelihood_integrable
#print axioms log_lower_alternative_square_integrable
#print axioms log_lower_likelihood_square_integrable
#print axioms log_lower_sample_withDensity
#print axioms log_lower_product_second_moment
#print axioms log_lower_seed_real_apply
#print axioms log_lower_seed_second_moment

end QuantyraNullCone
