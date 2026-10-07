import QuantyraNullCone.Measures

namespace QuantyraNullCone

open MeasureTheory

theorem InDensityClass.nonneg_ae {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) : 0 ≤ᵐ[diamondVolume] rho :=
  (ae_restrict_mem diamond_measurableSet).mono fun p hp =>
    le_trans (by norm_num : (0 : ℝ) ≤ 1 / 2) (h.bounds p hp).1

theorem InDensityClass.densityMeasure_apply {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) {S : Set DiamondPoint} (hS : MeasurableSet S) :
    densityMeasure rho S = ENNReal.ofReal (∫ p in S, rho p ∂diamondVolume) := by
  rw [densityMeasure, withDensity_apply _ hS,
    ← ofReal_integral_eq_lintegral_ofReal h.integrable.restrict
      (ae_restrict_of_ae h.nonneg_ae)]

theorem InDensityClass.densityMeasure_real_apply {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) {S : Set DiamondPoint} (hS : MeasurableSet S) :
    (densityMeasure rho S).toReal = ∫ p in S, rho p ∂diamondVolume := by
  rw [h.densityMeasure_apply hS, ENNReal.toReal_ofReal]
  exact integral_nonneg_of_ae (ae_restrict_of_ae h.nonneg_ae)

theorem InDensityClass.densityMeasure_apply_subset {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) {S : Set DiamondPoint} (hS : MeasurableSet S)
    (hSub : S ⊆ diamond) :
    densityMeasure rho S = ENNReal.ofReal
      (∫ p in S, rho p ∂(volume : Measure ℝ).prod volume) := by
  rw [h.densityMeasure_apply hS, diamondVolume, Measure.restrict_restrict_of_subset hSub]

theorem densityMeasure_inter_diamond (rho : DiamondPoint → ℝ)
    {S : Set DiamondPoint} (hS : MeasurableSet S) :
    densityMeasure rho S = densityMeasure rho (S ∩ diamond) := by
  rw [densityMeasure, diamondVolume, ← restrict_withDensity diamond_measurableSet]
  rw [Measure.restrict_apply hS, Measure.restrict_apply (hS.inter diamond_measurableSet)]
  simp only [Set.inter_assoc, Set.inter_self]

theorem InDensityClass.uProduct_mass {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) {S : Set ℝ} (hS : MeasurableSet S)
    (hSub : S ⊆ Set.Icc (0 : ℝ) 1) :
    densityMeasure rho (S ×ˢ Set.Icc (0 : ℝ) 1) = volume S := by
  have hProd : S ×ˢ Set.Icc (0 : ℝ) 1 ⊆ diamond := by
    rintro p ⟨hp, hq⟩
    exact ⟨hSub hp, hq⟩
  have hInt : IntegrableOn rho (S ×ˢ Set.Icc (0 : ℝ) 1)
      ((volume : Measure ℝ).prod volume) :=
    (show IntegrableOn rho diamond ((volume : Measure ℝ).prod volume) from
      h.integrable).mono_set hProd
  rw [h.densityMeasure_apply_subset (hS.prod measurableSet_Icc) hProd,
    setIntegral_prod rho hInt]
  have hInner : ∀ u ∈ S, (∫ v in Set.Icc (0 : ℝ) 1, rho (u, v)) = 1 := by
    intro u hu
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact h.marginalU u (hSub hu)
  rw [setIntegral_congr_fun hS hInner, setIntegral_const]
  simp only [smul_eq_mul, mul_one, Measure.real]
  apply ENNReal.ofReal_toReal
  exact ne_top_of_le_ne_top (by simp) (measure_mono hSub)

theorem InDensityClass.vProduct_mass {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) {T : Set ℝ} (hT : MeasurableSet T)
    (hSub : T ⊆ Set.Icc (0 : ℝ) 1) :
    densityMeasure rho (Set.Icc (0 : ℝ) 1 ×ˢ T) = volume T := by
  have hProd : Set.Icc (0 : ℝ) 1 ×ˢ T ⊆ diamond := by
    rintro p ⟨hp, hq⟩
    exact ⟨hp, hSub hq⟩
  have hInt : Integrable rho
      (((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)).prod
        ((volume : Measure ℝ).restrict T)) := by
    rw [Measure.prod_restrict]
    exact (show IntegrableOn rho diamond ((volume : Measure ℝ).prod volume) from
      h.integrable).mono_set hProd
  rw [h.densityMeasure_apply_subset (measurableSet_Icc.prod hT) hProd,
    ← Measure.prod_restrict, integral_prod_symm rho hInt]
  have hInner : ∀ v ∈ T, (∫ u in Set.Icc (0 : ℝ) 1, rho (u, v)) = 1 := by
    intro v hv
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact h.marginalV v (hSub hv)
  rw [setIntegral_congr_fun hT hInner, setIntegral_const]
  simp only [smul_eq_mul, mul_one, Measure.real]
  apply ENNReal.ofReal_toReal
  exact ne_top_of_le_ne_top (by simp) (measure_mono hSub)

theorem InDensityClass.uMarginal_mass {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) {S : Set ℝ} (hS : MeasurableSet S) :
    densityMeasure rho (Prod.fst ⁻¹' S) = volume (S ∩ Set.Icc (0 : ℝ) 1) := by
  rw [densityMeasure_inter_diamond rho (hS.preimage measurable_fst)]
  have hSet : (Prod.fst ⁻¹' S) ∩ diamond =
      (S ∩ Set.Icc (0 : ℝ) 1) ×ˢ Set.Icc (0 : ℝ) 1 := by
    ext p
    simp only [diamond, Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod]
    exact and_assoc.symm
  rw [hSet]
  exact h.uProduct_mass (hS.inter measurableSet_Icc) Set.inter_subset_right

theorem InDensityClass.vMarginal_mass {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) {T : Set ℝ} (hT : MeasurableSet T) :
    densityMeasure rho (Prod.snd ⁻¹' T) = volume (T ∩ Set.Icc (0 : ℝ) 1) := by
  rw [densityMeasure_inter_diamond rho (hT.preimage measurable_snd)]
  have hSet : (Prod.snd ⁻¹' T) ∩ diamond =
      Set.Icc (0 : ℝ) 1 ×ˢ (T ∩ Set.Icc (0 : ℝ) 1) := by
    ext p
    change (p.2 ∈ T ∧ (p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.2 ∈ Set.Icc (0 : ℝ) 1)) ↔
      (p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ (p.2 ∈ T ∧ p.2 ∈ Set.Icc (0 : ℝ) 1))
    tauto
  rw [hSet]
  exact h.vProduct_mass (hT.inter measurableSet_Icc) Set.inter_subset_right

def cdfRegion (s t : ℝ) : Set DiamondPoint := {p | p.1 ≤ s ∧ p.2 ≤ t}

theorem cdfRegion_measurableSet (s t : ℝ) : MeasurableSet (cdfRegion s t) :=
  (measurableSet_le measurable_fst measurable_const).inter
    (measurableSet_le measurable_snd measurable_const)

theorem abs_real_mass_sub_le_of_subset {μ : Measure DiamondPoint}
    [IsFiniteMeasure μ] {A B S : Set DiamondPoint} (hA : MeasurableSet A)
    (hSub : A ⊆ B) (hDiff : B \ A ⊆ S) : |μ.real A - μ.real B| ≤ μ.real S := by
  have hAdd := measureReal_inter_add_diff (μ := μ) (s := B) hA
  rw [Set.inter_eq_right.mpr hSub] at hAdd
  have hMono : μ.real A ≤ μ.real B := measureReal_mono hSub
  have hBound : μ.real (B \ A) ≤ μ.real S := measureReal_mono hDiff
  rw [abs_of_nonpos (sub_nonpos.mpr hMono)]
  linarith

theorem InDensityClass.uInterval_mass_le {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) {s s' : ℝ} (hss' : s ≤ s') :
    (densityMeasure rho).real (Prod.fst ⁻¹' Set.Ioc s s') ≤ s' - s := by
  rw [Measure.real, h.uMarginal_mass measurableSet_Ioc]
  calc
    (volume (Set.Ioc s s' ∩ Set.Icc (0 : ℝ) 1)).toReal
        ≤ (volume (Set.Ioc s s')).toReal :=
      ENNReal.toReal_mono (by simp) (measure_mono Set.inter_subset_left)
    _ = s' - s := by simp [Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr hss')]

theorem InDensityClass.vInterval_mass_le {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) {t t' : ℝ} (htt' : t ≤ t') :
    (densityMeasure rho).real (Prod.snd ⁻¹' Set.Ioc t t') ≤ t' - t := by
  rw [Measure.real, h.vMarginal_mass measurableSet_Ioc]
  calc
    (volume (Set.Ioc t t' ∩ Set.Icc (0 : ℝ) 1)).toReal
        ≤ (volume (Set.Ioc t t')).toReal :=
      ENNReal.toReal_mono (by simp) (measure_mono Set.inter_subset_left)
    _ = t' - t := by simp [Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr htt')]

theorem InDensityClass.populationCDF_u_step {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) {s s' : ℝ} (hss' : s ≤ s') (t : ℝ) :
    |populationCDF rho s t - populationCDF rho s' t| ≤ s' - s := by
  letI := h.isProbabilityMeasure
  have hSub : cdfRegion s t ⊆ cdfRegion s' t := fun _ hp => ⟨hp.1.trans hss', hp.2⟩
  have hDiff : cdfRegion s' t \ cdfRegion s t ⊆ Prod.fst ⁻¹' Set.Ioc s s' := by
    rintro p ⟨hp, hn⟩
    have hs : s < p.1 := by
      by_contra hNot
      exact hn ⟨le_of_not_gt hNot, hp.2⟩
    exact ⟨hs, hp.1⟩
  exact (abs_real_mass_sub_le_of_subset (cdfRegion_measurableSet s t) hSub hDiff).trans
    (h.uInterval_mass_le hss')

theorem InDensityClass.populationCDF_v_step {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) (s : ℝ) {t t' : ℝ} (htt' : t ≤ t') :
    |populationCDF rho s t - populationCDF rho s t'| ≤ t' - t := by
  letI := h.isProbabilityMeasure
  have hSub : cdfRegion s t ⊆ cdfRegion s t' := fun _ hp => ⟨hp.1, hp.2.trans htt'⟩
  have hDiff : cdfRegion s t' \ cdfRegion s t ⊆ Prod.snd ⁻¹' Set.Ioc t t' := by
    rintro p ⟨hp, hn⟩
    have ht : t < p.2 := by
      by_contra hNot
      exact hn ⟨hp.1, le_of_not_gt hNot⟩
    exact ⟨ht, hp.2⟩
  exact (abs_real_mass_sub_le_of_subset (cdfRegion_measurableSet s t) hSub hDiff).trans
    (h.vInterval_mass_le htt')

theorem InDensityClass.populationCDF_u_lipschitz {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) (s s' t : ℝ) :
    |populationCDF rho s t - populationCDF rho s' t| ≤ |s - s'| := by
  rcases le_total s s' with hle | hle
  · simpa [abs_of_nonpos (sub_nonpos.mpr hle)] using h.populationCDF_u_step hle t
  · simpa only [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hle)] using
      h.populationCDF_u_step hle t

theorem InDensityClass.populationCDF_v_lipschitz {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) (s t t' : ℝ) :
    |populationCDF rho s t - populationCDF rho s t'| ≤ |t - t'| := by
  rcases le_total t t' with hle | hle
  · simpa [abs_of_nonpos (sub_nonpos.mpr hle)] using h.populationCDF_v_step s hle
  · simpa only [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hle)] using
      h.populationCDF_v_step s hle

theorem InDensityClass.populationCDF_thresholdStability {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) (s t s' t' : ℝ) :
    |populationCDF rho s t - populationCDF rho s' t'| ≤ |s - s'| + |t - t'| := by
  calc
    |populationCDF rho s t - populationCDF rho s' t'|
        ≤ |populationCDF rho s t - populationCDF rho s' t| +
          |populationCDF rho s' t - populationCDF rho s' t'| := abs_sub_le _ _ _
    _ ≤ |s - s'| + |t - t'| := add_le_add
      (h.populationCDF_u_lipschitz s s' t) (h.populationCDF_v_lipschitz s' t t')

theorem InDensityClass.populationCDF_u_one {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    populationCDF rho s 1 = s := by
  have hRegion : cdfRegion s 1 ∩ diamond = (Prod.fst ⁻¹' Set.Iic s) ∩ diamond := by
    ext p
    change ((p.1 ≤ s ∧ p.2 ≤ 1) ∧
      ((0 ≤ p.1 ∧ p.1 ≤ 1) ∧ (0 ≤ p.2 ∧ p.2 ≤ 1))) ↔
      (p.1 ≤ s ∧ ((0 ≤ p.1 ∧ p.1 ≤ 1) ∧ (0 ≤ p.2 ∧ p.2 ≤ 1)))
    tauto
  have hInter : Set.Iic s ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 s := by
    ext x
    change (x ≤ s ∧ (0 ≤ x ∧ x ≤ 1)) ↔ (0 ≤ x ∧ x ≤ s)
    constructor
    · tauto
    · rintro ⟨hx0, hxs⟩
      exact ⟨hxs, hx0, hxs.trans hs1⟩
  change (densityMeasure rho (cdfRegion s 1)).toReal = s
  rw [densityMeasure_inter_diamond rho (cdfRegion_measurableSet s 1), hRegion,
    ← densityMeasure_inter_diamond rho (measurableSet_Iic.preimage measurable_fst),
    h.uMarginal_mass measurableSet_Iic, hInter]
  simp [Real.volume_Icc, hs0]

theorem InDensityClass.populationCDF_one_v {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    populationCDF rho 1 t = t := by
  have hRegion : cdfRegion 1 t ∩ diamond = (Prod.snd ⁻¹' Set.Iic t) ∩ diamond := by
    ext p
    change ((p.1 ≤ 1 ∧ p.2 ≤ t) ∧
      ((0 ≤ p.1 ∧ p.1 ≤ 1) ∧ (0 ≤ p.2 ∧ p.2 ≤ 1))) ↔
      (p.2 ≤ t ∧ ((0 ≤ p.1 ∧ p.1 ≤ 1) ∧ (0 ≤ p.2 ∧ p.2 ≤ 1)))
    tauto
  have hInter : Set.Iic t ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 t := by
    ext x
    change (x ≤ t ∧ (0 ≤ x ∧ x ≤ 1)) ↔ (0 ≤ x ∧ x ≤ t)
    constructor
    · tauto
    · rintro ⟨hx0, hxt⟩
      exact ⟨hxt, hx0, hxt.trans ht1⟩
  change (densityMeasure rho (cdfRegion 1 t)).toReal = t
  rw [densityMeasure_inter_diamond rho (cdfRegion_measurableSet 1 t), hRegion,
    ← densityMeasure_inter_diamond rho (measurableSet_Iic.preimage measurable_snd),
    h.vMarginal_mass measurableSet_Iic, hInter]
  simp [Real.volume_Icc, ht0]

#print axioms InDensityClass.uMarginal_mass
#print axioms InDensityClass.vMarginal_mass
#print axioms InDensityClass.populationCDF_thresholdStability

end QuantyraNullCone
