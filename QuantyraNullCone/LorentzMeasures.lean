import QuantyraNullCone.LorentzDiamond
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic.Linarith

namespace QuantyraNullCone

open MeasureTheory

theorem lorentz_norm_sq3 (p : LorentzPoint3) : ‖p‖ ^ 2 = p 0 ^ 2 + spatialSquared3 p := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [Fin.sum_univ_succ, spatialSquared3]

theorem closed_lorentz_diamond_subset_ball3 :
    closedLorentzDiamond3 ⊆ Metric.closedBall (0 : LorentzPoint3) 1 := by
  intro p hp
  change |p 0| + spatialRadius3 p ≤ 1 at hp
  have hNonneg := add_nonneg (abs_nonneg (p 0)) (spatial_radius_nonneg3 p)
  have hSquare := (sq_le_sq₀ hNonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr hp
  have hCross : 0 ≤ 2 * |p 0| * spatialRadius3 p :=
    mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg _)) (spatial_radius_nonneg3 p)
  have hNorm : ‖p‖ ^ 2 ≤ (1 : ℝ) ^ 2 := by
    rw [lorentz_norm_sq3]
    nlinarith [sq_abs (p 0), spatial_radius_sq3 p]
  change dist p 0 ≤ 1
  rw [dist_zero_right]
  exact (sq_le_sq₀ (norm_nonneg p) (by norm_num : (0 : ℝ) ≤ 1)).mp hNorm

theorem isCompact_closedLorentzDiamond3 : IsCompact closedLorentzDiamond3 :=
  (isCompact_closedBall (0 : LorentzPoint3) 1).of_isClosed_subset
    isClosed_closedLorentzDiamond3 closed_lorentz_diamond_subset_ball3

theorem lorentz_volume_pos3 : 0 < lorentzVolume3 := by
  unfold lorentzVolume3
  positivity

theorem flat_diamond3_ae_mem : ∀ᵐ p ∂flatDiamondMeasure3, p ∈ closedLorentzDiamond3 := by
  have hMem : ∀ᵐ p ∂(volume : Measure LorentzPoint3).restrict lorentzDiamond3,
      p ∈ closedLorentzDiamond3 :=
    (ae_restrict_mem isOpen_lorentzDiamond3.measurableSet).mono
      (fun _ hp => lorentz_diamond_subset_closed3 hp)
  exact Measure.ae_smul_measure hMem _

theorem InDensityClass3.continuousOn {rho : LorentzPoint3 → ℝ} (h : InDensityClass3 rho) :
    ContinuousOn rho closedLorentzDiamond3 := by
  obtain ⟨U, _hOpen, hSubset, hSmooth⟩ := h.smoothNeighborhood
  exact hSmooth.continuousOn.mono hSubset

theorem InDensityClass3.integrable {rho : LorentzPoint3 → ℝ} (h : InDensityClass3 rho) :
    Integrable rho flatDiamondMeasure3 := by
  have hInt : IntegrableOn rho closedLorentzDiamond3 (volume : Measure LorentzPoint3) :=
    h.continuousOn.integrableOn_compact isCompact_closedLorentzDiamond3
  have hD := hInt.mono_set lorentz_diamond_subset_closed3
  change Integrable rho ((ENNReal.ofReal lorentzVolume3)⁻¹ •
    (volume : Measure LorentzPoint3).restrict lorentzDiamond3)
  exact hD.smul_measure (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr lorentz_volume_pos3))

theorem InDensityClass3.densityMeasure_univ {rho : LorentzPoint3 → ℝ} (h : InDensityClass3 rho) :
    densityMeasure3 rho Set.univ = 1 := by
  have hNonneg : 0 ≤ᵐ[flatDiamondMeasure3] rho :=
    flat_diamond3_ae_mem.mono (fun p hp => (by norm_num : (0 : ℝ) ≤ 1 / 2).trans (h.bounds p hp).1)
  rw [densityMeasure3, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal h.integrable hNonneg, h.normalized, ENNReal.ofReal_one]

theorem InDensityClass3.isProbabilityMeasure {rho : LorentzPoint3 → ℝ} (h : InDensityClass3 rho) :
    IsProbabilityMeasure (densityMeasure3 rho) := ⟨h.densityMeasure_univ⟩

theorem InDensityClass3.sample_isProbabilityMeasure {rho : LorentzPoint3 → ℝ}
    (h : InDensityClass3 rho) (n : ℕ) : IsProbabilityMeasure (sampleMeasure3 rho n) := by
  letI : IsProbabilityMeasure (densityMeasure3 rho) := h.isProbabilityMeasure
  unfold sampleMeasure3
  infer_instance

theorem InDensityClass3.orderLaw_isProbabilityMeasure {rho : LorentzPoint3 → ℝ}
    (h : InDensityClass3 rho) (n : ℕ) : IsProbabilityMeasure (orderLaw3 rho n) := by
  letI : IsProbabilityMeasure (sampleMeasure3 rho n) := h.sample_isProbabilityMeasure n
  exact Measure.isProbabilityMeasure_map (sampledOrder3_measurable n).aemeasurable

#print axioms lorentz_norm_sq3
#print axioms isCompact_closedLorentzDiamond3
#print axioms flat_diamond3_ae_mem
#print axioms InDensityClass3.integrable
#print axioms InDensityClass3.densityMeasure_univ
#print axioms InDensityClass3.orderLaw_isProbabilityMeasure

end QuantyraNullCone
