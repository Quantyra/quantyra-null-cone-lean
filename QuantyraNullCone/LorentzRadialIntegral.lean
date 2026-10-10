import QuantyraNullCone.LorentzTimeMoments
import Mathlib.MeasureTheory.Constructions.HaarToSphere

namespace QuantyraNullCone
open MeasureTheory Set
noncomputable section
set_option maxHeartbeats 1000000

/-- Actual two-dimensional Haar integration for a radial statistic on a spatial disk. -/
theorem integral_spatial_radial_ball3 (f : ℝ → ℝ) (R : ℝ) :
    (∫ z : SpatialPoint3 in Metric.ball 0 R, f ‖z‖) =
      (2*Real.pi) * ∫ r in Ioo 0 R, r*f r := by
  have he : (Metric.ball (0 : SpatialPoint3) R).indicator (fun z => f ‖z‖) =
      (fun z : SpatialPoint3 => (Iio R).indicator f ‖z‖) := by
    funext z
    simp only [indicator,Metric.mem_ball,dist_zero_right,mem_Iio]
  rw [← integral_indicator measurableSet_ball,he,integral_fun_norm_addHaar]
  have hv : (volume : Measure SpatialPoint3).real (Metric.ball 0 1) = Real.pi := by
    simp [Measure.real,EuclideanSpace.volume_ball_fin_two,Real.pi_pos.le]
  simp only [finrank_euclideanSpace, Fintype.card_fin, hv]
  norm_num only [Nat.reduceSub, pow_one, nsmul_eq_mul, smul_eq_mul]
  have hh : (∫ r in Ioi (0 : ℝ), r*((Iio R).indicator f r)) =
      ∫ r in Ioo 0 R, r*f r := by
    rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioo]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro r
    by_cases h0 : 0 < r <;> by_cases hR : r < R <;> simp [indicator,h0,hR]
  rw [hh]
  ring

theorem split_lorentz_diamond_preimage3 :
    splitLorentzEquiv3 ⁻¹' splitLorentzDiamond3 = lorentzDiamond3 := by
  ext p
  exact split_lorentz_diamond_mem3 p

/-- Fubini reduction through the genuine spatial disks, not an assumed radial sampling law. -/
theorem integral_flat_spatial3 {H : ℝ × SpatialPoint3 → ℝ} (hH : Continuous H) :
    (∫ p, H (splitLorentzEquiv3 p) ∂flatDiamondMeasure3) =
      lorentzVolume3⁻¹ * ∫ t, ∫ z in Metric.ball (0 : SpatialPoint3) (1-|t|), H (t,z) := by
  have hc : Continuous (fun p => H (splitLorentzEquiv3 p)) := by
    apply hH.comp
    change Continuous (fun p : LorentzPoint3 => (p 0, WithLp.toLp 2 (fun i : Fin 2 => p i.succ)))
    fun_prop
  have hi : IntegrableOn (fun p => H (splitLorentzEquiv3 p)) lorentzDiamond3
      (volume : Measure LorentzPoint3) :=
    (hc.continuousOn.integrableOn_compact isCompact_closedLorentzDiamond3).mono_set
      lorentz_diamond_subset_closed3
  have hj : IntegrableOn H splitLorentzDiamond3
      ((volume : Measure ℝ).prod (volume : Measure SpatialPoint3)) := by
    apply (split_lorentz_volume_preserving3.integrableOn_comp_preimage
      splitLorentzEquiv3.measurableEmbedding).mp
    simpa only [split_lorentz_diamond_preimage3,Function.comp_def] using hi
  rw [flatDiamondMeasure3, integral_smul_measure]
  simp only [ENNReal.toReal_inv,ENNReal.toReal_ofReal lorentz_volume_pos3.le,smul_eq_mul]
  congr 1
  rw [← split_lorentz_diamond_preimage3,
    split_lorentz_volume_preserving3.setIntegral_preimage_emb splitLorentzEquiv3.measurableEmbedding]
  change (∫ q in splitLorentzDiamond3, H q ∂(volume : Measure ℝ).prod volume) = _
  rw [← integral_indicator isOpen_splitLorentzDiamond3.measurableSet,
    integral_prod _ (hj.integrable_indicator isOpen_splitLorentzDiamond3.measurableSet)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  change (∫ z : SpatialPoint3, splitLorentzDiamond3.indicator H (t,z)) =
    ∫ z in Metric.ball (0 : SpatialPoint3) (1-|t|), H (t,z)
  rw [← integral_indicator measurableSet_ball]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  simp [splitLorentzDiamond3,indicator]

/-- Normalized actual radial/time integral: angular integration contributes the factor three. -/
theorem integral_flat_radial3 {H : ℝ × ℝ → ℝ} (hH : Continuous H) :
    (∫ p, H (p 0,spatialRadius3 p) ∂flatDiamondMeasure3) =
      3 * ∫ t, ∫ r in Ioo 0 (1-|t|), r*H (t,r) := by
  have h := integral_flat_spatial3 (H := fun q => H (q.1,‖q.2‖)) (by fun_prop)
  simp only [split_lorentz_time3,split_lorentz_radius3] at h
  change (∫ p, H (p 0,spatialRadius3 p) ∂flatDiamondMeasure3) = _ at h
  rw [h]
  change lorentzVolume3⁻¹ *
    (∫ t, ∫ z in Metric.ball (0 : SpatialPoint3) (1-|t|), (fun r => H (t,r)) ‖z‖) = _
  have he : (∫ t, ∫ z in Metric.ball (0 : SpatialPoint3) (1-|t|), H (t,‖z‖)) =
      ∫ t, (2*Real.pi) * ∫ r in Ioo 0 (1-|t|), r*H (t,r) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun t => integral_spatial_radial_ball3 (fun r => H (t,r)) _
  rw [he]
  rw [integral_const_mul]
  unfold lorentzVolume3
  field_simp [Real.pi_ne_zero]

#print axioms integral_spatial_radial_ball3
#print axioms integral_flat_spatial3
#print axioms integral_flat_radial3
end
end QuantyraNullCone
