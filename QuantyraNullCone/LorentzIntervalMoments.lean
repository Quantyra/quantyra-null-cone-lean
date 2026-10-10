import QuantyraNullCone.LorentzIntervalVolume
import QuantyraNullCone.LorentzAffineMoments
import QuantyraNullCone.LorentzTimeFamily

namespace QuantyraNullCone
open MeasureTheory Set
noncomputable section
set_option maxHeartbeats 1200000

theorem lorentz_interval_map_time3 {p q : LorentzPoint3} (h : chronological3 p q)
    (v : LorentzPoint3) :
    lorentzIntervalMap3 p q v 0 = (p 0+q 0)/2 +
      ((q 0-p 0)*v 0+(q 1-p 1)*v 1+(q 2-p 2)*v 2)/2 := by
  have ht := interval_duration_pos3 h
  have hc (i : Fin 3) : intervalDuration3 p q *
      (lorentzBoost3 (intervalBoostA3 p q) (intervalBoostB3 p q) lorentzTop3) i =
        q i-p i := by
    rw [interval_boost_top3 h]
    simp [smul_eq_mul,ht.ne']
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  rw [lorentz_boost_apply3] at h0 h1 h2
  simp [lorentzTop3,lorentzPoint3] at h0 h1 h2
  change (1/2 : ℝ)*(p 0+q 0) + (intervalDuration3 p q/2)*
    (lorentzBoost3 (intervalBoostA3 p q) (intervalBoostB3 p q) v) 0 = _
  rw [lorentz_boost_apply3]
  change (1/2 : ℝ)*(p 0+q 0) + (intervalDuration3 p q/2)*
    (((1+intervalBoostA3 p q^2+intervalBoostB3 p q^2)*v 0+
      2*intervalBoostA3 p q*v 1+2*intervalBoostB3 p q*v 2)/
        (1-intervalBoostA3 p q^2-intervalBoostB3 p q^2)) = _
  linear_combination (v 0/2)*h0+(v 1/2)*h1+(v 2/2)*h2

theorem integral_volume_diamond_eq_flat3 (f : LorentzPoint3 → ℝ) :
    (∫ p in lorentzDiamond3, f p) = lorentzVolume3*(∫ p, f p ∂flatDiamondMeasure3) := by
  rw [flatDiamondMeasure3,integral_smul_measure]
  simp only [ENNReal.toReal_inv,ENNReal.toReal_ofReal lorentz_volume_pos3.le,smul_eq_mul]
  field_simp [lorentz_volume_pos3.ne']

theorem integral_flat_future3 {p : LorentzPoint3} (hp : p ∈ lorentzDiamond3)
    {f : LorentzPoint3 → ℝ} (hf : Continuous f) :
    (∫ q in {q | chronological3 p q}, f q ∂flatDiamondMeasure3) =
      (intervalDuration3 p lorentzTop3/2)^3 *
        ∫ v, f (lorentzIntervalMap3 p lorentzTop3 v) ∂flatDiamondMeasure3 := by
  have hpt := ((lorentz_diamond_iff_tips3 p).mp hp).2
  have hs : MeasurableSet {q | chronological3 p q} :=
    (isOpen_lt (continuous_spatial_radius3.comp (continuous_id.sub continuous_const))
      (by fun_prop)).measurableSet
  have he : {q | chronological3 p q} ∩ lorentzDiamond3 = chronologicalInterval3 p lorentzTop3 := by
    rw [← chronological_future_interval3 hp]
    ext q
    simp only [mem_inter_iff,mem_setOf_eq,and_comm]
  rw [flatDiamondMeasure3,Measure.restrict_smul,integral_smul_measure,
    Measure.restrict_restrict hs,he,integral_chronological_interval3 hpt hf,
    integral_volume_diamond_eq_flat3]
  simp only [ENNReal.toReal_inv,ENNReal.toReal_ofReal lorentz_volume_pos3.le,smul_eq_mul]
  field_simp [lorentz_volume_pos3.ne']
  rfl

def futureTimeShapeMean3 (p : LorentzPoint3) : ℝ :=
  (7+18*p 0+11*p 0^2)/40 + (3/80)*spatialSquared3 p

theorem flat_interval_future_time_square3 {p : LorentzPoint3} (hp : p ∈ lorentzDiamond3) :
    (∫ v, (lorentzIntervalMap3 p lorentzTop3 v 0)^2 ∂flatDiamondMeasure3) =
      futureTimeShapeMean3 p + 1/10 := by
  have hpt := ((lorentz_diamond_iff_tips3 p).mp hp).2
  have he : (fun v => (lorentzIntervalMap3 p lorentzTop3 v 0)^2) =
      (fun v : LorentzPoint3 => ((p 0+1)/2 +
        ∑ i : Fin 3, ![(1-p 0)/2,-p 1/2,-p 2/2] i*v i)^2) := by
    funext v
    rw [lorentz_interval_map_time3 hpt]
    simp [lorentzTop3,lorentzPoint3,Fin.sum_univ_succ]
    ring
  rw [he,flat_affine_second_moment3]
  simp [futureTimeShapeMean3,spatialSquared3]
  ring

theorem flat_interval_future_shape_mean3 {p : LorentzPoint3} (hp : p ∈ lorentzDiamond3) :
    (∫ v, timeQuadraticShape3 (lorentzIntervalMap3 p lorentzTop3 v) ∂flatDiamondMeasure3) =
      futureTimeShapeMean3 p := by
  letI := flat_diamond_probability3
  have hi : Integrable (fun v => (lorentzIntervalMap3 p lorentzTop3 v 0)^2) flatDiamondMeasure3 :=
    continuous_integrable_flat3
      (((show Continuous (fun v : LorentzPoint3 => v 0) by fun_prop).comp
        (continuous_lorentz_interval_map3 p lorentzTop3)).pow 2)
  change (∫ v, (lorentzIntervalMap3 p lorentzTop3 v 0)^2-1/10 ∂flatDiamondMeasure3) = _
  rw [integral_sub hi (integrable_const _),flat_interval_future_time_square3 hp]
  simp

theorem integral_flat_future_density3 (theta : ℝ) {p : LorentzPoint3} (hp : p ∈ lorentzDiamond3) :
    (∫ q in {q | chronological3 p q}, timeQuadraticDensity3 theta q ∂flatDiamondMeasure3) =
      (intervalDuration3 p lorentzTop3/2)^3*(1+theta*futureTimeShapeMean3 p) := by
  letI := flat_diamond_probability3
  rw [integral_flat_future3 hp (by unfold timeQuadraticDensity3 timeQuadraticShape3; fun_prop)]
  have hi : Integrable (fun v => timeQuadraticShape3 (lorentzIntervalMap3 p lorentzTop3 v))
      flatDiamondMeasure3 := continuous_integrable_flat3
        (continuous_time_quadratic_shape3.comp (continuous_lorentz_interval_map3 _ _))
  congr 1
  change (∫ v, 1+theta*timeQuadraticShape3 (lorentzIntervalMap3 p lorentzTop3 v)
    ∂flatDiamondMeasure3) = _
  rw [integral_add (integrable_const _) (hi.const_mul _),integral_const_mul,
    flat_interval_future_shape_mean3 hp]
  simp

theorem InDensityClass3.measure_apply3 {rho : LorentzPoint3 → ℝ} (h : InDensityClass3 rho)
    {s : Set LorentzPoint3} (hs : MeasurableSet s) :
    densityMeasure3 rho s = ENNReal.ofReal (∫ p in s, rho p ∂flatDiamondMeasure3) := by
  have hn : 0 ≤ᵐ[flatDiamondMeasure3] rho :=
    flat_diamond3_ae_mem.mono fun p hp => (by norm_num : (0 : ℝ) ≤ 1/2).trans (h.bounds p hp).1
  rw [densityMeasure3,withDensity_apply _ hs,
    ← ofReal_integral_eq_lintegral_ofReal h.integrable.integrableOn (hn.filter_mono ae_restrict_le)]

theorem time_quadratic_future_probability3 {theta : ℝ} (ht : theta ∈ Icc (0 : ℝ) (1/2))
    {p : LorentzPoint3} (hp : p ∈ lorentzDiamond3) :
    densityMeasure3 (timeQuadraticDensity3 theta) {q | chronological3 p q} =
      ENNReal.ofReal ((intervalDuration3 p lorentzTop3/2)^3*(1+theta*futureTimeShapeMean3 p)) := by
  have hs : MeasurableSet {q | chronological3 p q} :=
    (isOpen_lt (continuous_spatial_radius3.comp (continuous_id.sub continuous_const))
      (by fun_prop)).measurableSet
  rw [(time_quadratic_density_class3 ht).measure_apply3 hs,integral_flat_future_density3 theta hp]

#print axioms lorentz_interval_map_time3
#print axioms integral_flat_future3
#print axioms flat_interval_future_time_square3
#print axioms flat_interval_future_shape_mean3
#print axioms integral_flat_future_density3
#print axioms time_quadratic_future_probability3
end
end QuantyraNullCone
