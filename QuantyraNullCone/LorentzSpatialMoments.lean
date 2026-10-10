import QuantyraNullCone.LorentzRadialIntegral

namespace QuantyraNullCone
open MeasureTheory Set
noncomputable section
set_option maxHeartbeats 1000000

def lorentzCoordinateReflection3 (i : Fin 3) : LorentzPoint3 ≃ₗᵢ[ℝ] LorentzPoint3 :=
  LinearIsometryEquiv.piLpCongrRight 2 fun j : Fin 3 =>
    if j=i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ

theorem lorentz_coordinate_reflection_apply3 (i j : Fin 3) (p : LorentzPoint3) :
    lorentzCoordinateReflection3 i p j = if j=i then -p j else p j := by
  by_cases h : j=i <;>
    simp [lorentzCoordinateReflection3,LinearIsometryEquiv.piLpCongrRight_apply,h]

theorem lorentz_coordinate_reflection_preimage3 (i : Fin 3) :
    lorentzCoordinateReflection3 i ⁻¹' lorentzDiamond3 = lorentzDiamond3 := by
  ext p
  fin_cases i <;>
    simp [lorentzDiamond3,spatialRadius3,spatialSquared3,lorentz_coordinate_reflection_apply3]

theorem flat_diamond_isometry_preserving3 (e : LorentzPoint3 ≃ₗᵢ[ℝ] LorentzPoint3)
    (he : e ⁻¹' lorentzDiamond3 = lorentzDiamond3) :
    MeasurePreserving e flatDiamondMeasure3 flatDiamondMeasure3 := by
  have h := e.measurePreserving.restrict_preimage isOpen_lorentzDiamond3.measurableSet
  have hm : Measure.map e ((volume : Measure LorentzPoint3).restrict lorentzDiamond3) =
      volume.restrict lorentzDiamond3 := by simpa only [he] using h.map_eq
  refine ⟨e.continuous.measurable, ?_⟩
  rw [flatDiamondMeasure3,Measure.map_smul,hm]

theorem flat_reflection_integral3 (i : Fin 3) (f : LorentzPoint3 → ℝ) :
    (∫ p, f (lorentzCoordinateReflection3 i p) ∂flatDiamondMeasure3) =
      ∫ p, f p ∂flatDiamondMeasure3 :=
  (flat_diamond_isometry_preserving3 _ (lorentz_coordinate_reflection_preimage3 i)).integral_comp
    (lorentzCoordinateReflection3 i).toHomeomorph.measurableEmbedding f

theorem flat_coordinate_mean3 (i : Fin 3) :
    (∫ p : LorentzPoint3, p i ∂flatDiamondMeasure3) = 0 := by
  have h := flat_reflection_integral3 i (fun p => p i)
  change (∫ p, lorentzCoordinateReflection3 i p i ∂flatDiamondMeasure3) = _ at h
  simp only [lorentz_coordinate_reflection_apply3,ite_true] at h
  rw [integral_neg] at h
  linarith

theorem flat_coordinate_cross_moment3 {i j : Fin 3} (hij : i ≠ j) :
    (∫ p : LorentzPoint3, p i*p j ∂flatDiamondMeasure3) = 0 := by
  have h := flat_reflection_integral3 i (fun p => p i*p j)
  change (∫ p, lorentzCoordinateReflection3 i p i * lorentzCoordinateReflection3 i p j
    ∂flatDiamondMeasure3) = _ at h
  simp only [lorentz_coordinate_reflection_apply3,ite_true,if_neg (Ne.symm hij),neg_mul] at h
  rw [integral_neg] at h
  linarith

def lorentzSpatialSwap3 : LorentzPoint3 ≃ₗᵢ[ℝ] LorentzPoint3 :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (1 : Fin 3) 2)

theorem lorentz_spatial_swap_apply3 (p : LorentzPoint3) (i : Fin 3) :
    lorentzSpatialSwap3 p i = p (Equiv.swap (1 : Fin 3) 2 i) := by
  simp [lorentzSpatialSwap3,LinearIsometryEquiv.piLpCongrLeft_apply,Equiv.piCongrLeft']

theorem lorentz_spatial_swap_preimage3 :
    lorentzSpatialSwap3 ⁻¹' lorentzDiamond3 = lorentzDiamond3 := by
  ext p
  have hs : Equiv.swap (1 : Fin 3) 2 0 = 0 := by decide
  simp [lorentzDiamond3,spatialRadius3,spatialSquared3,lorentz_spatial_swap_apply3,hs,add_comm]

theorem flat_spatial_moments_equal3 :
    (∫ p : LorentzPoint3, p 1^2 ∂flatDiamondMeasure3) =
      ∫ p : LorentzPoint3, p 2^2 ∂flatDiamondMeasure3 := by
  have h := (flat_diamond_isometry_preserving3 _ lorentz_spatial_swap_preimage3).integral_comp
    lorentzSpatialSwap3.toHomeomorph.measurableEmbedding (fun p => p 1^2)
  simpa [lorentz_spatial_swap_apply3] using h.symm

theorem integral_spatial_ball_norm_sq3 {R : ℝ} (hR : 0 ≤ R) :
    (∫ z : SpatialPoint3 in Metric.ball 0 R, ‖z‖^2) = Real.pi*R^4/2 := by
  rw [integral_spatial_radial_ball3 (fun r : ℝ => r^2) R]
  simp_rw [show (fun r : ℝ => r*r^2) = (fun r => r^3) by funext r; ring]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hR,integral_pow]
  norm_num
  ring

theorem integral_spatial_slice_norm_sq3 (t : ℝ) :
    (∫ z : SpatialPoint3 in Metric.ball 0 (1-|t|), ‖z‖^2) =
      lorentzSliceArea3 t*(1-|t|)^2/2 := by
  by_cases h : 0 ≤ 1-|t|
  · rw [integral_spatial_ball_norm_sq3 h]
    simp only [lorentzSliceArea3,max_eq_right h]
    ring
  · have hh : 1-|t| ≤ 0 := (lt_of_not_ge h).le
    rw [Metric.ball_eq_empty.mpr hh]
    simp [lorentzSliceArea3,max_eq_left hh]

theorem integral_slice_width_sq3 :
    (∫ t, lorentzSliceArea3 t*(1-|t|)^2) = 2*Real.pi/5 := by
  rw [integral_slice_statistic3 (f := fun t : ℝ => (1-|t|)^2) (by fun_prop)]
  have hl : (∫ t in (-1 : ℝ)..0, Real.pi*(1+t)^2*(1-|t|)^2) = Real.pi/5 := by
    calc
      _ = Real.pi*(∫ t in (-1 : ℝ)..0, (1+t)^4) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro t ht
        have ht' : t ∈ Icc (-1 : ℝ) 0 := by
          simpa [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] using ht
        change Real.pi*(1+t)^2*(1-|t|)^2 = _
        rw [abs_of_nonpos ht'.2]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_comp_add_left (fun t : ℝ => t^4) 1,integral_pow]
        norm_num
        ring
  have hr : (∫ t in (0 : ℝ)..1, Real.pi*(1-t)^2*(1-|t|)^2) = Real.pi/5 := by
    calc
      _ = Real.pi*(∫ t in (0 : ℝ)..1, (1-t)^4) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro t ht
        have ht' : t ∈ Icc (0 : ℝ) 1 := by
          simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
        change Real.pi*(1-t)^2*(1-|t|)^2 = _
        rw [abs_of_nonneg ht'.1]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_comp_sub_left (fun t : ℝ => t^4) 1,integral_pow]
        norm_num
        ring
  rw [hl,hr]
  ring

theorem flat_spatial_radius_second_moment3 :
    (∫ p, spatialRadius3 p^2 ∂flatDiamondMeasure3) = 3/10 := by
  have h := integral_flat_spatial3 (H := fun q => ‖q.2‖^2) (by fun_prop)
  simp only [split_lorentz_radius3] at h
  change (∫ p, spatialRadius3 p^2 ∂flatDiamondMeasure3) =
    lorentzVolume3⁻¹*(∫ t, ∫ z : SpatialPoint3 in Metric.ball 0 (1-|t|), ‖z‖^2) at h
  rw [h]
  simp_rw [integral_spatial_slice_norm_sq3]
  rw [integral_div,integral_slice_width_sq3]
  unfold lorentzVolume3
  field_simp [Real.pi_ne_zero]
  norm_num

theorem flat_spatial_coordinate_second_moment3 :
    (∫ p : LorentzPoint3, p 1^2 ∂flatDiamondMeasure3) = 3/20 ∧
      (∫ p : LorentzPoint3, p 2^2 ∂flatDiamondMeasure3) = 3/20 := by
  have he := flat_spatial_radius_second_moment3
  simp_rw [spatial_radius_sq3] at he
  change (∫ p : LorentzPoint3, p 1^2+p 2^2 ∂flatDiamondMeasure3) = 3/10 at he
  rw [integral_add (continuous_integrable_flat3 (by fun_prop))
    (continuous_integrable_flat3 (by fun_prop))] at he
  have hh := flat_spatial_moments_equal3
  constructor <;> linarith

#print axioms flat_coordinate_mean3
#print axioms flat_coordinate_cross_moment3
#print axioms flat_spatial_moments_equal3
#print axioms flat_spatial_radius_second_moment3
#print axioms flat_spatial_coordinate_second_moment3
end
end QuantyraNullCone
