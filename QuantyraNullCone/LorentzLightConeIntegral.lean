import QuantyraNullCone.LorentzRadialIntegral
import Mathlib.MeasureTheory.Function.Jacobian

namespace QuantyraNullCone
open MeasureTheory Set
noncomputable section
set_option maxHeartbeats 1200000

def radialDiamond3 : Set (ℝ × ℝ) := {z | 0 < z.2 ∧ |z.1|+z.2 < 1}
def lightConeTriangle3 : Set (ℝ × ℝ) := {z | 0 < z.1 ∧ z.1 < z.2 ∧ z.2 < 1}
def lightConeMap3 (z : ℝ × ℝ) : ℝ × ℝ := (1-z.1-z.2,z.2-z.1)
def lightConeLinear3 : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ) !![-1,-1;-1,1]).toContinuousLinearMap

theorem light_cone_map_deriv3 (z : ℝ × ℝ) :
    HasFDerivAt lightConeMap3 lightConeLinear3 z := by
  have he : lightConeMap3 = (fun z => (1,0)+lightConeLinear3 z) := by
    funext z
    simp [lightConeMap3,lightConeLinear3,Matrix.toLin_finTwoProd_apply]
    constructor <;> ring
  rw [he]
  exact lightConeLinear3.hasFDerivAt.const_add (1,0)

theorem light_cone_linear_det3 : lightConeLinear3.det = -2 := by
  norm_num [lightConeLinear3,LinearMap.det_toLin,Matrix.det_fin_two]

theorem light_cone_map_injective3 : Function.Injective lightConeMap3 := by
  intro x y h
  have h0 := congrArg Prod.fst h
  have h1 := congrArg Prod.snd h
  dsimp [lightConeMap3] at h0 h1
  apply Prod.ext <;> linarith

theorem light_cone_triangle_image3 : lightConeMap3 '' lightConeTriangle3 = radialDiamond3 := by
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    change 0 < w.1 ∧ w.1 < w.2 ∧ w.2 < 1 at hw
    change 0 < w.2-w.1 ∧ |1-w.1-w.2|+(w.2-w.1) < 1
    constructor
    · linarith [hw.2.1]
    · have hh : |1-w.1-w.2| < 1-(w.2-w.1) :=
        abs_lt.mpr ⟨by linarith [hw.2.2],by linarith [hw.1]⟩
      linarith
  · intro hz
    change 0 < z.2 ∧ |z.1|+z.2 < 1 at hz
    refine ⟨((1-z.1-z.2)/2,(1-z.1+z.2)/2), ?_, ?_⟩
    · change 0 < (1-z.1-z.2)/2 ∧ (1-z.1-z.2)/2 < (1-z.1+z.2)/2 ∧
        (1-z.1+z.2)/2 < 1
      constructor
      · linarith [le_abs_self z.1,hz.2]
      · constructor <;> linarith [neg_le_abs z.1,hz.1,hz.2]
    · apply Prod.ext <;> dsimp [lightConeMap3] <;> ring

theorem isOpen_lightConeTriangle3 : IsOpen lightConeTriangle3 :=
  (isOpen_lt continuous_const continuous_fst).inter
    ((isOpen_lt continuous_fst continuous_snd).inter (isOpen_lt continuous_snd continuous_const))

theorem isOpen_radialDiamond3 : IsOpen radialDiamond3 :=
  (isOpen_lt continuous_const continuous_snd).inter
    (isOpen_lt (continuous_fst.abs.add continuous_snd) continuous_const)

theorem integral_radial_light_cone3 (f : ℝ × ℝ → ℝ) :
    (∫ z in radialDiamond3, f z) = 2*∫ z in lightConeTriangle3, f (lightConeMap3 z) := by
  rw [← light_cone_triangle_image3,
    integral_image_eq_integral_abs_det_fderiv_smul volume isOpen_lightConeTriangle3.measurableSet
      (fun z _ => (light_cone_map_deriv3 z).hasFDerivWithinAt) light_cone_map_injective3.injOn]
  norm_num only [light_cone_linear_det3,abs_neg,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    smul_eq_mul,integral_const_mul]

theorem integral_radial_slices3 {f : ℝ × ℝ → ℝ} (hf : Continuous f) :
    (∫ z in radialDiamond3, f z) = ∫ t, ∫ r in Ioo 0 (1-|t|), f (t,r) := by
  have hsub : radialDiamond3 ⊆ Icc ((-1 : ℝ),0) (1,1) := by
    intro z hz
    change 0 < z.2 ∧ |z.1|+z.2 < 1 at hz
    exact ⟨⟨by linarith [neg_le_abs z.1,hz.2],hz.1.le⟩,
      ⟨by linarith [le_abs_self z.1,hz.1,hz.2],by linarith [abs_nonneg z.1,hz.2]⟩⟩
  have hi : IntegrableOn f radialDiamond3 (volume : Measure (ℝ × ℝ)) :=
    (hf.continuousOn.integrableOn_compact isCompact_Icc).mono_set hsub
  rw [← integral_indicator isOpen_radialDiamond3.measurableSet]
  change (∫ z, radialDiamond3.indicator f z ∂(volume : Measure ℝ).prod volume) = _
  rw [integral_prod _ (hi.integrable_indicator isOpen_radialDiamond3.measurableSet)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  change (∫ r, radialDiamond3.indicator f (t,r)) = ∫ r in Ioo 0 (1-|t|), f (t,r)
  rw [← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro r
  have he : (t,r) ∈ radialDiamond3 ↔ r ∈ Ioo 0 (1-|t|) := by
    change (0 < r ∧ |t|+r < 1) ↔ (0 < r ∧ r < 1-|t|)
    constructor <;> rintro ⟨h0,h1⟩ <;> exact ⟨h0,by linarith⟩
  simp only [indicator,he]

theorem integral_triangle_slices3 {f : ℝ × ℝ → ℝ} (hf : Continuous f) :
    (∫ z in lightConeTriangle3, f z) = ∫ b in Ioo 0 1, ∫ a in Ioo 0 b, f (a,b) := by
  have hsub : lightConeTriangle3 ⊆ Icc ((0 : ℝ),0) (1,1) := by
    intro z hz
    change 0 < z.1 ∧ z.1 < z.2 ∧ z.2 < 1 at hz
    exact ⟨⟨hz.1.le,(hz.1.trans hz.2.1).le⟩,⟨(hz.2.1.trans hz.2.2).le,hz.2.2.le⟩⟩
  have hi : IntegrableOn f lightConeTriangle3 (volume : Measure (ℝ × ℝ)) :=
    (hf.continuousOn.integrableOn_compact isCompact_Icc).mono_set hsub
  rw [← integral_indicator isOpen_lightConeTriangle3.measurableSet]
  change (∫ z, lightConeTriangle3.indicator f z ∂(volume : Measure ℝ).prod volume) = _
  rw [integral_prod_symm _ (hi.integrable_indicator isOpen_lightConeTriangle3.measurableSet),
    ← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro b
  change (∫ a, lightConeTriangle3.indicator f (a,b)) =
    (Ioo (0 : ℝ) 1).indicator (fun b => ∫ a in Ioo 0 b, f (a,b)) b
  by_cases hb : b ∈ Ioo (0 : ℝ) 1
  · rw [indicator_of_mem hb,← integral_indicator measurableSet_Ioo]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro a
    have he : (a,b) ∈ lightConeTriangle3 ↔ a ∈ Ioo 0 b := by
      change (0 < a ∧ a < b ∧ b < 1) ↔ (0 < a ∧ a < b)
      exact ⟨fun h => ⟨h.1,h.2.1⟩,fun h => ⟨h.1,h.2,hb.2⟩⟩
    simp only [indicator,he]
  · rw [indicator_of_notMem hb]
    apply integral_eq_zero_of_ae
    apply Filter.Eventually.of_forall
    intro a
    have he : (a,b) ∉ lightConeTriangle3 := by
      intro hz
      exact hb ⟨hz.1.trans hz.2.1,hz.2.2⟩
    exact indicator_of_notMem he f

theorem integral_flat_light_cone_triangle3 {H : ℝ × ℝ → ℝ} (hH : Continuous H) :
    (∫ p, H (p 0,spatialRadius3 p) ∂flatDiamondMeasure3) =
      6*∫ z in lightConeTriangle3, (z.2-z.1)*H (lightConeMap3 z) := by
  rw [integral_flat_radial3 hH,← integral_radial_slices3 (f := fun z => z.2*H z) (by fun_prop),
    integral_radial_light_cone3]
  dsimp [lightConeMap3]
  ring

/-- Actual light-cone coordinates for the normalized original flat sampling measure. -/
theorem integral_flat_light_cone3 {H : ℝ × ℝ → ℝ} (hH : Continuous H) :
    (∫ p, H (p 0,spatialRadius3 p) ∂flatDiamondMeasure3) =
      6*∫ b in Ioo 0 1, ∫ a in Ioo 0 b, (b-a)*H (1-a-b,b-a) := by
  rw [integral_flat_radial3 hH,← integral_radial_slices3 (f := fun z => z.2*H z) (by fun_prop),
    integral_radial_light_cone3]
  rw [integral_triangle_slices3 (f := fun z => (lightConeMap3 z).2*H (lightConeMap3 z))
    (by unfold lightConeMap3; fun_prop)]
  dsimp [lightConeMap3]
  ring

#print axioms light_cone_map_deriv3
#print axioms light_cone_linear_det3
#print axioms light_cone_triangle_image3
#print axioms integral_radial_light_cone3
#print axioms integral_flat_light_cone_triangle3
#print axioms integral_flat_light_cone3
end
end QuantyraNullCone
