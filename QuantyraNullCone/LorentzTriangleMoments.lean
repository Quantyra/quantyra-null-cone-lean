import QuantyraNullCone.LorentzLightConeIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace QuantyraNullCone
open MeasureTheory Set
noncomputable section
set_option maxHeartbeats 1200000

theorem integral_Ioo_rpow3 {s b : ℝ} (hs : 0 ≤ s) (hb : 0 ≤ b) :
    (∫ a in Ioo 0 b, a^s) = b^(s+1)/(s+1) := by
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hb,integral_rpow (Or.inl (by linarith))]
  rw [Real.zero_rpow (by linarith : s+1 ≠ 0),sub_zero]

theorem integrableOn_triangle_continuous3 {f : ℝ × ℝ → ℝ} (hf : Continuous f) :
    IntegrableOn f lightConeTriangle3 (volume : Measure (ℝ × ℝ)) := by
  have hi : IntegrableOn f (Icc ((0 : ℝ),0) (1,1)) volume :=
    hf.continuousOn.integrableOn_compact isCompact_Icc
  apply hi.mono_set
  intro z hz
  exact ⟨⟨hz.1.le,(hz.1.trans hz.2.1).le⟩,⟨(hz.2.1.trans hz.2.2).le,hz.2.2.le⟩⟩

theorem integral_triangle_inner_rpow3 {s t b : ℝ} (hs : 0 ≤ s) (hb : 0 < b) :
    (∫ a in Ioo 0 b, (b-a)*a^s*b^t) = b^(s+t+2)/((s+1)*(s+2)) := by
  have hi : IntegrableOn (fun a : ℝ => a^s) (Ioo 0 b) volume :=
    ((Real.continuous_rpow_const hs).continuousOn.integrableOn_compact
      (isCompact_Icc : IsCompact (Icc (0 : ℝ) b))).mono_set Ioo_subset_Icc_self
  have hj : IntegrableOn (fun a : ℝ => a^(s+1)) (Ioo 0 b) volume :=
    ((Real.continuous_rpow_const (by linarith : 0 ≤ s+1)).continuousOn.integrableOn_compact
      (isCompact_Icc : IsCompact (Icc (0 : ℝ) b))).mono_set Ioo_subset_Icc_self
  have he : (∫ a in Ioo 0 b, (b-a)*a^s*b^t) =
      (∫ a in Ioo 0 b, b*a^s-a^(s+1))*b^t := by
    rw [← integral_mul_const]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with a ha
    rw [Real.rpow_add_one ha.1.ne']
    ring
  rw [he,integral_sub (hi.const_mul b) hj,integral_const_mul,
    integral_Ioo_rpow3 hs hb.le,integral_Ioo_rpow3 (by linarith : 0 ≤ s+1) hb.le]
  rw [show s+1+1 = s+2 by ring]
  have h1 : b^(s+1) = b^s*b := Real.rpow_add_one hb.ne' s
  have h2 : b^(s+2) = b^s*b^2 := by
    rw [show s+2 = (s+1)+1 by ring,Real.rpow_add_one hb.ne',h1]
    ring
  have h3 : b^(s+t+2) = b^s*b^t*b^2 := by
    rw [show s+t+2 = (s+2)+t by ring,Real.rpow_add hb (s+2) t,h2]
    ring
  rw [h1,h2,h3]
  field_simp
  ring

theorem integral_triangle_rpow3 {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (∫ z in lightConeTriangle3, (z.2-z.1)*z.1^s*z.2^t) =
      1/((s+1)*(s+2)*(s+t+3)) := by
  have hc : Continuous (fun z : ℝ × ℝ => (z.2-z.1)*z.1^s*z.2^t) :=
    (continuous_snd.sub continuous_fst).mul
      ((Real.continuous_rpow_const hs).comp continuous_fst) |>.mul
        ((Real.continuous_rpow_const ht).comp continuous_snd)
  rw [integral_triangle_slices3 hc]
  have he : (∫ b in Ioo (0 : ℝ) 1, ∫ a in Ioo 0 b, (b-a)*a^s*b^t) =
      ∫ b in Ioo (0 : ℝ) 1, b^(s+t+2)/((s+1)*(s+2)) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with b hb
    exact integral_triangle_inner_rpow3 hs hb.1
  rw [he,integral_div,integral_Ioo_rpow3 (by linarith : 0 ≤ s+t+2) (by norm_num)]
  rw [Real.one_rpow]
  field_simp
  ring

def lightConeWeight3 (z : ℝ × ℝ) : ℝ := (z.2-z.1)*(z.1*z.2)^((3 : ℝ)/2)

theorem continuous_lightConeWeight3 : Continuous lightConeWeight3 := by
  exact (continuous_snd.sub continuous_fst).mul
    ((Real.continuous_rpow_const (by norm_num : 0 ≤ (3 : ℝ)/2)).comp
      (continuous_fst.mul continuous_snd))

theorem integral_triangle_monomial3 (i j : ℕ) :
    (∫ z in lightConeTriangle3, lightConeWeight3 z*z.1^i*z.2^j) =
      1/(((i : ℝ)+5/2)*((i : ℝ)+7/2)*((i : ℝ)+(j : ℝ)+6)) := by
  have he : (∫ z in lightConeTriangle3, lightConeWeight3 z*z.1^i*z.2^j) =
      ∫ z in lightConeTriangle3, (z.2-z.1)*z.1^((i : ℝ)+3/2)*z.2^((j : ℝ)+3/2) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem isOpen_lightConeTriangle3.measurableSet] with z hz
    dsimp [lightConeWeight3]
    rw [Real.mul_rpow hz.1.le (hz.1.trans hz.2.1).le,
      Real.rpow_add hz.1,Real.rpow_add (hz.1.trans hz.2.1),
      Real.rpow_natCast,Real.rpow_natCast]
    ring
  rw [he,integral_triangle_rpow3 (by positivity) (by positivity)]
  congr 1
  ring

#print axioms integral_triangle_rpow3
#print axioms integral_triangle_monomial3
end
end QuantyraNullCone
