import QuantyraNullCone.LorentzBoost
import QuantyraNullCone.LorentzRadialIntegral
import QuantyraNullCone.LorentzBoundary

namespace QuantyraNullCone
open MeasureTheory Set
noncomputable section
set_option maxHeartbeats 1400000

def chronologicalInterval3 (p q : LorentzPoint3) : Set LorentzPoint3 :=
  {z | chronological3 p z ∧ chronological3 z q}

def intervalDuration3 (p q : LorentzPoint3) : ℝ := Real.sqrt (-lorentzSquare3 (q-p))

theorem interval_duration_pos3 {p q : LorentzPoint3} (h : chronological3 p q) :
    0 < intervalDuration3 p q := by
  exact Real.sqrt_pos.mpr (neg_pos.mpr ((chronological_iff_square3 p q).mp h).1)

theorem interval_duration_sq3 {p q : LorentzPoint3} (h : chronological3 p q) :
    intervalDuration3 p q ^ 2 = (q 0-p 0)^2-(q 1-p 1)^2-(q 2-p 2)^2 := by
  have hs := Real.sq_sqrt (neg_nonneg.mpr ((chronological_iff_square3 p q).mp h).1.le)
  dsimp [intervalDuration3]
  rw [hs]
  simp only [lorentzSquare3,spatialSquared3,PiLp.sub_apply]
  ring

def intervalBoostA3 (p q : LorentzPoint3) : ℝ :=
  (q 1-p 1)/(q 0-p 0+intervalDuration3 p q)
def intervalBoostB3 (p q : LorentzPoint3) : ℝ :=
  (q 2-p 2)/(q 0-p 0+intervalDuration3 p q)

theorem interval_boost_denominator3 {p q : LorentzPoint3} (h : chronological3 p q) :
    1-intervalBoostA3 p q^2-intervalBoostB3 p q^2 =
      2*intervalDuration3 p q/(q 0-p 0+intervalDuration3 p q) := by
  have ht := interval_duration_pos3 h
  have hd := ((chronological_iff_square3 p q).mp h).2
  have hs : q 0-p 0+intervalDuration3 p q ≠ 0 := ne_of_gt (by linarith)
  dsimp [intervalBoostA3,intervalBoostB3]
  field_simp [hs]
  nlinarith [interval_duration_sq3 h]

theorem interval_boost_denominator_pos3 {p q : LorentzPoint3} (h : chronological3 p q) :
    0 < 1-intervalBoostA3 p q^2-intervalBoostB3 p q^2 := by
  rw [interval_boost_denominator3 h]
  exact div_pos (mul_pos (by norm_num) (interval_duration_pos3 h))
    (add_pos ((chronological_iff_square3 p q).mp h).2 (interval_duration_pos3 h))

theorem interval_boost_top3 {p q : LorentzPoint3} (h : chronological3 p q) :
    lorentzBoost3 (intervalBoostA3 p q) (intervalBoostB3 p q) lorentzTop3 =
      (intervalDuration3 p q)⁻¹ • (q-p) := by
  have ht := interval_duration_pos3 h
  have hs : q 0-p 0+intervalDuration3 p q ≠ 0 := ne_of_gt
    (add_pos ((chronological_iff_square3 p q).mp h).2 ht)
  rw [lorentz_boost_apply3,interval_boost_denominator3 h]
  ext i
  fin_cases i <;>
    simp [lorentzPoint3,lorentzTop3,intervalBoostA3,intervalBoostB3,smul_eq_mul]
  all_goals field_simp [ht.ne',hs]
  all_goals nlinarith only [interval_duration_sq3 h]

def lorentzIntervalMap3 (p q v : LorentzPoint3) : LorentzPoint3 :=
  (1/2 : ℝ) • (p+q) + (intervalDuration3 p q/2) •
    lorentzBoost3 (intervalBoostA3 p q) (intervalBoostB3 p q) v

theorem continuous_lorentz_interval_map3 (p q : LorentzPoint3) :
    Continuous (lorentzIntervalMap3 p q) :=
  continuous_const.add ((lorentzBoost3 (intervalBoostA3 p q)
    (intervalBoostB3 p q)).continuous_of_finiteDimensional.const_smul _)

theorem lorentz_interval_map_top3 {p q : LorentzPoint3} (h : chronological3 p q) :
    lorentzIntervalMap3 p q lorentzTop3 = q := by
  rw [lorentzIntervalMap3,interval_boost_top3 h,smul_smul]
  have ht := interval_duration_pos3 h
  have he : (intervalDuration3 p q/2)* (intervalDuration3 p q)⁻¹ = (1/2 : ℝ) := by
    field_simp [ht.ne']
  rw [he]
  module

theorem lorentz_interval_map_bottom3 {p q : LorentzPoint3} (h : chronological3 p q) :
    lorentzIntervalMap3 p q lorentzBottom3 = p := by
  have hb : lorentzBottom3 = -lorentzTop3 := by
    ext i
    fin_cases i <;> simp [lorentzBottom3,lorentzTop3,lorentzPoint3]
  rw [lorentzIntervalMap3,hb,map_neg,interval_boost_top3 h,smul_neg,smul_smul]
  have ht := interval_duration_pos3 h
  have he : (intervalDuration3 p q/2)* (intervalDuration3 p q)⁻¹ = (1/2 : ℝ) := by
    field_simp [ht.ne']
  rw [he]
  module

theorem chronological_smul_translate_iff3 {r : ℝ} (hr : 0 < r)
    (z p q : LorentzPoint3) : chronological3 (z+r•p) (z+r•q) ↔ chronological3 p q := by
  have he : (z+r•q)-(z+r•p) = r•(q-p) := by module
  simp only [chronological3,he,spatial_radius_smul3,abs_of_pos hr,PiLp.add_apply,
    PiLp.smul_apply,smul_eq_mul]
  rw [show z 0+r*q 0-(z 0+r*p 0) = r*(q 0-p 0) by ring]
  exact mul_lt_mul_iff_right₀ hr

theorem lorentz_interval_map_chronological_iff3 {p q : LorentzPoint3}
    (h : chronological3 p q) (u v : LorentzPoint3) :
    chronological3 (lorentzIntervalMap3 p q u) (lorentzIntervalMap3 p q v) ↔
      chronological3 u v := by
  rw [lorentzIntervalMap3,lorentzIntervalMap3,
    chronological_smul_translate_iff3 (div_pos (interval_duration_pos3 h) (by norm_num)),
    lorentz_boost_chronological_iff3 (interval_boost_denominator_pos3 h)]

theorem lorentz_interval_map_preimage3 {p q : LorentzPoint3} (h : chronological3 p q) :
    lorentzIntervalMap3 p q ⁻¹' chronologicalInterval3 p q = lorentzDiamond3 := by
  ext v
  change (chronological3 p (lorentzIntervalMap3 p q v) ∧
    chronological3 (lorentzIntervalMap3 p q v) q) ↔ v ∈ lorentzDiamond3
  have hl := lorentz_interval_map_chronological_iff3 h lorentzBottom3 v
  have hr := lorentz_interval_map_chronological_iff3 h v lorentzTop3
  rw [lorentz_interval_map_bottom3 h] at hl
  rw [lorentz_interval_map_top3 h] at hr
  rw [hl,hr,lorentz_diamond_iff_tips3]

theorem isOpen_chronologicalInterval3 (p q : LorentzPoint3) :
    IsOpen (chronologicalInterval3 p q) := by
  apply IsOpen.inter
  · exact isOpen_lt (continuous_spatial_radius3.comp (continuous_id.sub continuous_const))
      (by fun_prop)
  · exact isOpen_lt (continuous_spatial_radius3.comp (continuous_const.sub continuous_id))
      (by fun_prop)

#print axioms interval_duration_sq3
#print axioms interval_boost_denominator_pos3
#print axioms interval_boost_top3
#print axioms lorentz_interval_map_top3
#print axioms lorentz_interval_map_bottom3
#print axioms lorentz_interval_map_chronological_iff3
#print axioms lorentz_interval_map_preimage3
end
end QuantyraNullCone
