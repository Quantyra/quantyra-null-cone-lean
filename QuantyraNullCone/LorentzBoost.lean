import QuantyraNullCone.LorentzMetricJacobian
import QuantyraNullCone.LorentzFlat
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

namespace QuantyraNullCone
open MeasureTheory Set
noncomputable section
set_option maxHeartbeats 1600000

/-- Rational half-velocity parametrization of an actual linear Lorentz boost. -/
def lorentzBoostMatrix3 (a b : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (1-a^2-b^2)⁻¹ • !![1+a^2+b^2, 2*a, 2*b;
    2*a, 1+a^2-b^2, 2*a*b;
    2*b, 2*a*b, 1-a^2+b^2]

def lorentzBoost3 (a b : ℝ) : LorentzPoint3 →ₗ[ℝ] LorentzPoint3 :=
  (lorentzBoostMatrix3 a b).toLpLin 2 2

theorem lorentz_boost_apply3 (a b : ℝ) (v : LorentzPoint3) :
    lorentzBoost3 a b v = lorentzPoint3
      (((1+a^2+b^2)*v 0+2*a*v 1+2*b*v 2)/(1-a^2-b^2))
      ((2*a*v 0+(1+a^2-b^2)*v 1+2*a*b*v 2)/(1-a^2-b^2))
      ((2*b*v 0+2*a*b*v 1+(1-a^2+b^2)*v 2)/(1-a^2-b^2)) := by
  ext i
  fin_cases i <;>
    simp [lorentzBoost3,lorentzBoostMatrix3,Matrix.toLpLin_apply,
      dotProduct,Fin.sum_univ_succ,lorentzPoint3,smul_eq_mul,div_eq_mul_inv] <;> ring

theorem lorentz_boost_inverse3 {a b : ℝ} (hd : 1-a^2-b^2 ≠ 0) (v : LorentzPoint3) :
    lorentzBoost3 (-a) (-b) (lorentzBoost3 a b v) = v := by
  rw [lorentz_boost_apply3,lorentz_boost_apply3]
  ext i
  fin_cases i <;> simp [lorentzPoint3] <;> field_simp [hd] <;> ring

theorem lorentz_boost_bilinear3 {a b : ℝ} (hd : 1-a^2-b^2 ≠ 0)
    (u v : LorentzPoint3) :
    lorentzBilinear3 (lorentzBoost3 a b u) (lorentzBoost3 a b v) = lorentzBilinear3 u v := by
  rw [lorentz_boost_apply3,lorentz_boost_apply3]
  simp [lorentzBilinear3,lorentzPoint3]
  field_simp [hd]
  ring

theorem lorentz_boost_square3 {a b : ℝ} (hd : 1-a^2-b^2 ≠ 0) (v : LorentzPoint3) :
    lorentzSquare3 (lorentzBoost3 a b v) = lorentzSquare3 v := by
  simpa [lorentzBilinear3,lorentzSquare3,spatialSquared3,pow_two,add_assoc] using
    lorentz_boost_bilinear3 hd v v

theorem lorentz_boost_abs_det3 {a b : ℝ} (hd : 1-a^2-b^2 ≠ 0) :
    |(lorentzBoost3 a b).det| = 1 := by
  have h := lorentz_metric_linear_det3 (lorentzBoost3 a b).toContinuousLinearMap
    (a := 1) (b := 1) (by norm_num) (by norm_num) (fun u v => by
      simpa using (lorentz_boost_bilinear3 hd u v).symm)
  simpa using h

theorem lorentz_boost_det_ne_zero3 {a b : ℝ} (hd : 1-a^2-b^2 ≠ 0) :
    (lorentzBoost3 a b).det ≠ 0 := by
  intro h
  have hh := lorentz_boost_abs_det3 hd
  rw [h,abs_zero] at hh
  norm_num at hh

def lorentzBoostEquiv3 {a b : ℝ} (hd : 1-a^2-b^2 ≠ 0) :
    LorentzPoint3 ≃L[ℝ] LorentzPoint3 :=
  ((lorentzBoost3 a b).equivOfDetNeZero (lorentz_boost_det_ne_zero3 hd)).toContinuousLinearEquiv

theorem lorentz_boost_equiv_apply3 {a b : ℝ} (hd : 1-a^2-b^2 ≠ 0) (v : LorentzPoint3) :
    lorentzBoostEquiv3 hd v = lorentzBoost3 a b v := rfl

theorem lorentz_boost_volume_preserving3 {a b : ℝ} (hd : 1-a^2-b^2 ≠ 0) :
    MeasurePreserving (lorentzBoost3 a b) := by
  refine ⟨(lorentzBoost3 a b).continuous_of_finiteDimensional.measurable, ?_⟩
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume (lorentz_boost_det_ne_zero3 hd),
    abs_inv,lorentz_boost_abs_det3 hd]
  simp

theorem lorentz_boost_future_time3 {a b : ℝ} (hd : 0 < 1-a^2-b^2)
    {v : LorentzPoint3} (hv : spatialRadius3 v < v 0) :
    0 < lorentzBoost3 a b v 0 := by
  have ht : 0 < v 0 := (spatial_radius_nonneg3 v).trans_lt hv
  have hrad : v 1^2+v 2^2 < v 0^2 := by
    have hs := spatial_radius_sq3 v
    dsimp [spatialSquared3] at hs
    nlinarith [spatial_radius_nonneg3 v]
  have hdot : (a*v 1+b*v 2)^2 ≤ (a^2+b^2)*(v 1^2+v 2^2) := by
    nlinarith [sq_nonneg (a*v 2-b*v 1)]
  have hbound : (a*v 1+b*v 2)^2 ≤ (a^2+b^2)*v 0^2 :=
    hdot.trans (mul_le_mul_of_nonneg_left hrad.le (by positivity))
  have hpos : 0 < ((1-a^2-b^2)*v 0)^2 := sq_pos_of_pos (mul_pos hd ht)
  have hbase : 0 < (1+a^2+b^2)*v 0 := mul_pos (by positivity) ht
  have hn : 0 < (1+a^2+b^2)*v 0+2*a*v 1+2*b*v 2 := by
    nlinarith only [hbound,hpos,hbase,sq_nonneg ((1+a^2+b^2)*v 0+2*(a*v 1+b*v 2))]
  rw [lorentz_boost_apply3]
  change 0 < ((1+a^2+b^2)*v 0+2*a*v 1+2*b*v 2)/(1-a^2-b^2)
  exact div_pos hn hd

theorem lorentz_boost_future3 {a b : ℝ} (hd : 0 < 1-a^2-b^2)
    {v : LorentzPoint3} (hv : spatialRadius3 v < v 0) :
    spatialRadius3 (lorentzBoost3 a b v) < lorentzBoost3 a b v 0 := by
  have ht := lorentz_boost_future_time3 hd hv
  have he := lorentz_boost_square3 hd.ne' v
  have h1 := spatial_radius_sq3 v
  have h2 := spatial_radius_sq3 (lorentzBoost3 a b v)
  dsimp [lorentzSquare3] at he
  nlinarith [spatial_radius_nonneg3 v,spatial_radius_nonneg3 (lorentzBoost3 a b v)]

theorem lorentz_boost_chronological3 {a b : ℝ} (hd : 0 < 1-a^2-b^2)
    {p q : LorentzPoint3} (hpq : chronological3 p q) :
    chronological3 (lorentzBoost3 a b p) (lorentzBoost3 a b q) := by
  have h := lorentz_boost_future3 hd hpq
  rw [map_sub] at h
  exact h

theorem lorentz_boost_chronological_iff3 {a b : ℝ} (hd : 0 < 1-a^2-b^2)
    (p q : LorentzPoint3) :
    chronological3 (lorentzBoost3 a b p) (lorentzBoost3 a b q) ↔ chronological3 p q := by
  constructor
  · intro h
    have hh := lorentz_boost_chronological3 (a := -a) (b := -b) (by simpa using hd) h
    simpa only [lorentz_boost_inverse3 hd.ne'] using hh
  · exact lorentz_boost_chronological3 hd

#print axioms lorentz_boost_inverse3
#print axioms lorentz_boost_bilinear3
#print axioms lorentz_boost_abs_det3
#print axioms lorentz_boost_volume_preserving3
#print axioms lorentz_boost_future3
#print axioms lorentz_boost_chronological_iff3
end
end QuantyraNullCone
