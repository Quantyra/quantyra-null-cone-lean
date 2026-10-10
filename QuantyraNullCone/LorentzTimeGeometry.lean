import QuantyraNullCone.LorentzTimeFamily
import QuantyraNullCone.LorentzTimeEnvelope
import QuantyraNullCone.LorentzDensityForward

namespace QuantyraNullCone
open MeasureTheory Set
noncomputable section
set_option maxHeartbeats 1200000

theorem density_time_weight_family_lower3 {rho : LorentzPoint3 → ℝ} {p : LorentzPoint3}
    (hr : 19/20 ≤ rho p) : 96/125 ≤ densityTimeWeight3 rho p := by
  have hr0 : 0 ≤ rho p := by linarith
  have hw0 : 0 ≤ densityTimeWeight3 rho p :=
    Real.rpow_nonneg (div_nonneg hr0 lorentz_volume_pos3.le) _
  have he : lorentzVolume3 * densityTimeWeight3 rho p ^ 3 = rho p := by
    rw [density_time_weight_cube3 hr0, mul_div_cancel₀ _ lorentz_volume_pos3.ne']
  have hv : lorentzVolume3 ≤ 1571/750 := by
    unfold lorentzVolume3
    linarith [Real.pi_lt_d4]
  by_contra hn
  have hp := pow_le_pow_left₀ hw0 (le_of_not_ge hn) 3
  have hm := mul_le_mul hv hp (pow_nonneg hw0 _) (by norm_num : (0 : ℝ) ≤ 1571/750)
  rw [he] at hm
  norm_num at hm
  linarith

/-- A difference-of-cubes proof gives the family constant without differentiating real powers. -/
theorem density_time_weight_family_difference3 {rho sigma : LorentzPoint3 → ℝ}
    {p : LorentzPoint3} (hr : 19/20 ≤ rho p) (hs : 19/20 ≤ sigma p) :
    |densityTimeWeight3 rho p - densityTimeWeight3 sigma p| ≤ (27/100)*|rho p-sigma p| := by
  let u := densityTimeWeight3 rho p
  let v := densityTimeWeight3 sigma p
  have hu : 96/125 ≤ u := density_time_weight_family_lower3 hr
  have hv : 96/125 ≤ v := density_time_weight_family_lower3 hs
  have huc : lorentzVolume3*u^3 = rho p := by
    dsimp [u]
    rw [density_time_weight_cube3 (by linarith), mul_div_cancel₀ _ lorentz_volume_pos3.ne']
  have hvc : lorentzVolume3*v^3 = sigma p := by
    dsimp [v]
    rw [density_time_weight_cube3 (by linarith), mul_div_cancel₀ _ lorentz_volume_pos3.ne']
  have huv : (96/125 : ℝ)*(96/125) ≤ u*v :=
    mul_le_mul hu hv (by norm_num) (by linarith)
  have hsum : 3*(96/125 : ℝ)^2 ≤ u^2+u*v+v^2 := by nlinarith
  have hvol : 157/75 ≤ lorentzVolume3 := by
    unfold lorentzVolume3
    linarith [Real.pi_gt_d2]
  have hfac : 100/27 ≤ lorentzVolume3*(u^2+u*v+v^2) := by
    have h := mul_le_mul hvol hsum (by norm_num : (0 : ℝ) ≤ 3*(96/125)^2)
      lorentz_volume_pos3.le
    norm_num at h
    linarith
  change |u-v| ≤ (27/100)*|rho p-sigma p|
  rcases le_total u v with h | h
  · have hh := mul_le_mul_of_nonneg_right hfac (sub_nonneg.mpr h)
    have he : lorentzVolume3*(u^2+u*v+v^2)*(v-u) = sigma p-rho p := by
      nlinarith only [huc,hvc]
    rw [he] at hh
    have hrle : rho p ≤ sigma p := by linarith
    rw [abs_of_nonpos (sub_nonpos.mpr h), abs_of_nonpos (sub_nonpos.mpr hrle)]
    linarith
  · have hh := mul_le_mul_of_nonneg_right hfac (sub_nonneg.mpr h)
    have he : lorentzVolume3*(u^2+u*v+v^2)*(u-v) = rho p-sigma p := by
      nlinarith only [huc,hvc]
    rw [he] at hh
    have hsle : sigma p ≤ rho p := by linarith
    rw [abs_of_nonneg (sub_nonneg.mpr h), abs_of_nonneg (sub_nonneg.mpr hsle)]
    linarith

theorem time_quadratic_weight_envelope3 {theta phi : ℝ}
    (ht : theta ∈ Icc (0 : ℝ) (1/2)) (hf : phi ∈ Icc (0 : ℝ) (1/2))
    {p : LorentzPoint3} (hp : p ∈ closedLorentzDiamond3) :
    |densityTimeWeight3 (timeQuadraticDensity3 theta) p -
      densityTimeWeight3 (timeQuadraticDensity3 phi) p| ≤
        ((27/100)*|theta-phi|)*timeShapeEnvelope3 (p 0) := by
  have h := density_time_weight_family_difference3
    (time_quadratic_density_bounds3 ht hp).1 (time_quadratic_density_bounds3 hf hp).1
  rw [time_quadratic_density_difference3] at h
  have hm := mul_le_mul_of_nonneg_left (abs_time_shape_le_envelope3 (p 0))
    (show 0 ≤ (27/100)*|theta-phi| by positivity)
  dsimp [timeQuadraticShape3] at h
  nlinarith only [h,hm]

theorem FutureCurve3.time_quadratic_length_difference {p q : LorentzPoint3}
    (c : FutureCurve3 p q) {theta phi : ℝ}
    (ht : theta ∈ Icc (0 : ℝ) (1/2)) (hf : phi ∈ Icc (0 : ℝ) (1/2)) :
    |c.weightedLength (densityTimeWeight3 (timeQuadraticDensity3 theta)) -
      c.weightedLength (densityTimeWeight3 (timeQuadraticDensity3 phi))| ≤
        (3/20)*|theta-phi| := by
  let w := densityTimeWeight3 (timeQuadraticDensity3 theta)
  let z := densityTimeWeight3 (timeQuadraticDensity3 phi)
  let K : ℝ := (27/100)*|theta-phi|
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hw := (time_quadratic_density_class3 ht).timeWeight
  have hz := (time_quadratic_density_class3 hf).timeWeight
  change |c.weightedLength w-c.weightedLength z| ≤ _
  unfold FutureCurve3.weightedLength
  rw [← integral_sub (c.integrable_weightedSpeed hw) (c.integrable_weightedSpeed hz)]
  have hle : (∫ t, |w (c.point t)*c.flatSpeed t-z (c.point t)*c.flatSpeed t| ∂curveMeasure) ≤
      ∫ t, K*(timeShapeEnvelope3 (c.coord 0 t)*deriv (c.coord 0) t) ∂curveMeasure := by
    apply integral_mono_ae ((c.integrable_weightedSpeed hw).sub
      (c.integrable_weightedSpeed hz)).abs (c.integrable_time_envelope.const_mul K)
    filter_upwards [self_mem_ae_restrict measurableSet_Icc,c.future] with t hmem hfuture
    change |w (c.point t)*c.flatSpeed t-z (c.point t)*c.flatSpeed t| ≤ _
    rw [← sub_mul, abs_mul, abs_of_nonneg
      (show 0 ≤ c.flatSpeed t from flat_proper_speed_nonneg3 _)]
    have he := time_quadratic_weight_envelope3 ht hf (c.inDiamond t hmem)
    have hs : c.flatSpeed t ≤ deriv (c.coord 0) t := flat_proper_speed_le_time3 hfuture
    have h := mul_le_mul he hs (flat_proper_speed_nonneg3 _)
      (mul_nonneg hK (time_shape_envelope_nonneg3 _))
    simpa only [w,z,K,FutureCurve3.point,PiLp.toLp_apply,mul_assoc] using h
  rw [integral_const_mul] at hle
  have hb := mul_le_mul_of_nonneg_left c.integral_time_envelope_le hK
  have hh := abs_integral_le_integral_abs.trans (hle.trans hb)
  dsimp [K] at hh
  nlinarith only [hh]

theorem time_quadratic_separation_le_add3 {theta phi : ℝ}
    (ht : theta ∈ Icc (0 : ℝ) (1/2)) (hf : phi ∈ Icc (0 : ℝ) (1/2))
    (p q : LorentzPoint3) :
    weightedTimeSeparation3 (densityTimeWeight3 (timeQuadraticDensity3 theta)) p q ≤
      weightedTimeSeparation3 (densityTimeWeight3 (timeQuadraticDensity3 phi)) p q +
        (3/20)*|theta-phi| := by
  apply csSup_le (by simp : (insert 0 (range (fun c : FutureCurve3 p q =>
    c.weightedLength (densityTimeWeight3 (timeQuadraticDensity3 theta))))).Nonempty)
  rintro x (hx | ⟨c,rfl⟩)
  · subst x
    have h := weighted_time_separation_nonneg3 (time_quadratic_density_class3 hf).timeWeight p q
    positivity
  · have h := (abs_le.mp (c.time_quadratic_length_difference ht hf)).2
    linarith [c.weightedLength_le_timeSeparation (time_quadratic_density_class3 hf).timeWeight]

theorem time_quadratic_separation_difference3 {theta phi : ℝ}
    (ht : theta ∈ Icc (0 : ℝ) (1/2)) (hf : phi ∈ Icc (0 : ℝ) (1/2))
    (p q : LorentzPoint3) :
    |weightedTimeSeparation3 (densityTimeWeight3 (timeQuadraticDensity3 theta)) p q -
      weightedTimeSeparation3 (densityTimeWeight3 (timeQuadraticDensity3 phi)) p q| ≤
        (3/20)*|theta-phi| := by
  have h1 := time_quadratic_separation_le_add3 ht hf p q
  have h2 := time_quadratic_separation_le_add3 hf ht p q
  rw [abs_sub_comm phi theta] at h2
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem time_quadratic_shape_abs_integral3 :
    (∫ p, |timeQuadraticShape3 p| ∂flatDiamondMeasure3) ≤ 3/20 := by
  letI := flat_diamond_probability3
  have hi := continuous_integrable_flat3 continuous_time_quadratic_shape3
  have hi2 := continuous_integrable_flat3 (continuous_time_quadratic_shape3.pow 2)
  have hp (p : LorentzPoint3) : |timeQuadraticShape3 p| ≤
      (10/3)*timeQuadraticShape3 p^2+3/40 := by
    nlinarith [sq_nonneg (|timeQuadraticShape3 p|-3/20),sq_abs (timeQuadraticShape3 p)]
  have h := integral_mono_ae hi.abs ((hi2.const_mul (10/3)).add (integrable_const (3/40)))
    (Filter.Eventually.of_forall hp)
  change (∫ p, |timeQuadraticShape3 p| ∂flatDiamondMeasure3) ≤
    ∫ p, (10/3)*timeQuadraticShape3 p^2+3/40 ∂flatDiamondMeasure3 at h
  rw [integral_add (hi2.const_mul _) (integrable_const _), integral_const_mul,
    time_quadratic_shape_second_moment3] at h
  norm_num at h
  linarith

theorem common_density_integral_abs3 {rho sigma : LorentzPoint3 → ℝ}
    (hR : InDensityClass3 rho) (hS : InDensityClass3 sigma) :
    (∫ p, min (rho p) (sigma p) ∂flatDiamondMeasure3) =
      1-(∫ p, |rho p-sigma p| ∂flatDiamondMeasure3)/2 := by
  have he : (fun p => min (rho p) (sigma p)) =
      (fun p => (rho p+sigma p-|rho p-sigma p|)/2) := by
    funext p
    rcases le_total (rho p) (sigma p) with h | h
    · rw [min_eq_left h,abs_of_nonpos (sub_nonpos.mpr h)]; ring
    · rw [min_eq_right h,abs_of_nonneg (sub_nonneg.mpr h)]; ring
  have hadd : Integrable (fun p => rho p+sigma p) flatDiamondMeasure3 :=
    hR.integrable.add hS.integrable
  have habs : Integrable (fun p => |rho p-sigma p|) flatDiamondMeasure3 :=
    (hR.integrable.sub hS.integrable).abs
  rw [he,integral_div,integral_sub hadd habs, integral_add hR.integrable hS.integrable,
    hR.normalized,hS.normalized]
  ring

theorem time_quadratic_common_missing3 {theta phi : ℝ}
    (ht : theta ∈ Icc (0 : ℝ) (1/2)) (hf : phi ∈ Icc (0 : ℝ) (1/2)) :
    1-commonDensityMeasure3 (timeQuadraticDensity3 theta) (timeQuadraticDensity3 phi) univ ≤
      ENNReal.ofReal (((3/20)*|theta-phi|)/2) := by
  have hR := time_quadratic_density_class3 ht
  have hS := time_quadratic_density_class3 hf
  have hd : (∫ p, |timeQuadraticDensity3 theta p-timeQuadraticDensity3 phi p|
      ∂flatDiamondMeasure3) ≤ (3/20)*|theta-phi| := by
    simp_rw [time_quadratic_density_difference3]
    rw [integral_const_mul]
    have h := mul_le_mul_of_nonneg_left time_quadratic_shape_abs_integral3 (abs_nonneg (theta-phi))
    nlinarith only [h]
  have hl := common_density_integral_abs3 hR hS
  have hi : 0 ≤ ∫ p, min (timeQuadraticDensity3 theta p) (timeQuadraticDensity3 phi p)
      ∂flatDiamondMeasure3 := by
    apply integral_nonneg_of_ae
    filter_upwards [flat_diamond3_ae_mem] with p hp
    change 0 ≤ min (timeQuadraticDensity3 theta p) (timeQuadraticDensity3 phi p)
    exact le_min (by linarith [(hR.bounds p hp).1]) (by linarith [(hS.bounds p hp).1])
  apply tsub_le_iff_right.mpr
  rw [common_density_mass3 hR hS, ← ENNReal.ofReal_add (by positivity) hi]
  simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal
    (show 1 ≤ ((3/20)*|theta-phi|)/2 +
      ∫ p, min (timeQuadraticDensity3 theta p) (timeQuadraticDensity3 phi p)
        ∂flatDiamondMeasure3 by linarith)

/-- The restricted geometric constant for the original sampling law and actual AC time loss. -/
theorem time_quadratic_geometric_bound3 {theta phi : ℝ}
    (ht : theta ∈ Icc (0 : ℝ) (1/2)) (hf : phi ∈ Icc (0 : ℝ) (1/2)) :
    geometricDistortion3 (time_quadratic_density_class3 ht) (time_quadratic_density_class3 hf) ≤
      (3/20)*|theta-phi| := by
  have hR := time_quadratic_density_class3 ht
  have hS := time_quadratic_density_class3 hf
  letI := hR.closedDensity_isProbabilityMeasure
  letI := hS.closedDensity_isProbabilityMeasure
  letI : IsFiniteMeasure (commonDensityMeasure3 (timeQuadraticDensity3 theta)
      (timeQuadraticDensity3 phi)) :=
    isFiniteMeasure_of_le (closedDensityMeasure3 _) (common_density_le_left3 _ _)
  apply timeDistortionLoss_le_of_common
    (tx := quotientTime3 hR.timeWeight) (ty := quotientTime3 hS.timeWeight)
    (common_density_le_left3 _ _) (common_density_le_right3 _ _)
    (continuous_timeProfileProjection3 hR.timeWeight).measurable
    (continuous_timeProfileProjection3 hS.timeWeight).measurable
    (continuous_quotientTime3 hR.timeWeight).measurable
    (continuous_quotientTime3 hS.timeWeight).measurable (by positivity)
  · have h := time_quadratic_common_missing3 ht hf
    calc
      _ ≤ ENNReal.ofReal (((3/20)*|theta-phi|)/2) +
          ENNReal.ofReal (((3/20)*|theta-phi|)/2) := add_le_add h h
      _ = ENNReal.ofReal ((3/20)*|theta-phi|) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
  · intro p q
    rw [quotientTime3_projection,quotientTime3_projection]
    exact time_quadratic_separation_difference3 ht hf p.val q.val

#print axioms density_time_weight_family_difference3
#print axioms FutureCurve3.time_quadratic_length_difference
#print axioms time_quadratic_separation_difference3
#print axioms time_quadratic_shape_abs_integral3
#print axioms time_quadratic_common_missing3
#print axioms time_quadratic_geometric_bound3
end
end QuantyraNullCone
