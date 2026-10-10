import QuantyraNullCone.LorentzWeightedTime
import Mathlib.Analysis.Real.Pi.Bounds

namespace QuantyraNullCone
open Set
noncomputable section

theorem lorentz_volume_rational_bounds3 : 2 < lorentzVolume3 ∧ lorentzVolume3 < 9 / 4 := by
  unfold lorentzVolume3
  constructor <;> linarith [Real.pi_gt_three,Real.pi_lt_d2]

theorem density_time_weight_cube3 {rho : LorentzPoint3 → ℝ} {p : LorentzPoint3}
    (hp : 0 ≤ rho p) : densityTimeWeight3 rho p ^ 3 = rho p / lorentzVolume3 := by
  unfold densityTimeWeight3
  rw [Real.rpow_eq_pow,← Real.rpow_mul_natCast (div_nonneg hp lorentz_volume_pos3.le)]
  norm_num

theorem density_time_weight_lower_rational3 {rho : LorentzPoint3 → ℝ}
    (hR : InDensityClass3 rho) {p : LorentzPoint3} (hp : p ∈ closedLorentzDiamond3) :
    3 / 5 ≤ densityTimeWeight3 rho p := by
  have hr := (hR.bounds p hp).1
  have hn : 0 ≤ rho p := by linarith
  have hc := density_time_weight_cube3 hn
  have hv := lorentz_volume_rational_bounds3
  have he : lorentzVolume3 * densityTimeWeight3 rho p ^ 3 = rho p := by
    rw [hc,mul_div_cancel₀ _ lorentz_volume_pos3.ne']
  have hw := (hR.timeWeight.bounds p hp).1
  have hw0 := hR.timeWeight.lower_pos.le.trans hw
  by_contra h
  have hpow := pow_le_pow_left₀ hw0 (le_of_not_ge h) 3
  have hb := mul_le_mul_of_nonneg_left hpow lorentz_volume_pos3.le
  norm_num at hb
  nlinarith

/-- A rational cube-root bound sufficient for the final forward constant one. -/
theorem density_time_weight_difference3 {rho sigma : LorentzPoint3 → ℝ}
    (hR : InDensityClass3 rho) (hS : InDensityClass3 sigma)
    {p : LorentzPoint3} (hp : p ∈ closedLorentzDiamond3) :
    2 * |densityTimeWeight3 rho p - densityTimeWeight3 sigma p| ≤ |rho p - sigma p| := by
  let u := densityTimeWeight3 rho p
  let v := densityTimeWeight3 sigma p
  have hu : 3 / 5 ≤ u := density_time_weight_lower_rational3 hR hp
  have hv : 3 / 5 ≤ v := density_time_weight_lower_rational3 hS hp
  have hr : 0 ≤ rho p := by linarith [(hR.bounds p hp).1]
  have hs : 0 ≤ sigma p := by linarith [(hS.bounds p hp).1]
  have huc : lorentzVolume3 * u ^ 3 = rho p := by
    dsimp [u]; rw [density_time_weight_cube3 hr,mul_div_cancel₀ _ lorentz_volume_pos3.ne']
  have hvc : lorentzVolume3 * v ^ 3 = sigma p := by
    dsimp [v]; rw [density_time_weight_cube3 hs,mul_div_cancel₀ _ lorentz_volume_pos3.ne']
  have huv : (3 / 5 : ℝ) * (3 / 5) ≤ u * v :=
    mul_le_mul hu hv (by norm_num) (by linarith)
  have hsum : 27 / 25 ≤ u ^ 2 + u * v + v ^ 2 := by nlinarith
  have hfac : 2 ≤ lorentzVolume3 * (u ^ 2 + u * v + v ^ 2) := by
    have h := mul_le_mul (lorentz_volume_rational_bounds3.1.le) hsum
      (by norm_num : (0 : ℝ) ≤ 27 / 25) lorentz_volume_pos3.le
    linarith
  change 2 * |u - v| ≤ |rho p - sigma p|
  rcases le_total u v with h | h
  · have hh := mul_le_mul_of_nonneg_right hfac (sub_nonneg.mpr h)
    have he : lorentzVolume3 * (u ^ 2 + u * v + v ^ 2) * (v - u) = sigma p - rho p := by
      nlinarith only [huc,hvc]
    rw [he] at hh
    have hrle : rho p ≤ sigma p := by linarith
    rw [abs_of_nonpos (sub_nonpos.mpr h),abs_of_nonpos (sub_nonpos.mpr hrle)]
    linarith
  · have hh := mul_le_mul_of_nonneg_right hfac (sub_nonneg.mpr h)
    have he : lorentzVolume3 * (u ^ 2 + u * v + v ^ 2) * (u - v) = rho p - sigma p := by
      nlinarith only [huc,hvc]
    rw [he] at hh
    have hsle : sigma p ≤ rho p := by linarith
    rw [abs_of_nonneg (sub_nonneg.mpr h),abs_of_nonneg (sub_nonneg.mpr hsle)]
    exact hh

theorem density_time_separation_difference3 {rho sigma : LorentzPoint3 → ℝ}
    (hR : InDensityClass3 rho) (hS : InDensityClass3 sigma) {delta : ℝ} (hd : 0 ≤ delta)
    (hc : ∀ p ∈ closedLorentzDiamond3, |rho p - sigma p| ≤ delta) (p q : LorentzPoint3) :
    |weightedTimeSeparation3 (densityTimeWeight3 rho) p q -
      weightedTimeSeparation3 (densityTimeWeight3 sigma) p q| ≤ delta := by
  have h := weighted_time_separation_difference3 hR.timeWeight hS.timeWeight
    (show 0 ≤ delta / 2 by positivity)
    (fun p hp => by linarith [density_time_weight_difference3 hR hS hp,hc p hp]) p q
  linarith

#print axioms lorentz_volume_rational_bounds3
#print axioms density_time_weight_cube3
#print axioms density_time_weight_lower_rational3
#print axioms density_time_weight_difference3
#print axioms density_time_separation_difference3

end
end QuantyraNullCone
