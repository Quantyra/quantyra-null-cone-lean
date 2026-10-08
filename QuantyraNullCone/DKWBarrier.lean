import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace QuantyraNullCone

/-- Elementary analytic bounds used in the sharp-DKW likelihood barrier.
This module does not yet prove DKW concentration. -/
theorem dkw_log_ratio_lower {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) :
    2 * z ≤ Real.log ((1 + z) / (1 - z)) := by
  have h := Real.sum_range_le_log_div hz hz1 1
  simp only [Finset.sum_range_one, Nat.cast_zero, mul_zero, zero_add, pow_one,
    div_one] at h
  linarith

theorem dkw_log_ratio_upper {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) :
    Real.log ((1 + z) / (1 - z)) ≤ 2 * z / (1 - z ^ 2) := by
  have h := Real.log_div_le_sum_range_add hz hz1 0
  simp only [Finset.sum_range_zero, mul_zero, zero_add, pow_one] at h
  rw [mul_div_assoc]
  linarith

noncomputable def dkwStationarity (e p : ℝ) : ℝ :=
  Real.log (1 + e / p) + Real.log (1 + e / (1 - p - e)) - e / (p * (1 - p))

theorem dkw_stationarity_center_nonpos {e : ℝ} (he : 0 < e) (he1 : e < 1) :
    dkwStationarity e ((1 - e) / 2) ≤ 0 := by
  have hd : 1 - e ≠ 0 := ne_of_gt (by linarith)
  have hd2 : 1 - e ^ 2 ≠ 0 := ne_of_gt (by nlinarith)
  have hPlus : 1 + e ≠ 0 := ne_of_gt (by linarith)
  have h1 : 1 + e / ((1 - e) / 2) = (1 + e) / (1 - e) := by
    field_simp [hd, hd2, hPlus]
    ring
  have h2 : 1 - (1 - e) / 2 - e = (1 - e) / 2 := by ring
  have h3 : e / (((1 - e) / 2) * (1 - (1 - e) / 2)) =
      4 * e / (1 - e ^ 2) := by
    have hLeft : ((1 - e) / 2) * (1 - (1 - e) / 2) ≠ 0 :=
      ne_of_gt (mul_pos (by linarith) (by linarith))
    apply (div_eq_div_iff hLeft hd2).mpr
    ring
  unfold dkwStationarity
  rw [h2, h1, h3]
  have h := dkw_log_ratio_upper he.le he1
  have hDouble : 4 * e / (1 - e ^ 2) = 2 * (2 * e / (1 - e ^ 2)) := by ring
  rw [hDouble]
  linarith

theorem dkw_stationarity_half_nonneg {e : ℝ} (he : 0 < e) (heHalf : e < 1 / 2) :
    0 ≤ dkwStationarity e (1 / 2) := by
  have ha : 0 < 1 + e / (1 / 2 : ℝ) := by positivity
  have hb : 0 < 1 + e / (1 - (1 / 2 : ℝ) - e) := by
    have : 0 < 1 - (1 / 2 : ℝ) - e := by linarith
    positivity
  have hProduct : (1 + e / (1 / 2 : ℝ)) * (1 + e / (1 - (1 / 2 : ℝ) - e)) =
      (1 + 2 * e) / (1 - 2 * e) := by
    have hd : 1 - 2 * e ≠ 0 := ne_of_gt (by linarith)
    have hd' : 1 - (1 / 2 : ℝ) - e ≠ 0 := ne_of_gt (by linarith)
    have hEqual : 1 - 2 * e = 2 * (1 - (1 / 2 : ℝ) - e) := by ring
    have hSecond : 1 + e / (1 - (1 / 2 : ℝ) - e) = 1 / (1 - 2 * e) := by
      apply (eq_div_iff hd).mpr
      rw [hEqual]
      calc
        (1 + e / (1 - (1 / 2 : ℝ) - e)) * (2 * (1 - (1 / 2 : ℝ) - e)) =
            2 * (1 - (1 / 2 : ℝ) - e) +
              2 * (e / (1 - (1 / 2 : ℝ) - e) * (1 - (1 / 2 : ℝ) - e)) := by ring
        _ = 1 := by rw [div_mul_cancel₀ _ hd']; ring
    rw [hSecond]
    norm_num
    ring
  have hLogs := Real.log_mul (ne_of_gt ha) (ne_of_gt hb)
  have h := dkw_log_ratio_lower (show 0 ≤ 2 * e by positivity)
    (show 2 * e < 1 by linarith)
  unfold dkwStationarity
  rw [← hLogs, hProduct]
  norm_num
  linarith

noncomputable def dkwLikelihoodBarrier (e lambda t : ℝ) : ℝ :=
  (t + e) * Real.log (1 + lambda / t) - Real.log (1 + lambda)

theorem dkw_barrier_endpoint_identity {e p : ℝ} (he : 0 < e) (he1 : e < 1)
    (hpe : p < 1 - e) :
    dkwLikelihoodBarrier e (e / (1 - p - e)) (1 - e) =
      Real.log (1 + e ^ 2 / ((1 - e) * (1 - p))) := by
  have hd : 0 < 1 - p - e := by linarith
  have hE : 0 < 1 - e := by linarith
  have hP : 0 < 1 - p := by linarith
  have hA : 0 < 1 + (e / (1 - p - e)) / (1 - e) := by positivity
  have hB : 0 < 1 + e / (1 - p - e) := by positivity
  have hRatio : (1 + (e / (1 - p - e)) / (1 - e)) /
      (1 + e / (1 - p - e)) = 1 + e ^ 2 / ((1 - e) * (1 - p)) := by
    field_simp
    ring
  unfold dkwLikelihoodBarrier
  rw [sub_add_cancel, one_mul, ← Real.log_div (ne_of_gt hA) (ne_of_gt hB), hRatio]

theorem dkw_barrier_endpoint_lower {e p : ℝ} (he : 0 < e) (he1 : e < 1)
    (hp : (1 - e) / 2 ≤ p) (hpe : p < 1 - e) :
    2 * e ^ 2 ≤ dkwLikelihoodBarrier e (e / (1 - p - e)) (1 - e) := by
  have hE : 0 < 1 - e := by linarith
  have hP : 0 < 1 - p := by linarith
  have hSq : e ^ 2 < 1 := by nlinarith
  have hD : 0 < 1 - e ^ 2 := by linarith
  have hBound : (1 - e) * (1 - p) ≤ (1 - e ^ 2) / 2 := by nlinarith
  have hDiv := div_le_div_of_nonneg_left (sq_nonneg e)
    (show 0 < (1 - e) * (1 - p) by positivity) hBound
  have hRatio : (1 + e ^ 2) / (1 - e ^ 2) = 1 + e ^ 2 / ((1 - e ^ 2) / 2) := by
    field_simp
    ring
  have hLog : Real.log ((1 + e ^ 2) / (1 - e ^ 2)) ≤
      Real.log (1 + e ^ 2 / ((1 - e) * (1 - p))) := by
    apply Real.log_le_log (by positivity)
    rw [hRatio]
    linarith
  rw [dkw_barrier_endpoint_identity he he1 hpe]
  exact (dkw_log_ratio_lower (sq_nonneg e) hSq).trans hLog

#print axioms dkw_stationarity_center_nonpos
#print axioms dkw_stationarity_half_nonneg
#print axioms dkw_barrier_endpoint_identity
#print axioms dkw_barrier_endpoint_lower

end QuantyraNullCone
