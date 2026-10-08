import QuantyraNullCone.DKWBarrier
import Mathlib.Topology.Order.IntermediateValue

namespace QuantyraNullCone

theorem dkw_stationarity_continuousOn {e a b : ℝ} (he : 0 < e)
    (ha : 0 < a) (hb : b < 1 - e) :
    ContinuousOn (dkwStationarity e) (Set.Icc a b) := by
  intro p hp
  have hp0 : 0 < p := ha.trans_le hp.1
  have hpd : 0 < 1 - p - e := by linarith [hp.2]
  have hp1 : 0 < 1 - p := by linarith
  have hL : 0 < 1 + e / p := by positivity
  have hR : 0 < 1 + e / (1 - p - e) := by positivity
  have hFirst : ContinuousAt (fun p : ℝ => Real.log (1 + e / p)) p :=
    (continuousAt_const.add (continuousAt_const.div continuousAt_id (ne_of_gt hp0))).log
      (ne_of_gt hL)
  have hSecond : ContinuousAt (fun p : ℝ => Real.log (1 + e / (1 - p - e))) p :=
    (continuousAt_const.add (continuousAt_const.div
      ((continuousAt_const.sub continuousAt_id).sub continuousAt_const) (ne_of_gt hpd))).log
      (ne_of_gt hR)
  have hLast : ContinuousAt (fun p : ℝ => e / (p * (1 - p))) p :=
    continuousAt_const.div
      (continuousAt_id.mul (continuousAt_const.sub continuousAt_id)) (ne_of_gt (by positivity))
  exact ((hFirst.add hSecond).sub hLast).continuousWithinAt

theorem dkw_stationarity_root_small {e : ℝ} (he : 0 < e) (heHalf : e < 1 / 2) :
    ∃ p : ℝ, (1 - e) / 2 ≤ p ∧ p ≤ 1 / 2 ∧ p < 1 - e ∧
      dkwStationarity e p = 0 := by
  have he1 : e < 1 := by linarith
  have hab : (1 - e) / 2 ≤ (1 / 2 : ℝ) := by linarith
  have hCont := dkw_stationarity_continuousOn he
    (show 0 < (1 - e) / 2 by linarith) (show (1 / 2 : ℝ) < 1 - e by linarith)
  obtain ⟨p, hp, hZero⟩ := intermediate_value_Icc hab hCont
    ⟨dkw_stationarity_center_nonpos he he1, dkw_stationarity_half_nonneg he heHalf⟩
  exact ⟨p, hp.1, hp.2, by linarith [hp.2], hZero⟩

noncomputable def dkwLargeRootUpper (e : ℝ) : ℝ :=
  1 - e - (1 - e) / 2 * Real.exp (-4 / (1 - e))

theorem dkw_large_root_upper_bounds {e : ℝ} (heHalf : 1 / 2 ≤ e) (he1 : e < 1) :
    (1 - e) / 2 ≤ dkwLargeRootUpper e ∧ dkwLargeRootUpper e ≤ 1 / 2 ∧
      dkwLargeRootUpper e < 1 - e := by
  have hE : 0 < 1 - e := by linarith
  have hExp : Real.exp (-4 / (1 - e)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by norm_num) hE.le)
  have hProd : (1 - e) / 2 * Real.exp (-4 / (1 - e)) ≤ (1 - e) / 2 :=
    (mul_le_mul_of_nonneg_left hExp (by positivity)).trans_eq (mul_one _)
  have hPos : 0 < (1 - e) / 2 * Real.exp (-4 / (1 - e)) := by positivity
  unfold dkwLargeRootUpper
  constructor
  · linarith
  constructor <;> linarith

theorem dkw_stationarity_large_upper_nonneg {e : ℝ}
    (heHalf : 1 / 2 ≤ e) (he1 : e < 1) :
    0 ≤ dkwStationarity e (dkwLargeRootUpper e) := by
  have he : 0 < e := by linarith
  have hE : 0 < 1 - e := by linarith
  obtain ⟨hpLo, hpHi, hpEnd⟩ := dkw_large_root_upper_bounds heHalf he1
  let p := dkwLargeRootUpper e
  let s := (1 - e) / 2 * Real.exp (-4 / (1 - e))
  have hs : 0 < s := by dsimp [s]; positivity
  have hp : 0 < p := by dsimp [p]; linarith
  have hp1 : 0 < 1 - p := by dsimp [p]; linarith
  have hDen : 1 - p - e = s := by dsimp [p, s, dkwLargeRootUpper]; ring
  have hProd : Real.exp (4 / (1 - e)) * s = (1 - e) / 2 := by
    dsimp [s]
    rw [mul_left_comm, ← Real.exp_add]
    have : 4 / (1 - e) + -4 / (1 - e) = 0 := by ring
    rw [this, Real.exp_zero, mul_one]
  have hRatio : Real.exp (4 / (1 - e)) ≤ e / s := by
    apply (le_div_iff₀ hs).mpr
    rw [hProd]
    linarith
  have hLog : 4 / (1 - e) ≤ Real.log (1 + e / s) := by
    have hArg : Real.exp (4 / (1 - e)) ≤ 1 + e / s := hRatio.trans (by linarith)
    have h := Real.log_le_log (Real.exp_pos (4 / (1 - e)))
      hArg
    rwa [Real.log_exp] at h
  have hFirst : 0 ≤ Real.log (1 + e / p) :=
    Real.log_nonneg (by have : 0 < e / p := div_pos he hp; linarith)
  have hLowerDen : e * ((1 - e) / 2) ≤ p * (1 - p) := by
    have hA : e ≤ 1 - p := by dsimp [p]; linarith [hpEnd]
    have hB : (1 - e) / 2 ≤ p := hpLo
    calc
      e * ((1 - e) / 2) ≤ e * p := mul_le_mul_of_nonneg_left hB he.le
      _ ≤ (1 - p) * p := mul_le_mul_of_nonneg_right hA hp.le
      _ = p * (1 - p) := mul_comm _ _
  have hPenalty : e / (p * (1 - p)) ≤ 2 / (1 - e) := by
    apply (div_le_div_iff₀ (mul_pos hp hp1) hE).mpr
    nlinarith [hLowerDen]
  change 0 ≤ Real.log (1 + e / p) + Real.log (1 + e / (1 - p - e)) -
    e / (p * (1 - p))
  rw [hDen]
  have hExtra : 0 ≤ 2 / (1 - e) := by positivity
  rw [show 4 / (1 - e) = 2 * (2 / (1 - e)) by ring] at hLog
  linarith only [hLog, hFirst, hPenalty, hExtra]

theorem dkw_stationarity_root {e : ℝ} (he : 0 < e) (he1 : e < 1) :
    ∃ p : ℝ, (1 - e) / 2 ≤ p ∧ p ≤ 1 / 2 ∧ p < 1 - e ∧
      dkwStationarity e p = 0 := by
  by_cases hSmall : e < 1 / 2
  · exact dkw_stationarity_root_small he hSmall
  have hHalf : 1 / 2 ≤ e := le_of_not_gt hSmall
  obtain ⟨hLo, hHi, hEnd⟩ := dkw_large_root_upper_bounds hHalf he1
  have hCont := dkw_stationarity_continuousOn he
    (show 0 < (1 - e) / 2 by linarith) hEnd
  obtain ⟨p, hp, hZero⟩ := intermediate_value_Icc hLo hCont
    ⟨dkw_stationarity_center_nonpos he he1, dkw_stationarity_large_upper_nonneg hHalf he1⟩
  exact ⟨p, hp.1, hp.2.trans hHi, hp.2.trans_lt hEnd, hZero⟩

#print axioms dkw_stationarity_root

end QuantyraNullCone
