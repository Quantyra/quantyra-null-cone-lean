import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace QuantyraNullCone
noncomputable section

def bernsteinRadius (m v s : ℝ) : ℝ := s/(3*m)+Real.sqrt ((s/(3*m))^2+2*v*s/m)

theorem bernsteinRadius_pos {m v s : ℝ} (hm : 0 < m) (hv : 0 < v) (hs : 0 < s) :
    0 < bernsteinRadius m v s := by
  unfold bernsteinRadius
  positivity

theorem bernsteinRadius_identity {m v s : ℝ} (hm : 0 < m) (hv : 0 < v) (hs : 0 < s) :
    m*(bernsteinRadius m v s)^2 = 2*s*(v+bernsteinRadius m v s/3) := by
  have hsqrt := Real.sq_sqrt (show 0 ≤ (s/(3*m))^2+2*v*s/m by positivity)
  have hsq : (bernsteinRadius m v s)^2-2*(s/(3*m))*bernsteinRadius m v s = 2*v*s/m := by
    unfold bernsteinRadius
    nlinarith only [hsqrt]
  have hmul := congrArg (fun z : ℝ => m*z) hsq
  field_simp [hm.ne'] at hmul
  nlinarith only [hmul]

theorem bernsteinRadius_exponent {m v s : ℝ} (hm : 0 < m) (hv : 0 < v) (hs : 0 < s) :
    -m*(bernsteinRadius m v s)^2/(2*(v+bernsteinRadius m v s/3)) = -s := by
  have hr := bernsteinRadius_pos hm hv hs
  have hd : 0 < 2*(v+bernsteinRadius m v s/3) := by positivity
  rw [div_eq_iff hd.ne']
  nlinarith only [bernsteinRadius_identity hm hv hs]

theorem bernstein_log_radius_tail {m v alpha : ℝ} (hm : 0 < m) (hv : 0 < v)
    (ha0 : 0 < alpha) (ha1 : alpha < 1) :
    2*Real.exp (-m*(bernsteinRadius m v (Real.log (2/alpha)))^2/
      (2*(v+bernsteinRadius m v (Real.log (2/alpha))/3))) = alpha := by
  have hs : 0 < Real.log (2/alpha) := Real.log_pos ((lt_div_iff₀ ha0).mpr (by linarith))
  rw [bernsteinRadius_exponent hm hv hs,Real.exp_neg,Real.exp_log (by positivity)]
  field_simp

#print axioms bernsteinRadius_identity
#print axioms bernstein_log_radius_tail
end
end QuantyraNullCone
