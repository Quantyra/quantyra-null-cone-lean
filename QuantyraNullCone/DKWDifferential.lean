import QuantyraNullCone.DKWAnalytic

namespace QuantyraNullCone

noncomputable def dkwLikelihoodDerivative (e lambda t : ℝ) : ℝ :=
  Real.log (1 + lambda / t) - lambda * (t + e) / (t * (t + lambda))

noncomputable def dkwLikelihoodSecond (e lambda t : ℝ) : ℝ :=
  lambda * (t * (2 * e - lambda) + e * lambda) / (t ^ 2 * (t + lambda) ^ 2)

theorem dkw_likelihood_log_hasDerivAt {lambda t : ℝ} (hL : 0 < lambda) (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => Real.log (1 + lambda / t))
      (-lambda / (t * (t + lambda))) t := by
  have htn : t ≠ 0 := ne_of_gt ht
  have hTL : t + lambda ≠ 0 := ne_of_gt (by positivity)
  have hLT : lambda + t ≠ 0 := ne_of_gt (by positivity)
  have hArg : 1 + lambda / t ≠ 0 := ne_of_gt (by positivity)
  have h := (hasDerivAt_const t (1 : ℝ)).add
    ((hasDerivAt_const t lambda).div (hasDerivAt_id t) htn)
  convert h.log hArg using 1
  dsimp
  field_simp [htn, hTL, hLT, hArg]
  ring

theorem dkw_likelihood_hasDerivAt {e lambda t : ℝ} (hL : 0 < lambda) (ht : 0 < t) :
    HasDerivAt (dkwLikelihoodBarrier e lambda) (dkwLikelihoodDerivative e lambda t) t := by
  have h := (((hasDerivAt_id t).add_const e).mul
    (dkw_likelihood_log_hasDerivAt hL ht)).sub_const (Real.log (1 + lambda))
  convert h using 1
  dsimp [dkwLikelihoodDerivative]
  ring

theorem dkw_likelihood_derivative_hasDerivAt {e lambda t : ℝ}
    (hL : 0 < lambda) (ht : 0 < t) :
    HasDerivAt (dkwLikelihoodDerivative e lambda) (dkwLikelihoodSecond e lambda t) t := by
  have htn : t ≠ 0 := ne_of_gt ht
  have hTL : t + lambda ≠ 0 := ne_of_gt (by positivity)
  have hLT : lambda + t ≠ 0 := ne_of_gt (by positivity)
  have hDen : t * (t + lambda) ≠ 0 := mul_ne_zero htn hTL
  have hN := ((hasDerivAt_id t).add_const e).const_mul lambda
  have hD := (hasDerivAt_id t).mul ((hasDerivAt_id t).add_const lambda)
  have h := (dkw_likelihood_log_hasDerivAt hL ht).sub (hN.div hD hDen)
  convert h using 1
  dsimp [dkwLikelihoodSecond]
  field_simp [htn, hTL, hLT, hDen]
  ring

theorem dkw_likelihood_stationary_value {e p : ℝ} (he : 0 < e) (hp : 0 < p)
    (hpe : p < 1 - e) :
    dkwLikelihoodBarrier e (e / (1 - p - e)) p =
      (p + e) * Real.log ((p + e) / p) +
        (1 - (p + e)) * Real.log ((1 - (p + e)) / (1 - p)) := by
  have hd : 0 < 1 - p - e := by linarith
  have hP : 0 < 1 - p := by linarith
  have hPE : 0 < p + e := by positivity
  have h1 : 1 + e / (1 - p - e) = (1 - p) / (1 - p - e) := by
    apply (eq_div_iff (ne_of_gt hd)).mpr
    rw [add_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt hd)]
    ring
  have h2 : 1 + (e / (1 - p - e)) / p =
      ((p + e) / p) * ((1 - p) / (1 - p - e)) := by
    field_simp [ne_of_gt hp, ne_of_gt hd]
    ring
  have hLog1 := Real.log_mul (div_ne_zero (ne_of_gt hPE) (ne_of_gt hp))
    (div_ne_zero (ne_of_gt hP) (ne_of_gt hd))
  have hNeg : Real.log ((1 - (p + e)) / (1 - p)) =
      -Real.log ((1 - p) / (1 - p - e)) := by
    rw [Real.log_div (by linarith : 1 - (p + e) ≠ 0) (ne_of_gt hP),
      Real.log_div (ne_of_gt hP) (ne_of_gt hd)]
    have hSub : 1 - (p + e) = 1 - p - e := by ring
    rw [hSub]
    ring
  unfold dkwLikelihoodBarrier
  rw [h1, h2, hLog1, hNeg]
  ring

theorem dkw_likelihood_stationary_value_lower {e p : ℝ}
    (he : 0 < e) (hp : 0 < p) (hpe : p < 1 - e) :
    2 * e ^ 2 ≤ dkwLikelihoodBarrier e (e / (1 - p - e)) p := by
  rw [dkw_likelihood_stationary_value he hp hpe]
  have h := dkw_bernoulli_pinsker hp (show p ≤ p + e by linarith)
    (show p + e < 1 by linarith)
  simpa only [add_sub_cancel_left] using h

#print axioms dkw_likelihood_log_hasDerivAt
#print axioms dkw_likelihood_hasDerivAt
#print axioms dkw_likelihood_derivative_hasDerivAt
#print axioms dkw_likelihood_stationary_value_lower

end QuantyraNullCone
