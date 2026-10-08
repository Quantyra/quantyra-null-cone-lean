import QuantyraNullCone.DKWShape

namespace QuantyraNullCone

theorem dkw_likelihood_derivative_stationarity {e p : ℝ} (he : 0 < e)
    (hp : 0 < p) (hpe : p < 1 - e) :
    dkwLikelihoodDerivative e (e / (1 - p - e)) p = dkwStationarity e p := by
  have hd : 0 < 1 - p - e := by linarith
  have hp1 : 0 < 1 - p := by linarith
  have hL : 0 < e / (1 - p - e) := div_pos he hd
  have h1 : 1 + (e / (1 - p - e)) / p =
      (1 + e / p) * (1 + e / (1 - p - e)) := by
    field_simp [ne_of_gt hp, ne_of_gt hd]
    ring
  have hTerm : (e / (1 - p - e)) * (p + e) /
      (p * (p + e / (1 - p - e))) = e / (p * (1 - p)) := by
    have hLeft : p * (p + e / (1 - p - e)) ≠ 0 := ne_of_gt (by positivity)
    have hRight : p * (1 - p) ≠ 0 := ne_of_gt (mul_pos hp hp1)
    apply (div_eq_div_iff hLeft hRight).mpr
    field_simp [ne_of_gt hd]
    ring
  unfold dkwLikelihoodDerivative dkwStationarity
  rw [h1, Real.log_mul (ne_of_gt (show 0 < 1 + e / p by positivity))
    (ne_of_gt (show 0 < 1 + e / (1 - p - e) by positivity)), hTerm]

/-- The exact universal likelihood barrier for the sharp one-sided DKW proof.
This is an analytic theorem, not yet the empirical-process probability theorem. -/
theorem dkw_sharp_likelihood_barrier {e : ℝ} (he : 0 < e) (he1 : e < 1) :
    ∃ lambda : ℝ, 0 < lambda ∧ ∀ t : ℝ, 0 < t → t ≤ 1 - e →
      2 * e ^ 2 ≤ dkwLikelihoodBarrier e lambda t := by
  obtain ⟨p, hpLo, hpHalf, hpEnd, hRoot⟩ := dkw_stationarity_root he he1
  have hp : 0 < p := by linarith
  have hd : 0 < 1 - p - e := by linarith
  let lambda := e / (1 - p - e)
  have hL : 0 < lambda := div_pos he hd
  have hStationary : dkwLikelihoodDerivative e lambda p = 0 := by
    exact (dkw_likelihood_derivative_stationarity he hp hpEnd).trans hRoot
  have hDeriv : HasDerivAt (dkwLikelihoodBarrier e lambda) 0 p := by
    rw [← hStationary]
    exact dkw_likelihood_hasDerivAt hL hp
  have hValue : 2 * e ^ 2 ≤ dkwLikelihoodBarrier e lambda p :=
    dkw_likelihood_stationary_value_lower he hp hpEnd
  refine ⟨lambda, hL, ?_⟩
  intro t ht htEnd
  by_cases hLE : lambda ≤ 2 * e
  · exact hValue.trans (dkw_convex_stationary_min
      (dkw_likelihood_convex_all he.le hL hLE) hp ht hDeriv)
  have hEL : 2 * e < lambda := lt_of_not_ge hLE
  let c := dkwInflection e lambda
  have hc : 0 < c := div_pos (mul_pos he hL) (sub_pos.mpr hEL)
  have hCancellation : lambda * (1 - p - e) = e := div_mul_cancel₀ e (ne_of_gt hd)
  have hHalf : (1 / 2 : ℝ) ≤ c := by
    apply (le_div_iff₀ (sub_pos.mpr hEL)).mpr
    have hProd : 0 ≤ lambda * (1 / 2 - p) :=
      mul_nonneg hL.le (sub_nonneg.mpr hpHalf)
    nlinarith only [hProd, hCancellation]
  have hPC : p ≤ c := hpHalf.trans hHalf
  have hConv := dkw_likelihood_convex_left hL hEL
  by_cases htC : t ≤ c
  · exact hValue.trans (dkw_convex_stationary_min hConv ⟨hp, hPC⟩ ⟨ht, htC⟩ hDeriv)
  have hCt : c < t := lt_of_not_ge htC
  have hValueC : 2 * e ^ 2 ≤ dkwLikelihoodBarrier e lambda c :=
    hValue.trans (dkw_convex_stationary_min hConv ⟨hp, hPC⟩ ⟨hc, le_rfl⟩ hDeriv)
  have hValueEnd : 2 * e ^ 2 ≤ dkwLikelihoodBarrier e lambda (1 - e) :=
    dkw_barrier_endpoint_lower he he1 hpLo hpEnd
  exact dkw_concave_endpoint_lower (dkw_likelihood_concave_right he hL hEL)
    ⟨hCt.le, htEnd⟩ hValueC hValueEnd

#print axioms dkw_likelihood_derivative_stationarity
#print axioms dkw_sharp_likelihood_barrier

end QuantyraNullCone
