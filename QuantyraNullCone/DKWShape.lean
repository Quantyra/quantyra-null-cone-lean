import QuantyraNullCone.DKWDifferential
import Mathlib.Analysis.Convex.Deriv

namespace QuantyraNullCone

theorem dkw_convex_stationary_min {S : Set ℝ} {f : ℝ → ℝ} {p t : ℝ}
    (hConv : ConvexOn ℝ S f) (hp : p ∈ S) (ht : t ∈ S)
    (hDeriv : HasDerivAt f 0 p) : f p ≤ f t := by
  rcases lt_trichotomy t p with htp | htp | hpt
  · have h := hConv.slope_le_of_hasDerivAt ht hp htp hDeriv
    rw [slope_def_field] at h
    have hNum := (div_le_iff₀ (sub_pos.mpr htp)).mp h
    linarith
  · rw [htp]
  · have h := hConv.le_slope_of_hasDerivAt hp ht hpt hDeriv
    rw [slope_def_field] at h
    have hNum := (le_div_iff₀ (sub_pos.mpr hpt)).mp h
    linarith

theorem dkw_concave_endpoint_lower {f : ℝ → ℝ} {a b t B : ℝ}
    (hConc : ConcaveOn ℝ (Set.Icc a b) f) (ht : t ∈ Set.Icc a b)
    (hA : B ≤ f a) (hB : B ≤ f b) : B ≤ f t := by
  by_cases hab : a = b
  · have : t = a := by linarith [ht.1, ht.2]
    simpa [this] using hA
  have habLt : a < b := lt_of_le_of_ne (ht.1.trans ht.2) hab
  let u := (b - t) / (b - a)
  let v := (t - a) / (b - a)
  have hu : 0 ≤ u := div_nonneg (sub_nonneg.mpr ht.2) (sub_pos.mpr habLt).le
  have hv : 0 ≤ v := div_nonneg (sub_nonneg.mpr ht.1) (sub_pos.mpr habLt).le
  have hSum : u + v = 1 := by
    dsimp [u, v]
    field_simp [ne_of_gt (sub_pos.mpr habLt)]
    ring
  have hPoint : u * a + v * b = t := by
    dsimp [u, v]
    field_simp [ne_of_gt (sub_pos.mpr habLt)]
    ring
  have hJ := hConc.2 ⟨le_rfl, habLt.le⟩ ⟨habLt.le, le_rfl⟩ hu hv hSum
  simp only [smul_eq_mul] at hJ
  rw [hPoint] at hJ
  calc
    B = u * B + v * B := by rw [← add_mul, hSum, one_mul]
    _ ≤ u * f a + v * f b := add_le_add
      (mul_le_mul_of_nonneg_left hA hu) (mul_le_mul_of_nonneg_left hB hv)
    _ ≤ f t := hJ

theorem dkw_likelihood_convex_all {e lambda : ℝ} (he : 0 ≤ e)
    (hL : 0 < lambda) (hLE : lambda ≤ 2 * e) :
    ConvexOn ℝ (Set.Ioi 0) (dkwLikelihoodBarrier e lambda) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg
    (f' := dkwLikelihoodDerivative e lambda) (f'' := dkwLikelihoodSecond e lambda)
    (convex_Ioi 0)
  · intro t ht
    exact (dkw_likelihood_hasDerivAt hL ht).continuousAt.continuousWithinAt
  · intro t ht
    exact (dkw_likelihood_hasDerivAt hL (interior_subset ht)).hasDerivWithinAt
  · intro t ht
    exact (dkw_likelihood_derivative_hasDerivAt hL (interior_subset ht)).hasDerivWithinAt
  · intro t ht
    have ht0 : 0 < t := interior_subset ht
    unfold dkwLikelihoodSecond
    apply div_nonneg
    · exact mul_nonneg hL.le (add_nonneg
        (mul_nonneg ht0.le (sub_nonneg.mpr hLE)) (mul_nonneg he hL.le))
    · positivity

noncomputable def dkwInflection (e lambda : ℝ) : ℝ := e * lambda / (lambda - 2 * e)

theorem dkw_likelihood_convex_left {e lambda : ℝ}
    (hL : 0 < lambda) (hLE : 2 * e < lambda) :
    ConvexOn ℝ (Set.Ioc 0 (dkwInflection e lambda)) (dkwLikelihoodBarrier e lambda) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg
    (f' := dkwLikelihoodDerivative e lambda) (f'' := dkwLikelihoodSecond e lambda)
    (convex_Ioc 0 (dkwInflection e lambda))
  · intro t ht
    exact (dkw_likelihood_hasDerivAt hL ht.1).continuousAt.continuousWithinAt
  · intro t ht
    exact (dkw_likelihood_hasDerivAt hL (interior_subset ht).1).hasDerivWithinAt
  · intro t ht
    exact (dkw_likelihood_derivative_hasDerivAt hL (interior_subset ht).1).hasDerivWithinAt
  · intro t ht
    have htD := interior_subset ht
    have hNum : 0 ≤ t * (2 * e - lambda) + e * lambda := by
      have h := (le_div_iff₀ (sub_pos.mpr hLE)).mp htD.2
      change t * (lambda - 2 * e) ≤ e * lambda at h
      nlinarith
    unfold dkwLikelihoodSecond
    exact div_nonneg (mul_nonneg hL.le hNum) (by positivity)

theorem dkw_likelihood_concave_right {e lambda b : ℝ} (he : 0 < e)
    (hL : 0 < lambda) (hLE : 2 * e < lambda) :
    ConcaveOn ℝ (Set.Icc (dkwInflection e lambda) b) (dkwLikelihoodBarrier e lambda) := by
  have hc : 0 < dkwInflection e lambda := div_pos (mul_pos he hL) (sub_pos.mpr hLE)
  apply concaveOn_of_hasDerivWithinAt2_nonpos
    (f' := dkwLikelihoodDerivative e lambda) (f'' := dkwLikelihoodSecond e lambda)
    (convex_Icc (dkwInflection e lambda) b)
  · intro t ht
    exact (dkw_likelihood_hasDerivAt hL (hc.trans_le ht.1)).continuousAt.continuousWithinAt
  · intro t ht
    exact (dkw_likelihood_hasDerivAt hL (hc.trans_le (interior_subset ht).1)).hasDerivWithinAt
  · intro t ht
    exact (dkw_likelihood_derivative_hasDerivAt hL
      (hc.trans_le (interior_subset ht).1)).hasDerivWithinAt
  · intro t ht
    have htD := interior_subset ht
    have hNum : t * (2 * e - lambda) + e * lambda ≤ 0 := by
      have h := (div_le_iff₀ (sub_pos.mpr hLE)).mp htD.1
      change e * lambda ≤ t * (lambda - 2 * e) at h
      nlinarith
    unfold dkwLikelihoodSecond
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hL.le hNum)
      (by positivity)

end QuantyraNullCone
