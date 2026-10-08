import QuantyraNullCone.DKWBarrier
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace QuantyraNullCone

noncomputable def dkwBernoulliAdjusted (p q : ℝ) : ℝ :=
  q * Real.log (q / p) + (1 - q) * Real.log ((1 - q) / (1 - p)) - 2 * (q - p) ^ 2

noncomputable def dkwBernoulliDerivative (p q : ℝ) : ℝ :=
  Real.log (q / p) - Real.log ((1 - q) / (1 - p)) - 4 * (q - p)

theorem dkw_bernoulli_adjusted_hasDerivAt {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (hq1 : q < 1) :
    HasDerivAt (dkwBernoulliAdjusted p) (dkwBernoulliDerivative p q) q := by
  have hP : 1 - p ≠ 0 := ne_of_gt (by linarith)
  have hQ : 1 - q ≠ 0 := ne_of_gt (by linarith)
  have hLog1 : q / p ≠ 0 := div_ne_zero (ne_of_gt hq) (ne_of_gt hp)
  have hLog2 : (1 - q) / (1 - p) ≠ 0 := div_ne_zero hQ hP
  have hA := (hasDerivAt_id q).mul (((hasDerivAt_id q).div_const p).log hLog1)
  have hB := ((hasDerivAt_id q).const_sub 1).mul
    ((((hasDerivAt_id q).const_sub 1).div_const (1 - p)).log hLog2)
  have hC := (((hasDerivAt_id q).sub_const p).pow 2).const_mul 2
  convert (hA.add hB).sub hC using 1
  dsimp [dkwBernoulliDerivative]
  field_simp
  ring

theorem dkw_bernoulli_derivative_hasDerivAt {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (hq1 : q < 1) :
    HasDerivAt (dkwBernoulliDerivative p) ((2 * q - 1) ^ 2 / (q * (1 - q))) q := by
  have hP : 1 - p ≠ 0 := ne_of_gt (by linarith)
  have hQ : 1 - q ≠ 0 := ne_of_gt (by linarith)
  have hLog1 : q / p ≠ 0 := div_ne_zero (ne_of_gt hq) (ne_of_gt hp)
  have hLog2 : (1 - q) / (1 - p) ≠ 0 := div_ne_zero hQ hP
  have hA := ((hasDerivAt_id q).div_const p).log hLog1
  have hB := (((hasDerivAt_id q).const_sub 1).div_const (1 - p)).log hLog2
  have hC := ((hasDerivAt_id q).sub_const p).const_mul 4
  convert (hA.sub hB).sub hC using 1
  dsimp only [id]
  field_simp [ne_of_gt hp, ne_of_gt hq, hP, hQ]
  ring

/-- Bernoulli Pinsker in the direction needed by the upper empirical-CDF barrier.
It is derived by two monotonicity arguments from explicit derivatives. -/
theorem dkw_bernoulli_pinsker {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) (hq1 : q < 1) :
    2 * (q - p) ^ 2 ≤ q * Real.log (q / p) +
      (1 - q) * Real.log ((1 - q) / (1 - p)) := by
  have hp1 : p < 1 := hpq.trans_lt hq1
  have hDomain : ∀ x ∈ Set.Icc p q, 0 < x ∧ x < 1 := by
    intro x hx
    exact ⟨hp.trans_le hx.1, hx.2.trans_lt hq1⟩
  have hDerivMono : MonotoneOn (dkwBernoulliDerivative p) (Set.Icc p q) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc p q)
    · intro x hx
      obtain ⟨hx0, hx1⟩ := hDomain x hx
      exact (dkw_bernoulli_derivative_hasDerivAt hp hp1 hx0 hx1).continuousAt.continuousWithinAt
    · intro x hx
      obtain ⟨hx0, hx1⟩ := hDomain x (interior_subset hx)
      exact (dkw_bernoulli_derivative_hasDerivAt hp hp1 hx0 hx1).hasDerivWithinAt
    · intro x hx
      obtain ⟨hx0, hx1⟩ := hDomain x (interior_subset hx)
      exact div_nonneg (sq_nonneg _) (mul_nonneg hx0.le (by linarith))
  have hPrimeZero : dkwBernoulliDerivative p p = 0 := by
    simp [dkwBernoulliDerivative, ne_of_gt hp, ne_of_gt (show 0 < 1 - p by linarith)]
  have hMono : MonotoneOn (dkwBernoulliAdjusted p) (Set.Icc p q) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc p q)
    · intro x hx
      obtain ⟨hx0, hx1⟩ := hDomain x hx
      exact (dkw_bernoulli_adjusted_hasDerivAt hp hp1 hx0 hx1).continuousAt.continuousWithinAt
    · intro x hx
      obtain ⟨hx0, hx1⟩ := hDomain x (interior_subset hx)
      exact (dkw_bernoulli_adjusted_hasDerivAt hp hp1 hx0 hx1).hasDerivWithinAt
    · intro x hx
      have h := hDerivMono ⟨le_rfl, hpq⟩ (interior_subset hx) (interior_subset hx).1
      rwa [hPrimeZero] at h
  have hZero : dkwBernoulliAdjusted p p = 0 := by
    simp [dkwBernoulliAdjusted, ne_of_gt hp, ne_of_gt (show 0 < 1 - p by linarith)]
  have h := hMono ⟨le_rfl, hpq⟩ ⟨hpq, le_rfl⟩ hpq
  rw [hZero] at h
  unfold dkwBernoulliAdjusted at h
  linarith

#print axioms dkw_bernoulli_adjusted_hasDerivAt
#print axioms dkw_bernoulli_derivative_hasDerivAt
#print axioms dkw_bernoulli_pinsker

end QuantyraNullCone
