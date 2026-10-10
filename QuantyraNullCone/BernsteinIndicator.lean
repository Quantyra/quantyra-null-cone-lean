import QuantyraNullCone.BernoulliMGF
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Normed

namespace QuantyraNullCone
open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000

/-- The exponential remainder with the Bernstein denominator, for either sign. -/
theorem exp_remainder_bernstein {x : ℝ} (hx : |x| < 3) :
    Real.exp x-1-x ≤ x^2/(2*(1-|x|/3)) := by
  have hsum : HasSum (fun n : ℕ => x^n/(n.factorial : ℝ)) (Real.exp x) := by
    simpa only [← Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp x
  have hr : |(|x|/3)| < 1 := by rw [abs_of_nonneg (by positivity)]; linarith
  have hgeo : Summable (fun n : ℕ => (|x|/3)^n) :=
    summable_geometric_of_norm_lt_one (by simpa only [Real.norm_eq_abs] using hr)
  have htail : Summable (fun n : ℕ => x^(n+2)/((n+2).factorial : ℝ)) :=
    (summable_nat_add_iff 2).mpr hsum.summable
  have hterm (n : ℕ) : x^(n+2)/((n+2).factorial : ℝ) ≤ (x^2/2)*(|x|/3)^n := by
    have hf : (2 : ℝ)*3^n ≤ (n+2).factorial := by
      have hh := Nat.factorial_mul_pow_le_factorial (m := 2) (n := n)
      norm_num only [Nat.factorial_succ,Nat.factorial_zero,Nat.reduceMul,Nat.reduceAdd] at hh
      simpa only [Nat.add_comm] using (show (2 : ℝ)*3^n ≤ (2+n).factorial by exact_mod_cast hh)
    calc
      _ ≤ |x|^(n+2)/((n+2).factorial : ℝ) := by
        exact div_le_div_of_nonneg_right
          ((le_abs_self _).trans_eq (abs_pow x (n+2))) (by positivity)
      _ ≤ |x|^(n+2)/(2*3^n) := div_le_div_of_nonneg_left (by positivity) (by positivity) hf
      _ = (x^2/2)*(|x|/3)^n := by rw [pow_add,sq_abs,div_pow]; ring
  have hb := htail.tsum_le_tsum hterm (hgeo.mul_left (x^2/2))
  rw [tsum_mul_left,tsum_geometric_of_norm_lt_one (by simpa only [Real.norm_eq_abs] using hr)] at hb
  have he := hsum.summable.sum_add_tsum_nat_add 2
  rw [hsum.tsum_eq] at he
  norm_num [Finset.sum_range_succ] at he
  have halg : x^2/2*(1-|x|/3)⁻¹ = x^2/(2*(1-|x|/3)) := by
    simp only [div_eq_mul_inv,mul_inv]; ring
  rw [halg] at hb
  linarith

theorem exp_mul_bounded_bernstein {t z : ℝ} (ht : |t| < 3) (hz : |z| ≤ 1) :
    Real.exp (t*z) ≤ 1+t*z+(t^2/(2*(1-|t|/3)))*z^2 := by
  have htz : |t*z| ≤ |t| := by
    rw [abs_mul]
    nlinarith [abs_nonneg t]
  have h := exp_remainder_bernstein (htz.trans_lt ht)
  have hd : 0 < 2*(1-|t|/3) := by linarith
  have hc : (t*z)^2/(2*(1-|t*z|/3)) ≤ (t*z)^2/(2*(1-|t|/3)) :=
    div_le_div_of_nonneg_left (sq_nonneg _) hd (by linarith)
  have he : (t*z)^2/(2*(1-|t|/3)) = (t^2/(2*(1-|t|/3)))*z^2 := by ring
  rw [he] at hc
  linarith

theorem centered_indicator_mgf_eq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {S : Set Ω} (hS : MeasurableSet S) (t : ℝ) :
    mgf (fun q => S.indicator (fun _ => (1 : ℝ)) q-μ.real S) μ t =
      μ.real S*Real.exp (t*(1-μ.real S))+(1-μ.real S)*Real.exp (t*(-μ.real S)) := by
  have he := mgf_add_const (X := S.indicator (fun _ => (1 : ℝ))) (μ := μ) (t := t) (-μ.real S)
  simp only [← sub_eq_add_neg,indicator_mgf hS] at he
  rw [he,show t*(1-μ.real S) = t+t*(-μ.real S) by ring,Real.exp_add]
  ring

/-- Exact Bernoulli variance in the two-sided Bernstein MGF bound. -/
theorem centered_indicator_bernstein_mgf {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {S : Set Ω} (hS : MeasurableSet S)
    {t : ℝ} (ht : |t| < 3) :
    mgf (fun q => S.indicator (fun _ => (1 : ℝ)) q-μ.real S) μ t ≤
      Real.exp (μ.real S*(1-μ.real S)*t^2/(2*(1-|t|/3))) := by
  let p := μ.real S
  have hp0 : 0 ≤ p := measureReal_nonneg
  have hp1 : p ≤ 1 := measureReal_le_one
  have h0 := exp_mul_bounded_bernstein ht (z := -p) (by simpa only [abs_neg,abs_of_nonneg hp0] using hp1)
  have h1 := exp_mul_bounded_bernstein ht (z := 1-p)
    (by rw [abs_of_nonneg (by linarith)]; linarith)
  rw [centered_indicator_mgf_eq hS]
  change p*Real.exp (t*(1-p))+(1-p)*Real.exp (t*(-p)) ≤ _
  calc
    _ ≤ p*(1+t*(1-p)+(t^2/(2*(1-|t|/3)))*(1-p)^2) +
        (1-p)*(1+t*(-p)+(t^2/(2*(1-|t|/3)))*(-p)^2) :=
      add_le_add (mul_le_mul_of_nonneg_left h1 hp0) (mul_le_mul_of_nonneg_left h0 (by linarith))
    _ = 1+p*(1-p)*t^2/(2*(1-|t|/3)) := by ring
    _ ≤ Real.exp (p*(1-p)*t^2/(2*(1-|t|/3))) := by
      simpa only [add_comm] using Real.add_one_le_exp (p*(1-p)*t^2/(2*(1-|t|/3)))

#print axioms exp_remainder_bernstein
#print axioms exp_mul_bounded_bernstein
#print axioms centered_indicator_bernstein_mgf
end
end QuantyraNullCone
