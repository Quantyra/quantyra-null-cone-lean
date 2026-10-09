import QuantyraNullCone.ThinningMixture
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

namespace QuantyraNullCone

open MeasureTheory

theorem finite_retained_count_mass {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] {pi : Ω → ℝ}
    (hpi : Measurable pi) (hInt : Integrable pi mu)
    (hbounds : ∀ x, pi x ∈ Set.Icc 0 1) (N n : ℕ) :
    (Measure.pi (fun _ : Fin N => mu.prod uniform01Measure)) (retainedCountEvent pi N n) =
      ENNReal.ofReal (binomialMass N n (∫ x, pi x ∂mu)) := by
  by_cases hn : n ≤ N
  · let k : Fin (N+1) := ⟨n, Nat.lt_succ_of_le hn⟩
    have h := detected_count_atom mu hpi hInt hbounds N k
    rw [membershipCountLaw,
      map_measureReal_apply (measurable_of_countable boundedBitCount) (measurableSet_singleton k),
      membershipLaw, map_measureReal_apply (membership_code_measurable (retention_event_measurable hpi))
        ((measurableSet_singleton k).preimage (measurable_of_countable boundedBitCount))] at h
    have hset : membershipCode (retentionEvent pi) ⁻¹' (boundedBitCount ⁻¹' {k}) =
        retainedCountEvent pi N n := by
      ext sample
      simp [retainedCountEvent, boundedBitCount, Fin.ext_iff, k]
    rw [hset] at h
    rw [← ofReal_measureReal (μ := Measure.pi (fun _ : Fin N => mu.prod uniform01Measure)), h]
  · have hset : retainedCountEvent pi N n = ∅ := by
      ext sample
      constructor
      · intro hs
        change bitCount (membershipCode (retentionEvent pi) sample) = n at hs
        have hle := bit_count_le (membershipCode (retentionEvent pi) sample)
        have hfalse : False := by omega
        exact hfalse.elim
      · simp
    rw [hset, measure_empty]
    simp [binomialMass, Nat.choose_eq_zero_of_lt (lt_of_not_ge hn)]

theorem retention_mean_unit {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] {pi : Ω → ℝ} (hInt : Integrable pi mu)
    (hbounds : ∀ x, pi x ∈ Set.Icc 0 1) : (∫ x, pi x ∂mu) ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨integral_nonneg (fun x => (hbounds x).1), ?_⟩
  calc
    _ ≤ ∫ _x, (1 : ℝ) ∂mu := integral_mono hInt (integrable_const _) (fun x => (hbounds x).2)
    _ = 1 := by simp

theorem poisson_binomial_term (kappa p : ℝ) (n r : ℕ) :
    (Real.exp (-kappa) * kappa^(r+n) / (r+n).factorial) * binomialMass (r+n) n p =
      (Real.exp (-kappa) * (kappa*p)^n / n.factorial) *
        ((kappa*(1-p))^r / r.factorial) := by
  have hfact : ((r+n).choose n : ℝ) * (r.factorial : ℝ) * (n.factorial : ℝ) =
      ((r+n).factorial : ℝ) := by
    exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial r n
  have hr : (r.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hc : ((r+n).choose n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.le_add_left n r)).ne'
  simp only [binomialMass, Nat.add_sub_cancel, pow_add, mul_pow]
  rw [← hfact]
  field_simp [hr, hn, hc]

theorem poisson_binomial_hasSum (kappa p : ℝ) (n : ℕ) :
    HasSum (fun N => (Real.exp (-kappa) * kappa^N / N.factorial) * binomialMass N n p)
      (Real.exp (-(kappa*p)) * (kappa*p)^n / n.factorial) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp (kappa*(1-p))).mul_left
    (Real.exp (-kappa) * (kappa*p)^n / n.factorial)
  have hshift : HasSum
      (fun r => (Real.exp (-kappa) * kappa^(r+n) / (r+n).factorial) * binomialMass (r+n) n p)
      (Real.exp (-(kappa*p)) * (kappa*p)^n / n.factorial) := by
    convert h using 1
    · funext r
      exact poisson_binomial_term kappa p n r
    · rw [← Real.exp_eq_exp_ℝ]
      rw [show Real.exp (-kappa) * (kappa*p)^n / n.factorial * Real.exp (kappa*(1-p)) =
        (Real.exp (-kappa) * Real.exp (kappa*(1-p))) * (kappa*p)^n / n.factorial by ring,
        ← Real.exp_add,
        show -kappa + kappa*(1-p) = -(kappa*p) by ring]
  have hzero : ∑ N ∈ Finset.range n,
      (Real.exp (-kappa) * kappa^N / N.factorial) * binomialMass N n p = 0 := by
    apply Finset.sum_eq_zero
    intro N hN
    simp [binomialMass, Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hN)]
  simpa only [hzero, add_zero] using
    (hasSum_nat_add_iff
      (f := fun N => (Real.exp (-kappa) * kappa^N / N.factorial) * binomialMass N n p) n).mp hshift

theorem poisson_binomial_series (kappa : NNReal) {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) :
    (∑' N, (ProbabilityTheory.poissonMeasure kappa) {N} * ENNReal.ofReal (binomialMass N n p)) =
      ENNReal.ofReal (Real.exp (-((kappa : ℝ)*p)) * ((kappa : ℝ)*p)^n / n.factorial) := by
  have hs := poisson_binomial_hasSum (kappa : ℝ) p n
  have hnonneg (N : ℕ) : 0 ≤ Real.exp (-(kappa : ℝ)) * (kappa : ℝ)^N / N.factorial := by
    positivity
  have hp0 : 0 ≤ p := hp.1
  have hp1 : 0 ≤ 1-p := sub_nonneg.mpr hp.2
  simp_rw [ProbabilityTheory.poissonMeasure_singleton,
    ← ENNReal.ofReal_mul (hnonneg _)]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun N => by
    unfold binomialMass
    positivity) hs.summable, hs.tsum_eq]

end QuantyraNullCone
