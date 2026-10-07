import QuantyraNullCone.QuotientTV

namespace QuantyraNullCone

open MeasureTheory Filter Topology

/-- Isomorphism preserves directed chronology; it does not identify the time-reversed dual. -/
def OrderIsomorphic {n : ℕ} (code other : OrderCode n) : Prop :=
  ∃ π : Equiv.Perm (Fin n), relabelOrder π code = other

def orderIsomorphismSetoid (n : ℕ) : Setoid (OrderCode n) where
  r := OrderIsomorphic
  iseqv := {
    refl := fun code => ⟨Equiv.refl _, rfl⟩
    symm := by
      intro code other h
      obtain ⟨π, hπ⟩ := h
      refine ⟨π.symm, ?_⟩
      rw [← hπ]
      exact (relabelOrderEquiv π).left_inv code
    trans := by
      intro a b c hab hbc
      obtain ⟨π, hπ⟩ := hab
      obtain ⟨τ, hτ⟩ := hbc
      refine ⟨τ.trans π, ?_⟩
      change relabelOrder τ (relabelOrder π a) = c
      rw [hπ, hτ]
  }

abbrev UnlabeledOrderCode (n : ℕ) := Quotient (orderIsomorphismSetoid n)

noncomputable instance (n : ℕ) : Fintype (UnlabeledOrderCode n) := Fintype.ofFinite _

instance (n : ℕ) : MeasurableSpace (UnlabeledOrderCode n) := ⊤

def forgetOrderLabels {n : ℕ} (code : OrderCode n) : UnlabeledOrderCode n :=
  Quotient.mk _ code

theorem forgetOrderLabels_eq_iff {n : ℕ} (code other : OrderCode n) :
    forgetOrderLabels code = forgetOrderLabels other ↔
      ∃ π : Equiv.Perm (Fin n), relabelOrder π code = other := by
  constructor
  · exact Quotient.exact
  · intro h
    apply Quotient.sound
    exact h

noncomputable def unlabeledOrderLaw (rho : DiamondPoint → ℝ) (n : ℕ) :
    Measure (UnlabeledOrderCode n) := (orderLaw rho n).map forgetOrderLabels

theorem InDensityClass.unlabeledOrderLaw_isProbabilityMeasure {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) (n : ℕ) : IsProbabilityMeasure (unlabeledOrderLaw rho n) := by
  letI := h.orderLaw_isProbabilityMeasure n
  exact Measure.isProbabilityMeasure_map (measurable_of_countable forgetOrderLabels).aemeasurable

noncomputable def unlabeledOrderLawTV (rho sigma : DiamondPoint → ℝ) (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) * ∑ code : UnlabeledOrderCode n,
    |(unlabeledOrderLaw rho n).real {code} - (unlabeledOrderLaw sigma n).real {code}|

noncomputable def unlabeledFiniteLawDiscrepancy (rho sigma : DiamondPoint → ℝ) (N : ℕ) : ℝ :=
  sSup {d : ℝ | ∃ k : ℕ, 2 ≤ k ∧ k ≤ N ∧ d = unlabeledOrderLawTV rho sigma k}

theorem InDensityClass.orderLaw_fiber_constant {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) {n : ℕ} (code other : OrderCode n)
    (hEq : forgetOrderLabels code = forgetOrderLabels other) :
    (orderLaw rho n).real {code} = (orderLaw rho n).real {other} := by
  obtain ⟨π, hπ⟩ := Quotient.exact hEq
  rw [← hπ]
  exact congrArg ENNReal.toReal (h.orderLaw_singleton_relabel π code).symm

theorem InDensityClass.unlabeledOrderLawTV_eq {rho sigma : DiamondPoint → ℝ}
    (hR : InDensityClass rho) (hS : InDensityClass sigma) (n : ℕ) :
    unlabeledOrderLawTV rho sigma n = orderLawTV rho sigma n := by
  letI := hR.orderLaw_isProbabilityMeasure n
  letI := hS.orderLaw_isProbabilityMeasure n
  unfold unlabeledOrderLawTV unlabeledOrderLaw orderLawTV
  rw [finite_map_L1_of_fiber_constant _ _ _ hR.orderLaw_fiber_constant hS.orderLaw_fiber_constant]
  rfl

theorem InDensityClass.unlabeledFiniteLawDiscrepancy_eq {rho sigma : DiamondPoint → ℝ}
    (hR : InDensityClass rho) (hS : InDensityClass sigma) (N : ℕ) :
    unlabeledFiniteLawDiscrepancy rho sigma N = finiteLawDiscrepancy rho sigma N := by
  unfold unlabeledFiniteLawDiscrepancy finiteLawDiscrepancy
  simp_rw [hR.unlabeledOrderLawTV_eq hS]

/-- The original all-N estimate observes only directed-order isomorphism classes. -/
theorem InDensityClass.full_inverse_unlabeled {rho sigma : DiamondPoint → ℝ}
    (hR : InDensityClass rho) (hS : InDensityClass sigma) {N : ℕ} (hN : 2 ≤ N) :
    conformalDistance rho sigma ≤
      100 * ((N : ℝ) ^ (-1 / 12 : ℝ) + unlabeledFiniteLawDiscrepancy rho sigma N) := by
  rw [hR.unlabeledFiniteLawDiscrepancy_eq hS]
  exact hR.full_inverse hS hN

theorem unlabeled_discrepancy_zero_of_laws_equal {rho sigma : DiamondPoint → ℝ}
    (hLaw : ∀ n : ℕ, 2 ≤ n → unlabeledOrderLaw rho n = unlabeledOrderLaw sigma n)
    {N : ℕ} (hN : 2 ≤ N) : unlabeledFiniteLawDiscrepancy rho sigma N = 0 := by
  have hTV (n : ℕ) (hn : 2 ≤ n) : unlabeledOrderLawTV rho sigma n = 0 := by
    unfold unlabeledOrderLawTV
    rw [hLaw n hn]
    simp
  have hSet : {d : ℝ | ∃ k : ℕ, 2 ≤ k ∧ k ≤ N ∧ d = unlabeledOrderLawTV rho sigma k} = {0} := by
    ext d
    constructor
    · rintro ⟨k, hk, _, hd⟩
      simpa only [Set.mem_singleton_iff, hTV k hk] using hd
    · intro hd
      exact ⟨N, hN, le_rfl, by simpa only [hTV N hN] using hd⟩
  unfold unlabeledFiniteLawDiscrepancy
  rw [hSet]
  simp

theorem InDensityClass.all_unlabeled_law_identifiability {rho sigma : DiamondPoint → ℝ}
    (hR : InDensityClass rho) (hS : InDensityClass sigma)
    (hLaw : ∀ n : ℕ, 2 ≤ n → unlabeledOrderLaw rho n = unlabeledOrderLaw sigma n) :
    (∀ p ∈ diamond, rho p = sigma p) ∨
      (∀ p ∈ diamond, rho p = transposeDensity sigma p) := by
  have hRate : Tendsto (fun n : ℕ => 100 * (n : ℝ) ^ (-1 / 12 : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    have hPower := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 12)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [neg_div, mul_zero] using hPower.const_mul (100 : ℝ)
  have hLe : conformalDistance rho sigma ≤ 0 := by
    apply ge_of_tendsto hRate
    filter_upwards [eventually_ge_atTop 2] with N hN
    have h := hR.full_inverse_unlabeled hS hN
    rw [unlabeled_discrepancy_zero_of_laws_equal hLaw hN, add_zero] at h
    exact h
  exact (hR.conformalDistance_zero_iff hS).mp
    (le_antisymm hLe (hR.conformalDistance_bounds hS).1)

#print axioms InDensityClass.orderLaw_fiber_constant
#print axioms InDensityClass.unlabeledOrderLaw_isProbabilityMeasure
#print axioms forgetOrderLabels_eq_iff
#print axioms InDensityClass.unlabeledOrderLawTV_eq
#print axioms InDensityClass.unlabeledFiniteLawDiscrepancy_eq
#print axioms InDensityClass.full_inverse_unlabeled
#print axioms InDensityClass.all_unlabeled_law_identifiability

end QuantyraNullCone
