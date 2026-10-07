import QuantyraNullCone.InverseRate
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace QuantyraNullCone

open Filter Topology

theorem InDensityClass.coefficientDeviation_zero_iff {rho sigma : DiamondPoint → ℝ}
    (hR : InDensityClass rho) (hS : InDensityClass sigma) :
    coefficientDeviation rho sigma = 0 ↔ ∀ p ∈ diamond, rho p = sigma p := by
  constructor
  · intro hZero p hp
    have hBdd : BddAbove ((fun q => |rho q - sigma q|) '' diamond) := by
      refine ⟨1, ?_⟩
      rintro z ⟨q, hq, rfl⟩
      have hRq := hR.bounds q hq
      have hSq := hS.bounds q hq
      apply abs_le.mpr
      constructor <;> linarith
    have hLe : |rho p - sigma p| ≤ coefficientDeviation rho sigma :=
      le_csSup hBdd ⟨p, hp, rfl⟩
    rw [hZero] at hLe
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hLe (abs_nonneg _)))
  · intro hEqual
    obtain ⟨p, hp, hValue⟩ := hR.coefficientDeviation_attained hS
    rw [hValue, hEqual p hp, sub_self, abs_zero]

theorem InDensityClass.conformalDistance_zero_iff {rho sigma : DiamondPoint → ℝ}
    (hR : InDensityClass rho) (hS : InDensityClass sigma) :
    conformalDistance rho sigma = 0 ↔
      (∀ p ∈ diamond, rho p = sigma p) ∨
      (∀ p ∈ diamond, rho p = transposeDensity sigma p) := by
  constructor
  · intro hZero
    unfold conformalDistance at hZero
    rcases le_total (coefficientDeviation rho sigma)
      (coefficientDeviation rho (transposeDensity sigma)) with h | h
    · rw [min_eq_left h] at hZero
      exact Or.inl ((hR.coefficientDeviation_zero_iff hS).mp hZero)
    · rw [min_eq_right h] at hZero
      exact Or.inr ((hR.coefficientDeviation_zero_iff hS.transpose).mp hZero)
  · intro hEqual
    have hNonneg := (hR.conformalDistance_bounds hS).1
    apply le_antisymm _ hNonneg
    rcases hEqual with h | h
    · have hZero := (hR.coefficientDeviation_zero_iff hS).mpr h
      exact (min_le_left _ _).trans_eq hZero
    · have hZero := (hR.coefficientDeviation_zero_iff hS.transpose).mpr h
      exact (min_le_right _ _).trans_eq hZero

theorem finiteLawDiscrepancy_eq_zero_of_laws_equal {rho sigma : DiamondPoint → ℝ}
    (hLaw : ∀ n : ℕ, 2 ≤ n → orderLaw rho n = orderLaw sigma n) {N : ℕ} (hN : 2 ≤ N) :
    finiteLawDiscrepancy rho sigma N = 0 := by
  have hTV (n : ℕ) (hn : 2 ≤ n) : orderLawTV rho sigma n = 0 := by
    unfold orderLawTV
    rw [hLaw n hn]
    simp
  have hSet : {d : ℝ | ∃ k : ℕ, 2 ≤ k ∧ k ≤ N ∧ d = orderLawTV rho sigma k} = {0} := by
    ext d
    constructor
    · rintro ⟨k, hk, _, hd⟩
      simpa only [Set.mem_singleton_iff, hTV k hk] using hd
    · intro hd
      exact ⟨N, hN, le_rfl, by simpa only [hTV N hN] using hd⟩
  unfold finiteLawDiscrepancy
  rw [hSet]
  simp

/-- Equality of all actual directed-order laws determines the density on the square,
up to one global axis exchange. No coefficient equality is assumed. -/
theorem InDensityClass.all_law_identifiability {rho sigma : DiamondPoint → ℝ}
    (hR : InDensityClass rho) (hS : InDensityClass sigma)
    (hLaw : ∀ n : ℕ, 2 ≤ n → orderLaw rho n = orderLaw sigma n) :
    (∀ p ∈ diamond, rho p = sigma p) ∨
      (∀ p ∈ diamond, rho p = transposeDensity sigma p) := by
  have hRate : Tendsto (fun n : ℕ => 100 * (n : ℝ) ^ (-1 / 12 : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    have hPower := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 12)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [neg_div, mul_zero] using hPower.const_mul (100 : ℝ)
  have hLe : conformalDistance rho sigma ≤ 0 := by
    apply ge_of_tendsto hRate
    filter_upwards [eventually_ge_atTop 2] with N hN
    have h := hR.full_inverse hS hN
    rw [finiteLawDiscrepancy_eq_zero_of_laws_equal hLaw hN, add_zero] at h
    exact h
  have hZero : conformalDistance rho sigma = 0 :=
    le_antisymm hLe (hR.conformalDistance_bounds hS).1
  exact (hR.conformalDistance_zero_iff hS).mp hZero

#print axioms InDensityClass.coefficientDeviation_zero_iff
#print axioms InDensityClass.conformalDistance_zero_iff
#print axioms InDensityClass.all_law_identifiability

end QuantyraNullCone
