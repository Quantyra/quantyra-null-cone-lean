import QuantyraNullCone.DegreeMesh

namespace QuantyraNullCone

open MeasureTheory

def SampleDegreeReconstructed {n : ℕ} (rho : DiamondPoint → ℝ)
    (r : ℝ) (k : ℕ) (H w E : ℝ) (sample : Fin n → DiamondPoint) : Prop :=
  ∀ L : Realizer (Chronological (fun i => (sample i).1) (fun i => (sample i).2)),
    ∃ swap : Bool, ∀ p ∈ diamond, |(L.aligned swap).degreeHistogram r k H w p - rho p| ≤ E

/-- Concrete mesh and whole-square density recovery from one sampled order,
uniform over every realizer. The logarithmic outer mesh is discharged below;
the order-only measurable selector and all-n flat branches follow separately. -/
theorem InDensityClass.degree_histogram_probability {rho : DiamondPoint → ℝ}
    (hK : InDensityClass rho) {n m : ℕ} (hn : 65536 ≤ n) (hm : 65536 ≤ m)
    (hmSq : (m : ℝ) ^ 2 ≤ n / (8 * Real.log n)) :
    let r : ℝ := 1 / m
    let h := Real.sqrt r
    let k := Nat.floor (Real.sqrt (m : ℝ))
    let w := (1 - 16 * h) / k
    (19 / 20 : ℝ) ≤ (sampleMeasure rho n).real
      {sample | SampleDegreeReconstructed rho r k (8 * h) w (270 * h) sample} := by
  dsimp
  let r : ℝ := 1 / m
  let h := Real.sqrt r
  let k := Nat.floor (Real.sqrt (m : ℝ))
  let w := (1 - 16 * h) / k
  obtain ⟨hr, hh, hSquare, hmr, hhSmall, hk, hkSq, hw, hkw, hLow, hHigh⟩ := degree_inner_mesh_data hm
  obtain ⟨hH0, hH, _, hShift, hDeep⟩ := degree_mesh_margins hh hhSmall hSquare hLow
  have hnPos : 0 < n := by omega
  have hmR : (65536 : ℝ) ≤ m := by exact_mod_cast hm
  have hmPos : (0 : ℝ) < m := by linarith
  obtain ⟨hLog, _⟩ := log_large_bounds hn
  have hBudget := (le_div_iff₀ (by linarith : 0 < 8 * Real.log (n : ℝ))).mp hmSq
  have hSq : (m : ℝ) ^ 2 ≤ n / 8 := by
    have hmLog := mul_nonneg (sq_nonneg (m : ℝ)) (sub_nonneg.mpr hLog)
    nlinarith only [hmLog, hBudget]
  have hmN : (m : ℝ) ≤ n := by nlinarith only [hmR, hSq]
  have hnr : 1 / (n : ℝ) ≤ r := one_div_le_one_div_of_le hmPos hmN
  let sets (ij : Bool × (Fin k × Fin k)) :=
    shiftedInnerCell ij.1 (8 * h) w (32 * r) ij.2.1 ij.2.2
  have hSets (ij : Bool × (Fin k × Fin k)) : MeasurableSet (sets ij) := by
    dsimp [sets, shiftedInnerCell]
    split <;> exact square_cell_measurable _ _ _
  have hp (ij : Bool × (Fin k × Fin k)) : (densityMeasure rho).real (sets ij) ≤ 8 * h ^ 2 :=
    hK.shifted_inner_cell_mass hk hh hhSmall hSquare hkw hLow hHigh ij.1 ij.2.1.isLt ij.2.2.isLt
  have hCard : (Fintype.card (Bool × (Fin k × Fin k)) : ℝ) ≤ 4 * n := by
    simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat]
    nlinarith only [hkSq, hmN, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hProb := hK.degree_event_probability hn (by omega : 16 ≤ m) hr hmr hh.le
    (by linarith : h ≤ 4) hSquare hmSq sets hSets hp hCard
  letI : IsProbabilityMeasure (sampleMeasure rho n) := hK.sample_isProbabilityMeasure n
  apply hProb.trans
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro sample hs L
  have hAccuracy : InnerCountAccuracy rho k (8 * h) w (32 * r) (4 * h ^ 3) sample := by
    intro b i j hi hj
    exact hs.2 (b, (⟨i, hi⟩, ⟨j, hj⟩))
  obtain ⟨swap, hError⟩ := degree_histogram_error hK hnPos (by omega : 16 ≤ m) hk
    hr hh.le hSquare hmr hnr hH0 hH hw
    (by nlinarith only [hkw] : (k : ℝ) * w = 1 - 2 * (8 * h)) hShift hDeep hs.1 hAccuracy L
  refine ⟨swap, fun p hpD => (hError p hpD).trans ?_⟩
  have hConstant := degree_histogram_constant hh hhSmall hLow hHigh
  rw [hSquare] at hConstant
  nlinarith only [hConstant]

theorem degree_logarithmic_mesh_large {n : ℕ} (hn : 2 ≤ n)
    (hm : 65536 ≤ Nat.floor (Real.sqrt ((n : ℝ) / (8 * Real.log n)))) :
    65536 ≤ n ∧
      (Nat.floor (Real.sqrt ((n : ℝ) / (8 * Real.log n))) : ℝ) ^ 2 ≤ n / (8 * Real.log n) := by
  let x := Real.sqrt ((n : ℝ) / (8 * Real.log n))
  let m := Nat.floor x
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnPos : (0 : ℝ) < n := by linarith
  have hLogHalf : 1 / 2 ≤ Real.log (n : ℝ) :=
    log_two_lower.trans (Real.log_le_log (by norm_num : (0 : ℝ) < 2) hnR)
  have hDen : 0 < 8 * Real.log (n : ℝ) := by linarith
  have hxPos : 0 < x := Real.sqrt_pos.2 (div_pos hnPos hDen)
  have hmX : (m : ℝ) ≤ x := Nat.floor_le hxPos.le
  have hmR : (65536 : ℝ) ≤ m := by exact_mod_cast hm
  have hxSq : x ^ 2 = n / (8 * Real.log n) := Real.sq_sqrt (by positivity)
  have hmSq : (m : ℝ) ^ 2 ≤ n / (8 * Real.log n) := by
    rw [← hxSq]
    exact pow_le_pow_left₀ (Nat.cast_nonneg m) hmX 2
  have hBudget := (le_div_iff₀ hDen).mp hmSq
  have hFour : 4 * (m : ℝ) ^ 2 ≤ n := by
    have hmLog := mul_nonneg (sq_nonneg (m : ℝ)) (sub_nonneg.mpr hLogHalf)
    nlinarith only [hmLog, hBudget]
  have hnLarge : (65536 : ℝ) ≤ n := by nlinarith only [hFour, hmR]
  exact ⟨by exact_mod_cast hnLarge, hmSq⟩

/-- The probabilistic histogram theorem now uses the explicit logarithmic
outer mesh, without assumed concentration or geometric recovery events. -/
theorem InDensityClass.logarithmic_degree_histogram_probability {rho : DiamondPoint → ℝ}
    (hK : InDensityClass rho) {n : ℕ} (hn : 2 ≤ n)
    (hm : 65536 ≤ Nat.floor (Real.sqrt ((n : ℝ) / (8 * Real.log n)))) :
    let m := Nat.floor (Real.sqrt ((n : ℝ) / (8 * Real.log n)))
    let r : ℝ := 1 / m
    let h := Real.sqrt r
    let k := Nat.floor (Real.sqrt (m : ℝ))
    let w := (1 - 16 * h) / k
    (19 / 20 : ℝ) ≤ (sampleMeasure rho n).real
      {sample | SampleDegreeReconstructed rho r k (8 * h) w (270 * h) sample} := by
  obtain ⟨hnLarge, hmSq⟩ := degree_logarithmic_mesh_large hn hm
  exact hK.degree_histogram_probability hnLarge hm hmSq

#print axioms InDensityClass.degree_histogram_probability
#print axioms degree_logarithmic_mesh_large
#print axioms InDensityClass.logarithmic_degree_histogram_probability

end QuantyraNullCone
