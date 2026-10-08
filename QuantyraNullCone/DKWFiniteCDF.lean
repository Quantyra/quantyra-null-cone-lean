import QuantyraNullCone.DKWMaximal

namespace QuantyraNullCone

noncomputable def finiteBinCDF {n q : ℕ} (x : BinProfile n q) (k : ℕ) : ℝ :=
  (finiteBinCount x k : ℝ) / n

theorem finite_bin_count_le {n q k : ℕ} (x : BinProfile n q) : finiteBinCount x k ≤ n := by
  have h := Finset.card_le_card
    (Finset.filter_subset (fun i : Fin n => (x i).val < k) Finset.univ)
  simpa [finiteBinCount] using h

theorem finite_bin_CDF_bounds {n q k : ℕ} (hn : 0 < n) (x : BinProfile n q) :
    0 ≤ finiteBinCDF x k ∧ finiteBinCDF x k ≤ 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · unfold finiteBinCDF
    positivity
  · apply (div_le_one hnR).mpr
    exact_mod_cast finite_bin_count_le (k := k) x

theorem finite_bin_likelihood_pos {n q k : ℕ} {lambda : ℝ} (hL : 0 < lambda)
    (x : BinProfile n q) : 0 < finiteBinLikelihood lambda k x := by
  unfold finiteBinLikelihood
  positivity

theorem finite_bin_likelihood_log {n q k : ℕ} {lambda : ℝ} (hL : 0 < lambda)
    (x : BinProfile n q) :
    Real.log (finiteBinLikelihood lambda k x) =
      (finiteBinCount x k : ℝ) * Real.log (1 + lambda * q / k) -
        (n : ℝ) * Real.log (1 + lambda) := by
  unfold finiteBinLikelihood
  rw [Real.log_div (ne_of_gt (by positivity)) (ne_of_gt (by positivity)),
    Real.log_pow, Real.log_pow]

theorem finite_bin_deviation_likelihood {n q k : ℕ} {e lambda : ℝ}
    (hn : 0 < n) (hq : 0 < q) (hk : 0 < k) (hL : 0 < lambda)
    (x : BinProfile n q)
    (hBarrier : ∀ t : ℝ, 0 < t → t ≤ 1 - e →
      2 * e ^ 2 ≤ dkwLikelihoodBarrier e lambda t)
    (hBad : e < finiteBinCDF x k - (k : ℝ) / q) :
    Real.exp (2 * (n : ℝ) * e ^ 2) < finiteBinLikelihood lambda k x := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  let t : ℝ := (k : ℝ) / q
  have ht : 0 < t := div_pos hkR hqR
  have htEnd : t ≤ 1 - e := by
    have hCDF := (finite_bin_CDF_bounds (k := k) hn x).2
    change e < finiteBinCDF x k - t at hBad
    linarith
  have hCount : (n : ℝ) * (t + e) < finiteBinCount x k := by
    have hNormalized : t + e < (finiteBinCount x k : ℝ) / n := by
      change e < (finiteBinCount x k : ℝ) / n - t at hBad
      linarith
    have h := (lt_div_iff₀ hnR).mp hNormalized
    nlinarith only [h]
  have hFrac : lambda * q / k = lambda / t := by
    dsimp [t]
    field_simp [ne_of_gt hkR, ne_of_gt hqR]
  have hLog : 0 < Real.log (1 + lambda / t) :=
    Real.log_pos (by have : 0 < lambda / t := div_pos hL ht; linarith)
  have hProduct := mul_lt_mul_of_pos_right hCount hLog
  have hLower := mul_le_mul_of_nonneg_left (hBarrier t ht htEnd) hnR.le
  have hShape : (n : ℝ) * dkwLikelihoodBarrier e lambda t =
      (n : ℝ) * (t + e) * Real.log (1 + lambda / t) -
        (n : ℝ) * Real.log (1 + lambda) := by
    unfold dkwLikelihoodBarrier
    ring
  rw [hShape] at hLower
  have hLarge : 2 * (n : ℝ) * e ^ 2 < Real.log (finiteBinLikelihood lambda k x) := by
    rw [finite_bin_likelihood_log hL, hFrac]
    nlinarith only [hLower, hProduct]
  have hExp := Real.exp_lt_exp.mpr hLarge
  rwa [Real.exp_log (finite_bin_likelihood_pos hL x)] at hExp

noncomputable def finiteBinUpperDeviation {n q : ℕ} (e : ℝ) : Finset (BinProfile n q) := by
  classical
  exact Finset.univ.filter (fun x => ∃ k ∈ Finset.Icc 0 q,
    e < finiteBinCDF x k - (k : ℝ) / q)

/-- Sharp one-sided DKW on the actual uniform finite-bin profile space.
The probability is exactly cardinal divided by q^n, the uniform iid profile mass. -/
theorem finite_bin_upper_DKW {n q : ℕ} {e : ℝ} (hn : 0 < n) (hq : 0 < q)
    (he : 0 < e) (he1 : e < 1) :
    ((finiteBinUpperDeviation (n := n) (q := q) e).card : ℝ) / (q : ℝ) ^ n ≤
      Real.exp (-2 * (n : ℝ) * e ^ 2) := by
  classical
  obtain ⟨lambda, hL, hBarrier⟩ := dkw_sharp_likelihood_barrier he he1
  let B := Real.exp (2 * (n : ℝ) * e ^ 2)
  have hB : 0 < B := Real.exp_pos _
  have hSub : finiteBinUpperDeviation (n := n) (q := q) e ⊆
      finiteBinCrossing lambda B := by
    intro x hx
    simp only [finiteBinUpperDeviation, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨k, hk, hBad⟩ := hx
    have hk0 : k ≠ 0 := by
      intro h
      subst k
      have hNeg : e < 0 := by simpa [finiteBinCDF, finiteBinCount] using hBad
      exact (not_lt_of_ge he.le) hNeg
    have hkPos : 0 < k := Nat.pos_of_ne_zero hk0
    have hLarge := finite_bin_deviation_likelihood hn hq hkPos hL x hBarrier hBad
    exact finite_bin_crossing_of_threshold lambda B x
      (Finset.mem_Icc.mpr ⟨hkPos, (Finset.mem_Icc.mp hk).2⟩) hLarge.le
  have hCard : ((finiteBinUpperDeviation (n := n) (q := q) e).card : ℝ) ≤
      (finiteBinCrossing (n := n) (q := q) lambda B).card := by
    exact_mod_cast Finset.card_le_card hSub
  have hRatio := div_le_div_of_nonneg_right hCard (show 0 ≤ (q : ℝ) ^ n by positivity)
  have hVille := finite_bin_likelihood_maximal (n := n) hq hL hB
  have hExp : 1 / B = Real.exp (-2 * (n : ℝ) * e ^ 2) := by
    dsimp [B]
    rw [one_div, ← Real.exp_neg]
    congr 1
    ring
  exact (hRatio.trans hVille).trans_eq hExp

#print axioms finite_bin_deviation_likelihood
#print axioms finite_bin_upper_DKW

end QuantyraNullCone
