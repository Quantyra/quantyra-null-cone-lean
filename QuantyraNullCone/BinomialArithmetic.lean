import QuantyraNullCone.BinomialCalibration

namespace QuantyraNullCone

def binomialNumerator (n k m d : ℕ) : ℕ := n.choose k * m^k * (d-m)^(n-k)
def binomialUpperNumerator (n : ℕ) (k : Fin (n+1)) (m d : ℕ) : ℕ :=
  ∑ j : Fin (n+1), if k ≤ j then binomialNumerator n j m d else 0
def binomialLowerNumerator (n : ℕ) (k : Fin (n+1)) (m d : ℕ) : ℕ :=
  ∑ j : Fin (n+1), if j ≤ k then binomialNumerator n j m d else 0

theorem binomial_mass_integer_identity {n k m d : ℕ} (hk : k ≤ n) (hmd : m ≤ d) (hd : 0 < d) :
    binomialMassQ n k ((m : ℚ)/d) = (binomialNumerator n k m d : ℚ)/(d : ℚ)^n := by
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hd
  have hsplit : (d : ℚ)^n = (d : ℚ)^k * (d : ℚ)^(n-k) := by
    rw [← pow_add, Nat.add_sub_of_le hk]
  have hone : (1 : ℚ)-(m : ℚ)/d = ((d : ℚ)-m)/d := by field_simp
  simp only [binomialMassQ, hone, div_pow, binomialNumerator, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_sub hmd, hsplit]
  field_simp

theorem binomial_upper_integer_identity {n m d : ℕ} (k : Fin (n+1)) (hmd : m ≤ d) (hd : 0 < d) :
    binomialUpperTailQ n k ((m : ℚ)/d) = (binomialUpperNumerator n k m d : ℚ)/(d : ℚ)^n := by
  simp only [binomialUpperTailQ, binomialUpperNumerator, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs
  · exact binomial_mass_integer_identity (Nat.le_of_lt_succ j.isLt) hmd hd
  · simp

theorem binomial_lower_integer_identity {n m d : ℕ} (k : Fin (n+1)) (hmd : m ≤ d) (hd : 0 < d) :
    binomialLowerTailQ n k ((m : ℚ)/d) = (binomialLowerNumerator n k m d : ℚ)/(d : ℚ)^n := by
  simp only [binomialLowerTailQ, binomialLowerNumerator, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs
  · exact binomial_mass_integer_identity (Nat.le_of_lt_succ j.isLt) hmd hd
  · simp

theorem binomial_upper_integer_check {n m d c e : ℕ} (k : Fin (n+1))
    (hmd : m ≤ d) (hd : 0 < d) (he : 0 < e)
    (hc : binomialUpperNumerator n k m d * e ≤ c*d^n) :
    binomialUpperTailQ n k ((m : ℚ)/d) ≤ (c : ℚ)/e := by
  rw [binomial_upper_integer_identity k hmd hd]
  apply (div_le_div_iff₀ (by positivity : (0 : ℚ)<(d : ℚ)^n)
    (by exact_mod_cast he : (0 : ℚ)<e)).mpr
  exact_mod_cast hc

theorem binomial_lower_integer_check {n m d c e : ℕ} (k : Fin (n+1))
    (hmd : m ≤ d) (hd : 0 < d) (he : 0 < e)
    (hc : binomialLowerNumerator n k m d * e ≤ c*d^n) :
    binomialLowerTailQ n k ((m : ℚ)/d) ≤ (c : ℚ)/e := by
  rw [binomial_lower_integer_identity k hmd hd]
  apply (div_le_div_iff₀ (by positivity : (0 : ℚ)<(d : ℚ)^n)
    (by exact_mod_cast he : (0 : ℚ)<e)).mpr
  exact_mod_cast hc

/-- The integer recurrence used by the Python exact tail summation. -/
theorem binomial_numerator_recurrence {n k m d : ℕ} (hk : k < n) :
    binomialNumerator n (k+1) m d * ((k+1)*(d-m)) =
      binomialNumerator n k m d * (n-k) * m := by
  have hnk : n-(k+1)+1 = n-k := by omega
  calc
    _ = (n.choose (k+1)*(k+1)) * m^(k+1) * (d-m)^(n-(k+1)+1) := by
      simp only [binomialNumerator, pow_succ]
      ring
    _ = (n.choose k*(n-k)) * (m^k*m) * (d-m)^(n-k) := by
      rw [Nat.choose_succ_right_eq, hnk, pow_succ]
    _ = _ := by unfold binomialNumerator; ring

theorem binomial_numerator_division {n k m d : ℕ} (hk : k < n) (hmd : m < d) :
    (binomialNumerator n k m d * (n-k) * m) / ((k+1)*(d-m)) =
      binomialNumerator n (k+1) m d := by
  rw [← binomial_numerator_recurrence hk]
  exact Nat.mul_div_cancel _ (Nat.mul_pos (Nat.succ_pos _) (Nat.sub_pos_of_lt hmd))

instance binomialReportValid_decidable (n : ℕ) (delta : ℚ) (L U : Fin (n+1) → ℚ) :
    Decidable (BinomialReportValid n delta L U) := by
  unfold BinomialReportValid
  infer_instance

def binomialReportCheck (n : ℕ) (delta : ℚ) (L U : Fin (n+1) → ℚ) : Bool :=
  decide (BinomialReportValid n delta L U)

theorem binomial_report_check_sound {n : ℕ} {delta : ℚ} {L U : Fin (n+1) → ℚ}
    (hcheck : binomialReportCheck n delta L U = true) : BinomialReportValid n delta L U :=
  of_decide_eq_true hcheck

theorem binomial_no_data_valid (n : ℕ) {delta : ℚ} :
    BinomialReportValid n delta (fun _ => 0) (fun _ => 1) := by
  intro k
  norm_num

end QuantyraNullCone
