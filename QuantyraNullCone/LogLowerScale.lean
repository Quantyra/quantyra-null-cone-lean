import QuantyraNullCone.LogLowerProduct

namespace QuantyraNullCone

noncomputable def logMinimaxRate (n : ℕ) : ℝ :=
  (Real.log (n:ℝ)/(n:ℝ))^(1/4:ℝ)

noncomputable def logLowerScale (n : ℕ) : ℝ :=
  ((n:ℝ)/Real.log (n:ℝ))^(1/4:ℝ)

noncomputable def logLowerMesh (n : ℕ) : ℕ := ⌈logLowerScale n⌉₊

theorem log_lower_log_bound {n : ℕ} (hn : 2^64 ≤ n) : (32:ℝ) ≤ Real.log (n:ℝ) := by
  have hnR : (2:ℝ)^64 ≤ n := by exact_mod_cast hn
  have hLog := Real.log_le_log (pow_pos (by norm_num : (0:ℝ) < 2) 64) hnR
  rw [Real.log_pow] at hLog
  norm_num at hLog
  linarith [log_two_lower]

theorem nonneg_le_exp_half {t : ℝ} (ht : 0 ≤ t) : t ≤ Real.exp (t/2) := by
  have h := pow_le_pow_left₀ (by positivity : 0 ≤ t/4+1) (Real.add_one_le_exp (t/4)) 2
  have hEq : Real.exp (t/4)^2 = Real.exp (t/2) := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  rw [hEq] at h
  nlinarith [sq_nonneg (t-4)]

theorem log_lower_scale_positive {n : ℕ} (hn : 2^64 ≤ n) : 0 < logLowerScale n := by
  have hnPos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hLog := log_lower_log_bound hn
  apply Real.rpow_pos_of_pos
  exact div_pos hnPos (by linarith)

theorem log_lower_scale_log {n : ℕ} (hn : 2^64 ≤ n) :
    Real.log (n:ℝ)/8 ≤ Real.log (logLowerScale n) := by
  have hnPos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hLog := log_lower_log_bound hn
  have hLogPos : 0 < Real.log (n:ℝ) := by linarith
  have ht := Real.log_le_log hLogPos (nonneg_le_exp_half hLogPos.le)
  rw [Real.log_exp] at ht
  rw [logLowerScale,Real.log_rpow (div_pos hnPos hLogPos),Real.log_div hnPos.ne' hLogPos.ne']
  linarith

theorem log_lower_scale_large {n : ℕ} (hn : 2^64 ≤ n) : (16:ℝ) ≤ logLowerScale n := by
  have hLog := log_lower_log_bound hn
  have hScale := log_lower_scale_log hn
  have hFour : (4:ℝ) ≤ Real.log (logLowerScale n) := by linarith
  have hExp := Real.exp_le_exp.mpr hFour
  rw [Real.exp_log (log_lower_scale_positive hn)] at hExp
  have hOne : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have hPow := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hOne 4
  rw [← Real.exp_nat_mul] at hPow
  norm_num at hPow
  exact hPow.trans hExp

theorem log_lower_mesh_bounds {n : ℕ} (hn : 2^64 ≤ n) :
    16 ≤ logLowerMesh n ∧ logLowerScale n ≤ (logLowerMesh n:ℝ) ∧
      (logLowerMesh n:ℝ) ≤ 2*logLowerScale n := by
  have hLarge := log_lower_scale_large hn
  have hCeil := Nat.le_ceil (logLowerScale n)
  have hCeilHi := Nat.ceil_lt_add_one (log_lower_scale_positive hn).le
  refine ⟨?_,hCeil,?_⟩
  · exact_mod_cast hLarge.trans hCeil
  · change (⌈logLowerScale n⌉₊:ℝ) ≤ _
    linarith

theorem log_lower_scale_fourth {n : ℕ} (hn : 2^64 ≤ n) :
    logLowerScale n^4 = (n:ℝ)/Real.log (n:ℝ) := by
  have hPos : 0 < (n:ℝ)/Real.log (n:ℝ) := by
    apply div_pos
    · exact_mod_cast (show 0 < n by omega)
    · linarith [log_lower_log_bound hn]
  rw [logLowerScale,← Real.rpow_natCast,← Real.rpow_mul hPos.le]
  norm_num

theorem log_lower_mesh_budget {n : ℕ} (hn : 2^64 ≤ n) :
    Real.exp ((n:ℝ)*logLowerBandwidth (logLowerMesh n)^4/4) ≤ (logLowerMesh n:ℝ)/4 := by
  obtain ⟨hm,hx,hmHi⟩ := log_lower_mesh_bounds hn
  have hmR : (16:ℝ) ≤ logLowerMesh n := by exact_mod_cast hm
  have hmPos : (0:ℝ) < logLowerMesh n := by linarith
  have ht := log_lower_log_bound hn
  have htPos : 0 < Real.log (n:ℝ) := by linarith
  have hPow := pow_le_pow_left₀ (log_lower_scale_positive hn).le hx 4
  rw [log_lower_scale_fourth hn] at hPow
  have hN : (n:ℝ)/(logLowerMesh n:ℝ)^4 ≤ Real.log (n:ℝ) := by
    apply (div_le_iff₀ (pow_pos hmPos 4)).mpr
    have h := (div_le_iff₀ htPos).mp hPow
    nlinarith only [h]
  have hLogM := (log_lower_scale_log hn).trans
    (Real.log_le_log (log_lower_scale_positive hn) hx)
  have hEq : (n:ℝ)*logLowerBandwidth (logLowerMesh n)^4/4 =
      ((n:ℝ)/(logLowerMesh n:ℝ)^4)/262144 := by
    unfold logLowerBandwidth
    ring
  have hExponent : (n:ℝ)*logLowerBandwidth (logLowerMesh n)^4/4 ≤
      Real.log (logLowerMesh n:ℝ)/2 := by
    rw [hEq]
    linarith
  have hExp := Real.exp_le_exp.mpr hExponent
  rw [Real.exp_half,Real.exp_log hmPos] at hExp
  apply hExp.trans
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hMul := mul_nonneg (sub_nonneg.mpr hmR) hmPos.le
  nlinarith only [hMul]

theorem log_lower_rate_inverse {n : ℕ} (hn : 2^64 ≤ n) :
    logMinimaxRate n = 1/logLowerScale n := by
  have hnPos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have htPos : 0 < Real.log (n:ℝ) := by linarith [log_lower_log_bound hn]
  have hInv : Real.log (n:ℝ)/(n:ℝ) = ((n:ℝ)/Real.log (n:ℝ))⁻¹ := by
    field_simp [hnPos.ne',htPos.ne']
  rw [logMinimaxRate,hInv,Real.inv_rpow (div_pos hnPos htPos).le]
  simp only [logLowerScale,one_div]

theorem log_lower_target_radius {n : ℕ} (hn : 2^64 ≤ n) :
    logMinimaxRate n/8192 ≤ logLowerBandwidth (logLowerMesh n)/256 := by
  obtain ⟨hm,hx,hmHi⟩ := log_lower_mesh_bounds hn
  have hxPos := log_lower_scale_positive hn
  have hmPos : (0:ℝ) < logLowerMesh n := by exact_mod_cast (show 0 < logLowerMesh n by omega)
  rw [log_lower_rate_inverse hn,logLowerBandwidth]
  rw [show (1/logLowerScale n)/8192 = 1/(8192*logLowerScale n) by ring,
    show (1/(16*(logLowerMesh n:ℝ)))/256 = 1/(4096*(logLowerMesh n:ℝ)) by ring]
  apply (div_le_div_iff₀ (by positivity : 0 < 8192*logLowerScale n)
    (by positivity : 0 < 4096*(logLowerMesh n:ℝ))).mpr
  nlinarith only [hmHi]

#print axioms log_lower_log_bound
#print axioms nonneg_le_exp_half
#print axioms log_lower_scale_positive
#print axioms log_lower_scale_log
#print axioms log_lower_scale_large
#print axioms log_lower_mesh_bounds
#print axioms log_lower_scale_fourth
#print axioms log_lower_mesh_budget
#print axioms log_lower_rate_inverse
#print axioms log_lower_target_radius

end QuantyraNullCone
