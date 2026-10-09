import QuantyraNullCone.LogLowerAlternatives

namespace QuantyraNullCone

noncomputable def logLowerBandwidth (m : ℕ) : ℝ := 1/(16*(m:ℝ))

noncomputable def logLowerCenter (m : ℕ) (j : Fin m) : ℝ :=
  1/4 + ((j:ℝ)+1/2)/(2*(m:ℝ))

noncomputable def logLowerFamily (m : ℕ) (j : Fin m) : DiamondPoint → ℝ :=
  logLowerAlternative (logLowerBandwidth m) (logLowerCenter m j)

noncomputable def logLowerWitness (m : ℕ) (j : Fin m) : DiamondPoint :=
  (logLowerCenter m j + logLowerBandwidth m/2,
   logLowerCenter m j + logLowerBandwidth m/2)

theorem log_lower_bandwidth_bounds {m : ℕ} (hm : 1 ≤ m) :
    0 < logLowerBandwidth m ∧ logLowerBandwidth m ≤ 1/16 := by
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm
  unfold logLowerBandwidth
  constructor
  · positivity
  · apply (div_le_iff₀ (by positivity : 0 < 16*(m:ℝ))).mpr
    linarith

theorem log_lower_center_bounds {m : ℕ} (hm : 1 ≤ m) (j : Fin m) :
    (1/4:ℝ) ≤ logLowerCenter m j ∧ logLowerCenter m j ≤ 3/4 := by
  have hmR : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hj0 : (0:ℝ) ≤ j := by positivity
  have hj1 : (j:ℝ)+1 ≤ m := by exact_mod_cast (show j.val+1 ≤ m by omega)
  have hlo : 0 ≤ ((j:ℝ)+1/2)/(2*(m:ℝ)) := by positivity
  have hhi : ((j:ℝ)+1/2)/(2*(m:ℝ)) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2*(m:ℝ))).mpr
    linarith
  unfold logLowerCenter
  constructor <;> linarith

theorem log_lower_centers_separated {m : ℕ} (hm : 1 ≤ m) (j k : Fin m) (hjk : j ≠ k) :
    8*logLowerBandwidth m ≤ |logLowerCenter m j-logLowerCenter m k| := by
  have hmR : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hval : j.val ≠ k.val := fun h => hjk (Fin.ext h)
  have hd : (1:ℝ) ≤ |(j:ℝ)-(k:ℝ)| := by
    rcases lt_or_gt_of_ne hval with hlt | hgt
    · have hc : (j:ℝ)+1 ≤ k := by exact_mod_cast (show j.val+1 ≤ k.val by omega)
      rw [abs_of_nonpos (by linarith : (j:ℝ)-(k:ℝ) ≤ 0)]
      linarith
    · have hc : (k:ℝ)+1 ≤ j := by exact_mod_cast (show k.val+1 ≤ j.val by omega)
      rw [abs_of_nonneg (by linarith : 0 ≤ (j:ℝ)-(k:ℝ))]
      linarith
  have hEq : logLowerCenter m j-logLowerCenter m k = ((j:ℝ)-(k:ℝ))/(2*(m:ℝ)) := by
    unfold logLowerCenter
    ring
  rw [hEq, abs_div, abs_of_pos (by positivity : 0 < 2*(m:ℝ))]
  have hc := div_le_div_of_nonneg_right hd (by positivity : 0 ≤ 2*(m:ℝ))
  convert hc using 1
  unfold logLowerBandwidth
  ring

theorem log_lower_witness_mem {m : ℕ} (hm : 1 ≤ m) (j : Fin m) :
    logLowerWitness m j ∈ diamond := by
  obtain ⟨hh,hSmall⟩ := log_lower_bandwidth_bounds hm
  obtain ⟨hc,hc1⟩ := log_lower_center_bounds hm j
  constructor <;> constructor <;> dsimp [logLowerWitness] <;> linarith

theorem log_lower_other_profile_small {m : ℕ} (hm : 1 ≤ m) (j k : Fin m) (hjk : j ≠ k) :
    |logLowerProfile (logLowerBandwidth m) (logLowerCenter m k) (logLowerWitness m j).1| ≤ 1/8 := by
  obtain ⟨hh,hSmall⟩ := log_lower_bandwidth_bounds hm
  apply log_lower_profile_tail hh hSmall
  rw [abs_div, abs_of_pos hh]
  apply (le_div_iff₀ hh).mpr
  have hSep := log_lower_centers_separated hm j k hjk
  have hTriangle := abs_sub
    (logLowerCenter m j+logLowerBandwidth m/2-logLowerCenter m k)
    (logLowerBandwidth m/2)
  rw [show logLowerCenter m j+logLowerBandwidth m/2-logLowerCenter m k-logLowerBandwidth m/2 =
    logLowerCenter m j-logLowerCenter m k by ring,
    abs_of_pos (by positivity : 0 < logLowerBandwidth m/2)] at hTriangle
  dsimp [logLowerWitness]
  linarith

theorem log_lower_family_in_class {m : ℕ} (hm : 1 ≤ m) (j : Fin m) :
    InDensityClass (logLowerFamily m j) := by
  obtain ⟨hh,hSmall⟩ := log_lower_bandwidth_bounds hm
  exact log_lower_alternative_in_class hh hSmall _

theorem log_lower_family_transpose (m : ℕ) (j : Fin m) (p : DiamondPoint) :
    logLowerFamily m j (transposePoint p) = logLowerFamily m j p :=
  log_lower_alternative_transpose _ _ _

theorem log_lower_packing_separation {m : ℕ} (hm : 1 ≤ m) (j k : Fin m) (hjk : j ≠ k) :
    3*logLowerBandwidth m/128 ≤
      logLowerFamily m j (logLowerWitness m j)-logLowerFamily m k (logLowerWitness m j) := by
  obtain ⟨hh,hSmall⟩ := log_lower_bandwidth_bounds hm
  have hOwn := log_lower_profile_peak hh hSmall (logLowerCenter m j)
  have hOther := log_lower_other_profile_small hm j k hjk
  have hOwnSq := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/4) hOwn 2
  have hOtherSq := pow_le_pow_left₀ (abs_nonneg _) hOther 2
  rw [sq_abs] at hOtherSq
  dsimp [logLowerWitness] at hOtherSq
  have hDiff : (3/64:ℝ) ≤
      logLowerProfile (logLowerBandwidth m) (logLowerCenter m j)
        (logLowerCenter m j+logLowerBandwidth m/2)^2 -
      logLowerProfile (logLowerBandwidth m) (logLowerCenter m k)
        (logLowerCenter m j+logLowerBandwidth m/2)^2 := by nlinarith only [hOwnSq,hOtherSq]
  have hMul := mul_le_mul_of_nonneg_left hDiff (by positivity : 0 ≤ logLowerBandwidth m/2)
  dsimp [logLowerFamily,logLowerAlternative,logLowerWitness]
  nlinarith only [hMul]

theorem log_lower_success_disjoint {m : ℕ} (hm : 1 ≤ m) (j k : Fin m) (hjk : j ≠ k)
    {r : ℝ} (hr : r ≤ logLowerBandwidth m/256) (f : DiamondPoint → ℝ) :
    ¬ (DensityEstimateGood (logLowerFamily m j) r f ∧
      DensityEstimateGood (logLowerFamily m k) r f) := by
  rintro ⟨hj,hk⟩
  have hp := log_lower_witness_mem hm j
  have hSep := log_lower_packing_separation hm j k hjk
  have hh := (log_lower_bandwidth_bounds hm).1
  rcases density_estimate_common_orbit hj hk with hd | hs
  · have h := (le_abs_self _).trans (hd (logLowerWitness m j) hp)
    linarith
  · have h := hs (logLowerWitness m j) hp
    change |logLowerFamily m j (logLowerWitness m j) -
      logLowerFamily m k (transposePoint (logLowerWitness m j))| ≤ _ at h
    rw [log_lower_family_transpose] at h
    have hb := (le_abs_self _).trans h
    linarith

#print axioms log_lower_bandwidth_bounds
#print axioms log_lower_center_bounds
#print axioms log_lower_centers_separated
#print axioms log_lower_witness_mem
#print axioms log_lower_other_profile_small
#print axioms log_lower_family_in_class
#print axioms log_lower_family_transpose
#print axioms log_lower_packing_separation
#print axioms log_lower_success_disjoint

end QuantyraNullCone
