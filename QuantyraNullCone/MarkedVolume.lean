import QuantyraNullCone.Concentration

namespace QuantyraNullCone

open MeasureTheory ProbabilityTheory

theorem iid_indicator_hoeffding {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] {n : ℕ} (hn : 0 < n) {S : Set Omega}
    (hS : MeasurableSet S) {r : ℝ} (hr : 0 ≤ r) :
    (Measure.pi (fun _ : Fin n => mu)).real {sample |
      r ≤ |(∑ i : Fin n, S.indicator (fun _ => (1 : ℝ)) (sample i)) / n -
        (mu S).toReal|} ≤
      2 * Real.exp (-2 * (n : ℝ) * r ^ 2) := by
  classical
  let Y : Omega → ℝ := S.indicator (fun _ => 1)
  let p : ℝ := (mu S).toReal
  let X (i : Fin n) (sample : Fin n → Omega) : ℝ := Y (sample i) - p
  have hMeas : Measurable Y := measurable_const.indicator hS
  have hBound : ∀ q, Y q ∈ Set.Icc (0 : ℝ) 1 := by
    intro q
    by_cases hq : q ∈ S <;> simp [Y, hq]
  have hMean : (∫ q, Y q ∂mu) = p := by
    simp [Y, p, integral_indicator hS, Measure.real]
  have hSG : HasSubgaussianMGF (fun q => Y q - p) (1 / 4) (mu) := by
    have hSG' := hasSubgaussianMGF_of_mem_Icc (μ := mu)
      hMeas.aemeasurable (ae_of_all _ hBound)
    rw [hMean] at hSG'
    norm_num at hSG'
    exact hSG'
  have hIndep : iIndepFun X (Measure.pi (fun _ : Fin n => mu)) :=
    iIndepFun_pi (X := fun _ : Fin n => fun q => Y q - p)
      (fun _ => (hMeas.sub_const p).aemeasurable)
  have hEach (i : Fin n) : HasSubgaussianMGF (X i) (1 / 4) (Measure.pi (fun _ : Fin n => mu)) := by
    have hMap : (Measure.pi (fun _ : Fin n => mu)).map (Function.eval i) = mu :=
      (measurePreserving_eval (fun _ : Fin n => mu) i).map_eq
    have hSGMap : HasSubgaussianMGF (fun q => Y q - p) (1 / 4)
        ((Measure.pi (fun _ : Fin n => mu)).map (Function.eval i)) := by
      rw [hMap]
      exact hSG
    exact HasSubgaussianMGF.of_map (μ := Measure.pi (fun _ : Fin n => mu)) (Y := Function.eval i)
      (measurable_pi_apply i).aemeasurable hSGMap
  have hNegIndep : iIndepFun (fun i sample => -X i sample) (Measure.pi (fun _ : Fin n => mu)) :=
    hIndep.comp (fun _ => fun x : ℝ => -x) (fun _ => measurable_neg)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hThreshold : 0 ≤ (n : ℝ) * r := mul_nonneg hnR.le hr
  have hUpper := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hIndep
    (s := Finset.univ) (c := fun _ => (1 / 4 : NNReal)) (ε := (n : ℝ) * r)
    (fun i _ => hEach i) hThreshold
  have hLower := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hNegIndep
    (s := Finset.univ) (c := fun _ => (1 / 4 : NNReal)) (ε := (n : ℝ) * r)
    (fun i _ => (hEach i).neg) hThreshold
  have hExponent : -((n : ℝ) * r) ^ 2 / (2 * (∑ _i : Fin n, (1 / 4 : NNReal) : NNReal)) =
      -2 * (n : ℝ) * r ^ 2 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
    field_simp [ne_of_gt hnR]
    ring
  rw [hExponent] at hUpper hLower
  have hSum (sample : Fin n → Omega) :
      ∑ i : Fin n, X i sample = (n : ℝ) * ((∑ i : Fin n, Y (sample i)) / n - p) := by
    simp only [X, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp [ne_of_gt hnR]
  have hSub : {sample : Fin n → Omega |
      r ≤ |(∑ i, Y (sample i)) / n - p|} ⊆
      {sample | (n : ℝ) * r ≤ ∑ i, X i sample} ∪
      {sample | (n : ℝ) * r ≤ ∑ i, -X i sample} := by
    intro sample hs
    have hAbs : (n : ℝ) * r ≤ |∑ i, X i sample| := by
      rw [hSum, abs_mul, abs_of_nonneg hnR.le]
      exact mul_le_mul_of_nonneg_left hs hnR.le
    by_cases hSign : 0 ≤ ∑ i, X i sample
    · left
      rwa [abs_of_nonneg hSign] at hAbs
    · right
      change (n : ℝ) * r ≤ ∑ i : Fin n, -X i sample
      rw [Finset.sum_neg_distrib]
      rwa [abs_of_neg (lt_of_not_ge hSign)] at hAbs
  calc
    _ ≤ (Measure.pi (fun _ : Fin n => mu)).real
        ({sample | (n : ℝ) * r ≤ ∑ i, X i sample} ∪
          {sample | (n : ℝ) * r ≤ ∑ i, -X i sample}) := measureReal_mono hSub
    _ ≤ (Measure.pi (fun _ : Fin n => mu)).real {sample | (n : ℝ) * r ≤ ∑ i, X i sample} +
        (Measure.pi (fun _ : Fin n => mu)).real {sample | (n : ℝ) * r ≤ ∑ i, -X i sample} :=
      measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-2 * (n : ℝ) * r ^ 2) := by linarith

/-- Membership bits obtained by conjoining the two observed anchor flags. -/
noncomputable def markedIntervalCode {Omega : Type*} {n : ℕ}
    (R : Omega → Omega → Prop) (p q : Omega) (sample : Fin n → Omega) : Fin n → Bool :=
  fun i => @decide (R p (sample i) ∧ R (sample i) q) (Classical.propDecidable _)

def markedIntervalSet {Omega : Type*} (R : Omega → Omega → Prop) (p q : Omega) : Set Omega :=
  {x | R p x ∧ R x q}

noncomputable def markedFraction {n : ℕ} (code : Fin n → Bool) : ℝ :=
  (∑ i : Fin n, if code i then (1 : ℝ) else 0) / n

theorem marked_interval_code_measurable {Omega : Type*} [MeasurableSpace Omega]
    {n : ℕ} (R : Omega → Omega → Prop) (p q : Omega)
    (hS : MeasurableSet (markedIntervalSet R p q)) :
    Measurable (@markedIntervalCode Omega n R p q) := by
  classical
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_to_bool
  have hEq : (fun sample : Fin n → Omega => markedIntervalCode R p q sample i) ⁻¹' {true} =
      (Function.eval i) ⁻¹' markedIntervalSet R p q := by
    ext sample
    simp [markedIntervalCode, markedIntervalSet]
  rw [hEq]
  exact hS.preimage (measurable_pi_apply i)

theorem marked_fraction_indicator {Omega : Type*} {n : ℕ}
    (R : Omega → Omega → Prop) (p q : Omega) (sample : Fin n → Omega) :
    markedFraction (markedIntervalCode R p q sample) =
      (∑ i : Fin n, (markedIntervalSet R p q).indicator (fun _ => (1 : ℝ)) (sample i)) / n := by
  classical
  simp [markedFraction, markedIntervalCode, markedIntervalSet, Set.indicator_apply]

theorem marked_fraction_relabel {n : ℕ} (code : Fin n → Bool) (e : Fin n ≃ Fin n) :
    markedFraction (code ∘ e) = markedFraction code := by
  unfold markedFraction
  simpa only [Function.comp_apply] using congrArg (fun z : ℝ => z / n)
    (e.sum_comp (fun i => if code i then (1 : ℝ) else 0))

noncomputable def markedIntervalLaw {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (n : ℕ) (R : Omega → Omega → Prop) (p q : Omega) :
    Measure (Fin n → Bool) :=
  (Measure.pi (fun _ : Fin n => mu)).map (markedIntervalCode R p q)

theorem marked_interval_actual_law_hoeffding {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] {n : ℕ} (hn : 0 < n)
    (R : Omega → Omega → Prop) (p q : Omega)
    (hS : MeasurableSet (markedIntervalSet R p q)) {r : ℝ} (hr : 0 ≤ r) :
    (markedIntervalLaw mu n R p q).real
      {code | r ≤ |markedFraction code - mu.real (markedIntervalSet R p q)|} ≤
      2 * Real.exp (-2 * (n : ℝ) * r ^ 2) := by
  rw [markedIntervalLaw, map_measureReal_apply (marked_interval_code_measurable R p q hS)
    (Set.to_countable _ |>.measurableSet)]
  simpa only [Set.preimage_setOf_eq, marked_fraction_indicator, Measure.real] using
    iid_indicator_hoeffding mu hn hS hr

noncomputable def retentionLower (R x : ℝ) : ℝ := x / (R - (R - 1) * x)
noncomputable def retentionUpper (R x : ℝ) : ℝ := R * x / (1 + (R - 1) * x)

theorem retention_denominators {R x : ℝ} (hR : 1 ≤ R) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    0 < R - (R - 1) * x ∧ 0 < 1 + (R - 1) * x := by
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hR) hx.1,
    mul_nonneg (sub_nonneg.mpr hR) (sub_nonneg.mpr hx.2)]

theorem retention_lower_mono {R x y : ℝ} (hR : 1 ≤ R)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) (hxy : x ≤ y) :
    retentionLower R x ≤ retentionLower R y := by
  unfold retentionLower
  rw [div_le_div_iff₀ (retention_denominators hR hx).1 (retention_denominators hR hy).1]
  nlinarith

theorem retention_upper_mono {R x y : ℝ} (hR : 1 ≤ R)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) (hxy : x ≤ y) :
    retentionUpper R x ≤ retentionUpper R y := by
  unfold retentionUpper
  rw [div_le_div_iff₀ (retention_denominators hR hx).2 (retention_denominators hR hy).2]
  nlinarith [mul_nonneg (by linarith : 0 ≤ R) (sub_nonneg.mpr hxy)]

/-- Integrated retention masses imply the physical partial-identification interval. -/
theorem retention_mass_identification {a b v s t : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hv : v ∈ Set.Icc (0 : ℝ) 1)
    (hs : a * v ≤ s ∧ s ≤ b * v)
    (ht : a * (1-v) ≤ t ∧ t ≤ b * (1-v)) :
    retentionLower (b/a) (s/(s+t)) ≤ v ∧ v ≤ retentionUpper (b/a) (s/(s+t)) := by
  have hs0 : 0 ≤ s := le_trans (mul_nonneg ha.le hv.1) hs.1
  have ht0 : 0 ≤ t := le_trans (mul_nonneg ha.le (sub_nonneg.mpr hv.2)) ht.1
  have hst : 0 < s+t := by linarith [hs.1, ht.1]
  have hR : 1 ≤ b/a := (le_div_iff₀ ha).mpr (by simpa using hab)
  have htheta : s/(s+t) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hs0 hst.le, (div_le_one hst).mpr (by linarith)⟩
  have hden := retention_denominators hR htheta
  constructor
  · unfold retentionLower
    apply (div_le_iff₀ hden.1).mpr
    have hcross : a*s ≤ v*(a*s+b*t) := by
      have h1 := mul_le_mul_of_nonneg_right hs.2 (sub_nonneg.mpr hv.2)
      have h2 := mul_le_mul_of_nonneg_left ht.1 (mul_nonneg (ha.le.trans hab) hv.1)
      nlinarith [mul_le_mul_of_nonneg_left h1 ha.le]
    field_simp
    field_simp [ne_of_gt ha, ne_of_gt hst] at *
    nlinarith
  · unfold retentionUpper
    apply (le_div_iff₀ hden.2).mpr
    have hcross : v*(b*s+a*t) ≤ b*s := by
      have h1 := mul_le_mul_of_nonneg_right ht.2 hv.1
      have h2 := mul_le_mul_of_nonneg_left hs.1 (mul_nonneg (ha.le.trans hab) (sub_nonneg.mpr hv.2))
      nlinarith [mul_le_mul_of_nonneg_left h1 ha.le]
    field_simp [ne_of_gt ha, ne_of_gt hst] at *
    nlinarith

theorem retention_interval_composition {R theta v L U : ℝ} (hR : 1 ≤ R)
    (htheta : theta ∈ Set.Icc (0 : ℝ) 1) (hL : L ∈ Set.Icc (0 : ℝ) 1)
    (hU : U ∈ Set.Icc (0 : ℝ) 1)
    (hid : retentionLower R theta ≤ v ∧ v ≤ retentionUpper R theta)
    (hcover : L ≤ theta ∧ theta ≤ U) :
    retentionLower R L ≤ v ∧ v ≤ retentionUpper R U :=
  ⟨(retention_lower_mono hR hL htheta hcover.1).trans hid.1,
   hid.2.trans (retention_upper_mono hR htheta hU hcover.2)⟩

theorem marked_fraction_unit {n : ℕ} (hn : 0 < n) (code : Fin n → Bool) :
    markedFraction code ∈ Set.Icc (0 : ℝ) 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h0 : 0 ≤ ∑ i : Fin n, if code i then (1 : ℝ) else 0 :=
    Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)
  have h1 : (∑ i : Fin n, if code i then (1 : ℝ) else 0) ≤ n := by
    calc
      _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun i _ => by split_ifs <;> norm_num)
      _ = n := by simp
  exact ⟨div_nonneg h0 hnR.le, (div_le_one hnR).mpr h1⟩

noncomputable def markedLower {n : ℕ} (r : ℝ) (code : Fin n → Bool) : ℝ :=
  max 0 (markedFraction code - r)
noncomputable def markedUpper {n : ℕ} (r : ℝ) (code : Fin n → Bool) : ℝ :=
  min 1 (markedFraction code + r)

theorem marked_endpoints_unit {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 ≤ r)
    (code : Fin n → Bool) :
    markedLower r code ∈ Set.Icc (0 : ℝ) 1 ∧ markedUpper r code ∈ Set.Icc (0 : ℝ) 1 := by
  have hc := marked_fraction_unit hn code
  constructor
  · exact ⟨le_max_left _ _, max_le (by norm_num) (by linarith [hc.2])⟩
  · exact ⟨le_min (by norm_num) (by linarith [hc.1]), min_le_left _ _⟩

theorem marked_endpoints_cover {n : ℕ} {theta r : ℝ} {code : Fin n → Bool}
    (htheta : theta ∈ Set.Icc (0 : ℝ) 1)
    (herror : |markedFraction code - theta| ≤ r) :
    markedLower r code ≤ theta ∧ theta ≤ markedUpper r code := by
  have h := abs_le.mp herror
  exact ⟨max_le htheta.1 (by linarith), le_min htheta.2 (by linarith)⟩

/-- Full probability transfer on actual observed membership codes. -/
theorem marked_volume_retention_coverage {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] {n : ℕ} (hn : 0 < n)
    (C : Omega → Omega → Prop) (p q : Omega)
    (hS : MeasurableSet (markedIntervalSet C p q)) {R v r : ℝ}
    (hR : 1 ≤ R) (hr : 0 ≤ r)
    (hid : retentionLower R (mu.real (markedIntervalSet C p q)) ≤ v ∧
      v ≤ retentionUpper R (mu.real (markedIntervalSet C p q))) :
    (markedIntervalLaw mu n C p q).real
      {code | ¬ (retentionLower R (markedLower r code) ≤ v ∧
        v ≤ retentionUpper R (markedUpper r code))} ≤
      2 * Real.exp (-2 * (n : ℝ) * r ^ 2) := by
  have hMeas := marked_interval_code_measurable (n := n) C p q hS
  letI : IsProbabilityMeasure (markedIntervalLaw mu n C p q) :=
    Measure.isProbabilityMeasure_map hMeas.aemeasurable
  have htheta : mu.real (markedIntervalSet C p q) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨measureReal_nonneg, measureReal_le_one⟩
  have hsub : {code : Fin n → Bool | ¬ (retentionLower R (markedLower r code) ≤ v ∧
      v ≤ retentionUpper R (markedUpper r code))} ⊆
      {code | r ≤ |markedFraction code - mu.real (markedIntervalSet C p q)|} := by
    intro code hbad
    by_contra hsmall
    change ¬ r ≤ |markedFraction code - mu.real (markedIntervalSet C p q)| at hsmall
    have herror := (lt_of_not_ge hsmall).le
    exact hbad (retention_interval_composition hR htheta
      (marked_endpoints_unit hn hr code).1 (marked_endpoints_unit hn hr code).2 hid
      (marked_endpoints_cover htheta herror))
  exact (measureReal_mono hsub).trans (marked_interval_actual_law_hoeffding mu hn C p q hS hr)

end QuantyraNullCone

