import QuantyraNullCone.MarkedVolume

namespace QuantyraNullCone

open MeasureTheory

noncomputable def retainedMeasure {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (pi : Omega → ℝ) : Measure Omega :=
  mu.withDensity (fun x => ENNReal.ofReal (pi x / ∫ y, pi y ∂mu))

theorem retention_integral_bounds {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] {pi : Omega → ℝ}
    (hpi : Integrable pi mu) {a b : ℝ} (hbounds : ∀ x, a ≤ pi x ∧ pi x ≤ b)
    {S : Set Omega} (hS : MeasurableSet S) :
    a * mu.real S ≤ ∫ x in S, pi x ∂mu ∧ ∫ x in S, pi x ∂mu ≤ b * mu.real S := by
  have hlo := setIntegral_mono_on (integrable_const a).integrableOn hpi.integrableOn hS
    (fun x _ => (hbounds x).1)
  have hup := setIntegral_mono_on hpi.integrableOn (integrable_const b).integrableOn hS
    (fun x _ => (hbounds x).2)
  simpa [setIntegral_const, smul_eq_mul, mul_comm] using And.intro hlo hup

theorem retention_total_positive {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] {pi : Omega → ℝ}
    (hpi : Integrable pi mu) {a b : ℝ} (ha : 0 < a)
    (hbounds : ∀ x, a ≤ pi x ∧ pi x ≤ b) : 0 < ∫ x, pi x ∂mu := by
  have h := (retention_integral_bounds mu hpi hbounds MeasurableSet.univ).1
  have h' : a ≤ ∫ x, pi x ∂mu := by simpa using h
  exact ha.trans_le h'

theorem retained_measure_apply {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] {pi : Omega → ℝ}
    (hpi : Integrable pi mu) {a b : ℝ} (ha : 0 < a)
    (hbounds : ∀ x, a ≤ pi x ∧ pi x ≤ b) {S : Set Omega} (hS : MeasurableSet S) :
    retainedMeasure mu pi S = ENNReal.ofReal ((∫ x in S, pi x ∂mu) / ∫ x, pi x ∂mu) := by
  have hZ := retention_total_positive mu hpi ha hbounds
  have hn : 0 ≤ᵐ[mu] fun x => pi x / ∫ y, pi y ∂mu :=
    ae_of_all _ (fun x => div_nonneg (ha.le.trans (hbounds x).1) hZ.le)
  rw [retainedMeasure, withDensity_apply _ hS,
    ← ofReal_integral_eq_lintegral_ofReal (hpi.div_const _).restrict (ae_restrict_of_ae hn)]
  simp only [integral_div]

theorem retained_measure_probability {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] {pi : Omega → ℝ}
    (hpi : Integrable pi mu) {a b : ℝ} (ha : 0 < a)
    (hbounds : ∀ x, a ≤ pi x ∧ pi x ≤ b) : IsProbabilityMeasure (retainedMeasure mu pi) := by
  constructor
  rw [retained_measure_apply mu hpi ha hbounds MeasurableSet.univ]
  simp [ne_of_gt (retention_total_positive mu hpi ha hbounds)]

theorem retained_measure_real_apply {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] {pi : Omega → ℝ}
    (hpi : Integrable pi mu) {a b : ℝ} (ha : 0 < a)
    (hbounds : ∀ x, a ≤ pi x ∧ pi x ≤ b) {S : Set Omega} (hS : MeasurableSet S) :
    (retainedMeasure mu pi).real S = (∫ x in S, pi x ∂mu) / ∫ x, pi x ∂mu := by
  rw [Measure.real, retained_measure_apply mu hpi ha hbounds hS, ENNReal.toReal_ofReal]
  exact div_nonneg (integral_nonneg (fun x => ha.le.trans (hbounds x).1))
    (retention_total_positive mu hpi ha hbounds).le

theorem retained_physical_identification {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] {pi : Omega → ℝ}
    (hpi : Integrable pi mu) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hbounds : ∀ x, a ≤ pi x ∧ pi x ≤ b) {S : Set Omega} (hS : MeasurableSet S) :
    retentionLower (b/a) ((retainedMeasure mu pi).real S) ≤ mu.real S ∧
      mu.real S ≤ retentionUpper (b/a) ((retainedMeasure mu pi).real S) := by
  have hs := retention_integral_bounds mu hpi hbounds hS
  have ht := retention_integral_bounds mu hpi hbounds hS.compl
  rw [measureReal_compl hS, probReal_univ] at ht
  rw [retained_measure_real_apply mu hpi ha hbounds hS,
    ← integral_add_compl hS hpi]
  exact retention_mass_identification ha hab ⟨measureReal_nonneg, measureReal_le_one⟩ hs ht

/-- Actual iid retained observations, with physical volume as the target. -/
theorem retained_marked_volume_coverage {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] {pi : Omega → ℝ}
    (hpi : Integrable pi mu) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hbounds : ∀ x, a ≤ pi x ∧ pi x ≤ b) {n : ℕ} (hn : 0 < n)
    (C : Omega → Omega → Prop) (p q : Omega)
    (hS : MeasurableSet (markedIntervalSet C p q)) {r : ℝ} (hr : 0 ≤ r) :
    (markedIntervalLaw (retainedMeasure mu pi) n C p q).real
      {code | ¬ (retentionLower (b/a) (markedLower r code) ≤ mu.real (markedIntervalSet C p q) ∧
        mu.real (markedIntervalSet C p q) ≤ retentionUpper (b/a) (markedUpper r code))} ≤
      2 * Real.exp (-2 * (n : ℝ) * r ^ 2) := by
  letI := retained_measure_probability mu hpi ha hbounds
  exact marked_volume_retention_coverage (retainedMeasure mu pi) hn C p q hS
    ((le_div_iff₀ ha).mpr (by simpa using hab)) hr
    (retained_physical_identification mu hpi ha hab hbounds hS)

theorem marked_hoeffding_95 {n : ℕ} {r : ℝ} (hbudget : 2 ≤ (n : ℝ) * r^2) :
    2 * Real.exp (-2 * (n : ℝ) * r^2) ≤ (1/20 : ℝ) := by
  have he : (9/8 : ℝ) ≤ Real.exp (1/8) := by
    linarith [Real.add_one_le_exp (1/8 : ℝ)]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 9/8) he 32
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  have h40 : (40 : ℝ) ≤ Real.exp 4 := by linarith
  calc
    _ ≤ 2 * Real.exp (-4) := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith only [hbudget])) (by norm_num)
    _ = 2 / Real.exp 4 := by rw [Real.exp_neg]; rfl
    _ ≤ 1/20 := (div_le_iff₀ (Real.exp_pos 4)).mpr (by linarith)

/-- The rational arithmetic condition used by the executable analytic report. -/
theorem marked_rational_radius_95 {n : ℕ} {r : ℚ} (hbudget : 2 ≤ (n : ℚ) * r^2) :
    2 * Real.exp (-2 * (n : ℝ) * (r : ℝ)^2) ≤ (1/20 : ℝ) := by
  apply marked_hoeffding_95
  exact_mod_cast hbudget

theorem retained_marked_volume_95 {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] {pi : Omega → ℝ}
    (hpi : Integrable pi mu) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hbounds : ∀ x, a ≤ pi x ∧ pi x ≤ b) {n : ℕ} (hn : 0 < n)
    (C : Omega → Omega → Prop) (p q : Omega)
    (hS : MeasurableSet (markedIntervalSet C p q)) {r : ℚ} (hr : 0 ≤ r)
    (hbudget : 2 ≤ (n : ℚ) * r^2) :
    (markedIntervalLaw (retainedMeasure mu pi) n C p q).real
      {code | ¬ (retentionLower (b/a) (markedLower (r : ℝ) code) ≤ mu.real (markedIntervalSet C p q) ∧
        mu.real (markedIntervalSet C p q) ≤ retentionUpper (b/a) (markedUpper (r : ℝ) code))} ≤
      (1/20 : ℝ) :=
  (retained_marked_volume_coverage mu hpi ha hab hbounds hn C p q hS
    (by exact_mod_cast hr)).trans (marked_rational_radius_95 hbudget)

end QuantyraNullCone
