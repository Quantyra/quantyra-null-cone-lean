import QuantyraNullCone.LorentzOrderLaws

namespace QuantyraNullCone

open MeasureTheory

noncomputable section

/-- Reindex actual 2+1 samples. No coordinate transformation or time reversal. -/
def relabelSample3 {n : ℕ} (π : Equiv.Perm (Fin n)) :
    (Fin n → LorentzPoint3) ≃ᵐ (Fin n → LorentzPoint3) :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin n => LorentzPoint3) π.symm

theorem relabelSample3_apply {n : ℕ} (π : Equiv.Perm (Fin n))
    (sample : Fin n → LorentzPoint3) (i : Fin n) :
    relabelSample3 π sample i = sample (π i) := by
  simpa only [Equiv.symm_apply_apply] using
    MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : Fin n => LorentzPoint3) π.symm sample (π i)

theorem sampledOrder3_relabel {n : ℕ} (π : Equiv.Perm (Fin n)) :
    relabelOrder π ∘ sampledOrder3 = sampledOrder3 ∘ relabelSample3 π := by
  funext sample
  change relabelOrder π (sampledOrder3 sample) = sampledOrder3 (relabelSample3 π sample)
  rw [show relabelSample3 π sample = (fun i => sample (π i)) from
    funext (relabelSample3_apply π sample)]
  rfl

/-- Finite mass suffices; smooth density-class membership is unnecessary for labels. -/
theorem sample_relabel_preserving3 {rho : LorentzPoint3 → ℝ}
    [IsFiniteMeasure (densityMeasure3 rho)] {n : ℕ} (π : Equiv.Perm (Fin n)) :
    MeasurePreserving (relabelSample3 π) (sampleMeasure3 rho n) (sampleMeasure3 rho n) := by
  exact measurePreserving_piCongrLeft (fun _ : Fin n => densityMeasure3 rho) π.symm

theorem orderLaw3_exchangeable {rho : LorentzPoint3 → ℝ}
    [IsFiniteMeasure (densityMeasure3 rho)] {n : ℕ} (π : Equiv.Perm (Fin n)) :
    (orderLaw3 rho n).map (relabelOrder π) = orderLaw3 rho n := by
  unfold orderLaw3
  rw [Measure.map_map (measurable_of_countable _) (sampledOrder3_measurable n),
    sampledOrder3_relabel,
    ← Measure.map_map (sampledOrder3_measurable n) (relabelSample3 π).measurable,
    (sample_relabel_preserving3 π).map_eq]

theorem orderLaw3_singleton_relabel {rho : LorentzPoint3 → ℝ}
    [IsFiniteMeasure (densityMeasure3 rho)] {n : ℕ} (π : Equiv.Perm (Fin n))
    (code : OrderCode n) : orderLaw3 rho n {relabelOrder π code} = orderLaw3 rho n {code} := by
  let e := relabelOrderEquiv π
  have hPre : e ⁻¹' {e code} = {code} := by
    ext c
    simp only [Set.mem_preimage, Set.mem_singleton_iff, e.injective.eq_iff]
  have hMap : (orderLaw3 rho n).map e = orderLaw3 rho n := orderLaw3_exchangeable π
  calc
    _ = (orderLaw3 rho n).map e {e code} := by rw [hMap]; rfl
    _ = orderLaw3 rho n (e ⁻¹' {e code}) :=
      Measure.map_apply e.measurable (measurableSet_singleton _)
    _ = orderLaw3 rho n {code} := by rw [hPre]

theorem orderLaw3_fiber_constant {rho : LorentzPoint3 → ℝ}
    [IsFiniteMeasure (densityMeasure3 rho)] {n : ℕ} (code other : OrderCode n)
    (hEq : forgetOrderLabels code = forgetOrderLabels other) :
    (orderLaw3 rho n).real {code} = (orderLaw3 rho n).real {other} := by
  obtain ⟨π, hπ⟩ := Quotient.exact hEq
  rw [← hπ]
  exact congrArg ENNReal.toReal (orderLaw3_singleton_relabel π code).symm

def orderLawTV3 (rho sigma : LorentzPoint3 → ℝ) (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) * ∑ code : OrderCode n,
    |(orderLaw3 rho n).real {code} - (orderLaw3 sigma n).real {code}|

def unlabeledOrderLawTV3 (rho sigma : LorentzPoint3 → ℝ) (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) * ∑ code : UnlabeledOrderCode n,
    |(unlabeledOrderLaw3 rho n).real {code} - (unlabeledOrderLaw3 sigma n).real {code}|

theorem orderLaw3_finite {rho : LorentzPoint3 → ℝ}
    [IsFiniteMeasure (densityMeasure3 rho)] (n : ℕ) : IsFiniteMeasure (orderLaw3 rho n) := by
  letI : IsFiniteMeasure (sampleMeasure3 rho n) := by
    unfold sampleMeasure3
    infer_instance
  unfold orderLaw3
  infer_instance

/-- Exact finite labeled/unlabeled TV equality for the actual Lorentz chronology. -/
theorem unlabeledOrderLawTV3_eq {rho sigma : LorentzPoint3 → ℝ}
    [IsFiniteMeasure (densityMeasure3 rho)] [IsFiniteMeasure (densityMeasure3 sigma)] (n : ℕ) :
    unlabeledOrderLawTV3 rho sigma n = orderLawTV3 rho sigma n := by
  letI := orderLaw3_finite (rho := rho) n
  letI := orderLaw3_finite (rho := sigma) n
  unfold unlabeledOrderLawTV3 unlabeledOrderLaw3 orderLawTV3
  rw [finite_map_L1_of_fiber_constant _ _ _ orderLaw3_fiber_constant orderLaw3_fiber_constant]

/-- An elementary finite-measure fact, with finiteness explicit for real conversion. -/
theorem finite_measure_eq_of_L1_zero {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : (∑ a : α, |μ.real {a} - ν.real {a}|) = 0) : μ = ν := by
  classical
  apply Measure.ext_of_singleton
  intro a
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  have ha : |μ.real {a} - ν.real {a}| ≤ 0 := by
    calc
      _ ≤ ∑ x : α, |μ.real {x} - ν.real {x}| :=
        Finset.single_le_sum (fun x _ => abs_nonneg (μ.real {x} - ν.real {x})) (Finset.mem_univ a)
      _ = 0 := h
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm ha (abs_nonneg _)))

theorem unlabeledOrderLaw3_eq_iff {rho sigma : LorentzPoint3 → ℝ}
    [IsFiniteMeasure (densityMeasure3 rho)] [IsFiniteMeasure (densityMeasure3 sigma)] (n : ℕ) :
    unlabeledOrderLaw3 rho n = unlabeledOrderLaw3 sigma n ↔ orderLaw3 rho n = orderLaw3 sigma n := by
  constructor
  · intro h
    letI := orderLaw3_finite (rho := rho) n
    letI := orderLaw3_finite (rho := sigma) n
    have hTV : orderLawTV3 rho sigma n = 0 := by
      rw [← unlabeledOrderLawTV3_eq, unlabeledOrderLawTV3, h]
      simp
    apply finite_measure_eq_of_L1_zero
    unfold orderLawTV3 at hTV
    linarith
  · intro h
    simp only [unlabeledOrderLaw3, h]

theorem InDensityClass3.unlabeledOrderLawTV_eq {rho sigma : LorentzPoint3 → ℝ}
    (hR : InDensityClass3 rho) (hS : InDensityClass3 sigma) (n : ℕ) :
    unlabeledOrderLawTV3 rho sigma n = orderLawTV3 rho sigma n := by
  letI := hR.isProbabilityMeasure
  letI := hS.isProbabilityMeasure
  exact unlabeledOrderLawTV3_eq n

theorem InDensityClass3.unlabeledOrderLaw_eq_iff {rho sigma : LorentzPoint3 → ℝ}
    (hR : InDensityClass3 rho) (hS : InDensityClass3 sigma) (n : ℕ) :
    unlabeledOrderLaw3 rho n = unlabeledOrderLaw3 sigma n ↔ orderLaw3 rho n = orderLaw3 sigma n := by
  letI := hR.isProbabilityMeasure
  letI := hS.isProbabilityMeasure
  exact unlabeledOrderLaw3_eq_iff n

#print axioms relabelSample3_apply
#print axioms sampledOrder3_relabel
#print axioms sample_relabel_preserving3
#print axioms orderLaw3_exchangeable
#print axioms orderLaw3_singleton_relabel
#print axioms orderLaw3_fiber_constant
#print axioms orderLaw3_finite
#print axioms unlabeledOrderLawTV3_eq
#print axioms finite_measure_eq_of_L1_zero
#print axioms unlabeledOrderLaw3_eq_iff
#print axioms InDensityClass3.unlabeledOrderLawTV_eq
#print axioms InDensityClass3.unlabeledOrderLaw_eq_iff

end

end QuantyraNullCone
