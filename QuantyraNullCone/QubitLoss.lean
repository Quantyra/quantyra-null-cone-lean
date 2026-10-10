import QuantyraNullCone.BinomialCalibration
import QuantyraNullCone.ConfoundingMarked

namespace QuantyraNullCone

open MeasureTheory

/-- Parameters of the fixed loss-only Pauli-Z measurement model. -/
structure LossOnlyQubit where
  p : ℝ
  etaPlus : ℝ
  etaMinus : ℝ
  p_range : p ∈ Set.Icc (0 : ℝ) 1
  plus_range : etaPlus ∈ Set.Icc (1/2 : ℝ) 1
  minus_range : etaMinus ∈ Set.Icc (1/2 : ℝ) 1

def LossOnlyQubit.theta (q : LossOnlyQubit) : ℝ := 2*q.p-1

def LossOnlyQubit.rPlus (q : LossOnlyQubit) : ℝ := q.p*q.etaPlus

def LossOnlyQubit.rMinus (q : LossOnlyQubit) : ℝ := (1-q.p)*q.etaMinus

theorem qubit_click_ranges (q : LossOnlyQubit) :
    0 ≤ q.rPlus ∧ 0 ≤ q.rMinus ∧ q.rPlus+q.rMinus ≤ 1 := by
  obtain ⟨hp0, hp1⟩ := q.p_range
  obtain ⟨he0, he1⟩ := q.plus_range
  obtain ⟨hf0, hf1⟩ := q.minus_range
  dsimp [LossOnlyQubit.rPlus, LossOnlyQubit.rMinus]
  refine ⟨mul_nonneg hp0 (by linarith), mul_nonneg (by linarith) (by linarith), ?_⟩
  have h1 := mul_le_mul_of_nonneg_left he1 hp0
  have h2 := mul_le_mul_of_nonneg_left hf1 (sub_nonneg.mpr hp1)
  nlinarith

/-- Outcomes 0,1,2 are positive click, negative click, and no click. -/
noncomputable def qubitTrialLaw (q : LossOnlyQubit) : Measure (Fin 3) :=
  ENNReal.ofReal q.rPlus • Measure.dirac 0 +
  ENNReal.ofReal q.rMinus • Measure.dirac 1 +
  ENNReal.ofReal (1-q.rPlus-q.rMinus) • Measure.dirac 2

instance qubit_trial_probability (q : LossOnlyQubit) : IsProbabilityMeasure (qubitTrialLaw q) := by
  obtain ⟨hp, hm, ht⟩ := qubit_click_ranges q
  refine ⟨?_⟩
  simp only [qubitTrialLaw, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hp hm,
    ← ENNReal.ofReal_add (add_nonneg hp hm) (by linarith)]
  have heq : q.rPlus+q.rMinus+(1-q.rPlus-q.rMinus) = 1 := by ring
  rw [heq, ENNReal.ofReal_one]

theorem qubit_trial_click_masses (q : LossOnlyQubit) :
    (qubitTrialLaw q).real {0} = q.rPlus ∧
    (qubitTrialLaw q).real {1} = q.rMinus := by
  obtain ⟨hp, hm, _⟩ := qubit_click_ranges q
  simp [qubitTrialLaw, Measure.real, Measure.add_apply, Measure.smul_apply,
    ENNReal.toReal_ofReal hp, ENNReal.toReal_ofReal hm]

abbrev QubitRecords (n mPlus mMinus : ℕ) :=
  (Fin n → Fin 3) × (Fin (mPlus+1) × Fin (mMinus+1))

/-- Retain every probe outcome and the two independent calibration counts. -/
noncomputable def qubitRecordLaw (q : LossOnlyQubit) (n mPlus mMinus : ℕ) :
    Measure (QubitRecords n mPlus mMinus) :=
  (Measure.pi (fun _ : Fin n => qubitTrialLaw q)).prod
    ((binomialCountLaw mPlus q.etaPlus).prod (binomialCountLaw mMinus q.etaMinus))

instance qubit_record_probability (q : LossOnlyQubit) (n mPlus mMinus : ℕ) :
    IsProbabilityMeasure (qubitRecordLaw q n mPlus mMinus) := by
  unfold qubitRecordLaw
  infer_instance

noncomputable def qubitProbeCount {n mPlus mMinus : ℕ} (outcome : Fin 3)
    (record : QubitRecords n mPlus mMinus) : Fin (n+1) :=
  boundedBitCount (membershipCode {outcome} record.1)

theorem qubit_probe_count_preserving (q : LossOnlyQubit) (n mPlus mMinus : ℕ)
    (outcome : Fin 3) :
    MeasurePreserving (qubitProbeCount outcome)
      (qubitRecordLaw q n mPlus mMinus)
      (binomialCountLaw n ((qubitTrialLaw q).real {outcome})) := by
  have hc : MeasurePreserving
      (fun sample : Fin n → Fin 3 => boundedBitCount (membershipCode {outcome} sample))
      (Measure.pi (fun _ : Fin n => qubitTrialLaw q))
      (binomialCountLaw n ((qubitTrialLaw q).real {outcome})) := by
    refine ⟨measurable_of_countable _, ?_⟩
    rw [← membership_count_eq_binomial (qubitTrialLaw q) n (measurableSet_singleton outcome)]
    unfold membershipCountLaw membershipLaw
    rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
    rfl
  exact hc.comp measurePreserving_fst

theorem qubit_calibration_plus_preserving (q : LossOnlyQubit) (n mPlus mMinus : ℕ) :
    MeasurePreserving (fun record : QubitRecords n mPlus mMinus => record.2.1)
      (qubitRecordLaw q n mPlus mMinus) (binomialCountLaw mPlus q.etaPlus) :=
  measurePreserving_fst.comp measurePreserving_snd

theorem qubit_calibration_minus_preserving (q : LossOnlyQubit) (n mPlus mMinus : ℕ) :
    MeasurePreserving (fun record : QubitRecords n mPlus mMinus => record.2.2)
      (qubitRecordLaw q n mPlus mMinus) (binomialCountLaw mMinus q.etaMinus) :=
  measurePreserving_snd.comp measurePreserving_snd

noncomputable def qubitConfoundedA : LossOnlyQubit :=
  ⟨2/5, 3/4, 1/2, by norm_num, by norm_num, by norm_num⟩

noncomputable def qubitConfoundedB : LossOnlyQubit :=
  ⟨3/5, 1/2, 3/4, by norm_num, by norm_num, by norm_num⟩

theorem qubit_confounded_trial_law : qubitTrialLaw qubitConfoundedA = qubitTrialLaw qubitConfoundedB := by
  norm_num [qubitTrialLaw, LossOnlyQubit.rPlus, LossOnlyQubit.rMinus,
    qubitConfoundedA, qubitConfoundedB]

theorem qubit_confounded_full_probe_law (n : ℕ) :
    Measure.pi (fun _ : Fin n => qubitTrialLaw qubitConfoundedA) =
    Measure.pi (fun _ : Fin n => qubitTrialLaw qubitConfoundedB) := by
  rw [qubit_confounded_trial_law]

/-- No calibration: the full ternary records cannot uniformly resolve radius below 1/5. -/
theorem qubit_uncalibrated_randomized_obstruction (n : ℕ) {Ω : Type*}
    [MeasurableSpace Ω] (xi : Measure Ω) [IsProbabilityMeasure xi]
    (T : (Fin n → Fin 3) × Ω → ℝ) (hT : Measurable T) {r : ℝ} (hr : r < 1/5) :
    (1/2 : ℝ) ≤ max
      (((Measure.pi (fun _ : Fin n => qubitTrialLaw qubitConfoundedA)).prod xi).real
        {record | r < |T record - qubitConfoundedA.theta|})
      (((Measure.pi (fun _ : Fin n => qubitTrialLaw qubitConfoundedB)).prod xi).real
        {record | r < |T record - qubitConfoundedB.theta|}) := by
  apply identical_law_randomized_scalar_obstruction _ _ xi
    (qubit_confounded_full_probe_law n) T hT
  norm_num [LossOnlyQubit.theta, qubitConfoundedA, qubitConfoundedB]
  linarith

end QuantyraNullCone
