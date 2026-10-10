import QuantyraNullCone.QubitLoss

namespace QuantyraNullCone

open MeasureTheory

noncomputable def qubitBoxLower (L U : Fin 4 → ℝ) : ℝ :=
  max 0 (max (L 0 / U 2) (1-U 1 / max (1/2) (L 3)))

noncomputable def qubitBoxUpper (L U : Fin 4 → ℝ) : ℝ :=
  min 1 (min (U 0 / max (1/2) (L 2)) (1-L 1 / U 3))

/-- The four intervals are positive/negative probe, positive/negative calibration. -/
noncomputable def qubitBoxReport (L U : Fin 4 → ℝ) : ℝ × ℝ :=
  if U 2 < max (1/2) (L 2) ∨ U 3 < max (1/2) (L 3) ∨
      qubitBoxUpper L U < qubitBoxLower L U then (0, 1)
  else (qubitBoxLower L U, qubitBoxUpper L U)

theorem qubit_box_report_covers (q : LossOnlyQubit) (L U : Fin 4 → ℝ)
    (h0 : L 0 ≤ q.rPlus ∧ q.rPlus ≤ U 0)
    (h1 : L 1 ≤ q.rMinus ∧ q.rMinus ≤ U 1)
    (h2 : L 2 ≤ q.etaPlus ∧ q.etaPlus ≤ U 2)
    (h3 : L 3 ≤ q.etaMinus ∧ q.etaMinus ≤ U 3) :
    (qubitBoxReport L U).1 ≤ q.p ∧ q.p ≤ (qubitBoxReport L U).2 := by
  have hp := q.p_range
  have hmp : 0 ≤ 1-q.p := sub_nonneg.mpr hp.2
  have hel : max (1/2 : ℝ) (L 2) ≤ q.etaPlus := max_le q.plus_range.1 h2.1
  have hfl : max (1/2 : ℝ) (L 3) ≤ q.etaMinus := max_le q.minus_range.1 h3.1
  have helpos : 0 < max (1/2 : ℝ) (L 2) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hflpos : 0 < max (1/2 : ℝ) (L 3) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have heupos : 0 < U 2 := helpos.trans_le (hel.trans h2.2)
  have hfupos : 0 < U 3 := hflpos.trans_le (hfl.trans h3.2)
  have hpl : L 0 / U 2 ≤ q.p := (div_le_iff₀ heupos).mpr
    (h0.1.trans (mul_le_mul_of_nonneg_left h2.2 hp.1))
  have hpu : q.p ≤ U 0 / max (1/2) (L 2) := (le_div_iff₀ helpos).mpr
    ((mul_le_mul_of_nonneg_left hel hp.1).trans h0.2)
  have hml : L 1 / U 3 ≤ 1-q.p := (div_le_iff₀ hfupos).mpr
    (h1.1.trans (mul_le_mul_of_nonneg_left h3.2 hmp))
  have hmu : 1-q.p ≤ U 1 / max (1/2) (L 3) := (le_div_iff₀ hflpos).mpr
    ((mul_le_mul_of_nonneg_left hfl hmp).trans h1.2)
  have hlo : qubitBoxLower L U ≤ q.p := max_le hp.1 (max_le hpl (by linarith))
  have hup : q.p ≤ qubitBoxUpper L U := le_min hp.2 (le_min hpu (by linarith))
  unfold qubitBoxReport
  split_ifs
  · exact hp
  · exact ⟨hlo, hup⟩

theorem binomial_marginal_report_failure {Y : Type*} [MeasurableSpace Y]
    (mu : Measure Y) [IsProbabilityMeasure mu] {n : ℕ} {p : ℝ}
    (f : Y → Fin (n+1)) (hf : MeasurePreserving f mu (binomialCountLaw n p))
    (hp : p ∈ Set.Icc (0 : ℝ) 1) {delta : ℚ} (hd : 0 ≤ delta)
    (L U : Fin (n+1) → ℚ) (hv : BinomialReportValid n delta L U) :
    mu.real {y | ¬ ((L (f y) : ℝ) ≤ p ∧ p ≤ (U (f y) : ℝ))} ≤ (delta : ℝ) := by
  have h := binomial_report_coverage hp hd L U hv
  rw [← hf.map_eq, map_measureReal_apply hf.measurable (Set.to_countable _ |>.measurableSet)] at h
  exact h

/-- Full-record finite 95% coverage, allowing unequal and zero calibration blocks. -/
theorem loss_only_qubit_confidence (q : LossOnlyQubit) (n mPlus mMinus : ℕ)
    (Lp Up Ln Un : Fin (n+1) → ℚ)
    (Le Ue : Fin (mPlus+1) → ℚ) (Lf Uf : Fin (mMinus+1) → ℚ)
    (vp : BinomialReportValid n (1/80) Lp Up)
    (vn : BinomialReportValid n (1/80) Ln Un)
    (ve : BinomialReportValid mPlus (1/80) Le Ue)
    (vf : BinomialReportValid mMinus (1/80) Lf Uf) :
    let report := fun record : QubitRecords n mPlus mMinus => qubitBoxReport
      ![(Lp (qubitProbeCount 0 record) : ℝ), (Ln (qubitProbeCount 1 record) : ℝ),
        (Le record.2.1 : ℝ), (Lf record.2.2 : ℝ)]
      ![(Up (qubitProbeCount 0 record) : ℝ), (Un (qubitProbeCount 1 record) : ℝ),
        (Ue record.2.1 : ℝ), (Uf record.2.2 : ℝ)]
    (qubitRecordLaw q n mPlus mMinus).real {record |
      ¬ (2*(report record).1-1 ≤ q.theta ∧ q.theta ≤ 2*(report record).2-1)} ≤ (1/20 : ℝ) := by
  dsimp only
  let mu := qubitRecordLaw q n mPlus mMinus
  let E0 : Set (QubitRecords n mPlus mMinus) := {record |
    ¬ ((Lp (qubitProbeCount 0 record) : ℝ) ≤ q.rPlus ∧ q.rPlus ≤ (Up (qubitProbeCount 0 record) : ℝ))}
  let E1 : Set (QubitRecords n mPlus mMinus) := {record |
    ¬ ((Ln (qubitProbeCount 1 record) : ℝ) ≤ q.rMinus ∧ q.rMinus ≤ (Un (qubitProbeCount 1 record) : ℝ))}
  let E2 : Set (QubitRecords n mPlus mMinus) := {record |
    ¬ ((Le record.2.1 : ℝ) ≤ q.etaPlus ∧ q.etaPlus ≤ (Ue record.2.1 : ℝ))}
  let E3 : Set (QubitRecords n mPlus mMinus) := {record |
    ¬ ((Lf record.2.2 : ℝ) ≤ q.etaMinus ∧ q.etaMinus ≤ (Uf record.2.2 : ℝ))}
  have hp := qubit_probe_count_preserving q n mPlus mMinus 0
  rw [(qubit_trial_click_masses q).1] at hp
  have hn := qubit_probe_count_preserving q n mPlus mMinus 1
  rw [(qubit_trial_click_masses q).2] at hn
  obtain ⟨hrp, hrn, hsum⟩ := qubit_click_ranges q
  have h0 : mu.real E0 ≤ (1/80 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
      binomial_marginal_report_failure mu _ hp ⟨hrp, by linarith⟩ (by norm_num) Lp Up vp
  have h1 : mu.real E1 ≤ (1/80 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
      binomial_marginal_report_failure mu _ hn ⟨hrn, by linarith⟩ (by norm_num) Ln Un vn
  have h2 : mu.real E2 ≤ (1/80 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
      binomial_marginal_report_failure mu _
        (qubit_calibration_plus_preserving q n mPlus mMinus)
        ⟨by linarith [q.plus_range.1], q.plus_range.2⟩ (by norm_num) Le Ue ve
  have h3 : mu.real E3 ≤ (1/80 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
      binomial_marginal_report_failure mu _
        (qubit_calibration_minus_preserving q n mPlus mMinus)
        ⟨by linarith [q.minus_range.1], q.minus_range.2⟩ (by norm_num) Lf Uf vf
  have hsub : {record : QubitRecords n mPlus mMinus |
      ¬ (2*(qubitBoxReport
        ![(Lp (qubitProbeCount 0 record) : ℝ), (Ln (qubitProbeCount 1 record) : ℝ),
          (Le record.2.1 : ℝ), (Lf record.2.2 : ℝ)]
        ![(Up (qubitProbeCount 0 record) : ℝ), (Un (qubitProbeCount 1 record) : ℝ),
          (Ue record.2.1 : ℝ), (Uf record.2.2 : ℝ)]).1-1 ≤ q.theta ∧
        q.theta ≤ 2*(qubitBoxReport
        ![(Lp (qubitProbeCount 0 record) : ℝ), (Ln (qubitProbeCount 1 record) : ℝ),
          (Le record.2.1 : ℝ), (Lf record.2.2 : ℝ)]
        ![(Up (qubitProbeCount 0 record) : ℝ), (Un (qubitProbeCount 1 record) : ℝ),
          (Ue record.2.1 : ℝ), (Uf record.2.2 : ℝ)]).2-1)} ⊆ ((E0 ∪ E1) ∪ E2) ∪ E3 := by
    intro record hbad
    by_contra hgood
    simp only [Set.mem_union, E0, E1, E2, E3, Set.mem_setOf_eq, not_or, not_not] at hgood
    have hc := qubit_box_report_covers q
      ![(Lp (qubitProbeCount 0 record) : ℝ), (Ln (qubitProbeCount 1 record) : ℝ),
        (Le record.2.1 : ℝ), (Lf record.2.2 : ℝ)]
      ![(Up (qubitProbeCount 0 record) : ℝ), (Un (qubitProbeCount 1 record) : ℝ),
        (Ue record.2.1 : ℝ), (Uf record.2.2 : ℝ)]
      hgood.1.1.1 hgood.1.1.2 hgood.1.2 hgood.2
    apply hbad
    dsimp [LossOnlyQubit.theta]
    constructor <;> linarith [hc.1, hc.2]
  have hb := measureReal_mono (μ := mu) hsub
  have hu0 := measureReal_union_le (μ := mu) E0 E1
  have hu1 := measureReal_union_le (μ := mu) (E0 ∪ E1) E2
  have hu2 := measureReal_union_le (μ := mu) ((E0 ∪ E1) ∪ E2) E3
  linarith

end QuantyraNullCone
