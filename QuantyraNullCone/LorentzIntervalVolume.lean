import QuantyraNullCone.LorentzPairInterval

namespace QuantyraNullCone
open MeasureTheory Set
noncomputable section
set_option maxHeartbeats 1000000

theorem lorentz_interval_map_volume3 {p q : LorentzPoint3} (h : chronological3 p q) :
    Measure.map (lorentzIntervalMap3 p q) (volume : Measure LorentzPoint3) =
      (ENNReal.ofReal ((intervalDuration3 p q/2)^3))⁻¹ • volume := by
  let B := lorentzBoost3 (intervalBoostA3 p q) (intervalBoostB3 p q)
  let r := intervalDuration3 p q/2
  let m := (1/2 : ℝ) • (p+q)
  have hr : 0 < r := div_pos (interval_duration_pos3 h) (by norm_num)
  have hB : MeasurePreserving B :=
    lorentz_boost_volume_preserving3 (interval_boost_denominator_pos3 h).ne'
  change Measure.map ((fun v : LorentzPoint3 => m+v) ∘ ((fun v => r•v) ∘ B)) volume = _
  rw [← Measure.map_map (by fun_prop) ((measurable_const_smul r).comp hB.measurable),
    ← Measure.map_map (measurable_const_smul r) hB.measurable,hB.map_eq,
    Measure.map_addHaar_smul volume hr.ne',Measure.map_smul,map_add_left_eq_self]
  simp only [finrank_euclideanSpace, Fintype.card_fin,abs_inv,abs_of_pos (pow_pos hr 3),
    ENNReal.ofReal_inv_of_pos (pow_pos hr 3),r]

theorem lorentz_interval_map_scaled_preserving3 {p q : LorentzPoint3} (h : chronological3 p q) :
    MeasurePreserving (lorentzIntervalMap3 p q)
      (ENNReal.ofReal ((intervalDuration3 p q/2)^3) • (volume : Measure LorentzPoint3)) volume := by
  refine ⟨(continuous_lorentz_interval_map3 p q).measurable, ?_⟩
  rw [Measure.map_smul,lorentz_interval_map_volume3 h,smul_smul,
    ENNReal.mul_inv_cancel (ENNReal.ofReal_ne_zero_iff.mpr
      (pow_pos (div_pos (interval_duration_pos3 h) (by norm_num)) 3)) ENNReal.ofReal_ne_top,
    one_smul]

/-- The actual Lebesgue volume of the chronological interval of any strictly related endpoints. -/
theorem chronological_interval_volume3 {p q : LorentzPoint3} (h : chronological3 p q) :
    (volume : Measure LorentzPoint3) (chronologicalInterval3 p q) =
      ENNReal.ofReal (lorentzVolume3*(intervalDuration3 p q/2)^3) := by
  have he := (lorentz_interval_map_scaled_preserving3 h).measure_preimage
    (isOpen_chronologicalInterval3 p q).measurableSet.nullMeasurableSet
  rw [lorentz_interval_map_preimage3 h,Measure.smul_apply,lorentz_diamond_volume3,
    smul_eq_mul] at he
  rw [ENNReal.ofReal_mul lorentz_volume_pos3.le,mul_comm]
  exact he.symm

theorem lorentz_interval_map_restrict3 {p q : LorentzPoint3} (h : chronological3 p q) :
    Measure.map (lorentzIntervalMap3 p q)
      (ENNReal.ofReal ((intervalDuration3 p q/2)^3) •
        (volume : Measure LorentzPoint3).restrict lorentzDiamond3) =
      volume.restrict (chronologicalInterval3 p q) := by
  have hh := (lorentz_interval_map_scaled_preserving3 h).restrict_preimage
    (isOpen_chronologicalInterval3 p q).measurableSet
  simpa only [lorentz_interval_map_preimage3 h,Measure.restrict_smul] using hh.map_eq

/-- A change of variables for actual interval moments, with its volume factor proved. -/
theorem integral_chronological_interval3 {p q : LorentzPoint3} (h : chronological3 p q)
    {f : LorentzPoint3 → ℝ} (hf : Continuous f) :
    (∫ z in chronologicalInterval3 p q, f z) =
      (intervalDuration3 p q/2)^3 * ∫ v in lorentzDiamond3, f (lorentzIntervalMap3 p q v) := by
  rw [← lorentz_interval_map_restrict3 h,
    integral_map (continuous_lorentz_interval_map3 p q).measurable.aemeasurable hf.aestronglyMeasurable,
    integral_smul_measure,ENNReal.toReal_ofReal
      (pow_nonneg (div_nonneg (interval_duration_pos3 h).le (by norm_num)) 3),
    smul_eq_mul]

theorem chronological_future_interval3 {p : LorentzPoint3} (hp : p ∈ lorentzDiamond3) :
    {q | q ∈ lorentzDiamond3 ∧ chronological3 p q} = chronologicalInterval3 p lorentzTop3 := by
  ext q
  constructor
  · rintro ⟨hq,hpq⟩
    exact ⟨hpq,((lorentz_diamond_iff_tips3 q).mp hq).2⟩
  · rintro ⟨hpq,hqt⟩
    exact ⟨(lorentz_diamond_iff_tips3 q).mpr
      ⟨chronological3_transitive ((lorentz_diamond_iff_tips3 p).mp hp).1 hpq,hqt⟩,hpq⟩

#print axioms lorentz_interval_map_volume3
#print axioms chronological_interval_volume3
#print axioms lorentz_interval_map_restrict3
#print axioms integral_chronological_interval3
#print axioms chronological_future_interval3
end
end QuantyraNullCone
