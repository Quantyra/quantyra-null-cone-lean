import QuantyraNullCone.ConfoundingMarked

namespace QuantyraNullCone

open MeasureTheory

theorem calibration_pattern_mass_equal {epsilon : ℝ} (he : 0 ≤ epsilon)
    (heSmall : epsilon ≤ 1/2) {N : ℕ} (I : Finset (Fin N)) :
    (Measure.pi (fun _ : Fin N => (densityMeasure lowerFlat).prod uniform01Measure))
      (retentionPattern (fun _ => 1-epsilon) I) =
    (Measure.pi (fun _ : Fin N => (densityMeasure (calibrationDensity epsilon)).prod uniform01Measure))
      (retentionPattern (calibrationDetector epsilon) I) := by
  classical
  letI := lower_flat_in_class.isProbabilityMeasure
  letI := (calibration_density_in_class he heSmall).isProbabilityMeasure
  have hm := congrArg (fun mu : Measure DiamondPoint => mu Set.univ)
    (calibration_actual_detected_equal he heSmall)
  dsimp only at hm
  simp only [Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ,
    Measure.restrict_apply_univ] at hm
  rw [retentionPattern, Measure.pi_pi, retentionPattern, Measure.pi_pi]
  apply Finset.prod_congr rfl
  intro i _
  split_ifs
  · exact hm
  · rw [prob_compl_eq_one_sub (retention_event_measurable measurable_const),
      prob_compl_eq_one_sub (retention_event_measurable
        (calibration_detector_continuous heSmall).measurable), hm]

/-- Each recorded original retention pattern has the same joint retained-coordinate submeasure. -/
theorem calibration_pattern_submeasure_equal {epsilon : ℝ} (he : 0 ≤ epsilon)
    (heSmall : epsilon ≤ 1/2) {N : ℕ} (code : Fin N → Bool) (fallback : DiamondPoint) :
    ((Measure.pi (fun _ : Fin N => (densityMeasure lowerFlat).prod uniform01Measure)).restrict
      (membershipCode (retentionEvent (fun _ => 1-epsilon)) ⁻¹' {code})).map
        (retainedOrderedView (fun _ => 1-epsilon) fallback (bitCount code)) =
    ((Measure.pi (fun _ : Fin N => (densityMeasure (calibrationDensity epsilon)).prod uniform01Measure)).restrict
      (membershipCode (retentionEvent (calibrationDetector epsilon)) ⁻¹' {code})).map
        (retainedOrderedView (calibrationDetector epsilon) fallback (bitCount code)) := by
  letI := lower_flat_in_class.isProbabilityMeasure
  letI := (calibration_density_in_class he heSmall).isProbabilityMeasure
  have hc : 0 < 1-epsilon := by linarith
  have hZ : 0 < ∫ _ : DiamondPoint, 1-epsilon ∂densityMeasure lowerFlat := by simpa using hc
  rw [retained_pattern_submeasure_law _ measurable_const (integrable_const _)
      (fun _ => ⟨hc.le, by linarith⟩) hZ fallback code rfl,
    retained_pattern_submeasure_law _ (calibration_detector_continuous heSmall).measurable
      (calibration_detector_integrable he heSmall) (calibration_detector_unit he heSmall)
      (by rw [calibration_acceptance_mass he heSmall]; exact hc) fallback code rfl,
    retention_pattern_fiber, retention_pattern_fiber,
    calibration_pattern_mass_equal he heSmall, calibration_flat_retained heSmall,
    calibration_retained_flat he heSmall]

theorem calibration_retention_code_law_equal {epsilon : ℝ} (he : 0 ≤ epsilon)
    (heSmall : epsilon ≤ 1/2) (N : ℕ) :
    membershipLaw ((densityMeasure lowerFlat).prod uniform01Measure) N
      (retentionEvent (fun _ => 1-epsilon)) =
    membershipLaw ((densityMeasure (calibrationDensity epsilon)).prod uniform01Measure) N
      (retentionEvent (calibrationDetector epsilon)) := by
  apply Measure.ext_of_singleton
  intro code
  rw [membershipLaw, Measure.map_apply
    (membership_code_measurable (retention_event_measurable measurable_const)) (measurableSet_singleton code),
    membershipLaw, Measure.map_apply (membership_code_measurable
      (retention_event_measurable (calibration_detector_continuous heSmall).measurable))
      (measurableSet_singleton code), retention_pattern_fiber, retention_pattern_fiber]
  exact calibration_pattern_mass_equal he heSmall _

theorem calibration_terminal_mass_equal {epsilon : ℝ} (he : 0 ≤ epsilon)
    (heSmall : epsilon ≤ 1/2) (N n : ℕ) :
    (Measure.pi (fun _ : Fin N => (densityMeasure lowerFlat).prod uniform01Measure))
      (retainedTerminalEvent (fun _ => 1-epsilon) n N) =
    (Measure.pi (fun _ : Fin N => (densityMeasure (calibrationDensity epsilon)).prod uniform01Measure))
      (retainedTerminalEvent (calibrationDetector epsilon) n N) := by
  have h := congrArg (fun mu : Measure (Fin N → Bool) => mu (retainedTerminalCodes n N : Set _))
    (calibration_retention_code_law_equal he heSmall N)
  dsimp only at h
  simpa only [membershipLaw, Measure.map_apply
    (membership_code_measurable (retention_event_measurable measurable_const)) (Finset.measurableSet _),
    Measure.map_apply (membership_code_measurable
      (retention_event_measurable (calibration_detector_continuous heSmall).measurable))
      (Finset.measurableSet _), retainedTerminalEvent] using h

/-- Stopping-prefix information also leaves the two retained-coordinate laws indistinguishable. -/
theorem calibration_stopped_submeasure_equal {epsilon : ℝ} (he : 0 ≤ epsilon)
    (heSmall : epsilon ≤ 1/2) (N n : ℕ) (fallback : DiamondPoint) :
    ((generatedStreamLaw (densityMeasure lowerFlat)).restrict
      (retainedStopPrefix (fun _ => 1-epsilon) n ⁻¹' {N})).map
        (stoppedRetainedView (fun _ => 1-epsilon) fallback n) =
    ((generatedStreamLaw (densityMeasure (calibrationDensity epsilon))).restrict
      (retainedStopPrefix (calibrationDetector epsilon) n ⁻¹' {N})).map
        (stoppedRetainedView (calibrationDetector epsilon) fallback n) := by
  letI := lower_flat_in_class.isProbabilityMeasure
  letI := (calibration_density_in_class he heSmall).isProbabilityMeasure
  have hc : 0 < 1-epsilon := by linarith
  have hZ : 0 < ∫ _ : DiamondPoint, 1-epsilon ∂densityMeasure lowerFlat := by simpa using hc
  rw [stopped_retained_submeasure _ measurable_const (integrable_const _)
      (fun _ => ⟨hc.le, by linarith⟩) hZ,
    stopped_retained_submeasure _ (calibration_detector_continuous heSmall).measurable
      (calibration_detector_integrable he heSmall) (calibration_detector_unit he heSmall)
      (by rw [calibration_acceptance_mass he heSmall]; exact hc),
    calibration_terminal_mass_equal he heSmall, calibration_flat_retained heSmall,
    calibration_retained_flat he heSmall]

theorem calibration_finite_count_equal {epsilon : ℝ} (he : 0 ≤ epsilon)
    (heSmall : epsilon ≤ 1/2) (N n : ℕ) :
    (Measure.pi (fun _ : Fin N => (densityMeasure lowerFlat).prod uniform01Measure))
      (retainedCountEvent (fun _ => 1-epsilon) N n) =
    (Measure.pi (fun _ : Fin N => (densityMeasure (calibrationDensity epsilon)).prod uniform01Measure))
      (retainedCountEvent (calibrationDetector epsilon) N n) := by
  letI := lower_flat_in_class.isProbabilityMeasure
  letI := (calibration_density_in_class he heSmall).isProbabilityMeasure
  rw [finite_retained_count_mass _ measurable_const (integrable_const _)
      (fun _ => ⟨by linarith, by linarith⟩),
    finite_retained_count_mass _ (calibration_detector_continuous heSmall).measurable
      (calibration_detector_integrable he heSmall) (calibration_detector_unit he heSmall),
    calibration_acceptance_mass he heSmall]
  simp

theorem calibration_finite_submeasure_equal {epsilon : ℝ} (he : 0 ≤ epsilon)
    (heSmall : epsilon ≤ 1/2) (N n : ℕ) (fallback : DiamondPoint) :
    ((Measure.pi (fun _ : Fin N => (densityMeasure lowerFlat).prod uniform01Measure)).restrict
      (retainedCountEvent (fun _ => 1-epsilon) N n)).map
        (retainedOrderedView (fun _ => 1-epsilon) fallback n) =
    ((Measure.pi (fun _ : Fin N => (densityMeasure (calibrationDensity epsilon)).prod uniform01Measure)).restrict
      (retainedCountEvent (calibrationDetector epsilon) N n)).map
        (retainedOrderedView (calibrationDetector epsilon) fallback n) := by
  letI := lower_flat_in_class.isProbabilityMeasure
  letI := (calibration_density_in_class he heSmall).isProbabilityMeasure
  have hc : 0 < 1-epsilon := by linarith
  have hZ : 0 < ∫ _ : DiamondPoint, 1-epsilon ∂densityMeasure lowerFlat := by simpa using hc
  rw [retained_count_submeasure_law _ measurable_const (integrable_const _)
      (fun _ => ⟨hc.le, by linarith⟩) hZ,
    retained_count_submeasure_law _ (calibration_detector_continuous heSmall).measurable
      (calibration_detector_integrable he heSmall) (calibration_detector_unit he heSmall)
      (by rw [calibration_acceptance_mass he heSmall]; exact hc),
    calibration_finite_count_equal he heSmall, calibration_flat_retained heSmall,
    calibration_retained_flat he heSmall]

theorem calibration_mixed_count_equal {epsilon : ℝ} (he : 0 ≤ epsilon)
    (heSmall : epsilon ≤ 1/2) (q : Measure ℕ) (n : ℕ) :
    (randomGeneratedLaw (densityMeasure lowerFlat) q)
      {z | mixedRetainedCount (fun _ => 1-epsilon) z = n} =
    (randomGeneratedLaw (densityMeasure (calibrationDensity epsilon)) q)
      {z | mixedRetainedCount (calibrationDetector epsilon) z = n} := by
  letI := lower_flat_in_class.isProbabilityMeasure
  letI := (calibration_density_in_class he heSmall).isProbabilityMeasure
  have hc : 0 < 1-epsilon := by linarith
  have hZ : 0 < ∫ _ : DiamondPoint, 1-epsilon ∂densityMeasure lowerFlat := by simpa using hc
  rw [mixed_retained_count_mass _ q measurable_const (integrable_const _)
      (fun _ => ⟨hc.le, by linarith⟩) hZ n (0,0),
    mixed_retained_count_mass _ q (calibration_detector_continuous heSmall).measurable
      (calibration_detector_integrable he heSmall) (calibration_detector_unit he heSmall)
      (by rw [calibration_acceptance_mass he heSmall]; exact hc) n (0,0)]
  simp_rw [calibration_finite_count_equal he heSmall]

/-- Any common independently chosen generated count, including fixed and Poisson counts. -/
theorem calibration_mixed_observable_equal {epsilon : ℝ} (he : 0 ≤ epsilon)
    (heSmall : epsilon ≤ 1/2) (q : Measure ℕ) [IsProbabilityMeasure q]
    (fallback : DiamondPoint) {Y : Type*} [MeasurableSpace Y]
    (F : (n : ℕ) → (Fin n → DiamondPoint) → Y) (hF : ∀ n, Measurable (F n)) :
    (randomGeneratedLaw (densityMeasure lowerFlat) q).map
      (mixedRetainedObservable (fun _ => 1-epsilon) fallback F) =
    (randomGeneratedLaw (densityMeasure (calibrationDensity epsilon)) q).map
      (mixedRetainedObservable (calibrationDetector epsilon) fallback F) := by
  letI := lower_flat_in_class.isProbabilityMeasure
  letI := (calibration_density_in_class he heSmall).isProbabilityMeasure
  have hc : 0 < 1-epsilon := by linarith
  have hZ : 0 < ∫ _ : DiamondPoint, 1-epsilon ∂densityMeasure lowerFlat := by simpa using hc
  rw [mixed_retained_observable_law _ q measurable_const (integrable_const _)
      (fun _ => ⟨hc.le, by linarith⟩) hZ fallback F hF,
    mixed_retained_observable_law _ q (calibration_detector_continuous heSmall).measurable
      (calibration_detector_integrable he heSmall) (calibration_detector_unit he heSmall)
      (by rw [calibration_acceptance_mass he heSmall]; exact hc) fallback F hF]
  simp_rw [calibration_mixed_count_equal he heSmall,
    calibration_flat_retained heSmall, calibration_retained_flat he heSmall]

abbrev CountedMarkedOrderCode (m : ℕ) := (n : ℕ) × UnlabeledMarkedOrderCode n m

noncomputable def countedMarkedOrder {m : ℕ} (anchors : Fin m → DiamondPoint)
    (n : ℕ) (sample : Fin n → DiamondPoint) : CountedMarkedOrderCode m :=
  ⟨n, sampledUnlabeledMarkedOrder anchors sample⟩

theorem counted_marked_order_measurable {m : ℕ} (anchors : Fin m → DiamondPoint) (n : ℕ) :
    Measurable (countedMarkedOrder anchors n) :=
  (measurable_of_countable (fun code : UnlabeledMarkedOrderCode n m =>
    (⟨n, code⟩ : CountedMarkedOrderCode m))).comp (sampled_unlabeled_marked_order_measurable anchors)

theorem calibration_mixed_marked_equal {epsilon : ℝ} (he : 0 ≤ epsilon)
    (heSmall : epsilon ≤ 1/2) (q : Measure ℕ) [IsProbabilityMeasure q]
    (fallback : DiamondPoint) {m : ℕ} (anchors : Fin m → DiamondPoint) :
    (randomGeneratedLaw (densityMeasure lowerFlat) q).map
      (mixedRetainedObservable (fun _ => 1-epsilon) fallback (countedMarkedOrder anchors)) =
    (randomGeneratedLaw (densityMeasure (calibrationDensity epsilon)) q).map
      (mixedRetainedObservable (calibrationDetector epsilon) fallback (countedMarkedOrder anchors)) :=
  calibration_mixed_observable_equal he heSmall q fallback _ (counted_marked_order_measurable anchors)

end QuantyraNullCone
