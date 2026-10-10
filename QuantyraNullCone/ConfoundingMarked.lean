import QuantyraNullCone.ConfoundingLaw
import QuantyraNullCone.ConfoundingTargets
import QuantyraNullCone.MarkedOrder

namespace QuantyraNullCone

open MeasureTheory

noncomputable def retainedMarkedOrderLaw (rho pi : DiamondPoint → ℝ) (n : ℕ)
    {m : ℕ} (anchors : Fin m → DiamondPoint) : Measure (UnlabeledMarkedOrderCode n m) :=
  (Measure.pi (fun _ : Fin n => retainedMeasure (densityMeasure rho) pi)).map
    (sampledUnlabeledMarkedOrder anchors)

theorem calibration_full_marked_law_equal {epsilon : ℝ} (he : 0 ≤ epsilon)
    (heSmall : epsilon ≤ 1/2) (n : ℕ) {m : ℕ} (anchors : Fin m → DiamondPoint) :
    retainedMarkedOrderLaw lowerFlat (fun _ => 1-epsilon) n anchors =
      retainedMarkedOrderLaw (calibrationDensity epsilon) (calibrationDetector epsilon) n anchors :=
  calibration_retained_observable_equal he heSmall n (sampledUnlabeledMarkedOrder anchors)

theorem calibration_full_marked_probability {epsilon : ℝ} (heSmall : epsilon ≤ 1/2)
    (n : ℕ) {m : ℕ} (anchors : Fin m → DiamondPoint) :
    IsProbabilityMeasure (retainedMarkedOrderLaw lowerFlat (fun _ => 1-epsilon) n anchors) := by
  letI := diamondVolume_probability
  unfold retainedMarkedOrderLaw
  rw [calibration_flat_retained heSmall]
  exact Measure.isProbabilityMeasure_map (sampled_unlabeled_marked_order_measurable anchors).aemeasurable

theorem calibration_stopped_marked_law_equal {epsilon : ℝ} (he : 0 ≤ epsilon)
    (heSmall : epsilon ≤ 1/2) (n : ℕ) {m : ℕ} (anchors : Fin m → DiamondPoint)
    (fallback : DiamondPoint) :
    (generatedStreamLaw (densityMeasure lowerFlat)).map
      (fun sample => sampledUnlabeledMarkedOrder anchors
        (stoppedRetainedView (fun _ => 1-epsilon) fallback n sample)) =
    (generatedStreamLaw (densityMeasure (calibrationDensity epsilon))).map
      (fun sample => sampledUnlabeledMarkedOrder anchors
        (stoppedRetainedView (calibrationDetector epsilon) fallback n sample)) :=
  calibration_stopped_observable_equal he heSmall n fallback _
    (sampled_unlabeled_marked_order_measurable anchors)

/-- Identical observations cannot separate disjoint success events, with any independent seed. -/
theorem identical_law_randomized_obstruction {Y Ω : Type*} [MeasurableSpace Y] [MeasurableSpace Ω]
    (mu nu : Measure Y) [IsProbabilityMeasure mu] (xi : Measure Ω) [IsProbabilityMeasure xi]
    (hLaw : mu = nu) {A B : Set (Y × Ω)} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : Disjoint A B) :
    (1/2 : ℝ) ≤ max ((mu.prod xi).real Aᶜ) ((nu.prod xi).real Bᶜ) := by
  subst nu
  have hSum : (mu.prod xi).real A + (mu.prod xi).real B ≤ 1 := by
    rw [← measureReal_union hAB hB]
    exact measureReal_le_one
  have hAc := probReal_add_probReal_compl (μ := mu.prod xi) hA
  have hBc := probReal_add_probReal_compl (μ := mu.prod xi) hB
  have hMaxA := le_max_left ((mu.prod xi).real Aᶜ) ((mu.prod xi).real Bᶜ)
  have hMaxB := le_max_right ((mu.prod xi).real Aᶜ) ((mu.prod xi).real Bᶜ)
  linarith

theorem identical_law_randomized_scalar_obstruction {Y Ω : Type*}
    [MeasurableSpace Y] [MeasurableSpace Ω] (mu nu : Measure Y) [IsProbabilityMeasure mu]
    (xi : Measure Ω) [IsProbabilityMeasure xi] (hLaw : mu = nu)
    (T : Y × Ω → ℝ) (hT : Measurable T) {v0 v1 r : ℝ} (hgap : 2*r < v1-v0) :
    (1/2 : ℝ) ≤ max ((mu.prod xi).real {z | r < |T z-v0|})
      ((nu.prod xi).real {z | r < |T z-v1|}) := by
  have hA : MeasurableSet {z | |T z-v0| ≤ r} :=
    measurableSet_le (hT.sub_const v0).abs measurable_const
  have hB : MeasurableSet {z | |T z-v1| ≤ r} :=
    measurableSet_le (hT.sub_const v1).abs measurable_const
  have hAB : Disjoint {z | |T z-v0| ≤ r} {z | |T z-v1| ≤ r} := by
    rw [Set.disjoint_left]
    intro z hz0 hz1
    change |T z-v0| ≤ r at hz0
    change |T z-v1| ≤ r at hz1
    obtain ⟨_, h0⟩ := abs_le.mp hz0
    obtain ⟨h1, _⟩ := abs_le.mp hz1
    linarith
  simpa only [Set.compl_setOf, not_le] using
    identical_law_randomized_obstruction mu nu xi hLaw hA hB hAB

/-- A physical-volume obstruction for every full marked-order estimator and independent seed. -/
theorem calibration_volume_randomized_obstruction {epsilon : ℝ} (he : 0 < epsilon)
    (heSmall : epsilon ≤ 1/2) (n : ℕ) {m : ℕ} (anchors : Fin m → DiamondPoint)
    {Ω : Type*} [MeasurableSpace Ω] (xi : Measure Ω) [IsProbabilityMeasure xi]
    (T : UnlabeledMarkedOrderCode n m × Ω → ℝ) (hT : Measurable T)
    (r : ℝ) (hr : 2*r < epsilon/16) :
    (1/2 : ℝ) ≤ max
      (((retainedMarkedOrderLaw lowerFlat (fun _ => 1-epsilon) n anchors).prod xi).real
        {z | r < |T z - (densityMeasure lowerFlat).real
          (markedIntervalSet nullChronology (0,0) (1/2,1/2))|})
      (((retainedMarkedOrderLaw (calibrationDensity epsilon) (calibrationDetector epsilon) n anchors).prod xi).real
        {z | r < |T z - (densityMeasure (calibrationDensity epsilon)).real
          (markedIntervalSet nullChronology (0,0) (1/2,1/2))|}) := by
  letI := calibration_full_marked_probability heSmall n anchors
  apply identical_law_randomized_scalar_obstruction _ _ xi
    (calibration_full_marked_law_equal he.le heSmall n anchors) T hT
  rw [calibration_marked_volume he.le heSmall, calibration_flat_marked_volume]
  linarith

end QuantyraNullCone
