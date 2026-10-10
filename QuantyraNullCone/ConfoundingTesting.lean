import QuantyraNullCone.ConfoundingProcess
import QuantyraNullCone.ConfoundingTime

namespace QuantyraNullCone

open MeasureTheory

/-- The no-go also covers count-recording experiments, including known Poisson intensity. -/
theorem calibration_mixed_scalar_obstruction {epsilon : ℝ} (he : 0 ≤ epsilon)
    (heSmall : epsilon ≤ 1/2) (q : Measure ℕ) [IsProbabilityMeasure q]
    (fallback : DiamondPoint) {Y Ω : Type*} [MeasurableSpace Y] [MeasurableSpace Ω]
    (F : (n : ℕ) → (Fin n → DiamondPoint) → Y) (hF : ∀ n, Measurable (F n))
    (xi : Measure Ω) [IsProbabilityMeasure xi] (T : Y × Ω → ℝ) (hT : Measurable T)
    {v0 v1 r : ℝ} (hgap : 2*r < v1-v0) :
    (1/2 : ℝ) ≤ max
      ((((randomGeneratedLaw (densityMeasure lowerFlat) q).map
        (mixedRetainedObservable (fun _ => 1-epsilon) fallback F)).prod xi).real
          {z | r < |T z-v0|})
      ((((randomGeneratedLaw (densityMeasure (calibrationDensity epsilon)) q).map
        (mixedRetainedObservable (calibrationDetector epsilon) fallback F)).prod xi).real
          {z | r < |T z-v1|}) := by
  letI := lower_flat_in_class.isProbabilityMeasure
  letI : IsProbabilityMeasure ((randomGeneratedLaw (densityMeasure lowerFlat) q).map
      (mixedRetainedObservable (fun _ => 1-epsilon) fallback F)) :=
    Measure.isProbabilityMeasure_map
      (mixed_retained_observable_measurable measurable_const fallback F hF).aemeasurable
  exact identical_law_randomized_scalar_obstruction _ _ xi
    (calibration_mixed_observable_equal he heSmall q fallback F hF) T hT hgap

theorem calibration_mixed_volume_randomized_obstruction {epsilon : ℝ} (he : 0 < epsilon)
    (heSmall : epsilon ≤ 1/2) (q : Measure ℕ) [IsProbabilityMeasure q]
    (fallback : DiamondPoint) {m : ℕ} (anchors : Fin m → DiamondPoint)
    {Ω : Type*} [MeasurableSpace Ω] (xi : Measure Ω) [IsProbabilityMeasure xi]
    (T : CountedMarkedOrderCode m × Ω → ℝ) (hT : Measurable T)
    (r : ℝ) (hr : 2*r < epsilon/16) :
    (1/2 : ℝ) ≤ max
      ((((randomGeneratedLaw (densityMeasure lowerFlat) q).map
        (mixedRetainedObservable (fun _ => 1-epsilon) fallback (countedMarkedOrder anchors))).prod xi).real
          {z | r < |T z-(densityMeasure lowerFlat).real
            (markedIntervalSet nullChronology (0,0) (1/2,1/2))|})
      ((((randomGeneratedLaw (densityMeasure (calibrationDensity epsilon)) q).map
        (mixedRetainedObservable (calibrationDetector epsilon) fallback (countedMarkedOrder anchors))).prod xi).real
          {z | r < |T z-(densityMeasure (calibrationDensity epsilon)).real
            (markedIntervalSet nullChronology (0,0) (1/2,1/2))|}) := by
  apply calibration_mixed_scalar_obstruction he.le heSmall q fallback _
    (counted_marked_order_measurable anchors) xi T hT
  rw [calibration_marked_volume he.le heSmall, calibration_flat_marked_volume]
  linarith

theorem calibration_stopped_scalar_obstruction {epsilon : ℝ} (he : 0 ≤ epsilon)
    (heSmall : epsilon ≤ 1/2) (n : ℕ) (fallback : DiamondPoint)
    {Y Ω : Type*} [MeasurableSpace Y] [MeasurableSpace Ω]
    (F : (Fin n → DiamondPoint) → Y) (hF : Measurable F)
    (xi : Measure Ω) [IsProbabilityMeasure xi] (T : Y × Ω → ℝ) (hT : Measurable T)
    {v0 v1 r : ℝ} (hgap : 2*r < v1-v0) :
    (1/2 : ℝ) ≤ max
      ((((generatedStreamLaw (densityMeasure lowerFlat)).map
        (F ∘ stoppedRetainedView (fun _ => 1-epsilon) fallback n)).prod xi).real
          {z | r < |T z-v0|})
      ((((generatedStreamLaw (densityMeasure (calibrationDensity epsilon))).map
        (F ∘ stoppedRetainedView (calibrationDetector epsilon) fallback n)).prod xi).real
          {z | r < |T z-v1|}) := by
  letI := lower_flat_in_class.isProbabilityMeasure
  letI : IsProbabilityMeasure ((generatedStreamLaw (densityMeasure lowerFlat)).map
      (F ∘ stoppedRetainedView (fun _ => 1-epsilon) fallback n)) :=
    Measure.isProbabilityMeasure_map
      (hF.comp (stopped_retained_view_measurable measurable_const fallback n)).aemeasurable
  have hLaw : (generatedStreamLaw (densityMeasure lowerFlat)).map
      (F ∘ stoppedRetainedView (fun _ => 1-epsilon) fallback n) =
      (generatedStreamLaw (densityMeasure (calibrationDensity epsilon))).map
        (F ∘ stoppedRetainedView (calibrationDetector epsilon) fallback n) :=
    calibration_stopped_observable_equal he heSmall n fallback F hF
  exact identical_law_randomized_scalar_obstruction _ _ xi
    hLaw T hT hgap

theorem calibration_density_success_disjoint {epsilon : ℝ} (he : 0 < epsilon)
    (f : DiamondPoint → ℝ) {r : ℝ} (hr : 2*r < epsilon) :
    ¬ (DensityEstimateGood lowerFlat r f ∧
      DensityEstimateGood (calibrationDensity epsilon) r f) := by
  rintro ⟨h0, h1⟩
  have hp : (0,0) ∈ diamond := by constructor <;> constructor <;> norm_num
  have hv : |lowerFlat (0,0) - calibrationDensity epsilon (0,0)| = epsilon := by
    simp [lowerFlat, calibrationDensity, calibrationProfile, abs_of_pos he]
  rcases density_estimate_common_orbit h0 h1 with hd | hs
  · have h := hd (0,0) hp
    rw [hv] at h
    linarith
  · have h := hs (0,0) hp
    change |lowerFlat (0,0) - calibrationDensity epsilon (0,0)| ≤ _ at h
    rw [hv] at h
    linarith

theorem calibration_density_randomized_obstruction {epsilon : ℝ} (he : 0 < epsilon)
    (heSmall : epsilon ≤ 1/2) (n : ℕ) {m : ℕ} (anchors : Fin m → DiamondPoint)
    {Ω : Type*} [MeasurableSpace Ω] (xi : Measure Ω) [IsProbabilityMeasure xi]
    (T : UnlabeledMarkedOrderCode n m × Ω → DiamondPoint → ℝ)
    (r : ℝ) (hr : 2*r < epsilon)
    (h0 : MeasurableSet {z | DensityEstimateGood lowerFlat r (T z)})
    (h1 : MeasurableSet {z | DensityEstimateGood (calibrationDensity epsilon) r (T z)}) :
    (1/2 : ℝ) ≤ max
      (((retainedMarkedOrderLaw lowerFlat (fun _ => 1-epsilon) n anchors).prod xi).real
        {z | ¬ DensityEstimateGood lowerFlat r (T z)})
      (((retainedMarkedOrderLaw (calibrationDensity epsilon) (calibrationDetector epsilon) n anchors).prod xi).real
        {z | ¬ DensityEstimateGood (calibrationDensity epsilon) r (T z)}) := by
  letI := calibration_full_marked_probability heSmall n anchors
  apply identical_law_randomized_obstruction _ _ xi
    (calibration_full_marked_law_equal he.le heSmall n anchors) h0 h1
  rw [Set.disjoint_left]
  intro z hz0 hz1
  exact calibration_density_success_disjoint he (T z) hr ⟨hz0,hz1⟩

theorem calibration_time_randomized_obstruction (n : ℕ) {m : ℕ}
    (anchors : Fin m → DiamondPoint) {Ω : Type*} [MeasurableSpace Ω]
    (xi : Measure Ω) [IsProbabilityMeasure xi]
    (T : UnlabeledMarkedOrderCode n m × Ω → ℝ) (hT : Measurable T)
    (r : ℝ) (hr : 2*r ≤ Real.sqrt 2/30) :
    (1/2 : ℝ) ≤ max
      (((retainedMarkedOrderLaw lowerFlat (fun _ => (3/4 : ℝ)) n anchors).prod xi).real
        {z | r < |T z - timeSeparation lowerFlat (0,0) (1,1)|})
      (((retainedMarkedOrderLaw (calibrationDensity (1/4)) (calibrationDetector (1/4)) n anchors).prod xi).real
        {z | r < |T z - timeSeparation (calibrationDensity (1/4)) (0,0) (1,1)|}) := by
  have hSmall : (1/4 : ℝ) ≤ 1/2 := by norm_num
  have hFlat : (fun _ : DiamondPoint => (3/4 : ℝ)) = (fun _ => 1-(1/4 : ℝ)) := by
    funext _
    norm_num
  rw [hFlat]
  letI := calibration_full_marked_probability hSmall n anchors
  apply identical_law_randomized_scalar_obstruction _ _ xi
    (calibration_full_marked_law_equal (by norm_num) hSmall n anchors) T hT
  exact hr.trans_lt calibration_time_separation

end QuantyraNullCone
