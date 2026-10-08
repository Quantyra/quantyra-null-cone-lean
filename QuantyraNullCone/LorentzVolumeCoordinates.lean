import QuantyraNullCone.LorentzPreservation
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

namespace QuantyraNullCone

open MeasureTheory

noncomputable section

abbrev SpatialPoint3 := EuclideanSpace ℝ (Fin 2)

def splitLorentzEquiv3 : LorentzPoint3 ≃ᵐ (ℝ × SpatialPoint3) :=
  (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
      ((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))))

theorem split_lorentz_volume_preserving3 : MeasurePreserving splitLorentzEquiv3 := by
  have hId : MeasurePreserving (id : ℝ → ℝ) := ⟨measurable_id, by simp⟩
  have hProd : MeasurePreserving
      ((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))) := by
    change MeasurePreserving (Prod.map (id : ℝ → ℝ) (WithLp.toLp 2 : (Fin 2 → ℝ) → SpatialPoint3))
    exact hId.prod (PiLp.volume_preserving_toLp (Fin 2))
  exact (hProd.comp (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0)).comp
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3))

theorem split_lorentz_time3 (p : LorentzPoint3) : (splitLorentzEquiv3 p).1 = p 0 := rfl

theorem split_lorentz_radius3 (p : LorentzPoint3) : ‖(splitLorentzEquiv3 p).2‖ = spatialRadius3 p := by
  change ‖WithLp.toLp 2 (fun i : Fin 2 => p (Fin.succAbove 0 i))‖ = spatialRadius3 p
  simp [EuclideanSpace.norm_eq, spatialRadius3, spatialSquared3, Fin.sum_univ_succ,
    Real.norm_eq_abs, sq_abs]

def splitLorentzDiamond3 : Set (ℝ × SpatialPoint3) :=
  {q | q.2 ∈ Metric.ball 0 (1 - |q.1|)}

theorem spatial_radius_triangle3 (p q r : LorentzPoint3) :
    spatialRadius3 (r - p) ≤ spatialRadius3 (r - q) + spatialRadius3 (q - p) := by
  have hSplit : (splitLorentzEquiv3 (r - p)).2 =
      (splitLorentzEquiv3 (r - q)).2 + (splitLorentzEquiv3 (q - p)).2 := by
    ext i
    fin_cases i
    · change r 1 - p 1 = (r 1 - q 1) + (q 1 - p 1)
      ring
    · change r 2 - p 2 = (r 2 - q 2) + (q 2 - p 2)
      ring
  rw [← split_lorentz_radius3, hSplit, ← split_lorentz_radius3 (r - q),
    ← split_lorentz_radius3 (q - p)]
  exact norm_add_le _ _

theorem chronological3_transitive {p q r : LorentzPoint3}
    (hpq : chronological3 p q) (hqr : chronological3 q r) : chronological3 p r := by
  unfold chronological3 at *
  linarith [spatial_radius_triangle3 p q r]

theorem isOpen_splitLorentzDiamond3 : IsOpen splitLorentzDiamond3 := by
  have hSet : splitLorentzDiamond3 = {q : ℝ × SpatialPoint3 | ‖q.2‖ < 1 - |q.1|} := by
    ext q
    simp [splitLorentzDiamond3, Metric.mem_ball, dist_zero_right]
  rw [hSet]
  exact isOpen_lt continuous_snd.norm (continuous_const.sub continuous_fst.abs)

theorem split_lorentz_diamond_mem3 (p : LorentzPoint3) :
    splitLorentzEquiv3 p ∈ splitLorentzDiamond3 ↔ p ∈ lorentzDiamond3 := by
  simp only [splitLorentzDiamond3, Set.mem_setOf_eq, Metric.mem_ball, dist_zero_right,
    split_lorentz_time3, split_lorentz_radius3, lorentzDiamond3]
  constructor <;> intro h <;> linarith

theorem split_lorentz_diamond_volume3 :
    (volume : Measure LorentzPoint3) lorentzDiamond3 =
      ((volume : Measure ℝ).prod (volume : Measure SpatialPoint3)) splitLorentzDiamond3 := by
  have hPreimage : splitLorentzEquiv3 ⁻¹' splitLorentzDiamond3 = lorentzDiamond3 := by
    ext p
    exact split_lorentz_diamond_mem3 p
  simpa only [hPreimage] using
    split_lorentz_volume_preserving3.measure_preimage_equiv splitLorentzDiamond3

/-- Actual Euclidean spatial-ball cross-sections, valid even when the radius is nonpositive. -/
theorem lorentz_diamond_volume_slices3 :
    (volume : Measure LorentzPoint3) lorentzDiamond3 =
      ∫⁻ t : ℝ, ENNReal.ofReal (1 - |t|) ^ 2 * ENNReal.ofReal Real.pi ∂volume := by
  rw [split_lorentz_diamond_volume3, Measure.prod_apply isOpen_splitLorentzDiamond3.measurableSet]
  apply lintegral_congr
  intro t
  change (volume : Measure SpatialPoint3) (Metric.ball 0 (1 - |t|)) = _
  exact EuclideanSpace.volume_ball_fin_two 0 (1 - |t|)

#print axioms split_lorentz_volume_preserving3
#print axioms chronological3_transitive
#print axioms split_lorentz_radius3
#print axioms split_lorentz_diamond_volume3
#print axioms lorentz_diamond_volume_slices3

end

end QuantyraNullCone
