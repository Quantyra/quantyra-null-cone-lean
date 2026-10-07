import QuantyraNullCone.DensityInterpolation

namespace QuantyraNullCone

open MeasureTheory

theorem InDensityClass.transpose {rho : DiamondPoint → ℝ} (h : InDensityClass rho) :
    InDensityClass (transposeDensity rho) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨U, hOpen, hSub, hSmooth⟩ := h.smoothNeighborhood
    let e : DiamondPoint ≃L[ℝ] DiamondPoint :=
      (LinearIsometryEquiv.prodComm ℝ ℝ ℝ).toContinuousLinearEquiv
    refine ⟨e ⁻¹' U, hOpen.preimage e.continuous, ?_, ?_⟩
    · intro p hp
      exact hSub ((transposePoint_mem_diamond p).mpr hp)
    · exact e.contDiffOn_comp_iff.mpr hSmooth
  · intro p hp
    exact h.bounds (transposePoint p) ((transposePoint_mem_diamond p).mpr hp)
  · intro p hp q hq
    have hLip := h.lipschitz (transposePoint p) ((transposePoint_mem_diamond p).mpr hp)
      (transposePoint q) ((transposePoint_mem_diamond q).mpr hq)
    simpa only [transposeDensity, Function.comp_apply, transposePoint, add_comm] using hLip
  · intro u hu
    exact h.marginalV u hu
  · intro v hv
    exact h.marginalU v hv

theorem diamondVolume_transpose_preserving :
    MeasurePreserving transposePoint diamondVolume diamondVolume := by
  have hPre : Prod.swap ⁻¹' diamond = diamond := by
    ext p
    exact transposePoint_mem_diamond p
  have hSwap := Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
    (ν := (volume : Measure ℝ))
  have hRestricted := hSwap.restrict_preimage diamond_measurableSet
  rw [hPre] at hRestricted
  exact hRestricted

theorem densityMeasure_transpose_apply (rho : DiamondPoint → ℝ) {S : Set DiamondPoint}
    (hS : MeasurableSet S) :
    densityMeasure (transposeDensity rho) S = densityMeasure rho (transposePoint ⁻¹' S) := by
  have hMeas : Measurable transposePoint := measurable_swap
  have hEmbed : MeasurableEmbedding transposePoint := MeasurableEquiv.prodComm.measurableEmbedding
  have hTwice : transposePoint ⁻¹' (transposePoint ⁻¹' S) = S := by
    ext p
    rfl
  have hInt := diamondVolume_transpose_preserving.setLIntegral_comp_preimage_emb hEmbed
    (fun p => ENNReal.ofReal (rho p)) (transposePoint ⁻¹' S)
  rw [hTwice] at hInt
  rw [densityMeasure, densityMeasure, withDensity_apply _ hS,
    withDensity_apply _ (hS.preimage hMeas)]
  exact hInt

theorem populationCDF_transpose (rho : DiamondPoint → ℝ) (s t : ℝ) :
    populationCDF (transposeDensity rho) s t = populationCDF rho t s := by
  have hS : MeasurableSet {p : DiamondPoint | p.1 ≤ s ∧ p.2 ≤ t} :=
    (measurableSet_le measurable_fst measurable_const).inter
      (measurableSet_le measurable_snd measurable_const)
  have hPre : transposePoint ⁻¹' {p : DiamondPoint | p.1 ≤ s ∧ p.2 ≤ t} =
      {p : DiamondPoint | p.1 ≤ t ∧ p.2 ≤ s} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_setOf_eq, transposePoint]
    exact and_comm
  unfold populationCDF
  rw [densityMeasure_transpose_apply rho hS, hPre]

theorem coefficientDeviation_transpose_both (rho sigma : DiamondPoint → ℝ) :
    coefficientDeviation (transposeDensity rho) (transposeDensity sigma) =
      coefficientDeviation rho sigma := by
  unfold coefficientDeviation
  congr 1
  ext z
  constructor
  · rintro ⟨p, hp, hz⟩
    exact ⟨transposePoint p, (transposePoint_mem_diamond p).mpr hp, hz⟩
  · rintro ⟨p, hp, hz⟩
    exact ⟨transposePoint p, (transposePoint_mem_diamond p).mpr hp, hz⟩

#print axioms InDensityClass.transpose
#print axioms diamondVolume_transpose_preserving
#print axioms densityMeasure_transpose_apply
#print axioms populationCDF_transpose
#print axioms coefficientDeviation_transpose_both

end QuantyraNullCone
