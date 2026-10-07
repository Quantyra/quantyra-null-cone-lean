import QuantyraNullCone.Coordinates
import QuantyraNullCone.Concentration

namespace QuantyraNullCone

open MeasureTheory

def SampleGood {n : ℕ} (rho : DiamondPoint → ℝ) (m : ℕ) (r : ℝ)
    (sample : Fin n → DiamondPoint) : Prop :=
  (∀ i, sample i ∈ diamond) ∧
    Function.Injective (fun i => (sample i).1) ∧
    Function.Injective (fun i => (sample i).2) ∧
    GridOccupied (fun i => (sample i).1) (fun i => (sample i).2) m r ∧
    GridVertexAccuracy (fun i => (sample i).1) (fun i => (sample i).2) rho m r

theorem InDensityClass.sample_good_probability {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) {n m : ℕ} (hn : 0 < n) {r : ℝ}
    (hr : 0 < r) (hmr : (m : ℝ) * r = 1) :
    1 - ((m : ℝ) ^ 2 * Real.exp (-(n : ℝ) * r ^ 2 / 2) +
      2 * ((m : ℝ) + 1) ^ 2 * Real.exp (-2 * (n : ℝ) * r ^ 2)) ≤
      (sampleMeasure rho n).real {sample | SampleGood rho m r sample} := by
  classical
  letI : IsProbabilityMeasure (sampleMeasure rho n) := h.sample_isProbabilityMeasure n
  let base : Set (Fin n → DiamondPoint) := {sample | (∀ i, sample i ∈ diamond) ∧
    Function.Injective (fun i => (sample i).1) ∧ Function.Injective (fun i => (sample i).2)}
  let occBad : Set (Fin n → DiamondPoint) := {sample | ¬ GridOccupied
    (fun i => (sample i).1) (fun i => (sample i).2) m r}
  let vertexBad : Set (Fin n → DiamondPoint) := {sample | ¬ GridVertexAccuracy
    (fun i => (sample i).1) (fun i => (sample i).2) rho m r}
  let good : Set (Fin n → DiamondPoint) := {sample | SampleGood rho m r sample}
  have hBase : ∀ᵐ sample ∂sampleMeasure rho n, sample ∈ base :=
    (h.sample_ae_mem_diamond n).and (h.sample_coordinates_injective n)
  have hBaseZero : (sampleMeasure rho n).real baseᶜ = 0 := by
    have hz : sampleMeasure rho n baseᶜ = 0 := ae_iff.mp hBase
    exact congrArg ENNReal.toReal hz
  have hSub : goodᶜ ⊆ (baseᶜ ∪ occBad) ∪ vertexBad := by
    intro sample hs
    change ¬ SampleGood rho m r sample at hs
    change (¬ ((∀ i, sample i ∈ diamond) ∧
      Function.Injective (fun i => (sample i).1) ∧ Function.Injective (fun i => (sample i).2)) ∨
      ¬ GridOccupied (fun i => (sample i).1) (fun i => (sample i).2) m r) ∨
      ¬ GridVertexAccuracy (fun i => (sample i).1) (fun i => (sample i).2) rho m r
    unfold SampleGood at hs
    tauto
  have hFailure : (sampleMeasure rho n).real goodᶜ ≤
      (m : ℝ) ^ 2 * Real.exp (-(n : ℝ) * r ^ 2 / 2) +
        2 * ((m : ℝ) + 1) ^ 2 * Real.exp (-2 * (n : ℝ) * r ^ 2) := by
    calc
      _ ≤ (sampleMeasure rho n).real ((baseᶜ ∪ occBad) ∪ vertexBad) := measureReal_mono hSub
      _ ≤ ((sampleMeasure rho n).real baseᶜ + (sampleMeasure rho n).real occBad) +
          (sampleMeasure rho n).real vertexBad := by
        have hInner := measureReal_union_le (μ := sampleMeasure rho n) baseᶜ occBad
        have hOuter := measureReal_union_le (μ := sampleMeasure rho n) (baseᶜ ∪ occBad) vertexBad
        linarith only [hInner, hOuter]
      _ ≤ _ := by
        rw [hBaseZero]
        simpa only [zero_add] using add_le_add (h.grid_occupancy_failure n m hr hmr)
          (h.grid_vertices_failure hn m hr.le)
  have hCover : 1 ≤ (sampleMeasure rho n).real good + (sampleMeasure rho n).real goodᶜ := by
    calc
      1 = (sampleMeasure rho n).real Set.univ := probReal_univ.symm
      _ = (sampleMeasure rho n).real (good ∪ goodᶜ) := by rw [Set.union_compl_self]
      _ ≤ _ := measureReal_union_le _ _
  linarith

def SampleCDFReconstructed {n : ℕ} (rho : DiamondPoint → ℝ) (a : ℝ)
    (sample : Fin n → DiamondPoint) : Prop :=
  ∀ L : Realizer (Chronological (fun i => (sample i).1) (fun i => (sample i).2)),
    ∃ swap : Bool, ∀ s t : ℝ,
      |empiricalCDF (fun i => (rank (L.aligned swap).first i : ℝ) / n)
        (fun i => (rank (L.aligned swap).second i : ℝ) / n) s t -
        populationCDF rho s t| ≤ a

theorem InDensityClass.reconstruction_probability_grid {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) {n m : ℕ} (hn : 0 < n) (hm : 16 ≤ m) {r : ℝ}
    (hr : 0 < r) (hmr : (m : ℝ) * r = 1) :
    1 - ((m : ℝ) ^ 2 * Real.exp (-(n : ℝ) * r ^ 2 / 2) +
      2 * ((m : ℝ) + 1) ^ 2 * Real.exp (-2 * (n : ℝ) * r ^ 2)) ≤
      (sampleMeasure rho n).real {sample | SampleCDFReconstructed rho (87 * r) sample} := by
  letI : IsProbabilityMeasure (sampleMeasure rho n) := h.sample_isProbabilityMeasure n
  refine (h.sample_good_probability hn hr hmr).trans (measureReal_mono ?_)
  intro sample hs
  obtain ⟨hSquare, hU, hV, hOcc, hGrid⟩ := hs
  intro L
  exact finite_realizer_cumulative_error_of_grid_vertices h hn hm hr hmr
    (fun i => (hSquare i).1) (fun i => (hSquare i).2) hU hV hOcc L hGrid

#print axioms InDensityClass.sample_good_probability
#print axioms InDensityClass.reconstruction_probability_grid

end QuantyraNullCone
