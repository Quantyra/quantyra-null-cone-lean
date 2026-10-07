import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace QuantyraNullCone

open MeasureTheory

abbrev DiamondPoint := ℝ × ℝ

def diamond : Set DiamondPoint :=
  (Set.Icc (0 : ℝ) 1).prod (Set.Icc (0 : ℝ) 1)

def transposePoint (p : DiamondPoint) : DiamondPoint := (p.2, p.1)

def transposeDensity (rho : DiamondPoint → ℝ) : DiamondPoint → ℝ :=
  rho ∘ transposePoint

/-- The original density class, with an explicit Euclidean Lipschitz condition.
The product-space norm is not silently substituted for Euclidean distance. -/
structure InDensityClass (rho : DiamondPoint → ℝ) : Prop where
  smoothNeighborhood : ∃ U : Set DiamondPoint, IsOpen U ∧ diamond ⊆ U ∧
    ContDiffOn ℝ ⊤ rho U
  bounds : ∀ p ∈ diamond, (1 / 2 : ℝ) ≤ rho p ∧ rho p ≤ 3 / 2
  lipschitz : ∀ p ∈ diamond, ∀ q ∈ diamond,
    |rho p - rho q| ≤ 2 * Real.sqrt ((p.1 - q.1)^2 + (p.2 - q.2)^2)
  marginalU : ∀ u ∈ Set.Icc (0 : ℝ) 1,
    (∫ v in (0 : ℝ)..1, rho (u, v)) = 1
  marginalV : ∀ v ∈ Set.Icc (0 : ℝ) 1,
    (∫ u in (0 : ℝ)..1, rho (u, v)) = 1

noncomputable def diamondVolume : Measure DiamondPoint :=
  ((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict diamond

noncomputable def densityMeasure (rho : DiamondPoint → ℝ) : Measure DiamondPoint :=
  diamondVolume.withDensity (fun p => ENNReal.ofReal (rho p))

noncomputable def sampleMeasure (rho : DiamondPoint → ℝ) (n : ℕ) :
    Measure (Fin n → DiamondPoint) :=
  Measure.pi (fun _ : Fin n => densityMeasure rho)

/-- A finite observable encodes only directed chronology, including the false
diagonal. It does not encode either coordinate order or an embedding. -/
abbrev OrderCode (n : ℕ) := Fin n → Fin n → Bool

noncomputable def sampledOrder {n : ℕ} (sample : Fin n → DiamondPoint) : OrderCode n := by
  classical
  exact fun i j => decide ((sample i).1 < (sample j).1 ∧ (sample i).2 < (sample j).2)

noncomputable def orderLaw (rho : DiamondPoint → ℝ) (n : ℕ) : Measure (OrderCode n) :=
  Measure.map sampledOrder (sampleMeasure rho n)

noncomputable def populationCDF (rho : DiamondPoint → ℝ) (s t : ℝ) : ℝ :=
  (densityMeasure rho {p | p.1 ≤ s ∧ p.2 ≤ t}).toReal

noncomputable def coefficientDeviation (rho sigma : DiamondPoint → ℝ) : ℝ :=
  sSup ((fun p => |rho p - sigma p|) '' diamond)

noncomputable def conformalDistance (rho sigma : DiamondPoint → ℝ) : ℝ :=
  min (coefficientDeviation rho sigma) (coefficientDeviation rho (transposeDensity sigma))

noncomputable def orderLawTV (rho sigma : DiamondPoint → ℝ) (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) * ∑ code : OrderCode n,
    |(orderLaw rho n {code}).toReal - (orderLaw sigma n {code}).toReal|

noncomputable def finiteLawDiscrepancy (rho sigma : DiamondPoint → ℝ) (N : ℕ) : ℝ :=
  sSup {d : ℝ | ∃ k : ℕ, 2 ≤ k ∧ k ≤ N ∧ d = orderLawTV rho sigma k}

theorem transposePoint_involutive : Function.Involutive transposePoint := by
  intro p
  rfl

theorem transposeDensity_involutive (rho : DiamondPoint → ℝ) :
    transposeDensity (transposeDensity rho) = rho := by
  funext p
  rfl

theorem transposePoint_mem_diamond (p : DiamondPoint) :
    transposePoint p ∈ diamond ↔ p ∈ diamond := by
  simp only [diamond, transposePoint]
  exact and_comm

theorem InDensityClass.continuousOn {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) : ContinuousOn rho diamond := by
  obtain ⟨U, _, hU, hSmooth⟩ := h.smoothNeighborhood
  exact hSmooth.continuousOn.mono hU

/-- Measurability uses only the observed strict chronological relation. -/
theorem sampledOrder_measurable (n : ℕ) :
    Measurable (@sampledOrder n) := by
  classical
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_pi_iff.mpr
  intro j
  have hU : MeasurableSet {sample : Fin n → DiamondPoint |
      (sample i).1 < (sample j).1} :=
    measurableSet_lt (measurable_fst.comp (measurable_pi_apply i))
      (measurable_fst.comp (measurable_pi_apply j))
  have hV : MeasurableSet {sample : Fin n → DiamondPoint |
      (sample i).2 < (sample j).2} :=
    measurableSet_lt (measurable_snd.comp (measurable_pi_apply i))
      (measurable_snd.comp (measurable_pi_apply j))
  apply measurable_to_bool
  have hSet : (fun sample : Fin n → DiamondPoint => sampledOrder sample i j) ⁻¹' {true} =
      {sample | (sample i).1 < (sample j).1} ∩
      {sample | (sample i).2 < (sample j).2} := by
    ext sample
    simp [sampledOrder]
  rw [hSet]
  exact hU.inter hV

end QuantyraNullCone
