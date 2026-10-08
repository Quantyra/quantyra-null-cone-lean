import QuantyraNullCone.Model
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FunProp

namespace QuantyraNullCone

open MeasureTheory

noncomputable section

abbrev LorentzPoint3 := EuclideanSpace ℝ (Fin 3)

def lorentzPoint3 (t x y : ℝ) : LorentzPoint3 := WithLp.toLp 2 ![t, x, y]

def spatialSquared3 (p : LorentzPoint3) : ℝ := p 1 ^ 2 + p 2 ^ 2
def spatialRadius3 (p : LorentzPoint3) : ℝ := Real.sqrt (spatialSquared3 p)
def lorentzSquare3 (p : LorentzPoint3) : ℝ := -(p 0 ^ 2) + spatialSquared3 p
def lorentzBilinear3 (u v : LorentzPoint3) : ℝ := -(u 0 * v 0) + u 1 * v 1 + u 2 * v 2

def lorentzDiamond3 : Set LorentzPoint3 := {p | |p 0| + spatialRadius3 p < 1}
def closedLorentzDiamond3 : Set LorentzPoint3 := {p | |p 0| + spatialRadius3 p ≤ 1}

/-- Strict future-directed 2+1 Lorentzian chronology, using the spatial Euclidean radius. -/
def chronological3 (p q : LorentzPoint3) : Prop := spatialRadius3 (q - p) < q 0 - p 0

def lorentzVolume3 : ℝ := 2 * Real.pi / 3
def flatDiamondMeasure3 : Measure LorentzPoint3 :=
  (ENNReal.ofReal lorentzVolume3)⁻¹ • (volume : Measure LorentzPoint3).restrict lorentzDiamond3

/-- The selected smooth, bounded, genuinely Euclidean-Lipschitz density class. -/
structure InDensityClass3 (rho : LorentzPoint3 → ℝ) : Prop where
  smoothNeighborhood : ∃ U : Set LorentzPoint3, IsOpen U ∧ closedLorentzDiamond3 ⊆ U ∧
    ContDiffOn ℝ ⊤ rho U
  bounds : ∀ p ∈ closedLorentzDiamond3, (1 / 2 : ℝ) ≤ rho p ∧ rho p ≤ 3 / 2
  lipschitz : ∀ p ∈ closedLorentzDiamond3, ∀ q ∈ closedLorentzDiamond3,
    |rho p - rho q| ≤ 2 * ‖p - q‖
  normalized : (∫ p, rho p ∂flatDiamondMeasure3) = 1

def densityMeasure3 (rho : LorentzPoint3 → ℝ) : Measure LorentzPoint3 :=
  flatDiamondMeasure3.withDensity (fun p => ENNReal.ofReal (rho p))
def sampleMeasure3 (rho : LorentzPoint3 → ℝ) (n : ℕ) : Measure (Fin n → LorentzPoint3) :=
  Measure.pi (fun _ : Fin n => densityMeasure3 rho)
def sampledOrder3 {n : ℕ} (w : Fin n → LorentzPoint3) : OrderCode n := by
  classical
  exact fun i j => decide (chronological3 (w i) (w j))
def orderLaw3 (rho : LorentzPoint3 → ℝ) (n : ℕ) : Measure (OrderCode n) :=
  Measure.map sampledOrder3 (sampleMeasure3 rho n)

def flatDensity3 : LorentzPoint3 → ℝ := fun _ => 1
def densityMetric3 (rho : LorentzPoint3 → ℝ) (p u v : LorentzPoint3) : ℝ :=
  Real.rpow lorentzVolume3 (-2 / 3) * Real.rpow (rho p) (2 / 3) * lorentzBilinear3 u v

theorem spatial_squared_nonneg3 (p : LorentzPoint3) : 0 ≤ spatialSquared3 p := by
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)
theorem spatial_radius_nonneg3 (p : LorentzPoint3) : 0 ≤ spatialRadius3 p := Real.sqrt_nonneg _
theorem spatial_radius_sq3 (p : LorentzPoint3) : spatialRadius3 p ^ 2 = spatialSquared3 p :=
  Real.sq_sqrt (spatial_squared_nonneg3 p)

theorem lorentz_diamond_subset_closed3 : lorentzDiamond3 ⊆ closedLorentzDiamond3 := by
  intro p hp
  change |p 0| + spatialRadius3 p < 1 at hp
  change |p 0| + spatialRadius3 p ≤ 1
  exact hp.le

theorem closed_lorentz_diamond_bounds3 {p : LorentzPoint3} (hp : p ∈ closedLorentzDiamond3) :
    |p 0| ≤ 1 ∧ spatialRadius3 p ≤ 1 := by
  change |p 0| + spatialRadius3 p ≤ 1 at hp
  constructor
  · linarith [spatial_radius_nonneg3 p]
  · linarith [abs_nonneg (p 0)]

theorem chronological3_irreflexive (p : LorentzPoint3) : ¬chronological3 p p := by
  unfold chronological3
  rw [sub_self]
  exact not_lt_of_ge (by simpa using spatial_radius_nonneg3 (0 : LorentzPoint3))

@[fun_prop] theorem continuous_spatial_radius3 : Continuous spatialRadius3 := by
  unfold spatialRadius3 spatialSquared3
  fun_prop

theorem isOpen_lorentzDiamond3 : IsOpen lorentzDiamond3 :=
  isOpen_lt (by fun_prop) continuous_const
theorem isClosed_closedLorentzDiamond3 : IsClosed closedLorentzDiamond3 :=
  isClosed_le (by fun_prop) continuous_const

theorem sampledOrder3_measurable (n : ℕ) : Measurable (@sampledOrder3 n) := by
  classical
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_pi_iff.mpr
  intro j
  apply measurable_to_bool
  have hSet : (fun w : Fin n → LorentzPoint3 => sampledOrder3 w i j) ⁻¹' {true} =
      {w | spatialRadius3 (w j - w i) < (w j) 0 - (w i) 0} := by
    ext w
    simp [sampledOrder3, chronological3]
  rw [hSet]
  apply measurableSet_lt
  · exact continuous_spatial_radius3.measurable.comp ((measurable_pi_apply j).sub (measurable_pi_apply i))
  · fun_prop

#print axioms spatial_radius_sq3
#print axioms closed_lorentz_diamond_bounds3
#print axioms chronological3_irreflexive
#print axioms continuous_spatial_radius3
#print axioms sampledOrder3_measurable

end

end QuantyraNullCone
