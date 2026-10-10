import QuantyraNullCone.TimeCouplingLoss
import Mathlib.Probability.Kernel.Disintegration.StandardBorel

/-! Gluing actual probability couplings by disintegration over their common marginal. -/

namespace QuantyraNullCone
open MeasureTheory ProbabilityTheory Set
noncomputable section

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

theorem time_map_compProd_comap (mu : Measure X) [IsFiniteMeasure mu]
    (k : Kernel Y Z) [IsMarkovKernel k] {f : X → Y} (hf : Measurable f) :
    (mu ⊗ₘ k.comap f hf).map (fun p => (f p.1, p.2)) = mu.map f ⊗ₘ k := by
  have hp : Measurable (fun p : X × Z => (f p.1, p.2)) :=
    (hf.comp measurable_fst).prodMk measurable_snd
  ext s hs
  rw [Measure.map_apply hp hs, Measure.compProd_apply (hp hs),
    Measure.compProd_apply hs, lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf]
  rfl

variable [StandardBorelSpace Z] [Nonempty Z]

def gluedTimeMeasure (piXY : Measure (X × Y)) (piYZ : Measure (Y × Z))
    [IsFiniteMeasure piYZ] : Measure ((X × Y) × Z) :=
  piXY ⊗ₘ piYZ.condKernel.comap Prod.snd measurable_snd

theorem gluedTimeMeasure_left (piXY : Measure (X × Y)) (piYZ : Measure (Y × Z))
    [IsFiniteMeasure piXY] [IsFiniteMeasure piYZ] :
    (gluedTimeMeasure piXY piYZ).map Prod.fst = piXY :=
  Measure.fst_compProd _ _

theorem gluedTimeMeasure_right (piXY : Measure (X × Y)) (piYZ : Measure (Y × Z))
    [IsFiniteMeasure piXY] [IsFiniteMeasure piYZ]
    (hmid : piXY.map Prod.snd = piYZ.map Prod.fst) :
    (gluedTimeMeasure piXY piYZ).map (fun p => (p.1.2, p.2)) = piYZ := by
  rw [gluedTimeMeasure, time_map_compProd_comap piXY piYZ.condKernel measurable_snd, hmid]
  exact piYZ.disintegrate piYZ.condKernel

theorem gluedTimeMeasure_isProbabilityMeasure (piXY : Measure (X × Y)) (piYZ : Measure (Y × Z))
    [IsProbabilityMeasure piXY] [IsFiniteMeasure piYZ] :
    IsProbabilityMeasure (gluedTimeMeasure piXY piYZ) := by
  constructor
  simp [gluedTimeMeasure]

omit [StandardBorelSpace Z] [Nonempty Z] in
theorem isTimeCoupling_glued_endpoints {mu : Measure X} {nu : Measure Y} {xi : Measure Z}
    {piXY : Measure (X × Y)} {piYZ : Measure (Y × Z)}
    (hXY : IsTimeCoupling mu nu piXY) (hYZ : IsTimeCoupling nu xi piYZ)
    {gamma : Measure ((X × Y) × Z)} (hleft : gamma.map Prod.fst = piXY)
    (hright : gamma.map (fun p => (p.1.2, p.2)) = piYZ) :
    IsTimeCoupling mu xi (gamma.map (fun p => (p.1.1, p.2))) := by
  have hxz : Measurable (fun p : (X × Y) × Z => (p.1.1, p.2)) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hyz : Measurable (fun p : (X × Y) × Z => (p.1.2, p.2)) :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  constructor
  · calc
      (gamma.map (fun p => (p.1.1, p.2))).map Prod.fst =
          (gamma.map Prod.fst).map Prod.fst := by
        rw [Measure.map_map measurable_fst hxz, Measure.map_map measurable_fst measurable_fst]
        rfl
      _ = mu := by rw [hleft, hXY.left]
  · calc
      (gamma.map (fun p => (p.1.1, p.2))).map Prod.snd =
          (gamma.map (fun p => (p.1.2, p.2))).map Prod.snd := by
        rw [Measure.map_map measurable_snd hxz, Measure.map_map measurable_snd hyz]
        rfl
      _ = xi := by rw [hright, hYZ.right]

omit [Nonempty Z] in
theorem exists_timeCoupling_gluing {mu : Measure X} {nu : Measure Y} {xi : Measure Z}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] [IsProbabilityMeasure xi]
    {piXY : Measure (X × Y)} {piYZ : Measure (Y × Z)}
    (hXY : IsTimeCoupling mu nu piXY) (hYZ : IsTimeCoupling nu xi piYZ) :
    ∃ gamma : Measure ((X × Y) × Z), IsProbabilityMeasure gamma ∧
      gamma.map Prod.fst = piXY ∧ gamma.map (fun p => (p.1.2, p.2)) = piYZ := by
  letI := nonempty_of_isProbabilityMeasure xi
  letI := hXY.isProbabilityMeasure
  letI := hYZ.isProbabilityMeasure
  exact ⟨gluedTimeMeasure piXY piYZ, gluedTimeMeasure_isProbabilityMeasure piXY piYZ,
    gluedTimeMeasure_left piXY piYZ,
    gluedTimeMeasure_right piXY piYZ (hXY.right.trans hYZ.left.symm)⟩

#print axioms time_map_compProd_comap
#print axioms gluedTimeMeasure_left
#print axioms gluedTimeMeasure_right
#print axioms gluedTimeMeasure_isProbabilityMeasure
#print axioms isTimeCoupling_glued_endpoints
#print axioms exists_timeCoupling_gluing

end
end QuantyraNullCone
