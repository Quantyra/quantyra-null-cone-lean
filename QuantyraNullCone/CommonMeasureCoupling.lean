import QuantyraNullCone.TimeCouplingLoss
import Mathlib.MeasureTheory.Measure.Sub

namespace QuantyraNullCone
open MeasureTheory Set
noncomputable section

variable {X : Type*} [MeasurableSpace X]

/-- Equal residual masses are coupled by a normalized product, including mass zero. -/
def commonResidualCoupling (mu nu omega : Measure X) : Measure (X × X) :=
  ((mu - omega) univ)⁻¹ • (mu - omega).prod (nu - omega)

def commonMeasureCoupling (mu nu omega : Measure X) : Measure (X × X) :=
  graphTimeCoupling omega id + commonResidualCoupling mu nu omega

theorem common_residual_mass_eq {mu nu omega : Measure X}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] [IsFiniteMeasure omega]
    (hm : omega ≤ mu) (hn : omega ≤ nu) : (mu - omega) univ = (nu - omega) univ := by
  rw [Measure.sub_apply MeasurableSet.univ hm, Measure.sub_apply MeasurableSet.univ hn,
    measure_univ (μ := mu), measure_univ (μ := nu)]

theorem common_residual_left {mu nu omega : Measure X}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] [IsFiniteMeasure omega]
    (hm : omega ≤ mu) (hn : omega ≤ nu) :
    (commonResidualCoupling mu nu omega).map Prod.fst = mu - omega := by
  have he := common_residual_mass_eq hm hn
  by_cases hz : (mu - omega) univ = 0
  · have hzero : mu - omega = 0 := Measure.measure_univ_eq_zero.mp hz
    simp [commonResidualCoupling,hzero]
  · rw [commonResidualCoupling,Measure.map_smul,Measure.map_fst_prod,← he,smul_smul,
      ENNReal.inv_mul_cancel hz (measure_ne_top _ _),one_smul]

theorem common_residual_right {mu nu omega : Measure X}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] [IsFiniteMeasure omega]
    (hm : omega ≤ mu) (hn : omega ≤ nu) :
    (commonResidualCoupling mu nu omega).map Prod.snd = nu - omega := by
  have he := common_residual_mass_eq hm hn
  by_cases hz : (mu - omega) univ = 0
  · have hzero : nu - omega = 0 := Measure.measure_univ_eq_zero.mp (he.symm.trans hz)
    simp [commonResidualCoupling,hzero]
  · rw [commonResidualCoupling,Measure.map_smul,Measure.map_snd_prod,smul_smul,
      ENNReal.inv_mul_cancel hz (measure_ne_top _ _),one_smul]

theorem isTimeCoupling_common {mu nu omega : Measure X}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] [IsFiniteMeasure omega]
    (hm : omega ≤ mu) (hn : omega ≤ nu) : IsTimeCoupling mu nu (commonMeasureCoupling mu nu omega) := by
  have hg := isTimeCoupling_graph omega measurable_id
  constructor
  · rw [commonMeasureCoupling,Measure.map_add _ _ measurable_fst,hg.left,
      common_residual_left hm hn,add_comm,Measure.sub_add_cancel_of_le hm]
  · rw [commonMeasureCoupling,Measure.map_add _ _ measurable_snd,hg.right,
      Measure.map_id,common_residual_right hm hn,add_comm,Measure.sub_add_cancel_of_le hn]

theorem common_residual_univ {mu nu omega : Measure X}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] [IsFiniteMeasure omega]
    (hm : omega ≤ mu) (hn : omega ≤ nu) :
    commonResidualCoupling mu nu omega univ = 1 - omega univ := by
  have h := congrArg (fun m : Measure X => m univ) (common_residual_left hm hn)
  simpa only [Measure.map_apply measurable_fst MeasurableSet.univ,preimage_univ,
    Measure.sub_apply MeasurableSet.univ hm,measure_univ (μ := mu)] using h

theorem common_residual_isFiniteMeasure {mu nu omega : Measure X}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] [IsFiniteMeasure omega]
    (hm : omega ≤ mu) (hn : omega ≤ nu) : IsFiniteMeasure (commonResidualCoupling mu nu omega) := by
  letI := (isTimeCoupling_common hm hn).isProbabilityMeasure
  exact isFiniteMeasure_of_le (commonMeasureCoupling mu nu omega)
    (Measure.le_add_left (le_refl _))

theorem IsTimeCoupling.map {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    {mu nu : Measure X} {pi : Measure (X × X)} (h : IsTimeCoupling mu nu pi)
    {f : X → Y} {g : X → Z} (hf : Measurable f) (hg : Measurable g) :
    IsTimeCoupling (mu.map f) (nu.map g) (pi.map (Prod.map f g)) := by
  constructor
  · rw [Measure.map_map measurable_fst (hf.prodMap hg)]
    change pi.map (f ∘ Prod.fst) = _
    rw [← Measure.map_map hf measurable_fst,h.left]
  · rw [Measure.map_map measurable_snd (hf.prodMap hg)]
    change pi.map (g ∘ Prod.snd) = _
    rw [← Measure.map_map hg measurable_snd,h.right]

#print axioms common_residual_mass_eq
#print axioms common_residual_left
#print axioms common_residual_right
#print axioms isTimeCoupling_common
#print axioms common_residual_univ
#print axioms common_residual_isFiniteMeasure
#print axioms IsTimeCoupling.map

end
end QuantyraNullCone
