import QuantyraNullCone.TimeCouplingLimit

/-! Attainment of zero distortion by an actual coupling on compact metric spaces. -/

namespace QuantyraNullCone
open MeasureTheory Set Filter Topology
noncomputable section

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
  [BorelSpace X] [BorelSpace Y] [CompactSpace X] [CompactSpace Y]

theorem exists_zeroTimeCoupling_of_loss_zero (mu : Measure X) (nu : Measure Y)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {tx : X → X → ℝ} {ty : Y → Y → ℝ}
    (hx : Continuous (Function.uncurry tx)) (hy : Continuous (Function.uncurry ty))
    (hzero : timeDistortionLoss mu nu tx ty = 0) :
    ∃ pi : Measure (X × Y), IsZeroTimeCoupling mu nu tx ty pi := by
  have hchoose : ∀ n : ℕ, ∃ eps : ℝ, ∃ p : ProbabilityMeasure (X × Y),
      0 < eps ∧ eps < 1 / ((n : ℝ) + 1) ∧ IsTimeCoupling mu nu p.toMeasure ∧
      (p.toMeasure.prod p.toMeasure) (timeBadPairs tx ty eps) ≤ ENNReal.ofReal eps := by
    intro n
    have hsmall : sInf {e | TimeDistortionAdmissible mu nu tx ty e} < 1 / ((n : ℝ) + 1) := by
      change timeDistortionLoss mu nu tx ty < _
      rw [hzero]
      positivity
    obtain ⟨eps, he, hlt⟩ := exists_lt_of_csInf_lt (timeDistortion_nonempty mu nu tx ty) hsmall
    obtain ⟨hepos, pi, hpi, hbad⟩ := he
    exact ⟨eps, ⟨pi, hpi.isProbabilityMeasure⟩, hepos, hlt, hpi, hbad⟩
  choose eps ps hepos hesmall hcoupling hbad using hchoose
  have heps : Tendsto eps atTop (𝓝 0) :=
    squeeze_zero (fun n => (hepos n).le) (fun n => (hesmall n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨p, phi, hmono, hlim⟩ := CompactSpace.tendsto_subseq ps
  refine ⟨p.toMeasure, isZeroTimeCoupling_of_tendsto hlim (fun n => hcoupling (phi n)) hx hy
    (heps.comp hmono.tendsto_atTop) ?_⟩
  exact fun n => hbad (phi n)

theorem timeDistortionLoss_eq_zero_iff (mu : Measure X) (nu : Measure Y)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {tx : X → X → ℝ} {ty : Y → Y → ℝ}
    (hx : Continuous (Function.uncurry tx)) (hy : Continuous (Function.uncurry ty)) :
    timeDistortionLoss mu nu tx ty = 0 ↔
      ∃ pi : Measure (X × Y), IsZeroTimeCoupling mu nu tx ty pi :=
  ⟨exists_zeroTimeCoupling_of_loss_zero mu nu hx hy, fun ⟨_, h⟩ => h.loss_eq_zero⟩

#print axioms exists_zeroTimeCoupling_of_loss_zero
#print axioms timeDistortionLoss_eq_zero_iff

end
end QuantyraNullCone
