import QuantyraNullCone.TimeCouplingLoss
import Mathlib.Analysis.SpecificLimits.Basic

/-! Exact almost-everywhere time preservation by a coupling and its relation to the selected loss. -/

namespace QuantyraNullCone
open MeasureTheory Set Filter
noncomputable section

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

structure IsZeroTimeCoupling (mu : Measure X) (nu : Measure Y)
    (tx : X → X → ℝ) (ty : Y → Y → ℝ) (pi : Measure (X × Y)) : Prop
    extends IsTimeCoupling mu nu pi where
  time_eq : ∀ᵐ z ∂pi.prod pi, tx z.1.1 z.2.1 = ty z.1.2 z.2.2

omit [MeasurableSpace X] [MeasurableSpace Y] in
theorem timeBadPairs_antitone (tx : X → X → ℝ) (ty : Y → Y → ℝ)
    {eps eta : ℝ} (h : eps ≤ eta) : timeBadPairs tx ty eta ⊆ timeBadPairs tx ty eps :=
  fun _ hz => h.trans_lt hz

theorem time_eq_ae_of_bad_zero (pi : Measure (X × Y)) {tx : X → X → ℝ} {ty : Y → Y → ℝ}
    (h : ∀ eps : ℝ, 0 < eps → (pi.prod pi) (timeBadPairs tx ty eps) = 0) :
    ∀ᵐ z ∂pi.prod pi, tx z.1.1 z.2.1 = ty z.1.2 z.2.2 := by
  have hall : ∀ n : ℕ, ∀ᵐ z ∂pi.prod pi,
      |tx z.1.1 z.2.1 - ty z.1.2 z.2.2| ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    have hz := measure_eq_zero_iff_ae_notMem.mp (h (1 / ((n : ℝ) + 1)) (by positivity))
    filter_upwards [hz] with z hz
    exact le_of_not_gt hz
  filter_upwards [ae_all_iff.mpr hall] with z hz
  by_contra hn
  have hp : 0 < |tx z.1.1 z.2.1 - ty z.1.2 z.2.2| := abs_pos.mpr (sub_ne_zero.mpr hn)
  obtain ⟨n, hlt⟩ := exists_nat_one_div_lt hp
  exact (not_lt_of_ge (hz n)) hlt

theorem IsZeroTimeCoupling.bad_eq_zero {mu : Measure X} {nu : Measure Y}
    {tx : X → X → ℝ} {ty : Y → Y → ℝ} {pi : Measure (X × Y)}
    (h : IsZeroTimeCoupling mu nu tx ty pi) {eps : ℝ} (he : 0 ≤ eps) :
    (pi.prod pi) (timeBadPairs tx ty eps) = 0 := by
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [h.time_eq] with z hz
  change ¬eps < |tx z.1.1 z.2.1 - ty z.1.2 z.2.2|
  rw [hz, sub_self, abs_zero]
  exact not_lt_of_ge he

theorem IsZeroTimeCoupling.loss_eq_zero {mu : Measure X} {nu : Measure Y}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {tx : X → X → ℝ} {ty : Y → Y → ℝ} {pi : Measure (X × Y)}
    (h : IsZeroTimeCoupling mu nu tx ty pi) : timeDistortionLoss mu nu tx ty = 0 := by
  apply le_antisymm _ (timeDistortionLoss_nonneg mu nu tx ty)
  by_contra hn
  have hp : 0 < timeDistortionLoss mu nu tx ty := lt_of_not_ge hn
  have he : 0 < timeDistortionLoss mu nu tx ty / 2 := by linarith
  have had : TimeDistortionAdmissible mu nu tx ty (timeDistortionLoss mu nu tx ty / 2) :=
    ⟨he, pi, h.toIsTimeCoupling, by rw [h.bad_eq_zero he.le]; exact bot_le⟩
  have hb := timeDistortionLoss_le_of_admissible had
  linarith

#print axioms timeBadPairs_antitone
#print axioms time_eq_ae_of_bad_zero
#print axioms IsZeroTimeCoupling.bad_eq_zero
#print axioms IsZeroTimeCoupling.loss_eq_zero

end
end QuantyraNullCone
