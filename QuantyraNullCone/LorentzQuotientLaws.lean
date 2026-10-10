import QuantyraNullCone.LorentzQuotientMeasure
import QuantyraNullCone.LorentzUnlabeled

/-! Exact finite iid and directed-order laws on the compact time-profile quotient. -/

namespace QuantyraNullCone
open MeasureTheory
noncomputable section

def closedSampleMeasure3 (rho : LorentzPoint3 → ℝ) (n : ℕ) : Measure (Fin n → ClosedLorentzPoint3) :=
  Measure.pi (fun _ => closedDensityMeasure3 rho)

def closedSampleVal3 {n : ℕ} (s : Fin n → ClosedLorentzPoint3) : Fin n → LorentzPoint3 :=
  fun i => (s i).val

theorem measurable_closedSampleVal3 (n : ℕ) : Measurable (@closedSampleVal3 n) :=
  measurable_pi_lambda _ (fun i => measurable_subtype_coe.comp (measurable_pi_apply i))

theorem InDensityClass3.closedSample_isProbabilityMeasure {rho : LorentzPoint3 → ℝ}
    (hR : InDensityClass3 rho) (n : ℕ) : IsProbabilityMeasure (closedSampleMeasure3 rho n) := by
  letI := hR.closedDensity_isProbabilityMeasure
  unfold closedSampleMeasure3
  infer_instance

theorem InDensityClass3.closedSample_map_val {rho : LorentzPoint3 → ℝ}
    (hR : InDensityClass3 rho) (n : ℕ) :
    (closedSampleMeasure3 rho n).map closedSampleVal3 = sampleMeasure3 rho n := by
  letI := hR.closedDensity_isProbabilityMeasure
  letI : IsProbabilityMeasure ((closedDensityMeasure3 rho).map Subtype.val) :=
    Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
  unfold closedSampleMeasure3 closedSampleVal3 sampleMeasure3
  rw [Measure.pi_map_pi (fun _ => measurable_subtype_coe.aemeasurable)]
  simp_rw [closedDensityMeasure3_map_val]

variable {w : LorentzPoint3 → ℝ} {lo hi : ℝ} (hw : InTimeWeightClass3 w lo hi)

def quotientSampleMeasure3 (rho : LorentzPoint3 → ℝ) (n : ℕ) :
    Measure (Fin n → TimeProfileSpace3 hw) :=
  Measure.pi (fun _ => quotientDensityMeasure3 hw rho)

def quotientSampleProjection3 {n : ℕ} (s : Fin n → ClosedLorentzPoint3) :
    Fin n → TimeProfileSpace3 hw := fun i => timeProfileProjection3 hw (s i)

theorem measurable_quotientSampleProjection3 (n : ℕ) : Measurable (@quotientSampleProjection3 _ _ _ hw n) :=
  measurable_pi_lambda _ (fun i => (continuous_timeProfileProjection3 hw).measurable.comp
    (measurable_pi_apply i))

theorem InDensityClass3.quotientSample_isProbabilityMeasure {rho : LorentzPoint3 → ℝ}
    (hR : InDensityClass3 rho) (n : ℕ) : IsProbabilityMeasure (quotientSampleMeasure3 hw rho n) := by
  letI := hR.quotientDensity_isProbabilityMeasure hw
  unfold quotientSampleMeasure3
  infer_instance

theorem InDensityClass3.quotientSample_map_projection {rho : LorentzPoint3 → ℝ}
    (hR : InDensityClass3 rho) (n : ℕ) :
    (closedSampleMeasure3 rho n).map (quotientSampleProjection3 hw) =
      quotientSampleMeasure3 hw rho n := by
  letI := hR.closedDensity_isProbabilityMeasure
  letI : IsProbabilityMeasure ((closedDensityMeasure3 rho).map (timeProfileProjection3 hw)) :=
    hR.quotientDensity_isProbabilityMeasure hw
  unfold closedSampleMeasure3 quotientSampleProjection3 quotientSampleMeasure3 quotientDensityMeasure3
  exact Measure.pi_map_pi (fun _ => (continuous_timeProfileProjection3 hw).measurable.aemeasurable)

def quotientSampledOrder3 {n : ℕ} (s : Fin n → TimeProfileSpace3 hw) : OrderCode n := by
  classical
  exact fun i j => decide (0 < quotientTime3 hw (s i) (s j))

theorem measurable_quotientSampledOrder3 (n : ℕ) : Measurable (@quotientSampledOrder3 _ _ _ hw n) := by
  classical
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  apply measurable_to_bool
  have hs : (fun s : Fin n → TimeProfileSpace3 hw => quotientSampledOrder3 hw s i j) ⁻¹' {true} =
      {s | 0 < quotientTime3 hw (s i) (s j)} := by
    ext s
    simp [quotientSampledOrder3]
  rw [hs]
  have heval : Measurable (fun s : Fin n → TimeProfileSpace3 hw => (s i, s j)) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply j)
  have ht : Measurable (fun s : Fin n → TimeProfileSpace3 hw => quotientTime3 hw (s i) (s j)) :=
    (continuous_quotientTime3 hw).measurable.comp heval
  exact measurableSet_lt measurable_const ht

theorem quotientSampledOrder3_projection {n : ℕ} (s : Fin n → ClosedLorentzPoint3) :
    quotientSampledOrder3 hw (quotientSampleProjection3 hw s) = sampledOrder3 (closedSampleVal3 s) := by
  classical
  funext i j
  simp only [quotientSampledOrder3, quotientSampleProjection3, sampledOrder3, closedSampleVal3,
    quotientTime3_projection_pos_iff]
  rfl

def quotientOrderLaw3 (rho : LorentzPoint3 → ℝ) (n : ℕ) : Measure (OrderCode n) :=
  (quotientSampleMeasure3 hw rho n).map (quotientSampledOrder3 hw)

theorem InDensityClass3.quotientOrderLaw_eq {rho : LorentzPoint3 → ℝ}
    (hR : InDensityClass3 rho) (n : ℕ) : quotientOrderLaw3 hw rho n = orderLaw3 rho n := by
  unfold quotientOrderLaw3
  rw [← hR.quotientSample_map_projection hw n,
    Measure.map_map (measurable_quotientSampledOrder3 hw n) (measurable_quotientSampleProjection3 hw n)]
  have hcomp : quotientSampledOrder3 hw ∘ quotientSampleProjection3 hw =
      (@sampledOrder3 n) ∘ closedSampleVal3 := funext (quotientSampledOrder3_projection hw)
  rw [hcomp, ← Measure.map_map (sampledOrder3_measurable n) (measurable_closedSampleVal3 n),
    hR.closedSample_map_val n]
  rfl

def quotientUnlabeledOrderLaw3 (rho : LorentzPoint3 → ℝ) (n : ℕ) : Measure (UnlabeledOrderCode n) :=
  (quotientOrderLaw3 hw rho n).map forgetOrderLabels

theorem InDensityClass3.quotientUnlabeledOrderLaw_eq {rho : LorentzPoint3 → ℝ}
    (hR : InDensityClass3 rho) (n : ℕ) :
    quotientUnlabeledOrderLaw3 hw rho n = unlabeledOrderLaw3 rho n := by
  unfold quotientUnlabeledOrderLaw3 unlabeledOrderLaw3
  rw [hR.quotientOrderLaw_eq hw n]

theorem InDensityClass3.quotientOrderLaw_isProbabilityMeasure {rho : LorentzPoint3 → ℝ}
    (hR : InDensityClass3 rho) (n : ℕ) : IsProbabilityMeasure (quotientOrderLaw3 hw rho n) := by
  rw [hR.quotientOrderLaw_eq hw n]
  exact hR.orderLaw_isProbabilityMeasure n

theorem InDensityClass3.quotientOrderLaw_weight_independent {rho : LorentzPoint3 → ℝ}
    (hR : InDensityClass3 rho) {v : LorentzPoint3 → ℝ} {lo' hi' : ℝ}
    (hv : InTimeWeightClass3 v lo' hi') (n : ℕ) :
    quotientOrderLaw3 hw rho n = quotientOrderLaw3 hv rho n := by
  rw [hR.quotientOrderLaw_eq hw n, hR.quotientOrderLaw_eq hv n]

#print axioms measurable_closedSampleVal3
#print axioms InDensityClass3.closedSample_isProbabilityMeasure
#print axioms InDensityClass3.closedSample_map_val
#print axioms measurable_quotientSampleProjection3
#print axioms InDensityClass3.quotientSample_isProbabilityMeasure
#print axioms InDensityClass3.quotientSample_map_projection
#print axioms measurable_quotientSampledOrder3
#print axioms quotientSampledOrder3_projection
#print axioms InDensityClass3.quotientOrderLaw_eq
#print axioms InDensityClass3.quotientUnlabeledOrderLaw_eq
#print axioms InDensityClass3.quotientOrderLaw_isProbabilityMeasure
#print axioms InDensityClass3.quotientOrderLaw_weight_independent

end
end QuantyraNullCone
