import QuantyraNullCone.DegreeRelabel

namespace QuantyraNullCone

open MeasureTheory

/-- One density-independent estimator of an actual directed-order isomorphism
class. Its only choices are finite order representatives and realizers. -/
noncomputable def selectedDegreeDensity {n : ℕ} (code : UnlabeledOrderCode n) :
    DiamondPoint → ℝ := by
  classical
  exact if DegreeUseHistogram n then
    if hExists : Nonempty (Realizer (CodeRelation code.out)) then
      let m := degreeOuterMesh n
      let r : ℝ := 1 / m
      let h := Real.sqrt r
      let k := Nat.floor (Real.sqrt (m : ℝ))
      (Classical.choice hExists).degreeHistogram r k (8 * h) ((1 - 16 * h) / k)
    else fun _ => 1
  else fun _ => 1

def DensityEstimateGood (rho : DiamondPoint → ℝ) (E : ℝ)
    (estimate : DiamondPoint → ℝ) : Prop :=
  ∃ swap : Bool, ∀ p ∈ diamond,
    |estimate p - (if swap then rho (transposePoint p) else rho p)| ≤ E

theorem selectedDegreeDensity_query_measurable {n : ℕ} (code : UnlabeledOrderCode n) :
    Measurable (selectedDegreeDensity code) := by
  classical
  unfold selectedDegreeDensity
  split
  · split
    · exact Realizer.degreeHistogram_measurable _ _ _ _ _
    · exact measurable_const
  · exact measurable_const

theorem selectedDegreeDensity_measurable (n : ℕ) (p : DiamondPoint) :
    Measurable (fun code : UnlabeledOrderCode n => selectedDegreeDensity code p) :=
  measurable_of_countable _

theorem selectedDegreeDensity_function_measurable (n : ℕ) :
    Measurable (@selectedDegreeDensity n) := measurable_of_countable _

theorem selectedDegreeDensity_bounds {n : ℕ} (code : UnlabeledOrderCode n) (p : DiamondPoint) :
    1 / 2 ≤ selectedDegreeDensity code p ∧ selectedDegreeDensity code p ≤ 3 / 2 := by
  classical
  unfold selectedDegreeDensity
  split
  · split
    · exact Realizer.degreeHistogram_bounds _ _ _ _ _ _
    · norm_num
  · norm_num

theorem densityEstimateGood_measurable {n : ℕ} (rho : DiamondPoint → ℝ) (E : ℝ) :
    MeasurableSet {code : UnlabeledOrderCode n |
      DensityEstimateGood rho E (selectedDegreeDensity code)} :=
  Set.to_countable _ |>.measurableSet

theorem DensityEstimateGood.mono {rho f : DiamondPoint → ℝ} {E F : ℝ}
    (h : DensityEstimateGood rho E f) (hEF : E ≤ F) : DensityEstimateGood rho F f := by
  obtain ⟨b, hb⟩ := h
  exact ⟨b, fun p hp => (hb p hp).trans hEF⟩

theorem degree_reconstruction_quotient {n : ℕ} {rho : DiamondPoint → ℝ}
    {r H w E : ℝ} {k : ℕ} {code : OrderCode n}
    (hR : CodeDegreeReconstructed rho r k H w E code)
    (hL : Nonempty (Realizer (CodeRelation code))) :
    CodeDegreeReconstructed rho r k H w E (forgetOrderLabels code).out ∧
      Nonempty (Realizer (CodeRelation (forgetOrderLabels code).out)) := by
  obtain ⟨π, hπ⟩ : OrderIsomorphic (forgetOrderLabels code).out code :=
    Quotient.exact (Quotient.out_eq (forgetOrderLabels code))
  have hInv : relabelOrder π.symm code = (forgetOrderLabels code).out := by
    calc
      _ = relabelOrder π.symm (relabelOrder π (forgetOrderLabels code).out) :=
        congrArg (relabelOrder π.symm) hπ.symm
      _ = _ := (relabelOrderEquiv π).left_inv _
  constructor
  · simpa only [hInv] using hR.relabel π.symm
  · simpa only [hInv] using code_realizer_relabel hL π.symm

theorem reconstructed_selected_degree {n : ℕ} {rho : DiamondPoint → ℝ} {E : ℝ}
    (hUse : DegreeUseHistogram n) {sample : Fin n → DiamondPoint}
    (hu : Function.Injective (fun i => (sample i).1))
    (hv : Function.Injective (fun i => (sample i).2))
    (hR : SampleDegreeReconstructed rho (1 / (degreeOuterMesh n : ℝ))
      (Nat.floor (Real.sqrt (degreeOuterMesh n : ℝ)))
      (8 * Real.sqrt (1 / (degreeOuterMesh n : ℝ)))
      ((1 - 16 * Real.sqrt (1 / (degreeOuterMesh n : ℝ))) /
        Nat.floor (Real.sqrt (degreeOuterMesh n : ℝ))) E sample) :
    DensityEstimateGood rho E (selectedDegreeDensity (forgetOrderLabels (sampledOrder sample))) := by
  classical
  have hExists : Nonempty (Realizer (CodeRelation (sampledOrder sample))) := by
    rw [sampledOrder_relation]
    exact chronological_realizer_exists hu hv
  obtain ⟨hCode, hL⟩ := degree_reconstruction_quotient (code_degree_reconstructed_sample hR) hExists
  unfold selectedDegreeDensity
  rw [if_pos hUse, dif_pos hL]
  obtain ⟨b, hb⟩ := hCode (Classical.choice hL)
  refine ⟨b, ?_⟩
  cases b with
  | false => exact hb
  | true =>
    intro p hp
    have h := hb (transposePoint p) ((transposePoint_mem_diamond p).mpr hp)
    simpa only [Realizer.aligned, Realizer.degreeHistogram_swap, transposePoint_involutive,
      if_true] using h

/-- Full fourth-root upper endpoint, on the actual law of one unlabeled order.
The single estimator is independent of rho and uses one global axis choice. -/
theorem InDensityClass.fourth_root_density_estimation {rho : DiamondPoint → ℝ}
    (hK : InDensityClass rho) {n : ℕ} (hn : 2 ≤ n) :
    (19 / 20 : ℝ) ≤ (unlabeledOrderLaw rho n).real
      {code | DensityEstimateGood rho (degreeRadius n) (selectedDegreeDensity code)} := by
  classical
  letI := hK.unlabeledOrderLaw_isProbabilityMeasure n
  by_cases hUse : DegreeUseHistogram n
  · letI := hK.orderLaw_isProbabilityMeasure n
    letI := hK.sample_isProbabilityMeasure n
    rw [unlabeledOrderLaw, map_measureReal_apply (measurable_of_countable forgetOrderLabels)
      (densityEstimateGood_measurable _ _)]
    rw [orderLaw, map_measureReal_apply (sampledOrder_measurable n)
      ((densityEstimateGood_measurable _ _).preimage (measurable_of_countable forgetOrderLabels))]
    refine (hK.logarithmic_degree_histogram_probability hn hUse.1).trans ?_
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono_ae
    filter_upwards [hK.sample_coordinates_injective n] with sample hInj
    intro hR
    exact (reconstructed_selected_degree hUse hInj.1 hInj.2 hR).mono (degree_active_radius hn hUse)
  · have hGood (code : UnlabeledOrderCode n) :
        DensityEstimateGood rho (degreeRadius n) (selectedDegreeDensity code) := by
      refine ⟨false, ?_⟩
      intro p hp
      rw [selectedDegreeDensity, if_neg hUse, degree_flat_radius hn hUse]
      have hb := hK.bounds p hp
      simp only [Bool.false_eq_true, if_false]
      exact abs_le.mpr (by constructor <;> linarith only [hb.1, hb.2])
    have hSet : {code : UnlabeledOrderCode n |
        DensityEstimateGood rho (degreeRadius n) (selectedDegreeDensity code)} = Set.univ :=
      Set.eq_univ_iff_forall.mpr hGood
    rw [hSet, probReal_univ]
    norm_num

/-- Uniform existence statement with the estimator outside the quantifier over
the unknown original-K density, and with every bound explicit. -/
theorem fourth_root_order_only_estimator {n : ℕ} (hn : 2 ≤ n) :
    ∃ estimate : UnlabeledOrderCode n → DiamondPoint → ℝ,
      Measurable estimate ∧
      (∀ code, Measurable (estimate code)) ∧
      (∀ code p, (1 / 2 : ℝ) ≤ estimate code p ∧ estimate code p ≤ 3 / 2) ∧
      ∀ rho : DiamondPoint → ℝ, InDensityClass rho →
        (19 / 20 : ℝ) ≤ (unlabeledOrderLaw rho n).real
          {code | DensityEstimateGood rho
            (min (1 / 2 : ℝ) (650 * (Real.log (n : ℝ) / n) ^ (1 / 4 : ℝ))) (estimate code)} := by
  exact ⟨selectedDegreeDensity, selectedDegreeDensity_function_measurable n,
    selectedDegreeDensity_query_measurable, selectedDegreeDensity_bounds,
    fun _ hK => hK.fourth_root_density_estimation hn⟩

#print axioms selectedDegreeDensity_query_measurable
#print axioms selectedDegreeDensity_measurable
#print axioms selectedDegreeDensity_function_measurable
#print axioms selectedDegreeDensity_bounds
#print axioms densityEstimateGood_measurable
#print axioms DensityEstimateGood.mono
#print axioms degree_reconstruction_quotient
#print axioms reconstructed_selected_degree
#print axioms InDensityClass.fourth_root_density_estimation
#print axioms fourth_root_order_only_estimator

end QuantyraNullCone
