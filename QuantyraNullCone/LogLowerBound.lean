import QuantyraNullCone.LogLowerScale

namespace QuantyraNullCone

open MeasureTheory

/-- Full original-class lower bound for any radius up to the logarithmic target.
The only estimator assumption is measurability of its simultaneous success events. -/
theorem logarithmic_lower_bound_at_radius {n : ℕ} (hn : 2^64 ≤ n) {r : ℝ}
    (hr : r ≤ logMinimaxRate n/8192) {Ω : Type*} [MeasurableSpace Ω]
    (ξ : Measure Ω) [IsProbabilityMeasure ξ]
    (estimate : UnlabeledOrderCode n → Ω → DiamondPoint → ℝ)
    (hMeas : ∀ rho, InDensityClass rho → MeasurableSet (LowerEstimateSuccess rho r estimate)) :
    ∃ rho, InDensityClass rho ∧ (1/2:ℝ) ≤
      (((unlabeledOrderLaw rho n).prod ξ).real (LowerEstimateSuccess rho r estimate)ᶜ) := by
  classical
  let m := logLowerMesh n
  have hm : 1 ≤ m := by have h := (log_lower_mesh_bounds hn).1; dsimp [m]; omega
  let h := logLowerBandwidth m
  obtain ⟨hh,hSmall⟩ := log_lower_bandwidth_bounds hm
  have hRadius : r ≤ h/256 := hr.trans (log_lower_target_radius hn)
  let T : (Fin n → DiamondPoint) → UnlabeledOrderCode n := forgetOrderLabels ∘ sampledOrder
  have hT : Measurable T := (measurable_of_countable forgetOrderLabels).comp (sampledOrder_measurable n)
  let U : ((Fin n → DiamondPoint) × Ω) → UnlabeledOrderCode n × Ω := Prod.map T id
  have hU : Measurable U := hT.prodMap measurable_id
  let A := fun j : Fin m => U ⁻¹' LowerEstimateSuccess (logLowerFamily m j) r estimate
  have hA (j : Fin m) : MeasurableSet (A j) :=
    (hMeas _ (log_lower_family_in_class hm j)).preimage hU
  have hDisjoint : Pairwise (fun j k : Fin m => Disjoint (A j) (A k)) := by
    intro j k hjk
    rw [Set.disjoint_left]
    intro z hj hk
    exact log_lower_success_disjoint hm j k hjk hRadius (estimate (U z).1 (U z).2) ⟨hj,hk⟩
  let P := fun j : Fin m => (sampleMeasure (logLowerFamily m j) n).prod ξ
  have hP (j : Fin m) : IsProbabilityMeasure (P j) := by
    letI := (log_lower_family_in_class hm j).sample_isProbabilityMeasure n
    infer_instance
  let L := fun (j : Fin m) (z : (Fin n → DiamondPoint) × Ω) =>
    logLowerLikelihood h (logLowerCenter m j) z.1
  have hInt (j : Fin m) : Integrable (L j) ((lowerBaseSample n).prod ξ) :=
    (log_lower_likelihood_integrable hh hSmall (logLowerCenter m j) n).comp_fst ξ
  have hInt2 (j : Fin m) : Integrable (fun z => L j z^2) ((lowerBaseSample n).prod ξ) :=
    (log_lower_likelihood_square_integrable h (logLowerCenter m j) n).comp_fst ξ
  obtain ⟨j,hFailure⟩ := many_event_failure_exists hm ((lowerBaseSample n).prod ξ) P hP L hInt hInt2 A hA
    hDisjoint (fun j => log_lower_seed_real_apply hh hSmall (logLowerCenter m j) n ξ (hA j))
    (fun j => log_lower_seed_second_moment hh hSmall (logLowerCenter m j) n ξ)
    (log_lower_mesh_budget hn)
  let rho := logLowerFamily m j
  have hK := log_lower_family_in_class hm j
  letI := hK.sample_isProbabilityMeasure n
  have hLaw : unlabeledOrderLaw rho n = (sampleMeasure rho n).map T := by
    rw [unlabeledOrderLaw,orderLaw,Measure.map_map (measurable_of_countable forgetOrderLabels)
      (sampledOrder_measurable n)]
  have hProd : (unlabeledOrderLaw rho n).prod ξ = ((sampleMeasure rho n).prod ξ).map U := by
    rw [hLaw]
    simpa only [Measure.map_id] using Measure.map_prod_map (sampleMeasure rho n) ξ hT measurable_id
  refine ⟨rho,hK,?_⟩
  rw [hProd,map_measureReal_apply hU (hMeas rho hK).compl]
  exact hFailure

/-- The explicit logarithmic strict-error obstruction includes independent
randomization and requires no class membership of estimator outputs. -/
theorem logarithmic_randomized_minimax_obstruction {n : ℕ} (hn : 2^64 ≤ n)
    {Ω : Type*} [MeasurableSpace Ω] (ξ : Measure Ω) [IsProbabilityMeasure ξ]
    (estimate : UnlabeledOrderCode n → Ω → DiamondPoint → ℝ)
    (hMeas : ∀ rho, InDensityClass rho →
      MeasurableSet (LowerEstimateSuccess rho (logMinimaxRate n/8192) estimate)) :
    ∃ rho, InDensityClass rho ∧ (1/2:ℝ) ≤
      (((unlabeledOrderLaw rho n).prod ξ).real
        (LowerEstimateSuccess rho (logMinimaxRate n/8192) estimate)ᶜ) :=
  logarithmic_lower_bound_at_radius hn le_rfl ξ estimate hMeas

def UniformOrderConfidenceRadius {Ω : Type*} [MeasurableSpace Ω]
    (ξ : Measure Ω) (n : ℕ) (r : ℝ) : Prop :=
  ∃ estimate : UnlabeledOrderCode n → Ω → DiamondPoint → ℝ,
    (∀ rho, InDensityClass rho → MeasurableSet (LowerEstimateSuccess rho r estimate)) ∧
    ∀ rho, InDensityClass rho → (19/20:ℝ) ≤
      ((unlabeledOrderLaw rho n).prod ξ).real (LowerEstimateSuccess rho r estimate)

noncomputable def orderConfidenceRadius95 {Ω : Type*} [MeasurableSpace Ω]
    (ξ : Measure Ω) (n : ℕ) : ℝ :=
  sInf {r : ℝ | 0 ≤ r ∧ UniformOrderConfidenceRadius ξ n r}

theorem logarithmic_uniform_radius_necessary {n : ℕ} (hn : 2^64 ≤ n)
    {Ω : Type*} [MeasurableSpace Ω] (ξ : Measure Ω) [IsProbabilityMeasure ξ]
    {r : ℝ} (hRadius : UniformOrderConfidenceRadius ξ n r) : logMinimaxRate n/8192 < r := by
  obtain ⟨estimate,hMeas,hCoverage⟩ := hRadius
  by_contra hNot
  obtain ⟨rho,hK,hFailure⟩ := logarithmic_lower_bound_at_radius hn (le_of_not_gt hNot) ξ estimate hMeas
  letI := hK.unlabeledOrderLaw_isProbabilityMeasure n
  have hTotal := probReal_add_probReal_compl (μ := (unlabeledOrderLaw rho n).prod ξ) (hMeas rho hK)
  linarith [hCoverage rho hK]

theorem fourth_root_uniform_radius_achievable {n : ℕ} (hn : 2 ≤ n)
    {Ω : Type*} [MeasurableSpace Ω] (ξ : Measure Ω) [IsProbabilityMeasure ξ] :
    UniformOrderConfidenceRadius ξ n (min (1/2:ℝ) (650*logMinimaxRate n)) := by
  classical
  obtain ⟨estimate,_,_,_,hCoverage⟩ := fourth_root_order_only_estimator hn
  let r := min (1/2:ℝ) (650*logMinimaxRate n)
  let A := fun rho => {code | DensityEstimateGood rho r (estimate code)}
  have hEq (rho : DiamondPoint → ℝ) :
      LowerEstimateSuccess rho r (fun code (_ : Ω) => estimate code) = A rho ×ˢ Set.univ := by
    ext z
    simp only [LowerEstimateSuccess,A,Set.mem_setOf_eq,Set.mem_prod,Set.mem_univ,and_true]
  refine ⟨fun code _ => estimate code,?_,?_⟩
  · intro rho _
    rw [hEq]
    exact (Set.to_countable _).measurableSet.prod MeasurableSet.univ
  · intro rho hK
    rw [hEq,measureReal_prod_prod,probReal_univ,mul_one]
    exact hCoverage rho hK

/-- Fixed-confidence minimax rate, with explicit constants and sample threshold.
The bound holds for every independent seed space, including deterministic seeds. -/
theorem logarithmic_minimax_radius_bounds {n : ℕ} (hn : 2^64 ≤ n)
    {Ω : Type*} [MeasurableSpace Ω] (ξ : Measure Ω) [IsProbabilityMeasure ξ] :
    logMinimaxRate n/8192 ≤ orderConfidenceRadius95 ξ n ∧
      orderConfidenceRadius95 ξ n ≤ min (1/2:ℝ) (650*logMinimaxRate n) := by
  have hn2 : 2 ≤ n := by omega
  let R := min (1/2:ℝ) (650*logMinimaxRate n)
  have hR0 : 0 ≤ R := by dsimp [R,logMinimaxRate]; positivity
  have hUpper : R ∈ {r : ℝ | 0 ≤ r ∧ UniformOrderConfidenceRadius ξ n r} :=
    ⟨hR0,fourth_root_uniform_radius_achievable hn2 ξ⟩
  have hNonempty : Set.Nonempty {r : ℝ | 0 ≤ r ∧ UniformOrderConfidenceRadius ξ n r} := ⟨R,hUpper⟩
  have hBdd : BddBelow {r : ℝ | 0 ≤ r ∧ UniformOrderConfidenceRadius ξ n r} := ⟨0,fun _ hr => hr.1⟩
  constructor
  · exact le_csInf hNonempty (fun r hr => (logarithmic_uniform_radius_necessary hn ξ hr.2).le)
  · exact csInf_le hBdd hUpper

#print axioms logarithmic_lower_bound_at_radius
#print axioms logarithmic_randomized_minimax_obstruction
#print axioms logarithmic_uniform_radius_necessary
#print axioms fourth_root_uniform_radius_achievable
#print axioms logarithmic_minimax_radius_bounds

end QuantyraNullCone
