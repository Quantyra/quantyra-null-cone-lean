import QuantyraNullCone.LowerProduct

namespace QuantyraNullCone

open MeasureTheory

/-- Finite measurable observation cannot increase the likelihood L1 distance.
The domain may be continuous; no coordinate ranking information is assumed. -/
theorem finite_observation_L1_bound {X β : Type*} [MeasurableSpace X]
    [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {w : X → ℝ} (hw : Integrable w μ)
    (hν : ∀ S, MeasurableSet S → ν.real S = ∫ x in S, w x ∂μ)
    {T : X → β} (hT : Measurable T) :
    (∑ b, |(μ.map T).real {b} - (ν.map T).real {b}|) ≤ ∫ x, |w x - 1| ∂μ := by
  classical
  let fibers := fun b : β => T ⁻¹' {b}
  have hm (b : β) : MeasurableSet (fibers b) := hT (measurableSet_singleton b)
  have hi : Integrable (fun x => w x - 1) μ := hw.sub (integrable_const 1)
  have hFiber (b : β) : |(μ.map T).real {b} - (ν.map T).real {b}| ≤
      ∫ x in fibers b, |w x - 1| ∂μ := by
    rw [map_measureReal_apply hT (measurableSet_singleton b),
      map_measureReal_apply hT (measurableSet_singleton b), hν _ (hm b), abs_sub_comm]
    have hEq : (∫ x in fibers b, w x - 1 ∂μ) =
        (∫ x in fibers b, w x ∂μ) - μ.real (fibers b) := by
      rw [integral_sub hw.restrict (integrable_const 1)]
      simp
    rw [← hEq]
    exact abs_integral_le_integral_abs
  have hd : Pairwise (fun b c => Disjoint (fibers b) (fibers c)) := by
    intro b c hbc
    rw [Set.disjoint_left]
    intro x hb hc
    exact hbc (hb.symm.trans hc)
  have hu : (⋃ b, fibers b) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, fibers, Set.mem_preimage, Set.mem_singleton_iff,
      Set.mem_univ, iff_true]
    exact ⟨T x, rfl⟩
  have hSum := integral_iUnion_fintype hm hd (fun _ => hi.abs.restrict)
  rw [hu, setIntegral_univ] at hSum
  exact (Finset.sum_le_sum (fun b _ => hFiber b)).trans_eq hSum.symm

theorem integral_abs_le_sqrt_second {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ] {f : X → ℝ} (hf : Integrable f μ)
    (hf2 : Integrable (fun x => f x ^ 2) μ) :
    (∫ x, |f x| ∂μ) ≤ Real.sqrt (∫ x, f x ^ 2 ∂μ) := by
  let a := ∫ x, |f x| ∂μ
  have hPoint (x : X) : 2 * a * |f x| - a ^ 2 ≤ f x ^ 2 := by
    nlinarith only [sq_nonneg (|f x| - a), sq_abs (f x)]
  have hInt := integral_mono ((hf.abs.const_mul (2 * a)).sub (integrable_const (a ^ 2))) hf2 hPoint
  change (∫ x, 2 * a * |f x| - a ^ 2 ∂μ) ≤ (∫ x, f x ^ 2 ∂μ) at hInt
  rw [integral_sub (hf.abs.const_mul (2 * a)) (integrable_const (a ^ 2)),
    integral_const_mul, integral_const, probReal_univ, one_smul] at hInt
  have hSq : a ^ 2 ≤ ∫ x, f x ^ 2 ∂μ := by nlinarith only [hInt]
  exact Real.le_sqrt_of_sq_le hSq

theorem lower_sample_real_apply {h : ℝ} (hh : 0 < h) (hSmall : h ≤ 1 / 2) (n : ℕ)
    {S : Set (Fin n → DiamondPoint)} (hS : MeasurableSet S) :
    (sampleMeasure (lowerAlternative h) n).real S = ∫ x in S, lowerLikelihood h x ∂lowerBaseSample n := by
  rw [measureReal_def, lower_sample_withDensity hh hSmall n, withDensity_apply _ hS,
    ← ofReal_integral_eq_lintegral_ofReal (lower_likelihood_integrable hh hSmall n).restrict
      (Filter.Eventually.of_forall (lower_likelihood_nonneg hh hSmall)), ENNReal.toReal_ofReal]
  exact integral_nonneg (lower_likelihood_nonneg hh hSmall)

theorem lower_order_TV_bound {h : ℝ} (hh : 0 < h) (hSmall : h ≤ 1 / 2) (n : ℕ) :
    unlabeledOrderLawTV lowerFlat (lowerAlternative h) n ≤ lowerTVBound n h := by
  let T : (Fin n → DiamondPoint) → UnlabeledOrderCode n := forgetOrderLabels ∘ sampledOrder
  have hT : Measurable T := (measurable_of_countable forgetOrderLabels).comp (sampledOrder_measurable n)
  letI := (lower_alternative_in_class hh hSmall).sample_isProbabilityMeasure n
  have hLaw (rho : DiamondPoint → ℝ) : unlabeledOrderLaw rho n = (sampleMeasure rho n).map T := by
    rw [unlabeledOrderLaw, orderLaw, Measure.map_map (measurable_of_countable forgetOrderLabels)
      (sampledOrder_measurable n)]
  have hL1 := finite_observation_L1_bound (lowerBaseSample n) (sampleMeasure (lowerAlternative h) n)
    (lower_likelihood_integrable hh hSmall n) (fun S hS => lower_sample_real_apply hh hSmall n hS) hT
  have hi := (lower_likelihood_integrable hh hSmall n).sub (integrable_const 1)
  have hSq : Integrable (fun x => (lowerLikelihood h x - 1) ^ 2) (lowerBaseSample n) := by
    have hEq : (fun x : Fin n → DiamondPoint => (lowerLikelihood h x - 1) ^ 2) =
        (fun x => (lowerLikelihood h x ^ 2 - 2 * lowerLikelihood h x) + 1) := by funext x; ring
    rw [hEq]
    exact ((lower_likelihood_square_integrable h n).sub
      ((lower_likelihood_integrable hh hSmall n).const_mul 2)).add (integrable_const 1)
  have hCS := integral_abs_le_sqrt_second hi hSq
  have hDiv := Real.sqrt_le_sqrt (lower_product_divergence_bound hh hSmall n)
  unfold unlabeledOrderLawTV lowerTVBound
  rw [hLaw lowerFlat, hLaw (lowerAlternative h), lower_flat_sample]
  exact mul_le_mul_of_nonneg_left (hL1.trans (hCS.trans hDiv)) (by norm_num)

#print axioms finite_observation_L1_bound
#print axioms integral_abs_le_sqrt_second
#print axioms lower_sample_real_apply
#print axioms lower_order_TV_bound

end QuantyraNullCone
