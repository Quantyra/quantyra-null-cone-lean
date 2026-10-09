import QuantyraNullCone.LogLowerPacking

namespace QuantyraNullCone

open MeasureTheory

theorem disjoint_indicator_sum_square {X I : Type*} [Fintype I]
    (A : I → Set X) (L : I → X → ℝ)
    (hd : Pairwise (fun i j => Disjoint (A i) (A j))) (x : X) :
    (∑ i, (A i).indicator (L i) x)^2 =
      ∑ i, (A i).indicator (fun y => L i y^2) x := by
  classical
  by_cases hx : ∃ i, x ∈ A i
  · obtain ⟨i,hi⟩ := hx
    have hOther (j : I) (hji : j ≠ i) : x ∉ A j := by
      intro hj
      exact Set.disjoint_left.mp (hd hji) hj hi
    have hSum (f : I → X → ℝ) : (∑ j, (A j).indicator (f j) x) = f i x := by
      rw [Finset.sum_eq_single i]
      · exact Set.indicator_of_mem hi _
      · intro j _ hji
        exact Set.indicator_of_notMem (hOther j hji) _
      · simp
    rw [hSum L,hSum (fun i y => L i y^2)]
  · have hNone (i : I) : x ∉ A i := fun hi => hx ⟨i,hi⟩
    simp only [Set.indicator_of_notMem (hNone _),Finset.sum_const_zero,zero_pow (by decide : 2 ≠ 0)]

theorem many_event_likelihood_sum_le {X I : Type*} [MeasurableSpace X] [Fintype I]
    (Q : Measure X) [IsProbabilityMeasure Q] (L : I → X → ℝ)
    (hL : ∀ i, Integrable (L i) Q) (hL2 : ∀ i, Integrable (fun x => L i x^2) Q)
    (A : I → Set X) (hA : ∀ i, MeasurableSet (A i))
    (hd : Pairwise (fun i j => Disjoint (A i) (A j)))
    {B : ℝ} (hB : ∀ i, (∫ x, L i x^2 ∂Q) ≤ B) :
    (∑ i, ∫ x in A i, L i x ∂Q) ≤ Real.sqrt ((Fintype.card I:ℝ)*B) := by
  classical
  let F := fun x => ∑ i, (A i).indicator (L i) x
  have hF : Integrable F Q := integrable_finsetSum _ (fun i _ => (hL i).indicator (hA i))
  have hEq : (fun x => F x^2) = (fun x => ∑ i, (A i).indicator (fun y => L i y^2) x) := by
    funext x
    exact disjoint_indicator_sum_square A L hd x
  have hF2 : Integrable (fun x => F x^2) Q := by
    rw [hEq]
    exact integrable_finsetSum _ (fun i _ => (hL2 i).indicator (hA i))
  have hIntegral : (∫ x, F x ∂Q) = ∑ i, ∫ x in A i, L i x ∂Q := by
    rw [show F = (fun x => ∑ i, (A i).indicator (L i) x) from rfl,
      integral_finsetSum _ (fun i _ => (hL i).indicator (hA i))]
    exact Finset.sum_congr rfl (fun i _ => integral_indicator (hA i))
  have hMoment : (∫ x, F x^2 ∂Q) ≤ (Fintype.card I:ℝ)*B := by
    rw [hEq,integral_finsetSum _ (fun i _ => (hL2 i).indicator (hA i))]
    calc
      _ ≤ ∑ i : I, B := Finset.sum_le_sum (fun i _ => by
        rw [integral_indicator (hA i)]
        exact (setIntegral_le_integral (hL2 i)
          (Filter.Eventually.of_forall (fun _ => sq_nonneg _))).trans (hB i))
      _ = _ := by simp
  rw [← hIntegral]
  exact (integral_mono hF hF.abs (fun x => le_abs_self (F x))).trans
    ((integral_abs_le_sqrt_second hF hF2).trans (Real.sqrt_le_sqrt hMoment))

theorem many_event_failure_exists {X : Type*} [MeasurableSpace X] {m : ℕ} (hm : 1 ≤ m)
    (Q : Measure X) [IsProbabilityMeasure Q] (P : Fin m → Measure X)
    (hP : ∀ i, IsProbabilityMeasure (P i)) (L : Fin m → X → ℝ)
    (hL : ∀ i, Integrable (L i) Q) (hL2 : ∀ i, Integrable (fun x => L i x^2) Q)
    (A : Fin m → Set X) (hA : ∀ i, MeasurableSet (A i))
    (hd : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hApply : ∀ i, (P i).real (A i) = ∫ x in A i, L i x ∂Q)
    {B : ℝ} (hB : ∀ i, (∫ x, L i x^2 ∂Q) ≤ B) (hSmall : B ≤ (m:ℝ)/4) :
    ∃ i, (1/2:ℝ) ≤ (P i).real (A i)ᶜ := by
  classical
  have hSum := many_event_likelihood_sum_le Q L hL hL2 A hA hd hB
  simp only [Fintype.card_fin] at hSum
  have hSqrt : Real.sqrt ((m:ℝ)*B) ≤ (m:ℝ)/2 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have h := mul_le_mul_of_nonneg_left hSmall (Nat.cast_nonneg m : (0:ℝ) ≤ m)
    nlinarith only [h]
  have hSum' : (∑ i : Fin m, (P i).real (A i)) ≤ (m:ℝ)/2 := by
    simpa only [hApply] using hSum.trans hSqrt
  by_contra hNone
  push Not at hNone
  have hSuccess (i : Fin m) : (1/2:ℝ) < (P i).real (A i) := by
    letI := hP i
    have hTotal := probReal_add_probReal_compl (μ := P i) (hA i)
    linarith [hNone i]
  let i0 : Fin m := ⟨0,by omega⟩
  have hStrict := Finset.sum_lt_sum
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) => (hSuccess i).le)
    ⟨i0,Finset.mem_univ i0,hSuccess i0⟩
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hStrict
  linarith

#print axioms disjoint_indicator_sum_square
#print axioms many_event_likelihood_sum_le
#print axioms many_event_failure_exists

end QuantyraNullCone
