import QuantyraNullCone.Exchangeability

namespace QuantyraNullCone

open MeasureTheory

theorem abs_sum_of_constant {α : Type*} (s : Finset α) (g : α → ℝ)
    (hConst : ∀ x ∈ s, ∀ y ∈ s, g x = g y) :
    |∑ x ∈ s, g x| = ∑ x ∈ s, |g x| := by
  classical
  by_cases hEmpty : s = ∅
  · simp [hEmpty]
  obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
  have hSum : (∑ x ∈ s, g x) = (s.card : ℝ) * g a := by
    calc
      _ = ∑ x ∈ s, g a := Finset.sum_congr rfl (fun x hx => hConst x hx a ha)
      _ = _ := by simp [nsmul_eq_mul]
  have hAbs : (∑ x ∈ s, |g x|) = (s.card : ℝ) * |g a| := by
    calc
      _ = ∑ x ∈ s, |g a| := Finset.sum_congr rfl (fun x hx => congrArg abs (hConst x hx a ha))
      _ = _ := by simp [nsmul_eq_mul]
  rw [hSum, hAbs, abs_mul, abs_of_nonneg (Nat.cast_nonneg s.card)]

theorem finite_map_real_singleton {α β : Type*} [Fintype α] [DecidableEq β] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → β) (b : β) :
    (μ.map f).real {b} = ∑ x ∈ Finset.univ.filter (fun x => f x = b), μ.real {x} := by
  classical
  let s := Finset.univ.filter (fun x => f x = b)
  have hSet : (s : Set α) = f ⁻¹' {b} := by ext x; simp [s]
  rw [map_measureReal_apply (measurable_of_countable _) (measurableSet_singleton _),
    ← hSet, ← sum_measureReal_singleton s]

/-- Half-L1 is preserved when both finite laws are constant on each quotient fiber. -/
theorem finite_map_L1_of_fiber_constant {α β : Type*} [Fintype α] [Fintype β]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (f : α → β)
    (hμ : ∀ x y, f x = f y → μ.real {x} = μ.real {y})
    (hν : ∀ x y, f x = f y → ν.real {x} = ν.real {y}) :
    (∑ b : β, |(μ.map f).real {b} - (ν.map f).real {b}|) =
      ∑ x : α, |μ.real {x} - ν.real {x}| := by
  classical
  have hFiber (b : β) : |(μ.map f).real {b} - (ν.map f).real {b}| =
      ∑ x ∈ Finset.univ.filter (fun x => f x = b), |μ.real {x} - ν.real {x}| := by
    rw [finite_map_real_singleton, finite_map_real_singleton, ← Finset.sum_sub_distrib]
    apply abs_sum_of_constant
    intro x hx y hy
    have hxy : f x = f y := (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
    rw [hμ x y hxy, hν x y hxy]
  simp_rw [hFiber]
  exact Finset.sum_fiberwise Finset.univ f (fun x => |μ.real {x} - ν.real {x}|)

#print axioms abs_sum_of_constant
#print axioms finite_map_L1_of_fiber_constant

end QuantyraNullCone
