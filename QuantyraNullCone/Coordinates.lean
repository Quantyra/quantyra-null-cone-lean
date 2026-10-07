import QuantyraNullCone.Sampling
import Mathlib.Probability.Independence.Basic

namespace QuantyraNullCone

open MeasureTheory ProbabilityTheory

noncomputable def unitUniform : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

theorem InDensityClass.fst_map_uniform {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) : (densityMeasure rho).map Prod.fst = unitUniform := by
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply measurable_fst hS, h.uMarginal_mass hS,
    unitUniform, Measure.restrict_apply hS]

theorem InDensityClass.snd_map_uniform {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) : (densityMeasure rho).map Prod.snd = unitUniform := by
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply measurable_snd hS, h.vMarginal_mass hS,
    unitUniform, Measure.restrict_apply hS]

theorem unitUniform_diagonal_zero : unitUniform.prod unitUniform (Set.diagonal ℝ) = 0 := by
  letI : NoAtoms unitUniform := by unfold unitUniform; infer_instance
  letI : IsProbabilityMeasure unitUniform := ⟨by simp [unitUniform]⟩
  rw [Measure.prod_apply measurableSet_diagonal]
  have hSection (x : ℝ) : Prod.mk x ⁻¹' Set.diagonal ℝ = {x} := by
    ext y
    simp [Set.diagonal, eq_comm]
  simp only [hSection, measure_singleton, lintegral_zero]

theorem InDensityClass.sample_coordinate_ne {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {f : DiamondPoint → ℝ} (hf : Measurable f)
    (hLaw : (densityMeasure rho).map f = unitUniform) :
    ∀ᵐ sample ∂sampleMeasure rho n, f (sample i) ≠ f (sample j) := by
  letI : IsProbabilityMeasure (densityMeasure rho) := h.isProbabilityMeasure
  letI : IsProbabilityMeasure (sampleMeasure rho n) := h.sample_isProbabilityMeasure n
  have hIndep : iIndepFun (fun k : Fin n => fun sample : Fin n → DiamondPoint => f (sample k))
      (sampleMeasure rho n) := iIndepFun_pi (fun _ => hf.aemeasurable)
  have hMap (k : Fin n) :
      (sampleMeasure rho n).map (fun sample => f (sample k)) = unitUniform := by
    have hEval : (sampleMeasure rho n).map (Function.eval k) = densityMeasure rho :=
      (measurePreserving_eval (fun _ : Fin n => densityMeasure rho) k).map_eq
    rw [show (fun sample : Fin n → DiamondPoint => f (sample k)) =
      f ∘ Function.eval k from rfl, ← Measure.map_map hf (measurable_pi_apply k),
      hEval, hLaw]
  have hJoint : (sampleMeasure rho n).map (fun sample => (f (sample i), f (sample j))) =
      unitUniform.prod unitUniform := by
    have hJointRaw := (indepFun_iff_map_prod_eq_prod_map_map
      (hf.comp (measurable_pi_apply i)).aemeasurable
      (hf.comp (measurable_pi_apply j)).aemeasurable).mp (hIndep.indepFun hij)
    simp only [Function.comp_def] at hJointRaw
    rw [hMap i, hMap j] at hJointRaw
    exact hJointRaw
  have hZero : sampleMeasure rho n {sample | f (sample i) = f (sample j)} = 0 := by
    have hMapDiag := Measure.map_apply (μ := sampleMeasure rho n)
      ((hf.comp (measurable_pi_apply i)).prodMk (hf.comp (measurable_pi_apply j)))
      measurableSet_diagonal
    simp only [Function.comp_def] at hMapDiag
    rw [hJoint, unitUniform_diagonal_zero] at hMapDiag
    exact hMapDiag.symm
  apply ae_iff.mpr
  simpa only [not_not] using hZero

theorem InDensityClass.sample_coordinates_injective {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) (n : ℕ) :
    ∀ᵐ sample ∂sampleMeasure rho n,
      Function.Injective (fun i => (sample i).1) ∧
        Function.Injective (fun i => (sample i).2) := by
  have hGeneric (f : DiamondPoint → ℝ) (hf : Measurable f)
      (hLaw : (densityMeasure rho).map f = unitUniform) :
      ∀ᵐ sample ∂sampleMeasure rho n, Function.Injective (fun i => f (sample i)) := by
    have hPairs : ∀ᵐ sample ∂sampleMeasure rho n,
        ∀ i j : Fin n, i ≠ j → f (sample i) ≠ f (sample j) := by
      apply Filter.eventually_all.mpr
      intro i
      apply Filter.eventually_all.mpr
      intro j
      by_cases hij : i = j
      · exact ae_of_all _ fun _ hNe => False.elim (hNe hij)
      · exact (h.sample_coordinate_ne hij hf hLaw).mono fun _ hp _ => hp
    exact hPairs.mono fun _ hs i j hEq => by
      by_contra hij
      exact hs i j hij hEq
  exact (hGeneric Prod.fst measurable_fst h.fst_map_uniform).and
    (hGeneric Prod.snd measurable_snd h.snd_map_uniform)

#print axioms InDensityClass.fst_map_uniform
#print axioms InDensityClass.snd_map_uniform
#print axioms InDensityClass.sample_coordinates_injective

end QuantyraNullCone
