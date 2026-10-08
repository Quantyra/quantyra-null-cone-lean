import QuantyraNullCone.DKWUniform
import QuantyraNullCone.Coordinates

namespace QuantyraNullCone

open MeasureTheory

def coordinateSample {n : ℕ} (f : DiamondPoint → ℝ) (s : Fin n → DiamondPoint) : Fin n → ℝ :=
  fun i => f (s i)

theorem coordinate_sample_measurable {n : ℕ} {f : DiamondPoint → ℝ} (hf : Measurable f) :
    Measurable (coordinateSample (n := n) f) :=
  measurable_pi_lambda _ (fun i => hf.comp (measurable_pi_apply i))

theorem InDensityClass.coordinate_sample_uniform {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) {f : DiamondPoint → ℝ} (hf : Measurable f)
    (hLaw : (densityMeasure rho).map f = unitUniform) (n : ℕ) :
    (sampleMeasure rho n).map (coordinateSample f) = uniformSampleMeasure n := by
  letI : IsProbabilityMeasure (densityMeasure rho) := h.isProbabilityMeasure
  letI : IsProbabilityMeasure ((densityMeasure rho).map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  have hOpen : unitUniform = uniform01Measure := uniform01_closed_interval.symm
  unfold sampleMeasure coordinateSample
  rw [Measure.pi_map_pi (fun _ => hf.aemeasurable)]
  simp_rw [hLaw, hOpen]
  rfl

theorem InDensityClass.coordinate_DKW {rho : DiamondPoint → ℝ} (h : InDensityClass rho)
    {n : ℕ} {e : ℝ} (hn : 0 < n) (he : 0 ≤ e) {f : DiamondPoint → ℝ}
    (hf : Measurable f) (hLaw : (densityMeasure rho).map f = unitUniform) :
    (sampleMeasure rho n).real ((coordinateSample (n := n) f) ⁻¹' uniformBad n e) ≤
      2 * Real.exp (-2 * (n : ℝ) * e ^ 2) := by
  calc
    (sampleMeasure rho n).real ((coordinateSample f) ⁻¹' uniformBad n e) =
        ((sampleMeasure rho n).map (coordinateSample f)).real (uniformBad n e) :=
      congrArg ENNReal.toReal (Measure.map_apply (coordinate_sample_measurable hf)
        (uniform_bad_measurable hn e)).symm
    _ = (uniformSampleMeasure n).real (uniformBad n e) := by
      rw [h.coordinate_sample_uniform hf hLaw n]
    _ ≤ 2 * Real.exp (-2 * (n : ℝ) * e ^ 2) := uniform_DKW hn he

theorem InDensityClass.fst_DKW {rho : DiamondPoint → ℝ} (h : InDensityClass rho)
    {n : ℕ} {e : ℝ} (hn : 0 < n) (he : 0 ≤ e) :
    (sampleMeasure rho n).real ((coordinateSample (n := n) Prod.fst) ⁻¹' uniformBad n e) ≤
      2 * Real.exp (-2 * (n : ℝ) * e ^ 2) :=
  h.coordinate_DKW hn he measurable_fst h.fst_map_uniform

theorem InDensityClass.snd_DKW {rho : DiamondPoint → ℝ} (h : InDensityClass rho)
    {n : ℕ} {e : ℝ} (hn : 0 < n) (he : 0 ≤ e) :
    (sampleMeasure rho n).real ((coordinateSample (n := n) Prod.snd) ⁻¹' uniformBad n e) ≤
      2 * Real.exp (-2 * (n : ℝ) * e ^ 2) :=
  h.coordinate_DKW hn he measurable_snd h.snd_map_uniform

def sampleMarginalBad (n : ℕ) (e : ℝ) : Set (Fin n → DiamondPoint) :=
  ((coordinateSample Prod.fst) ⁻¹' uniformBad n e) ∪
    ((coordinateSample Prod.snd) ⁻¹' uniformBad n e)

theorem sample_marginal_bad_measurable {n : ℕ} (hn : 0 < n) (e : ℝ) :
    MeasurableSet (sampleMarginalBad n e) :=
  ((uniform_bad_measurable hn e).preimage (coordinate_sample_measurable measurable_fst)).union
    ((uniform_bad_measurable hn e).preimage (coordinate_sample_measurable measurable_snd))

/-- Both marginal tails for original K; within-point coordinate dependence is allowed. -/
theorem InDensityClass.split_marginal_failure {rho : DiamondPoint → ℝ} (h : InDensityClass rho)
    {n : ℕ} {e : ℝ} (hn : 0 < n) (he : 0 ≤ e) :
    (sampleMeasure rho n).real (sampleMarginalBad n e) ≤
      4 * Real.exp (-2 * (n : ℝ) * e ^ 2) := by
  letI : IsProbabilityMeasure (sampleMeasure rho n) := h.sample_isProbabilityMeasure n
  have hUnion := measureReal_union_le (μ := sampleMeasure rho n)
    ((coordinateSample (n := n) Prod.fst) ⁻¹' uniformBad n e)
    ((coordinateSample (n := n) Prod.snd) ⁻¹' uniformBad n e)
  exact hUnion.trans (by linarith only [h.fst_DKW hn he, h.snd_DKW hn he])

#print axioms InDensityClass.coordinate_sample_uniform
#print axioms InDensityClass.fst_DKW
#print axioms InDensityClass.snd_DKW
#print axioms InDensityClass.split_marginal_failure

end QuantyraNullCone
