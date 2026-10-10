import QuantyraNullCone.TimeZeroCoupling
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-! Weak limits preserve the coupling marginals and eliminate discrepancy events
when their probability thresholds tend to zero. -/

namespace QuantyraNullCone
open MeasureTheory Set Filter Topology
noncomputable section

variable {X Y : Type*}

theorem isOpen_timeBadPairs [TopologicalSpace X] [TopologicalSpace Y]
    {tx : X → X → ℝ} {ty : Y → Y → ℝ}
    (hx : Continuous (Function.uncurry tx)) (hy : Continuous (Function.uncurry ty)) (eps : ℝ) :
    IsOpen (timeBadPairs tx ty eps) := by
  apply isOpen_lt continuous_const
  simpa only [Real.norm_eq_abs] using ((hx.comp ((continuous_fst.comp continuous_fst).prodMk
      (continuous_fst.comp continuous_snd))).sub
    (hy.comp ((continuous_snd.comp continuous_fst).prodMk
      (continuous_snd.comp continuous_snd)))).norm

variable [MetricSpace X] [MetricSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
  [BorelSpace X] [BorelSpace Y] [SecondCountableTopology X] [SecondCountableTopology Y]

omit [SecondCountableTopology X] in
theorem isTimeCoupling_of_tendsto {mu : Measure X} {nu : Measure Y}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {ps : ℕ → ProbabilityMeasure (X × Y)} {p : ProbabilityMeasure (X × Y)}
    (hp : Tendsto ps atTop (𝓝 p)) (hs : ∀ n, IsTimeCoupling mu nu (ps n).toMeasure) :
    IsTimeCoupling mu nu p.toMeasure := by
  let m : ProbabilityMeasure X := ⟨mu, inferInstance⟩
  let n : ProbabilityMeasure Y := ⟨nu, inferInstance⟩
  constructor
  · have h := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous ps p hp continuous_fst
    have he : (fun i => (ps i).map continuous_fst.measurable.aemeasurable) = fun _ => m := by
      funext i
      exact Subtype.ext (hs i).left
    rw [he] at h
    exact congrArg ProbabilityMeasure.toMeasure (tendsto_nhds_unique h tendsto_const_nhds)
  · have h := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous ps p hp continuous_snd
    have he : (fun i => (ps i).map continuous_snd.measurable.aemeasurable) = fun _ => n := by
      funext i
      exact Subtype.ext (hs i).right
    rw [he] at h
    exact congrArg ProbabilityMeasure.toMeasure (tendsto_nhds_unique h tendsto_const_nhds)

theorem timeCoupling_selfProd_tendsto {ps : ℕ → ProbabilityMeasure (X × Y)}
    {p : ProbabilityMeasure (X × Y)} (hp : Tendsto ps atTop (𝓝 p)) :
    Tendsto (fun n => (ps n).prod (ps n)) atTop (𝓝 (p.prod p)) :=
  (ProbabilityMeasure.continuous_prod.tendsto (p, p)).comp (hp.prodMk_nhds hp)

theorem timeBadPairs_limit_eq_zero {ps : ℕ → ProbabilityMeasure (X × Y)}
    {p : ProbabilityMeasure (X × Y)} (hp : Tendsto ps atTop (𝓝 p))
    {tx : X → X → ℝ} {ty : Y → Y → ℝ}
    (hx : Continuous (Function.uncurry tx)) (hy : Continuous (Function.uncurry ty))
    {eps : ℕ → ℝ} (heps : Tendsto eps atTop (𝓝 0))
    (hbad : ∀ n, ((ps n).toMeasure.prod (ps n).toMeasure) (timeBadPairs tx ty (eps n)) ≤
      ENNReal.ofReal (eps n)) {delta : ℝ} (hd : 0 < delta) :
    (p.toMeasure.prod p.toMeasure) (timeBadPairs tx ty delta) = 0 := by
  apply le_antisymm _ bot_le
  have hl := ProbabilityMeasure.le_liminf_measure_open_of_tendsto
    (timeCoupling_selfProd_tendsto hp) (isOpen_timeBadPairs hx hy delta)
  have hle : ∀ᶠ n in atTop,
      ((ps n).toMeasure.prod (ps n).toMeasure) (timeBadPairs tx ty delta) ≤ ENNReal.ofReal (eps n) := by
    filter_upwards [heps.eventually_lt_const hd] with n hn
    exact (measure_mono (timeBadPairs_antitone tx ty hn.le)).trans (hbad n)
  have hzero : Tendsto (fun n => ENNReal.ofReal (eps n)) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal heps
  exact hl.trans ((liminf_le_liminf hle).trans_eq hzero.liminf_eq)

theorem isZeroTimeCoupling_of_tendsto {mu : Measure X} {nu : Measure Y}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {ps : ℕ → ProbabilityMeasure (X × Y)} {p : ProbabilityMeasure (X × Y)}
    (hp : Tendsto ps atTop (𝓝 p)) (hs : ∀ n, IsTimeCoupling mu nu (ps n).toMeasure)
    {tx : X → X → ℝ} {ty : Y → Y → ℝ}
    (hx : Continuous (Function.uncurry tx)) (hy : Continuous (Function.uncurry ty))
    {eps : ℕ → ℝ} (heps : Tendsto eps atTop (𝓝 0))
    (hbad : ∀ n, ((ps n).toMeasure.prod (ps n).toMeasure) (timeBadPairs tx ty (eps n)) ≤
      ENNReal.ofReal (eps n)) : IsZeroTimeCoupling mu nu tx ty p.toMeasure := by
  refine ⟨isTimeCoupling_of_tendsto hp hs, time_eq_ae_of_bad_zero _ ?_⟩
  exact fun _ hd => timeBadPairs_limit_eq_zero hp hx hy heps hbad hd

#print axioms isOpen_timeBadPairs
#print axioms isTimeCoupling_of_tendsto
#print axioms timeCoupling_selfProd_tendsto
#print axioms timeBadPairs_limit_eq_zero
#print axioms isZeroTimeCoupling_of_tendsto

end
end QuantyraNullCone
