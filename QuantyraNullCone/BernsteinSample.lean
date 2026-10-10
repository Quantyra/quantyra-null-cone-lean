import QuantyraNullCone.BernsteinIndicator
import Mathlib.MeasureTheory.Integral.Pi

namespace QuantyraNullCone
open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section

def centeredIndicatorSum {Ω : Type*} (S : Set Ω) (p : ℝ) {m : ℕ}
    (sample : Fin m → Ω) : ℝ := ∑ i, (S.indicator (fun _ => (1 : ℝ)) (sample i)-p)

theorem centeredIndicatorSum_measurable {Ω : Type*} [MeasurableSpace Ω]
    {S : Set Ω} (hS : MeasurableSet S) (p : ℝ) (m : ℕ) :
    Measurable (centeredIndicatorSum S p (m := m)) := by
  unfold centeredIndicatorSum
  exact Finset.measurable_sum _ (fun i _ =>
    ((measurable_const.indicator hS).comp (measurable_pi_apply i)).sub_const p)

theorem iid_indicator_sum_exp_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {S : Set Ω}
    (hS : MeasurableSet S) (p t : ℝ) (m : ℕ) :
    Integrable (fun x : Fin m → Ω => Real.exp (t*centeredIndicatorSum S p x))
      (Measure.pi (fun _ : Fin m => μ)) := by
  let X (i : Fin m) (x : Fin m → Ω) := S.indicator (fun _ => (1 : ℝ)) (x i)-p
  have hMeas (i : Fin m) : Measurable (X i) :=
    ((measurable_const.indicator hS).comp (measurable_pi_apply i)).sub_const p
  have hIndep : iIndepFun X (Measure.pi (fun _ : Fin m => μ)) :=
    iIndepFun_pi (X := fun _ : Fin m => fun q => S.indicator (fun _ => (1 : ℝ)) q-p)
      (fun _ => ((measurable_const.indicator hS).sub_const p).aemeasurable)
  simpa only [Finset.sum_apply] using hIndep.integrable_exp_mul_sum (t := t) hMeas
    (s := Finset.univ) (fun i _ => integrable_comp_eval
      (μ := fun _ : Fin m => μ) (i := i) (centered_indicator_exp_integrable hS p t))

theorem iid_indicator_sum_bernstein_mgf {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {S : Set Ω}
    (hS : MeasurableSet S) (m : ℕ) {t : ℝ} (ht : |t| < 3) :
    mgf (centeredIndicatorSum S (μ.real S) (m := m)) (Measure.pi (fun _ : Fin m => μ)) t ≤
      Real.exp ((m : ℝ)*μ.real S*(1-μ.real S)*t^2/(2*(1-|t|/3))) := by
  classical
  let P := Measure.pi (fun _ : Fin m => μ)
  let X (i : Fin m) (x : Fin m → Ω) := S.indicator (fun _ => (1 : ℝ)) (x i)-μ.real S
  have hMeas (i : Fin m) : Measurable (X i) :=
    ((measurable_const.indicator hS).comp (measurable_pi_apply i)).sub_const _
  have hIndep : iIndepFun X P :=
    iIndepFun_pi (X := fun _ : Fin m => fun q => S.indicator (fun _ => (1 : ℝ)) q-μ.real S)
      (fun _ => ((measurable_const.indicator hS).sub_const _).aemeasurable)
  have hEach (i : Fin m) : mgf (X i) P t ≤
      Real.exp (μ.real S*(1-μ.real S)*t^2/(2*(1-|t|/3))) := by
    have he : mgf (X i) P t = mgf (fun q => S.indicator (fun _ => (1 : ℝ)) q-μ.real S) μ t :=
      integral_comp_eval (μ := fun _ : Fin m => μ) (i := i)
        (centered_indicator_exp_integrable hS (μ.real S) t).aestronglyMeasurable
    rw [he]
    exact centered_indicator_bernstein_mgf hS ht
  change mgf (centeredIndicatorSum S (μ.real S) (m := m)) P t ≤ _
  rw [show centeredIndicatorSum S (μ.real S) (m := m) = ∑ i : Fin m, X i by
    funext sample; simp only [centeredIndicatorSum,X,Finset.sum_apply],
    hIndep.mgf_sum hMeas Finset.univ]
  calc
    _ ≤ ∏ _i : Fin m, Real.exp (μ.real S*(1-μ.real S)*t^2/(2*(1-|t|/3))) :=
      Finset.prod_le_prod (fun _ _ => mgf_nonneg) (fun i _ => hEach i)
    _ = _ := by
      rw [← Real.exp_sum]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      congr 1
      ring

#print axioms iid_indicator_sum_exp_integrable
#print axioms iid_indicator_sum_bernstein_mgf
end
end QuantyraNullCone
