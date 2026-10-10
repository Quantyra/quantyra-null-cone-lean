import QuantyraNullCone.PairConcentration

namespace QuantyraNullCone
open MeasureTheory ProbabilityTheory
noncomputable section
set_option maxHeartbeats 1000000

theorem pairIndicator_chernoff {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {S : Set (Ω × Ω)} (hS : MeasurableSet S)
    {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht0 : 0 ≤ t) (ht3 : t < 3) (r : ℝ) :
    (Measure.pi (fun _ : Fin n => μ)).real {x | r ≤ |pairIndicatorMean S x-(μ.prod μ).real S|} ≤
      2*Real.exp (((n/2 : ℕ) : ℝ)*(μ.prod μ).real S*(1-(μ.prod μ).real S)*t^2/(2*(1-t/3))-
        ((n/2 : ℕ) : ℝ)*t*r) := by
  let P := Measure.pi (fun _ : Fin n => μ)
  let p := (μ.prod μ).real S
  let m : ℝ := (n/2 : ℕ)
  let X (x : Fin n → Ω) := m*(pairIndicatorMean S x-p)
  have hm : 0 < m := by
    have : 0 < n/2 := by omega
    change (0 : ℝ) < (n/2 : ℕ)
    exact_mod_cast this
  have hi (z : ℝ) : Integrable (fun x => Real.exp (z*X x)) P := by
    simpa only [mul_assoc] using pairIndicator_exp_integrable hS hn p z
  have hg (z : ℝ) (hz : |z| < 3) : mgf X P z ≤
      Real.exp (m*p*(1-p)*z^2/(2*(1-|z|/3))) := pairIndicator_bernstein_mgf hS hn hz
  have ht : |t| < 3 := by rwa [abs_of_nonneg ht0]
  have hU := (measure_ge_le_exp_mul_mgf (μ := P) (m*r) ht0 (hi t)).trans
    (mul_le_mul_of_nonneg_left (hg t ht) (Real.exp_pos _).le)
  have hL := (measure_le_le_exp_mul_mgf (μ := P) (-(m*r)) (neg_nonpos.mpr ht0) (hi (-t))).trans
    (mul_le_mul_of_nonneg_left (hg (-t) (by simpa only [abs_neg] using ht)) (Real.exp_pos _).le)
  rw [← Real.exp_add,abs_of_nonneg ht0] at hU
  rw [← Real.exp_add,abs_neg,abs_of_nonneg ht0] at hL
  have hUE : -t*(m*r)+m*p*(1-p)*t^2/(2*(1-t/3)) =
      m*p*(1-p)*t^2/(2*(1-t/3))-m*t*r := by ring
  have hLE : -(-t)*(-(m*r))+m*p*(1-p)*(-t)^2/(2*(1-t/3)) =
      m*p*(1-p)*t^2/(2*(1-t/3))-m*t*r := by ring
  rw [hUE] at hU
  rw [hLE] at hL
  have hs : {x : Fin n → Ω | r ≤ |pairIndicatorMean S x-p|} ⊆
      {x | m*r ≤ X x} ∪ {x | X x ≤ -(m*r)} := by
    intro x hx
    have hb : m*r ≤ |X x| := by
      change m*r ≤ |m*(pairIndicatorMean S x-p)|
      rw [abs_mul,abs_of_pos hm]
      exact mul_le_mul_of_nonneg_left hx hm.le
    rcases le_abs.mp hb with h | h
    · exact Or.inl h
    · right
      change X x ≤ -(m*r)
      linarith
  calc
    _ ≤ P.real ({x | m*r ≤ X x} ∪ {x | X x ≤ -(m*r)}) := measureReal_mono hs
    _ ≤ P.real {x | m*r ≤ X x}+P.real {x | X x ≤ -(m*r)} := measureReal_union_le _ _
    _ ≤ _ := by linarith

/-- Bernstein concentration using a uniform upper bound on the single-pair variance.
The effective independent block size is floor(n/2), although the observable uses every pair. -/
theorem pairIndicator_bernstein_tail {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {S : Set (Ω × Ω)} (hS : MeasurableSet S)
    {n : ℕ} (hn : 2 ≤ n) {v r : ℝ} (hv0 : 0 < v) (hr : 0 < r)
    (hv : (μ.prod μ).real S*(1-(μ.prod μ).real S) ≤ v) :
    (Measure.pi (fun _ : Fin n => μ)).real {x | r ≤ |pairIndicatorMean S x-(μ.prod μ).real S|} ≤
      2*Real.exp (-((n/2 : ℕ) : ℝ)*r^2/(2*(v+r/3))) := by
  let t := r/(v+r/3)
  have hd : 0 < v+r/3 := by positivity
  have ht0 : 0 < t := div_pos hr hd
  have ht3 : t < 3 := by
    apply (div_lt_iff₀ hd).mpr
    linarith
  have hden : 0 < 2*(1-t/3) := by linarith
  have h := pairIndicator_chernoff (μ := μ) hS hn ht0.le ht3 r
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ ((n/2 : ℕ) : ℝ)*v*t^2/(2*(1-t/3))-((n/2 : ℕ) : ℝ)*t*r := by
      apply sub_le_sub_right
      apply div_le_div_of_nonneg_right _ hden.le
      have hmul := mul_le_mul_of_nonneg_left hv
        (show 0 ≤ ((n/2 : ℕ) : ℝ)*t^2 by positivity)
      nlinarith only [hmul]
    _ = _ := by
      dsimp [t]
      field_simp
      ring

#print axioms pairIndicator_chernoff
#print axioms pairIndicator_bernstein_tail
end
end QuantyraNullCone
