import QuantyraNullCone.LorentzBoundary
import QuantyraNullCone.ProperTime
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

namespace QuantyraNullCone

open MeasureTheory Set

noncomputable section

/-- Flat proper speed of a genuine 2+1 velocity. It is used on the future cone. -/
def flatProperSpeed3 (v : LorentzPoint3) : ℝ :=
  Real.sqrt (v 0 ^ 2 - spatialSquared3 v)

/-- Coordinatewise absolutely continuous causal curves in the closed diamond.
No length bound, endpoint causality or regularity of the derivative is assumed. -/
structure FutureCurve3 (p q : LorentzPoint3) where
  coord : Fin 3 → ℝ → ℝ
  coordAC : ∀ i, AbsolutelyContinuousOnInterval (coord i) 0 1
  start : ∀ i, coord i 0 = p i
  finish : ∀ i, coord i 1 = q i
  inDiamond : ∀ t ∈ Icc (0 : ℝ) 1,
    WithLp.toLp 2 (fun i => coord i t) ∈ closedLorentzDiamond3
  future : ∀ᵐ t ∂curveMeasure,
    spatialRadius3 (WithLp.toLp 2 (fun i => deriv (coord i) t)) ≤ deriv (coord 0) t

def FutureCurve3.point {p q : LorentzPoint3} (c : FutureCurve3 p q) (t : ℝ) :
    LorentzPoint3 := WithLp.toLp 2 (fun i => c.coord i t)

def FutureCurve3.velocity {p q : LorentzPoint3} (c : FutureCurve3 p q) (t : ℝ) :
    LorentzPoint3 := WithLp.toLp 2 (fun i => deriv (c.coord i) t)

def FutureCurve3.flatSpeed {p q : LorentzPoint3} (c : FutureCurve3 p q) (t : ℝ) : ℝ :=
  flatProperSpeed3 (c.velocity t)

def FutureCurve3.flatLength {p q : LorentzPoint3} (c : FutureCurve3 p q) : ℝ :=
  ∫ t, c.flatSpeed t ∂curveMeasure

theorem flat_proper_speed_nonneg3 (v : LorentzPoint3) : 0 ≤ flatProperSpeed3 v :=
  Real.sqrt_nonneg _

theorem flat_proper_speed_sq3 {v : LorentzPoint3} (hv : spatialRadius3 v ≤ v 0) :
    flatProperSpeed3 v ^ 2 = v 0 ^ 2 - spatialSquared3 v := by
  apply Real.sq_sqrt
  have ht := (spatial_radius_nonneg3 v).trans hv
  have hs := (sq_le_sq₀ (spatial_radius_nonneg3 v) ht).mpr hv
  rw [spatial_radius_sq3] at hs
  linarith

theorem flat_proper_speed_le_time3 {v : LorentzPoint3} (hv : spatialRadius3 v ≤ v 0) :
    flatProperSpeed3 v ≤ v 0 := by
  unfold flatProperSpeed3
  apply (Real.sqrt_le_left ((spatial_radius_nonneg3 v).trans hv)).mpr
  linarith [spatial_squared_nonneg3 v]

/-- The Euclidean lift of a causal velocity has norm equal to elapsed coordinate time. -/
theorem proper_speed_lift_norm3 {v : LorentzPoint3} (hv : spatialRadius3 v ≤ v 0) :
    ‖lorentzPoint3 (flatProperSpeed3 v) (v 1) (v 2)‖ = v 0 := by
  have ht := (spatial_radius_nonneg3 v).trans hv
  have hn := lorentz_norm_sq3 (lorentzPoint3 (flatProperSpeed3 v) (v 1) (v 2))
  change ‖lorentzPoint3 (flatProperSpeed3 v) (v 1) (v 2)‖ ^ 2 =
    flatProperSpeed3 v ^ 2 + spatialSquared3 v at hn
  rw [flat_proper_speed_sq3 hv] at hn
  nlinarith [norm_nonneg (lorentzPoint3 (flatProperSpeed3 v) (v 1) (v 2))]

theorem FutureCurve3.integrable_deriv {p q : LorentzPoint3} (c : FutureCurve3 p q)
    (i : Fin 3) : Integrable (deriv (c.coord i)) curveMeasure :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
    (c.coordAC i).intervalIntegrable_deriv

theorem FutureCurve3.integral_deriv {p q : LorentzPoint3} (c : FutureCurve3 p q)
    (i : Fin 3) : (∫ t, deriv (c.coord i) t ∂curveMeasure) = q i - p i := by
  change (∫ t in Icc (0 : ℝ) 1, deriv (c.coord i) t) = _
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
  rw [(c.coordAC i).integral_deriv_eq_sub, c.finish, c.start]

theorem FutureCurve3.time_deriv_nonneg {p q : LorentzPoint3} (c : FutureCurve3 p q) :
    ∀ᵐ t ∂curveMeasure, 0 ≤ deriv (c.coord 0) t :=
  c.future.mono fun _ ht => (spatial_radius_nonneg3 _).trans ht

theorem FutureCurve3.endpoint_time_nonneg {p q : LorentzPoint3} (c : FutureCurve3 p q) :
    0 ≤ q 0 - p 0 := by
  rw [← c.integral_deriv 0]
  exact integral_nonneg_of_ae c.time_deriv_nonneg

theorem FutureCurve3.integrable_flatSpeed {p q : LorentzPoint3} (c : FutureCurve3 p q) :
    Integrable c.flatSpeed curveMeasure := by
  have hm : AEStronglyMeasurable c.flatSpeed curveMeasure := by
    exact Real.continuous_sqrt.comp_aestronglyMeasurable
      (((c.integrable_deriv 0).aestronglyMeasurable.pow 2).sub
        (((c.integrable_deriv 1).aestronglyMeasurable.pow 2).add
          ((c.integrable_deriv 2).aestronglyMeasurable.pow 2)))
  apply (c.integrable_deriv 0).mono' hm
  filter_upwards [c.future] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg
    (show 0 ≤ c.flatSpeed t from flat_proper_speed_nonneg3 _)]
  exact flat_proper_speed_le_time3 ht

def FutureCurve3.speedLift {p q : LorentzPoint3} (c : FutureCurve3 p q) (t : ℝ) :
    LorentzPoint3 := lorentzPoint3 (c.flatSpeed t) (deriv (c.coord 1) t)
      (deriv (c.coord 2) t)

theorem FutureCurve3.integrable_speedLift {p q : LorentzPoint3} (c : FutureCurve3 p q) :
    Integrable c.speedLift curveMeasure := by
  apply Integrable.of_eval_piLp
  intro i
  fin_cases i
  · exact c.integrable_flatSpeed
  · exact c.integrable_deriv 1
  · exact c.integrable_deriv 2

theorem FutureCurve3.integral_speedLift {p q : LorentzPoint3} (c : FutureCurve3 p q) :
    (∫ t, c.speedLift t ∂curveMeasure) =
      lorentzPoint3 c.flatLength (q 1 - p 1) (q 2 - p 2) := by
  ext i
  rw [eval_integral_piLp (fun j => c.integrable_speedLift.eval_piLp j)]
  fin_cases i
  · rfl
  · exact c.integral_deriv 1
  · exact c.integral_deriv 2

theorem FutureCurve3.integral_speedLift_norm {p q : LorentzPoint3}
    (c : FutureCurve3 p q) : (∫ t, ‖c.speedLift t‖ ∂curveMeasure) = q 0 - p 0 := by
  rw [← c.integral_deriv 0]
  apply integral_congr_ae
  filter_upwards [c.future] with t ht
  exact proper_speed_lift_norm3 ht

theorem FutureCurve3.flatLength_nonneg {p q : LorentzPoint3} (c : FutureCurve3 p q) :
    0 ≤ c.flatLength := integral_nonneg fun _ => flat_proper_speed_nonneg3 _

/-- The endpoint bound is derived from the actual derivative integral. -/
theorem FutureCurve3.flatLength_sq_bound {p q : LorentzPoint3} (c : FutureCurve3 p q) :
    c.flatLength ^ 2 + spatialSquared3 (q - p) ≤ (q 0 - p 0) ^ 2 := by
  have hn := norm_integral_le_integral_norm c.speedLift (μ := curveMeasure)
  rw [c.integral_speedLift, c.integral_speedLift_norm] at hn
  have hs := (sq_le_sq₀ (norm_nonneg _) c.endpoint_time_nonneg).mpr hn
  rw [lorentz_norm_sq3] at hs
  exact hs

theorem FutureCurve3.endpoint_causal {p q : LorentzPoint3} (c : FutureCurve3 p q) :
    causal3 p q := by
  unfold causal3
  have hs := c.flatLength_sq_bound
  have ht := c.endpoint_time_nonneg
  nlinarith [spatial_radius_sq3 (q - p), spatial_radius_nonneg3 (q - p),
    sq_nonneg c.flatLength]

theorem FutureCurve3.flatLength_le_endpoint {p q : LorentzPoint3} (c : FutureCurve3 p q) :
    c.flatLength ≤ flatProperSpeed3 (q - p) := by
  apply Real.le_sqrt_of_sq_le
  have hs := c.flatLength_sq_bound
  change c.flatLength ^ 2 ≤ (q 0 - p 0) ^ 2 - spatialSquared3 (q - p)
  linarith

theorem FutureCurve3.flatLength_le_two {p q : LorentzPoint3} (c : FutureCurve3 p q) :
    c.flatLength ≤ 2 := by
  have hp := closed_lorentz_diamond_bounds3 (c.inDiamond 0 (by constructor <;> norm_num))
  have hq := closed_lorentz_diamond_bounds3 (c.inDiamond 1 (by constructor <;> norm_num))
  change |c.coord 0 0| ≤ 1 ∧ _ at hp
  change |c.coord 0 1| ≤ 1 ∧ _ at hq
  rw [c.start] at hp
  rw [c.finish] at hq
  have h := c.flatLength_le_endpoint.trans (flat_proper_speed_le_time3 c.endpoint_causal)
  change c.flatLength ≤ q 0 - p 0 at h
  linarith [le_abs_self (q 0), neg_le_abs (p 0)]

theorem spatial_radius_smul3 (s : ℝ) (v : LorentzPoint3) :
    spatialRadius3 (s • v) = |s| * spatialRadius3 v := by
  change Real.sqrt ((s * v 1) ^ 2 + (s * v 2) ^ 2) = _
  rw [show (s * v 1) ^ 2 + (s * v 2) ^ 2 = s ^ 2 * spatialSquared3 v by
    unfold spatialSquared3; ring]
  rw [Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq_eq_abs]
  rfl

def straightPoint3 (p q : LorentzPoint3) (t : ℝ) : LorentzPoint3 := p + t • (q - p)

theorem straight_point_causal3 {p q : LorentzPoint3} (hpq : causal3 p q)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    causal3 p (straightPoint3 p q t) ∧ causal3 (straightPoint3 p q t) q := by
  have hsub : straightPoint3 p q t - p = t • (q - p) := by
    simp [straightPoint3]
  have hsub' : q - straightPoint3 p q t = (1 - t) • (q - p) := by
    ext i
    change q i - (p i + t * (q i - p i)) = (1 - t) * (q i - p i)
    ring
  constructor
  · unfold causal3
    rw [hsub, spatial_radius_smul3, abs_of_nonneg ht.1]
    have h := mul_le_mul_of_nonneg_left hpq ht.1
    change t * spatialRadius3 (q - p) ≤ p 0 + t * (q 0 - p 0) - p 0
    linarith
  · unfold causal3
    rw [hsub', spatial_radius_smul3, abs_of_nonneg (sub_nonneg.mpr ht.2)]
    have h := mul_le_mul_of_nonneg_left hpq (sub_nonneg.mpr ht.2)
    change (1 - t) * spatialRadius3 (q - p) ≤ q 0 - (p 0 + t * (q 0 - p 0))
    nlinarith

theorem straight_coord_deriv3 (p q : LorentzPoint3) (i : Fin 3) (t : ℝ) :
    deriv (fun s => p i + s * (q i - p i)) t = q i - p i := by
  simpa only [one_mul] using (((hasDerivAt_id t).mul_const (q i - p i)).const_add (p i)).deriv

/-- A causal segment belongs to the same actual AC-curve class. -/
def straightCurve3 {p q : LorentzPoint3} (hp : p ∈ closedLorentzDiamond3)
    (hq : q ∈ closedLorentzDiamond3) (hpq : causal3 p q) : FutureCurve3 p q where
  coord i t := p i + t * (q i - p i)
  coordAC i := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    fun_prop
  start i := by simp
  finish i := by simp
  inDiamond t ht := causal_diamond_subset_closed3 hp hq (straight_point_causal3 hpq ht)
  future := Filter.Eventually.of_forall fun t => by
    simpa only [straight_coord_deriv3] using hpq

theorem straight_curve_velocity3 {p q : LorentzPoint3} (hp : p ∈ closedLorentzDiamond3)
    (hq : q ∈ closedLorentzDiamond3) (hpq : causal3 p q) (t : ℝ) :
    (straightCurve3 hp hq hpq).velocity t = q - p := by
  ext i
  exact straight_coord_deriv3 p q i t

theorem straight_curve_flatLength3 {p q : LorentzPoint3} (hp : p ∈ closedLorentzDiamond3)
    (hq : q ∈ closedLorentzDiamond3) (hpq : causal3 p q) :
    (straightCurve3 hp hq hpq).flatLength = flatProperSpeed3 (q - p) := by
  unfold FutureCurve3.flatLength FutureCurve3.flatSpeed
  simp only [straight_curve_velocity3]
  simp [curveMeasure, Measure.real]

theorem future_curve_nonempty_iff_causal3 {p q : LorentzPoint3}
    (hp : p ∈ closedLorentzDiamond3) (hq : q ∈ closedLorentzDiamond3) :
    Nonempty (FutureCurve3 p q) ↔ causal3 p q :=
  ⟨fun ⟨c⟩ => c.endpoint_causal, fun h => ⟨straightCurve3 hp hq h⟩⟩

theorem flat_proper_speed_pos_iff3 {p q : LorentzPoint3} (hpq : causal3 p q) :
    0 < flatProperSpeed3 (q - p) ↔ chronological3 p q := by
  have ht : 0 ≤ q 0 - p 0 := (spatial_radius_nonneg3 (q - p)).trans hpq
  have hs := spatial_radius_sq3 (q - p)
  change 0 < Real.sqrt ((q 0 - p 0) ^ 2 - spatialSquared3 (q - p)) ↔
    spatialRadius3 (q - p) < q 0 - p 0
  rw [Real.sqrt_pos]
  constructor <;> intro h <;> nlinarith [spatial_radius_nonneg3 (q - p)]

/-- Flat time separation from the supremum over all actual AC causal curves. -/
def flatTimeSeparation3 (p q : LorentzPoint3) : ℝ :=
  sSup (insert 0 (Set.range (fun c : FutureCurve3 p q => c.flatLength)))

theorem flat_lengths_bddAbove3 (p q : LorentzPoint3) :
    BddAbove (insert 0 (Set.range (fun c : FutureCurve3 p q => c.flatLength))) := by
  refine ⟨2, ?_⟩
  rintro x (hx | ⟨c, rfl⟩)
  · subst x; norm_num
  · exact c.flatLength_le_two

theorem flat_time_separation_nonneg3 (p q : LorentzPoint3) :
    0 ≤ flatTimeSeparation3 p q := le_csSup (flat_lengths_bddAbove3 p q) (by simp)

theorem flat_time_separation_eq3 {p q : LorentzPoint3}
    (hp : p ∈ closedLorentzDiamond3) (hq : q ∈ closedLorentzDiamond3)
    (hpq : causal3 p q) : flatTimeSeparation3 p q = flatProperSpeed3 (q - p) := by
  apply le_antisymm
  · apply csSup_le (by simp : (insert 0 (Set.range
      (fun c : FutureCurve3 p q => c.flatLength))).Nonempty)
    rintro x (hx | ⟨c, rfl⟩)
    · subst x; exact flat_proper_speed_nonneg3 _
    · exact c.flatLength_le_endpoint
  · rw [← straight_curve_flatLength3 hp hq hpq]
    exact le_csSup (flat_lengths_bddAbove3 p q) (by simp)

theorem flat_time_separation_of_not_causal3 {p q : LorentzPoint3} (hpq : ¬causal3 p q) :
    flatTimeSeparation3 p q = 0 := by
  have hr : Set.range (fun c : FutureCurve3 p q => c.flatLength) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro x ⟨c, rfl⟩
    exact hpq c.endpoint_causal
  simp [flatTimeSeparation3, hr]

theorem flat_time_separation_pos_iff3 {p q : LorentzPoint3}
    (hp : p ∈ closedLorentzDiamond3) (hq : q ∈ closedLorentzDiamond3) :
    0 < flatTimeSeparation3 p q ↔ chronological3 p q := by
  by_cases h : causal3 p q
  · rw [flat_time_separation_eq3 hp hq h, flat_proper_speed_pos_iff3 h]
  · rw [flat_time_separation_of_not_causal3 h]
    constructor
    · norm_num
    · intro h'
      exact (h (le_of_lt h')).elim

#print axioms flat_proper_speed_nonneg3
#print axioms flat_proper_speed_sq3
#print axioms flat_proper_speed_le_time3
#print axioms proper_speed_lift_norm3
#print axioms FutureCurve3.integrable_deriv
#print axioms FutureCurve3.integral_deriv
#print axioms FutureCurve3.time_deriv_nonneg
#print axioms FutureCurve3.endpoint_time_nonneg
#print axioms FutureCurve3.integrable_flatSpeed
#print axioms FutureCurve3.integrable_speedLift
#print axioms FutureCurve3.integral_speedLift
#print axioms FutureCurve3.integral_speedLift_norm
#print axioms FutureCurve3.flatLength_nonneg
#print axioms FutureCurve3.flatLength_sq_bound
#print axioms FutureCurve3.endpoint_causal
#print axioms FutureCurve3.flatLength_le_endpoint
#print axioms FutureCurve3.flatLength_le_two
#print axioms spatial_radius_smul3
#print axioms straight_point_causal3
#print axioms straight_coord_deriv3
#print axioms straight_curve_velocity3
#print axioms straight_curve_flatLength3
#print axioms future_curve_nonempty_iff_causal3
#print axioms flat_proper_speed_pos_iff3
#print axioms flat_lengths_bddAbove3
#print axioms flat_time_separation_nonneg3
#print axioms flat_time_separation_eq3
#print axioms flat_time_separation_of_not_causal3
#print axioms flat_time_separation_pos_iff3

end
end QuantyraNullCone
