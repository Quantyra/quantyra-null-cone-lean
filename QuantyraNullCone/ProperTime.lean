import QuantyraNullCone.ImprovedInverse
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Function.L2Space

namespace QuantyraNullCone

open MeasureTheory Set

noncomputable def curveMeasure : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)

/-- Actual absolutely continuous future curves in the closed null-coordinate diamond. -/
structure FutureCurve (p q : DiamondPoint) where
  u : ℝ → ℝ
  v : ℝ → ℝ
  uAC : AbsolutelyContinuousOnInterval u 0 1
  vAC : AbsolutelyContinuousOnInterval v 0 1
  startU : u 0 = p.1
  startV : v 0 = p.2
  endU : u 1 = q.1
  endV : v 1 = q.2
  inDiamond : ∀ t ∈ Icc (0 : ℝ) 1, (u t, v t) ∈ diamond
  futureU : ∀ᵐ t ∂curveMeasure, 0 ≤ deriv u t
  futureV : ∀ᵐ t ∂curveMeasure, 0 ≤ deriv v t

def FutureCurve.point {p q : DiamondPoint} (c : FutureCurve p q) (t : ℝ) :
    DiamondPoint := (c.u t, c.v t)

noncomputable def FutureCurve.weight {p q : DiamondPoint} (c : FutureCurve p q)
    (t : ℝ) : ℝ := Real.sqrt (deriv c.u t * deriv c.v t)

/-- The Lorentzian length integrand from the paper, with no assumed length estimate. -/
noncomputable def FutureCurve.length {p q : DiamondPoint} (c : FutureCurve p q)
    (rho : DiamondPoint → ℝ) : ℝ :=
  ∫ t, Real.sqrt (2 * rho (c.point t) * deriv c.u t * deriv c.v t) ∂curveMeasure

theorem FutureCurve.integrable_derivU {p q : DiamondPoint} (c : FutureCurve p q) :
    Integrable (deriv c.u) curveMeasure := by
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
    c.uAC.intervalIntegrable_deriv

theorem FutureCurve.integrable_derivV {p q : DiamondPoint} (c : FutureCurve p q) :
    Integrable (deriv c.v) curveMeasure := by
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
    c.vAC.intervalIntegrable_deriv

theorem FutureCurve.integral_derivU {p q : DiamondPoint} (c : FutureCurve p q) :
    (∫ t, deriv c.u t ∂curveMeasure) = q.1 - p.1 := by
  change (∫ t in Icc (0 : ℝ) 1, deriv c.u t) = _
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
  rw [c.uAC.integral_deriv_eq_sub, c.endU, c.startU]

theorem FutureCurve.integral_derivV {p q : DiamondPoint} (c : FutureCurve p q) :
    (∫ t, deriv c.v t ∂curveMeasure) = q.2 - p.2 := by
  change (∫ t in Icc (0 : ℝ) 1, deriv c.v t) = _
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
  rw [c.vAC.integral_deriv_eq_sub, c.endV, c.startV]

theorem sqrt_coefficient_lipschitz {a b : ℝ} (ha : 1 / 2 ≤ a) (hb : 1 / 2 ≤ b) :
    |Real.sqrt (2 * a) - Real.sqrt (2 * b)| ≤ |a - b| := by
  have ha0 : 0 ≤ 2 * a := by linarith
  have hb0 : 0 ≤ 2 * b := by linarith
  have ha1 : 1 ≤ Real.sqrt (2 * a) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hb1 : 1 ≤ Real.sqrt (2 * b) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hsqA := Real.sq_sqrt ha0
  have hsqB := Real.sq_sqrt hb0
  have hId : (Real.sqrt (2 * a) - Real.sqrt (2 * b)) *
      (Real.sqrt (2 * a) + Real.sqrt (2 * b)) = 2 * (a - b) := by nlinarith
  have hAbs := congrArg abs hId
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.sqrt (2 * a) + Real.sqrt (2 * b)),
    abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hAbs
  have hNonneg := abs_nonneg (Real.sqrt (2 * a) - Real.sqrt (2 * b))
  nlinarith

theorem sqrt_memLp_two {f : ℝ → ℝ} {μ : Measure ℝ}
    (hf : Integrable f μ) (hPos : ∀ᵐ t ∂μ, 0 ≤ f t) :
    MemLp (fun t => Real.sqrt (f t)) 2 μ := by
  apply (memLp_two_iff_integrable_sq
    (Real.continuous_sqrt.comp_aestronglyMeasurable hf.aestronglyMeasurable)).mpr
  apply hf.congr
  filter_upwards [hPos] with t ht
  exact (Real.sq_sqrt ht).symm

theorem FutureCurve.weight_eq {p q : DiamondPoint} (c : FutureCurve p q) :
    c.weight =ᵐ[curveMeasure] fun t => Real.sqrt (deriv c.u t) *
      Real.sqrt (deriv c.v t) := by
  filter_upwards [c.futureU] with t ht
  exact Real.sqrt_mul ht _

theorem FutureCurve.integrable_weight {p q : DiamondPoint} (c : FutureCurve p q) :
    Integrable c.weight curveMeasure := by
  have hu := sqrt_memLp_two c.integrable_derivU c.futureU
  have hv := sqrt_memLp_two c.integrable_derivV c.futureV
  exact (hu.integrable_mul hv).congr c.weight_eq.symm

theorem FutureCurve.integral_weight_cauchy_schwarz {p q : DiamondPoint}
    (c : FutureCurve p q) :
    (∫ t, c.weight t ∂curveMeasure) ≤ Real.sqrt (q.1 - p.1) * Real.sqrt (q.2 - p.2) := by
  have hu := sqrt_memLp_two c.integrable_derivU c.futureU
  have hv := sqrt_memLp_two c.integrable_derivV c.futureV
  have hHolder : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hHolder
    (Filter.Eventually.of_forall (fun t => Real.sqrt_nonneg (deriv c.u t)))
    (Filter.Eventually.of_forall (fun t => Real.sqrt_nonneg (deriv c.v t)))
    (by simpa using hu) (by simpa using hv)
  have hU : (∫ t, (Real.sqrt (deriv c.u t)) ^ (2 : ℝ) ∂curveMeasure) = q.1 - p.1 := by
    rw [← c.integral_derivU]
    apply integral_congr_ae
    filter_upwards [c.futureU] with t ht
    rw [Real.rpow_two, Real.sq_sqrt ht]
  have hV : (∫ t, (Real.sqrt (deriv c.v t)) ^ (2 : ℝ) ∂curveMeasure) = q.2 - p.2 := by
    rw [← c.integral_derivV]
    apply integral_congr_ae
    filter_upwards [c.futureV] with t ht
    rw [Real.rpow_two, Real.sq_sqrt ht]
  rw [hU, hV, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at h
  exact (integral_congr_ae c.weight_eq).le.trans h

theorem FutureCurve.integral_weight_le_one {p q : DiamondPoint} (c : FutureCurve p q) :
    (∫ t, c.weight t ∂curveMeasure) ≤ 1 := by
  have hp := c.inDiamond 0 (by constructor <;> norm_num)
  have hq := c.inDiamond 1 (by constructor <;> norm_num)
  rw [c.startU, c.startV] at hp
  rw [c.endU, c.endV] at hq
  have hu : Real.sqrt (q.1 - p.1) ≤ 1 := by
    apply (Real.sqrt_le_left (by norm_num)).mpr
    rcases hp with ⟨hpU, _⟩
    rcases hq with ⟨hqU, _⟩
    nlinarith [hpU.1, hqU.2]
  have hv : Real.sqrt (q.2 - p.2) ≤ 1 := by
    apply (Real.sqrt_le_left (by norm_num)).mpr
    rcases hp with ⟨_, hpV⟩
    rcases hq with ⟨_, hqV⟩
    nlinarith [hpV.1, hqV.2]
  have h := c.integral_weight_cauchy_schwarz
  have hprod := mul_le_mul hu hv (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  norm_num at hprod
  exact h.trans hprod

theorem FutureCurve.continuousOn_point {p q : DiamondPoint} (c : FutureCurve p q) :
    ContinuousOn c.point (Icc (0 : ℝ) 1) := by
  have hu : ContinuousOn c.u (Icc (0 : ℝ) 1) := by
    simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using c.uAC.continuousOn
  have hv : ContinuousOn c.v (Icc (0 : ℝ) 1) := by
    simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using c.vAC.continuousOn
  exact hu.prodMk hv

theorem FutureCurve.coefficient_measurable {p q : DiamondPoint} (c : FutureCurve p q)
    {rho : DiamondPoint → ℝ} (hR : InDensityClass rho) :
    AEStronglyMeasurable (fun t => Real.sqrt (2 * rho (c.point t))) curveMeasure := by
  have hCont : ContinuousOn (fun t => rho (c.point t)) (Icc (0 : ℝ) 1) :=
    hR.continuousOn.comp c.continuousOn_point c.inDiamond
  exact Real.continuous_sqrt.comp_aestronglyMeasurable
    ((hCont.aestronglyMeasurable measurableSet_Icc).const_mul 2)

theorem FutureCurve.length_integrand_eq {p q : DiamondPoint} (c : FutureCurve p q)
    {rho : DiamondPoint → ℝ} (hR : InDensityClass rho) :
    (fun t => Real.sqrt (2 * rho (c.point t) * deriv c.u t * deriv c.v t))
      =ᵐ[curveMeasure] (fun t => Real.sqrt (2 * rho (c.point t)) * c.weight t) := by
  filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
  have hPos : 0 ≤ 2 * rho (c.point t) := by
    have hb : 1 / 2 ≤ rho (c.point t) := (hR.bounds _ (c.inDiamond t ht)).1
    linarith
  rw [mul_assoc, Real.sqrt_mul hPos]
  rfl

theorem FutureCurve.integrable_factored_length {p q : DiamondPoint} (c : FutureCurve p q)
    {rho : DiamondPoint → ℝ} (hR : InDensityClass rho) :
    Integrable (fun t => Real.sqrt (2 * rho (c.point t)) * c.weight t) curveMeasure := by
  apply (c.integrable_weight.const_mul (Real.sqrt 3)).mono'
    (c.coefficient_measurable hR |>.mul c.integrable_weight.aestronglyMeasurable)
  filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
  have hb : rho (c.point t) ≤ 3 / 2 := (hR.bounds _ (c.inDiamond t ht)).2
  have hCoef : Real.sqrt (2 * rho (c.point t)) ≤ Real.sqrt 3 :=
    Real.sqrt_le_sqrt (by linarith)
  change ‖Real.sqrt (2 * rho (c.point t)) * c.weight t‖ ≤ Real.sqrt 3 * c.weight t
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (Real.sqrt_nonneg _) (show 0 ≤ c.weight t from Real.sqrt_nonneg _))]
  exact mul_le_mul_of_nonneg_right hCoef (Real.sqrt_nonneg _)

theorem FutureCurve.integrable_length {p q : DiamondPoint} (c : FutureCurve p q)
    {rho : DiamondPoint → ℝ} (hR : InDensityClass rho) :
    Integrable (fun t => Real.sqrt (2 * rho (c.point t) * deriv c.u t * deriv c.v t))
      curveMeasure :=
  (c.integrable_factored_length hR).congr (c.length_integrand_eq hR).symm

theorem FutureCurve.length_eq_factored {p q : DiamondPoint} (c : FutureCurve p q)
    {rho : DiamondPoint → ℝ} (hR : InDensityClass rho) :
    c.length rho = ∫ t, Real.sqrt (2 * rho (c.point t)) * c.weight t ∂curveMeasure :=
  integral_congr_ae (c.length_integrand_eq hR)

theorem FutureCurve.length_nonneg {p q : DiamondPoint} (c : FutureCurve p q)
    (rho : DiamondPoint → ℝ) : 0 ≤ c.length rho := by
  exact integral_nonneg (fun _ => Real.sqrt_nonneg _)

theorem FutureCurve.length_le_sqrt_three {p q : DiamondPoint} (c : FutureCurve p q)
    {rho : DiamondPoint → ℝ} (hR : InDensityClass rho) :
    c.length rho ≤ Real.sqrt 3 := by
  rw [c.length_eq_factored hR]
  have hLe : (∫ t, Real.sqrt (2 * rho (c.point t)) * c.weight t ∂curveMeasure) ≤
      ∫ t, Real.sqrt 3 * c.weight t ∂curveMeasure := by
    apply integral_mono_ae (c.integrable_factored_length hR)
      (c.integrable_weight.const_mul _)
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
    have hb : rho (c.point t) ≤ 3 / 2 := (hR.bounds _ (c.inDiamond t ht)).2
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by linarith))
      (Real.sqrt_nonneg _)
  rw [integral_const_mul] at hLe
  have hBound := mul_le_mul_of_nonneg_left c.integral_weight_le_one (Real.sqrt_nonneg 3)
  simpa using hLe.trans hBound

theorem InDensityClass.abs_sub_le_coefficientDeviation {rho sigma : DiamondPoint → ℝ}
    (hR : InDensityClass rho) (hS : InDensityClass sigma) {p : DiamondPoint}
    (hp : p ∈ diamond) : |rho p - sigma p| ≤ coefficientDeviation rho sigma := by
  apply le_csSup
  · exact (diamond_isCompact.image_of_continuousOn
      (hR.continuousOn.sub hS.continuousOn).abs).bddAbove
  · exact ⟨p, hp, rfl⟩

theorem FutureCurve.length_difference {p q : DiamondPoint} (c : FutureCurve p q)
    {rho sigma : DiamondPoint → ℝ} (hR : InDensityClass rho) (hS : InDensityClass sigma) :
    |c.length rho - c.length sigma| ≤ coefficientDeviation rho sigma := by
  rw [c.length_eq_factored hR, c.length_eq_factored hS,
    ← integral_sub (c.integrable_factored_length hR) (c.integrable_factored_length hS)]
  have hInt : Integrable (fun t => |Real.sqrt (2 * rho (c.point t)) * c.weight t -
      Real.sqrt (2 * sigma (c.point t)) * c.weight t|) curveMeasure :=
    ((c.integrable_factored_length hR).sub (c.integrable_factored_length hS)).abs
  have hBound : (∫ t, |Real.sqrt (2 * rho (c.point t)) * c.weight t -
      Real.sqrt (2 * sigma (c.point t)) * c.weight t| ∂curveMeasure) ≤
      ∫ t, coefficientDeviation rho sigma * c.weight t ∂curveMeasure := by
    apply integral_mono_ae hInt (c.integrable_weight.const_mul _)
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
    have hp := c.inDiamond t ht
    have hCoef := (sqrt_coefficient_lipschitz (hR.bounds _ hp).1
      (hS.bounds _ hp).1).trans (hR.abs_sub_le_coefficientDeviation hS hp)
    rw [← sub_mul, abs_mul, abs_of_nonneg (show 0 ≤ c.weight t from Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_right hCoef (Real.sqrt_nonneg _)
  rw [integral_const_mul] at hBound
  have hDelta := (hR.coefficientDeviation_bounds hS).1
  have hLast := mul_le_mul_of_nonneg_left c.integral_weight_le_one hDelta
  exact abs_integral_le_integral_abs.trans (hBound.trans (by simpa using hLast))

/-- Zero is included so an empty admissible curve class has separation zero. -/
noncomputable def timeSeparation (rho : DiamondPoint → ℝ) (p q : DiamondPoint) : ℝ :=
  sSup (insert 0 (Set.range (fun c : FutureCurve p q => c.length rho)))

theorem InDensityClass.lengths_bddAbove {rho : DiamondPoint → ℝ}
    (hR : InDensityClass rho) (p q : DiamondPoint) :
    BddAbove (insert 0 (Set.range (fun c : FutureCurve p q => c.length rho))) := by
  refine ⟨Real.sqrt 3, ?_⟩
  rintro x (hx | ⟨c, rfl⟩)
  · subst x
    exact Real.sqrt_nonneg (3 : ℝ)
  · exact c.length_le_sqrt_three hR

theorem InDensityClass.timeSeparation_nonneg {rho : DiamondPoint → ℝ}
    (hR : InDensityClass rho) (p q : DiamondPoint) : 0 ≤ timeSeparation rho p q := by
  exact le_csSup (hR.lengths_bddAbove p q) (by simp)

theorem InDensityClass.length_le_timeSeparation {rho : DiamondPoint → ℝ}
    (hR : InDensityClass rho) {p q : DiamondPoint} (c : FutureCurve p q) :
    c.length rho ≤ timeSeparation rho p q := by
  exact le_csSup (hR.lengths_bddAbove p q) (by simp)

theorem timeSeparation_empty (rho : DiamondPoint → ℝ) (p q : DiamondPoint)
    [IsEmpty (FutureCurve p q)] : timeSeparation rho p q = 0 := by
  have hRange : Set.range (fun c : FutureCurve p q => c.length rho) = ∅ := by
    ext x
    constructor
    · rintro ⟨c, _⟩
      exact isEmptyElim c
    · intro h
      exact False.elim h
  simp [timeSeparation, hRange]

theorem InDensityClass.timeSeparation_le_sqrt_three {rho : DiamondPoint → ℝ}
    (hR : InDensityClass rho) (p q : DiamondPoint) :
    timeSeparation rho p q ≤ Real.sqrt 3 := by
  apply csSup_le (by simp : (insert 0 (Set.range
    (fun c : FutureCurve p q => c.length rho))).Nonempty)
  rintro x (hx | ⟨c, rfl⟩)
  · subst x
    exact Real.sqrt_nonneg (3 : ℝ)
  · exact c.length_le_sqrt_three hR

theorem InDensityClass.timeSeparation_le_add {rho sigma : DiamondPoint → ℝ}
    (hR : InDensityClass rho) (hS : InDensityClass sigma) (p q : DiamondPoint) :
    timeSeparation rho p q ≤ timeSeparation sigma p q + coefficientDeviation rho sigma := by
  apply csSup_le (by simp : (insert 0 (Set.range
    (fun c : FutureCurve p q => c.length rho))).Nonempty)
  rintro x (hx | ⟨c, rfl⟩)
  · have hSep := hS.timeSeparation_nonneg p q
    have hDelta := (hR.coefficientDeviation_bounds hS).1
    simp only [hx]
    linarith
  · have hLen := (abs_le.mp (c.length_difference hR hS)).2
    have hSep := hS.length_le_timeSeparation c
    linarith

theorem coefficientDeviation_symm (rho sigma : DiamondPoint → ℝ) :
    coefficientDeviation sigma rho = coefficientDeviation rho sigma := by
  have hfun : (fun p => |sigma p - rho p|) = (fun p => |rho p - sigma p|) :=
    funext (fun p => abs_sub_comm (sigma p) (rho p))
  unfold coefficientDeviation
  rw [hfun]

theorem InDensityClass.timeSeparation_difference {rho sigma : DiamondPoint → ℝ}
    (hR : InDensityClass rho) (hS : InDensityClass sigma) (p q : DiamondPoint) :
    |timeSeparation rho p q - timeSeparation sigma p q| ≤ coefficientDeviation rho sigma := by
  have hA := hR.timeSeparation_le_add hS p q
  have hB := hS.timeSeparation_le_add hR p q
  rw [coefficientDeviation_symm] at hB
  exact abs_le.mpr ⟨by linarith, by linarith⟩

def FutureCurve.transpose {p q : DiamondPoint} (c : FutureCurve p q) :
    FutureCurve (transposePoint p) (transposePoint q) where
  u := c.v
  v := c.u
  uAC := c.vAC
  vAC := c.uAC
  startU := c.startV
  startV := c.startU
  endU := c.endV
  endV := c.endU
  inDiamond := fun t ht => (transposePoint_mem_diamond _).mpr (c.inDiamond t ht)
  futureU := c.futureV
  futureV := c.futureU

theorem FutureCurve.transpose_length {p q : DiamondPoint} (c : FutureCurve p q)
    (rho : DiamondPoint → ℝ) : c.transpose.length rho = c.length (transposeDensity rho) := by
  unfold FutureCurve.length
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp [FutureCurve.transpose, FutureCurve.point, transposeDensity, transposePoint]
  congr 1
  ring

theorem InDensityClass.timeSeparation_transpose_le {rho : DiamondPoint → ℝ}
    (hR : InDensityClass rho) (p q : DiamondPoint) :
    timeSeparation (transposeDensity rho) p q ≤
      timeSeparation rho (transposePoint p) (transposePoint q) := by
  apply csSup_le (by simp : (insert 0 (Set.range
    (fun c : FutureCurve p q => c.length (transposeDensity rho)))).Nonempty)
  rintro x (hx | ⟨c, rfl⟩)
  · simpa [hx] using hR.timeSeparation_nonneg (transposePoint p) (transposePoint q)
  · exact (c.transpose_length rho).symm.le.trans (hR.length_le_timeSeparation c.transpose)

theorem InDensityClass.timeSeparation_transpose {rho : DiamondPoint → ℝ}
    (hR : InDensityClass rho) (p q : DiamondPoint) :
    timeSeparation (transposeDensity rho) p q =
      timeSeparation rho (transposePoint p) (transposePoint q) := by
  apply le_antisymm (hR.timeSeparation_transpose_le p q)
  have h := hR.transpose.timeSeparation_transpose_le (transposePoint p) (transposePoint q)
  simpa [transposeDensity_involutive, transposePoint] using h

def alignedPoint (swap : Bool) (p : DiamondPoint) : DiamondPoint :=
  if swap then transposePoint p else p

/-- One orientation is chosen for every endpoint pair simultaneously. -/
theorem InDensityClass.proper_time_conformalDistance {rho sigma : DiamondPoint → ℝ}
    (hR : InDensityClass rho) (hS : InDensityClass sigma) :
    ∃ swap : Bool, ∀ p q : DiamondPoint,
      |timeSeparation rho p q - timeSeparation sigma (alignedPoint swap p)
        (alignedPoint swap q)| ≤ conformalDistance rho sigma := by
  by_cases h : coefficientDeviation rho sigma ≤ coefficientDeviation rho (transposeDensity sigma)
  · refine ⟨false, ?_⟩
    intro p q
    simpa [alignedPoint, conformalDistance, min_eq_left h] using
      hR.timeSeparation_difference hS p q
  · refine ⟨true, ?_⟩
    intro p q
    have hTime := hR.timeSeparation_difference hS.transpose p q
    rw [hS.timeSeparation_transpose] at hTime
    have hReverse : coefficientDeviation rho (transposeDensity sigma) ≤
        coefficientDeviation rho sigma := le_of_lt (lt_of_not_ge h)
    simpa [alignedPoint, conformalDistance, min_eq_right hReverse] using hTime

theorem InDensityClass.proper_time_inverse_unlabeled {rho sigma : DiamondPoint → ℝ}
    (hR : InDensityClass rho) (hS : InDensityClass sigma) {N : ℕ} (hN : 2 ≤ N) :
    ∃ swap : Bool, ∀ p q : DiamondPoint,
      |timeSeparation rho p q - timeSeparation sigma (alignedPoint swap p)
        (alignedPoint swap q)| ≤
      100 * ((N : ℝ) ^ (-1 / 12 : ℝ) + unlabeledFiniteLawDiscrepancy rho sigma N) := by
  obtain ⟨swap, hTime⟩ := hR.proper_time_conformalDistance hS
  exact ⟨swap, fun p q => (hTime p q).trans (hR.full_inverse_unlabeled hS hN)⟩

theorem InDensityClass.proper_time_logarithmic_unlabeled {rho sigma : DiamondPoint → ℝ}
    (hR : InDensityClass rho) (hS : InDensityClass sigma) {N : ℕ} (hN : 2 ≤ N) :
    ∃ swap : Bool, ∀ p q : DiamondPoint,
      |timeSeparation rho p q - timeSeparation sigma (alignedPoint swap p)
        (alignedPoint swap q)| ≤
      130 * ((Real.log (N : ℝ) / N) ^ (1 / 6 : ℝ) +
        unlabeledFiniteLawDiscrepancy rho sigma N) := by
  obtain ⟨swap, hTime⟩ := hR.proper_time_conformalDistance hS
  exact ⟨swap, fun p q => (hTime p q).trans (hR.full_inverse_logarithmic_unlabeled hS hN)⟩

#print axioms FutureCurve.integral_derivU
#print axioms sqrt_coefficient_lipschitz
#print axioms FutureCurve.integral_weight_cauchy_schwarz
#print axioms FutureCurve.length_difference
#print axioms InDensityClass.proper_time_conformalDistance
#print axioms InDensityClass.proper_time_logarithmic_unlabeled

end QuantyraNullCone
