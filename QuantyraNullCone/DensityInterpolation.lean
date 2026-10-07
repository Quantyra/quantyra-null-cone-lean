import QuantyraNullCone.DensityCDF
import Mathlib.Topology.Order.Compact

namespace QuantyraNullCone

open MeasureTheory

theorem InDensityClass.rectangle_mass_cdf {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    (densityMeasure rho).real (Set.Ioc a b ×ˢ Set.Ioc c d) =
      populationCDF rho b d - populationCDF rho a d -
        populationCDF rho b c + populationCDF rho a c := by
  letI : IsProbabilityMeasure (densityMeasure rho) := h.isProbabilityMeasure
  let R := cdfRegion b d
  let A := cdfRegion a d
  let B := cdfRegion b c
  have hSub : A ∪ B ⊆ R := by
    intro q hq
    rcases hq with hq | hq
    · exact ⟨hq.1.trans hab, hq.2⟩
    · exact ⟨hq.1, hq.2.trans hcd⟩
  have hCap : A ∩ B = cdfRegion a c := by
    ext q
    constructor
    · intro hq
      exact ⟨hq.1.1, hq.2.2⟩
    · intro hq
      exact ⟨⟨hq.1, hq.2.trans hcd⟩, ⟨hq.1.trans hab, hq.2⟩⟩
  have hDiffSet : R \ (A ∪ B) = Set.Ioc a b ×ˢ Set.Ioc c d := by
    ext q
    constructor
    · rintro ⟨hq, hNot⟩
      exact ⟨⟨lt_of_not_ge (fun ha => hNot (Or.inl ⟨ha, hq.2⟩)), hq.1⟩,
        ⟨lt_of_not_ge (fun hc => hNot (Or.inr ⟨hq.1, hc⟩)), hq.2⟩⟩
    · rintro ⟨hx, hy⟩
      refine ⟨⟨hx.2, hy.2⟩, ?_⟩
      rintro (hq | hq)
      · exact (not_le_of_gt hx.1) hq.1
      · exact (not_le_of_gt hy.1) hq.2
  have hA : MeasurableSet A := cdfRegion_measurableSet a d
  have hB : MeasurableSet B := cdfRegion_measurableSet b c
  have hDiff := measureReal_diff (μ := densityMeasure rho) hSub (hA.union hB)
  have hUnion := measureReal_union_add_inter (μ := densityMeasure rho) (s := A) hB
  rw [hDiffSet] at hDiff
  rw [hCap] at hUnion
  change (densityMeasure rho).real (Set.Ioc a b ×ˢ Set.Ioc c d) =
    (densityMeasure rho).real R - (densityMeasure rho).real A -
      (densityMeasure rho).real B + (densityMeasure rho).real (cdfRegion a c)
  linarith only [hDiff, hUnion]

theorem InDensityClass.densityMeasure_real_subset {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) {S : Set DiamondPoint} (hS : MeasurableSet S) (hSub : S ⊆ diamond) :
    (densityMeasure rho).real S = ∫ q in S, rho q ∂(volume : Measure ℝ).prod volume := by
  change (densityMeasure rho S).toReal = ∫ q in S, rho q ∂(volume : Measure ℝ).prod volume
  rw [h.densityMeasure_real_apply hS, diamondVolume, Measure.restrict_restrict_of_subset hSub]

theorem InDensityClass.coefficientDeviation_attained {rho sigma : DiamondPoint → ℝ}
    (hR : InDensityClass rho) (hS : InDensityClass sigma) :
    ∃ p ∈ diamond, coefficientDeviation rho sigma = |rho p - sigma p| := by
  have hNonempty : diamond.Nonempty := ⟨(0, 0), by constructor <;> constructor <;> norm_num⟩
  have hCont : ContinuousOn (fun p => |rho p - sigma p|) diamond :=
    (hR.continuousOn.sub hS.continuousOn).abs
  obtain ⟨p, hp, hMax⟩ := diamond_isCompact.exists_isMaxOn hNonempty hCont
  have hGreat : IsGreatest ((fun q => |rho q - sigma q|) '' diamond) |rho p - sigma p| := by
    refine ⟨⟨p, hp, rfl⟩, ?_⟩
    rintro y ⟨q, hq, rfl⟩
    exact hMax hq
  exact ⟨p, hp, hGreat.csSup_eq⟩

theorem interval_difference_bound {a w p q : ℝ} (hp : p ∈ Set.Icc a (a + w))
    (hq : q ∈ Set.Ioc a (a + w)) : |q - p| ≤ w := by
  apply abs_le.mpr
  constructor <;> linarith [hp.1, hp.2, hq.1, hq.2]

theorem boundary_interval {p w : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    0 ≤ min p (1 - w) ∧ min p (1 - w) + w ≤ 1 ∧
      p ∈ Set.Icc (min p (1 - w)) (min p (1 - w) + w) := by
  refine ⟨le_min hp.1 (by linarith), ?_, ⟨min_le_left _ _, ?_⟩⟩
  · linarith [min_le_right p (1 - w)]
  · by_cases h : p ≤ 1 - w
    · rw [min_eq_left h]
      linarith
    · rw [min_eq_right (le_of_not_ge h)]
      linarith [hp.2]

theorem signed_density_square_lower {rho sigma : DiamondPoint → ℝ}
    (hR : InDensityClass rho) (hS : InDensityClass sigma) {p : DiamondPoint} (hp : p ∈ diamond)
    {delta : ℝ} (hd : 0 < delta) (hValue : rho p - sigma p = delta) :
    let w := delta / 16
    let a := min p.1 (1 - w)
    let c := min p.2 (1 - w)
    delta ^ 3 / 512 ≤ (densityMeasure rho).real (Set.Ioc a (a + w) ×ˢ Set.Ioc c (c + w)) -
      (densityMeasure sigma).real (Set.Ioc a (a + w) ×ˢ Set.Ioc c (c + w)) := by
  dsimp
  let w := delta / 16
  let a := min p.1 (1 - w)
  let c := min p.2 (1 - w)
  let Q : Set DiamondPoint := Set.Ioc a (a + w) ×ˢ Set.Ioc c (c + w)
  let V : Measure DiamondPoint := (volume : Measure ℝ).prod volume
  have hw : 0 < w := by dsimp [w]; positivity
  have hd1 : delta ≤ 1 := by linarith [(hR.bounds p hp).2, (hS.bounds p hp).1]
  have hw1 : w ≤ 1 := by dsimp [w]; linarith
  obtain ⟨ha0, ha1, hpA⟩ := boundary_interval hp.1 hw.le hw1
  obtain ⟨hc0, hc1, hpC⟩ := boundary_interval hp.2 hw.le hw1
  have hQM : MeasurableSet Q := measurableSet_Ioc.prod measurableSet_Ioc
  have hQD : Q ⊆ diamond := by
    intro q hq
    exact ⟨⟨ha0.trans hq.1.1.le, hq.1.2.trans ha1⟩,
      ⟨hc0.trans hq.2.1.le, hq.2.2.trans hc1⟩⟩
  have hLower : ∀ q ∈ Q, delta / 2 ≤ rho q - sigma q := by
    intro q hq
    have hX := interval_difference_bound hpA hq.1
    have hY := interval_difference_bound hpC hq.2
    have hXSq : (q.1 - p.1) ^ 2 ≤ w ^ 2 := by
      have ht := mul_nonneg (show 0 ≤ w - (q.1 - p.1) by linarith [(abs_le.mp hX).2])
        (show 0 ≤ w + (q.1 - p.1) by linarith [(abs_le.mp hX).1])
      nlinarith only [ht]
    have hYSq : (q.2 - p.2) ^ 2 ≤ w ^ 2 := by
      have ht := mul_nonneg (show 0 ≤ w - (q.2 - p.2) by linarith [(abs_le.mp hY).2])
        (show 0 ≤ w + (q.2 - p.2) by linarith [(abs_le.mp hY).1])
      nlinarith only [ht]
    have hDist : Real.sqrt ((q.1 - p.1)^2 + (q.2 - p.2)^2) ≤ 2 * w :=
      Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith [sq_nonneg w]⟩
    have hRho := (abs_le.mp (hR.lipschitz q (hQD hq) p hp)).1
    have hSigma := (abs_le.mp (hS.lipschitz q (hQD hq) p hp)).2
    dsimp [w] at hDist
    linarith
  have hArea : V Q = ENNReal.ofReal (w ^ 2) := by
    change ((volume : Measure ℝ).prod volume) (Set.Ioc a (a + w) ×ˢ Set.Ioc c (c + w)) = _
    rw [Measure.prod_prod, Real.volume_Ioc, Real.volume_Ioc]
    simp only [add_sub_cancel_left]
    rw [← ENNReal.ofReal_mul hw.le]
    congr 1
    ring
  letI : IsFiniteMeasure (V.restrict Q) := ⟨by rw [Measure.restrict_apply_univ, hArea]; finiteness⟩
  have hRI : IntegrableOn rho Q V :=
    (show IntegrableOn rho diamond V from hR.integrable).mono_set hQD
  have hSI : IntegrableOn sigma Q V :=
    (show IntegrableOn sigma diamond V from hS.integrable).mono_set hQD
  have hCompare : (∫ _q in Q, delta / 2 ∂V) ≤ ∫ q in Q, rho q - sigma q ∂V :=
    integral_mono_ae (integrable_const _) (hRI.sub hSI)
      ((ae_restrict_mem hQM).mono fun q hq => hLower q hq)
  rw [setIntegral_const, Measure.real, hArea, ENNReal.toReal_ofReal (sq_nonneg w),
    smul_eq_mul, integral_sub hRI hSI] at hCompare
  rw [← hR.densityMeasure_real_subset hQM hQD, ← hS.densityMeasure_real_subset hQM hQD] at hCompare
  change delta ^ 3 / 512 ≤ (densityMeasure rho).real Q - (densityMeasure sigma).real Q
  dsimp [w] at hCompare
  nlinarith only [hCompare]

theorem InDensityClass.coefficient_interpolation {rho sigma : DiamondPoint → ℝ}
    (hR : InDensityClass rho) (hS : InDensityClass sigma) {epsilon : ℝ}
    (hCDF : ∀ s t : ℝ, |populationCDF rho s t - populationCDF sigma s t| ≤ epsilon) :
    coefficientDeviation rho sigma ^ 3 ≤ 2048 * epsilon := by
  obtain ⟨p, hp, hValue⟩ := hR.coefficientDeviation_attained hS
  let delta := coefficientDeviation rho sigma
  have hd0 : 0 ≤ delta := by rw [show delta = |rho p - sigma p| from hValue]; positivity
  have he : 0 ≤ epsilon := (abs_nonneg _).trans (hCDF 0 0)
  by_cases hd : delta = 0
  · change delta ^ 3 ≤ _
    rw [hd]
    simpa using (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2048) he)
  have hdPos : 0 < delta := lt_of_le_of_ne hd0 (Ne.symm hd)
  let w := delta / 16
  let a := min p.1 (1 - w)
  let c := min p.2 (1 - w)
  have hw : 0 < w := by dsimp [w]; positivity
  have hQuadR := hR.rectangle_mass_cdf (a := a) (b := a + w) (c := c) (d := c + w)
    (by linarith) (by linarith)
  have hQuadS := hS.rectangle_mass_cdf (a := a) (b := a + w) (c := c) (d := c + w)
    (by linarith) (by linarith)
  have hCornerBD := abs_le.mp (hCDF (a + w) (c + w))
  have hCornerAD := abs_le.mp (hCDF a (c + w))
  have hCornerBC := abs_le.mp (hCDF (a + w) c)
  have hCornerAC := abs_le.mp (hCDF a c)
  have hCube : delta ^ 3 / 512 ≤ 4 * epsilon := by
    by_cases hSign : 0 ≤ rho p - sigma p
    · have hSigned : rho p - sigma p = delta := by
        rw [show delta = |rho p - sigma p| from hValue, abs_of_nonneg hSign]
      have hLower := signed_density_square_lower hR hS hp hdPos hSigned
      change delta ^ 3 / 512 ≤ (densityMeasure rho).real (Set.Ioc a (a + w) ×ˢ Set.Ioc c (c + w)) -
        (densityMeasure sigma).real (Set.Ioc a (a + w) ×ˢ Set.Ioc c (c + w)) at hLower
      rw [hQuadR, hQuadS] at hLower
      linarith only [hLower, hCornerBD.2, hCornerAD.1, hCornerBC.1, hCornerAC.2]
    · have hSigned : sigma p - rho p = delta := by
        rw [show delta = |rho p - sigma p| from hValue, abs_of_neg (lt_of_not_ge hSign)]
        ring
      have hLower := signed_density_square_lower hS hR hp hdPos hSigned
      change delta ^ 3 / 512 ≤ (densityMeasure sigma).real (Set.Ioc a (a + w) ×ˢ Set.Ioc c (c + w)) -
        (densityMeasure rho).real (Set.Ioc a (a + w) ×ˢ Set.Ioc c (c + w)) at hLower
      rw [hQuadS, hQuadR] at hLower
      linarith only [hLower, hCornerBD.1, hCornerAD.2, hCornerBC.2, hCornerAC.1]
  change delta ^ 3 ≤ _
  linarith only [hCube]

#print axioms InDensityClass.rectangle_mass_cdf
#print axioms InDensityClass.coefficientDeviation_attained
#print axioms InDensityClass.coefficient_interpolation

end QuantyraNullCone
