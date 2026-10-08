import QuantyraNullCone.DensityCells

namespace QuantyraNullCone

open MeasureTheory

/-- Chord majorant of distance to any point of a closed interval. -/
noncomputable def cellChord (a w p x : ℝ) : ℝ := (p - a) + (1 - 2 * (p - a) / w) * (x - a)

theorem cell_chord_continuous (a w p : ℝ) : Continuous (cellChord a w p) :=
  continuous_const.add (continuous_const.mul (continuous_id.sub continuous_const))

theorem cell_chord_distance {a w p x : ℝ} (hw : 0 < w)
    (hp : p ∈ Set.Icc a (a + w)) (hx : x ∈ Set.Icc a (a + w)) :
    |x - p| ≤ cellChord a w p x := by
  have hMul : w * cellChord a w p x = w * (p - a) + (w - 2 * (p - a)) * (x - a) := by
    unfold cellChord
    field_simp [hw.ne']
  apply (mul_le_mul_iff_right₀ hw).mp
  rw [hMul]
  rcases le_total p x with hpx | hxp
  · rw [abs_of_nonneg (sub_nonneg.mpr hpx)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hp.1) (sub_nonneg.mpr hx.2)]
  · rw [abs_of_nonpos (sub_nonpos.mpr hxp)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hp.2) (sub_nonneg.mpr hx.1)]

theorem cell_chord_integral {a w p : ℝ} (hw : 0 < w) :
    (∫ x in a..a + w, cellChord a w p x) = w ^ 2 / 2 := by
  have hShift : (∫ x in a..a + w, x - a) = w ^ 2 / 2 := by
    rw [intervalIntegral.integral_sub (f := fun x : ℝ => x) (g := fun _ : ℝ => a) (μ := volume)
        (continuous_id.intervalIntegrable a (a + w))
        (continuous_const.intervalIntegrable a (a + w)),
      integral_id, intervalIntegral.integral_const]
    simp only [smul_eq_mul, add_sub_cancel_left]
    ring
  unfold cellChord
  rw [intervalIntegral.integral_add (f := fun _ : ℝ => p - a)
      (g := fun x : ℝ => (1 - 2 * (p - a) / w) * (x - a)) (μ := volume)
      (continuous_const.intervalIntegrable a (a + w))
      ((continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable a (a + w)),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, hShift]
  simp only [smul_eq_mul, add_sub_cancel_left]
  field_simp [hw.ne']
  ring

noncomputable def cellMajorant (a c w : ℝ) (p q : DiamondPoint) : ℝ :=
  2 * (cellChord a w p.1 q.1 + cellChord c w p.2 q.2)

theorem cell_majorant_continuous (a c w : ℝ) (p : DiamondPoint) :
    Continuous (cellMajorant a c w p) :=
  continuous_const.mul (((cell_chord_continuous a w p.1).comp continuous_fst).add
    ((cell_chord_continuous c w p.2).comp continuous_snd))

theorem cell_majorant_integrable (a c w : ℝ) (p : DiamondPoint) :
    IntegrableOn (cellMajorant a c w p) (squareCell a c w) ((volume : Measure ℝ).prod volume) :=
  ((cell_majorant_continuous a c w p).continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)).mono_set (square_cell_subset_closed a c w)

theorem cell_majorant_integral {a c w : ℝ} (hw : 0 < w) (p : DiamondPoint) :
    (∫ q in squareCell a c w, cellMajorant a c w p q ∂(volume : Measure ℝ).prod volume) =
      2 * w ^ 3 := by
  rw [squareCell, setIntegral_prod _ (cell_majorant_integrable a c w p)]
  rw [← intervalIntegral.integral_of_le (by linarith : a ≤ a + w)]
  have hInner : ∀ x : ℝ, (∫ y in Set.Ioc c (c + w), cellMajorant a c w p (x, y)) =
      2 * (w * cellChord a w p.1 x + w ^ 2 / 2) := by
    intro x
    rw [← intervalIntegral.integral_of_le (by linarith : c ≤ c + w)]
    unfold cellMajorant
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (f := fun _ : ℝ => cellChord a w p.1 x)
        (g := cellChord c w p.2) (μ := volume)
        (continuous_const.intervalIntegrable c (c + w))
        ((cell_chord_continuous c w p.2).intervalIntegrable c (c + w)),
      intervalIntegral.integral_const, cell_chord_integral hw]
    simp only [smul_eq_mul, add_sub_cancel_left]
  simp_rw [hInner]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (f := fun x : ℝ => w * cellChord a w p.1 x)
      (g := fun _ : ℝ => w ^ 2 / 2) (μ := volume)
      ((continuous_const.mul (cell_chord_continuous a w p.1)).intervalIntegrable a (a + w))
      (continuous_const.intervalIntegrable a (a + w)),
    intervalIntegral.integral_const_mul, cell_chord_integral hw, intervalIntegral.integral_const]
  simp only [smul_eq_mul, add_sub_cancel_left]
  ring

theorem InDensityClass.cell_majorant_bound {rho : DiamondPoint → ℝ} (h : InDensityClass rho)
    {a c w : ℝ} (hw : 0 < w) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (haw : a + w ≤ 1) (hcw : c + w ≤ 1)
    {p q : DiamondPoint} (hp : p ∈ closedSquareCell a c w) (hq : q ∈ squareCell a c w) :
    |rho q - rho p| ≤ cellMajorant a c w p q := by
  have hSub := closed_square_cell_subset ha hc haw hcw
  have hqc := square_cell_subset_closed a c w hq
  have hX := cell_chord_distance hw hp.1 hqc.1
  have hY := cell_chord_distance hw hp.2 hqc.2
  have hEuclid : Real.sqrt ((q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2) ≤
      |q.1 - p.1| + |q.2 - p.2| := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    nlinarith [sq_abs (q.1 - p.1), sq_abs (q.2 - p.2),
      mul_nonneg (abs_nonneg (q.1 - p.1)) (abs_nonneg (q.2 - p.2))]
  have hLip := h.lipschitz q (hSub hqc) p (hSub hp)
  unfold cellMajorant
  linarith

/-- The 2w pointwise expansion holds at EVERY point of the closed cell, including corners. -/
theorem InDensityClass.cell_mean_point_bias {rho : DiamondPoint → ℝ} (h : InDensityClass rho)
    {a c w : ℝ} (hw : 0 < w) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (haw : a + w ≤ 1) (hcw : c + w ≤ 1)
    {p : DiamondPoint} (hp : p ∈ closedSquareCell a c w) :
    |densityCellMean rho a c w - rho p| ≤ 2 * w := by
  let Q := squareCell a c w
  let V : Measure DiamondPoint := (volume : Measure ℝ).prod volume
  have hQM : MeasurableSet Q := square_cell_measurable a c w
  have hSub : Q ⊆ diamond := (square_cell_subset_closed a c w).trans
    (closed_square_cell_subset ha hc haw hcw)
  have hArea : V Q = ENNReal.ofReal (w ^ 2) := square_cell_volume hw.le
  letI : IsFiniteMeasure (V.restrict Q) := ⟨by rw [Measure.restrict_apply_univ, hArea]; finiteness⟩
  have hInt : IntegrableOn rho Q V := h.cell_integrable ha hc haw hcw
  have hConst : IntegrableOn (fun _q : DiamondPoint => rho p) Q V := integrable_const _
  have hCompare : (∫ q in Q, |rho q - rho p| ∂V) ≤ ∫ q in Q, cellMajorant a c w p q ∂V :=
    integral_mono_ae (hInt.sub hConst).abs (cell_majorant_integrable a c w p)
      ((ae_restrict_mem hQM).mono fun q hq => h.cell_majorant_bound hw ha hc haw hcw hp hq)
  have hAbs : |∫ q in Q, rho q - rho p ∂V| ≤ 2 * w ^ 3 :=
    abs_integral_le_integral_abs.trans (hCompare.trans_eq (cell_majorant_integral hw p))
  have hIdentity : (∫ q in Q, rho q - rho p ∂V) =
      w ^ 2 * (densityCellMean rho a c w - rho p) := by
    rw [integral_sub hInt hConst, setIntegral_const, Measure.real, hArea,
      ENNReal.toReal_ofReal (sq_nonneg w), smul_eq_mul,
      ← h.densityMeasure_real_subset hQM hSub]
    unfold densityCellMean
    field_simp [hw.ne']
    ring
  rw [hIdentity, abs_mul, abs_of_nonneg (sq_nonneg w)] at hAbs
  have hRight : 2 * w ^ 3 = w ^ 2 * (2 * w) := by ring
  rw [hRight] at hAbs
  exact (mul_le_mul_iff_right₀ (sq_pos_of_pos hw)).mp hAbs

#print axioms cell_chord_distance
#print axioms cell_chord_integral
#print axioms cell_majorant_integral
#print axioms InDensityClass.cell_mean_point_bias

end QuantyraNullCone
