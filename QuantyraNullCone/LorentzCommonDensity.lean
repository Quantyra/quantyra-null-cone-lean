import QuantyraNullCone.LorentzQuotientMeasure
import QuantyraNullCone.CommonMeasureCoupling

namespace QuantyraNullCone
open MeasureTheory Set
noncomputable section

def commonDensityMeasure3 (rho sigma : LorentzPoint3 → ℝ) : Measure ClosedLorentzPoint3 :=
  closedDensityMeasure3 (fun p => min (rho p) (sigma p))

theorem common_density_le_left3 (rho sigma : LorentzPoint3 → ℝ) :
    commonDensityMeasure3 rho sigma ≤ closedDensityMeasure3 rho := by
  have h : densityMeasure3 (fun p => min (rho p) (sigma p)) ≤ densityMeasure3 rho :=
    withDensity_mono (Filter.Eventually.of_forall fun p => ENNReal.ofReal_le_ofReal (min_le_left _ _))
  intro s
  change closedDensityMeasure3 (fun p => min (rho p) (sigma p)) s ≤ closedDensityMeasure3 rho s
  rw [closedDensityMeasure3_apply,closedDensityMeasure3_apply]
  exact h (Subtype.val '' s)

theorem common_density_le_right3 (rho sigma : LorentzPoint3 → ℝ) :
    commonDensityMeasure3 rho sigma ≤ closedDensityMeasure3 sigma := by
  have h : densityMeasure3 (fun p => min (rho p) (sigma p)) ≤ densityMeasure3 sigma :=
    withDensity_mono (Filter.Eventually.of_forall fun p => ENNReal.ofReal_le_ofReal (min_le_right _ _))
  intro s
  change closedDensityMeasure3 (fun p => min (rho p) (sigma p)) s ≤ closedDensityMeasure3 sigma s
  rw [closedDensityMeasure3_apply,closedDensityMeasure3_apply]
  exact h (Subtype.val '' s)

theorem closed_density_univ3 (rho : LorentzPoint3 → ℝ) :
    closedDensityMeasure3 rho univ = densityMeasure3 rho univ := by
  have h := congrArg (fun m : Measure LorentzPoint3 => m univ) (closedDensityMeasure3_map_val rho)
  simpa only [Measure.map_apply measurable_subtype_coe MeasurableSet.univ,preimage_univ] using h

theorem common_density_integral_lower3 {rho sigma : LorentzPoint3 → ℝ}
    (hR : InDensityClass3 rho) (hS : InDensityClass3 sigma) {delta : ℝ}
    (hc : ∀ p ∈ closedLorentzDiamond3, |rho p - sigma p| ≤ delta) :
    1 - delta / 2 ≤ ∫ p, min (rho p) (sigma p) ∂flatDiamondMeasure3 := by
  letI := flat_diamond_probability3
  have hmin : Integrable (fun p => min (rho p) (sigma p)) flatDiamondMeasure3 :=
    hR.integrable.inf hS.integrable
  have hlin : Integrable (fun p => (rho p + sigma p - delta) / 2) flatDiamondMeasure3 :=
    ((hR.integrable.add hS.integrable).sub (integrable_const delta)).div_const 2
  have hlo : (fun p => (rho p + sigma p - delta) / 2) ≤ᵐ[flatDiamondMeasure3]
      (fun p => min (rho p) (sigma p)) := by
    filter_upwards [flat_diamond3_ae_mem] with p hp
    have h := abs_le.mp (hc p hp)
    rcases le_total (rho p) (sigma p) with he | he
    · rw [min_eq_left he]; linarith
    · rw [min_eq_right he]; linarith
  have he : (∫ p, (rho p + sigma p - delta) / 2 ∂flatDiamondMeasure3) = 1 - delta / 2 := by
    have ha : Integrable (fun p => rho p + sigma p) flatDiamondMeasure3 :=
      hR.integrable.add hS.integrable
    rw [integral_div,integral_sub ha (integrable_const delta),
      integral_add hR.integrable hS.integrable,hR.normalized,hS.normalized]
    simp
    ring
  rw [← he]
  exact integral_mono_ae hlin hmin hlo

theorem common_density_mass3 {rho sigma : LorentzPoint3 → ℝ}
    (hR : InDensityClass3 rho) (hS : InDensityClass3 sigma) :
    commonDensityMeasure3 rho sigma univ =
      ENNReal.ofReal (∫ p, min (rho p) (sigma p) ∂flatDiamondMeasure3) := by
  have hi : Integrable (fun p => min (rho p) (sigma p)) flatDiamondMeasure3 :=
    hR.integrable.inf hS.integrable
  have hn : 0 ≤ᵐ[flatDiamondMeasure3] (fun p => min (rho p) (sigma p)) := by
    filter_upwards [flat_diamond3_ae_mem] with p hp
    change (0 : ℝ) ≤ min (rho p) (sigma p)
    exact le_min (by linarith [(hR.bounds p hp).1]) (by linarith [(hS.bounds p hp).1])
  rw [commonDensityMeasure3,closed_density_univ3,densityMeasure3,
    withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi hn]

theorem common_density_missing_mass3 {rho sigma : LorentzPoint3 → ℝ}
    (hR : InDensityClass3 rho) (hS : InDensityClass3 sigma) {delta : ℝ} (hd : 0 ≤ delta)
    (hc : ∀ p ∈ closedLorentzDiamond3, |rho p - sigma p| ≤ delta) :
    1 - commonDensityMeasure3 rho sigma univ ≤ ENNReal.ofReal (delta / 2) := by
  have hl := common_density_integral_lower3 hR hS hc
  have hi : 0 ≤ ∫ p, min (rho p) (sigma p) ∂flatDiamondMeasure3 := by
    apply integral_nonneg_of_ae
    filter_upwards [flat_diamond3_ae_mem] with p hp
    change (0 : ℝ) ≤ min (rho p) (sigma p)
    exact le_min (by linarith [(hR.bounds p hp).1]) (by linarith [(hS.bounds p hp).1])
  apply tsub_le_iff_right.mpr
  rw [common_density_mass3 hR hS,← ENNReal.ofReal_add (by positivity) hi]
  simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal
    (show 1 ≤ delta / 2 + ∫ p, min (rho p) (sigma p) ∂flatDiamondMeasure3 by linarith)

#print axioms common_density_le_left3
#print axioms common_density_le_right3
#print axioms closed_density_univ3
#print axioms common_density_integral_lower3
#print axioms common_density_mass3
#print axioms common_density_missing_mass3

end
end QuantyraNullCone
