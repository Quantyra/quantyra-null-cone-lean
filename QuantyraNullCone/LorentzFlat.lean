import QuantyraNullCone.LorentzVolume
import QuantyraNullCone.LorentzChronology
import QuantyraNullCone.LorentzGaugeLipschitz
import QuantyraNullCone.LorentzDerivative
import QuantyraNullCone.LorentzSpatialDistance

namespace QuantyraNullCone

open MeasureTheory

noncomputable section

theorem flat_diamond_measure_mass3 : flatDiamondMeasure3 Set.univ = 1 := by
  simp only [flatDiamondMeasure3, Measure.smul_apply, Measure.restrict_apply_univ,
    lorentz_diamond_volume3, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr lorentz_volume_pos3)
    ENNReal.ofReal_ne_top

theorem flat_diamond_probability3 : IsProbabilityMeasure flatDiamondMeasure3 :=
  ⟨flat_diamond_measure_mass3⟩

theorem flat_density_class3 : InDensityClass3 flatDensity3 := by
  letI := flat_diamond_probability3
  constructor
  · exact ⟨Set.univ, isOpen_univ, Set.subset_univ _, contDiffOn_const⟩
  · intro p hp
    norm_num [flatDensity3]
  · intro p hp q hq
    simp only [flatDensity3, sub_self, abs_zero]
    positivity
  · simp [flatDensity3]

theorem sampledOrder3_flow_eq {a : ℝ} (ha : |a| < 1) {n : ℕ}
    (w : Fin n → LorentzPoint3) (hw : ∀ i, w i ∈ closedLorentzDiamond3) :
    sampledOrder3 (fun i => lorentzFlow3 a (w i)) = sampledOrder3 w := by
  classical
  funext i j
  simp only [sampledOrder3, lorentz_flow_chronological_iff3 ha (hw i) (hw j)]

#print axioms flat_diamond_measure_mass3
#print axioms flat_density_class3
#print axioms sampledOrder3_flow_eq

end

end QuantyraNullCone
