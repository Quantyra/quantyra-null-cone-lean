import QuantyraNullCone.DegreeFilter
import QuantyraNullCone.DensityInterpolation

namespace QuantyraNullCone

open MeasureTheory

theorem InDensityClass.densityMeasure_ceiling {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) : densityMeasure rho ≤
      (ENNReal.ofReal (3 / 2 : ℝ)) • diamondVolume := by
  rw [densityMeasure, ← withDensity_const]
  apply withDensity_mono
  exact (ae_restrict_mem diamond_measurableSet).mono fun p hp =>
    ENNReal.ofReal_le_ofReal (h.bounds p hp).2

/-- Actual fixed rectangle masses, for both the degree filter and its later
variance-sensitive concentration argument. -/
theorem InDensityClass.rectangle_mass_bounds {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) {a b c d : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (hc : 0 ≤ c) (hcd : c ≤ d) (hd : d ≤ 1) :
    (b - a) * (d - c) / 2 ≤ (densityMeasure rho).real (Set.Ioc a b ×ˢ Set.Ioc c d) ∧
      (densityMeasure rho).real (Set.Ioc a b ×ˢ Set.Ioc c d) ≤
        (3 / 2 : ℝ) * (b - a) * (d - c) := by
  letI : IsProbabilityMeasure (densityMeasure rho) := h.isProbabilityMeasure
  let R := Set.Ioc a b ×ˢ Set.Ioc c d
  have hRM : MeasurableSet R := measurableSet_Ioc.prod measurableSet_Ioc
  have hSub : R ⊆ diamond := by
    rintro p ⟨hp, hq⟩
    exact ⟨⟨ha.trans hp.1.le, hp.2.trans hb⟩, ⟨hc.trans hq.1.le, hq.2.trans hd⟩⟩
  have hVol : diamondVolume R = ENNReal.ofReal ((b - a) * (d - c)) := by
    rw [diamondVolume, Measure.restrict_apply hRM, Set.inter_eq_left.mpr hSub]
    rw [show R = Set.Ioc a b ×ˢ Set.Ioc c d from rfl,
      Measure.prod_prod, Real.volume_Ioc, Real.volume_Ioc,
      ← ENNReal.ofReal_mul (sub_nonneg.mpr hab)]
  have hArea : 0 ≤ (b - a) * (d - c) := mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hcd)
  have hlo := h.densityMeasure_floor R
  have hhi := h.densityMeasure_ceiling R
  simp only [Measure.smul_apply, smul_eq_mul, hVol] at hlo hhi
  have hloR := ENNReal.toReal_mono (measure_ne_top _ _) hlo
  have hhiR := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hhi
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ENNReal.toReal_ofReal hArea] at hloR
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3 / 2),
    ENNReal.toReal_ofReal hArea] at hhiR
  change (b - a) * (d - c) / 2 ≤ (densityMeasure rho R).toReal ∧
    (densityMeasure rho R).toReal ≤ (3 / 2 : ℝ) * (b - a) * (d - c)
  constructor <;> nlinarith only [hloR, hhiR]

theorem InDensityClass.populationCDF_lower {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : s * t / 2 ≤ populationCDF rho s t := by
  letI : IsProbabilityMeasure (densityMeasure rho) := h.isProbabilityMeasure
  have hlo := (h.rectangle_mass_bounds (a := 0) (b := s) (c := 0) (d := t)
    le_rfl hs0 hs1 le_rfl ht0 ht1).1
  have hSub : Set.Ioc (0 : ℝ) s ×ˢ Set.Ioc (0 : ℝ) t ⊆ cdfRegion s t :=
    fun _ hp => ⟨hp.1.2, hp.2.2⟩
  have hmono := measureReal_mono (μ := densityMeasure rho) hSub
  simpa only [sub_zero] using hlo.trans hmono

theorem InDensityClass.northeastCDF_lower {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - s) * (1 - t) / 2 ≤ 1 - s - t + populationCDF rho s t := by
  have hlo := (h.rectangle_mass_bounds hs0 hs1 le_rfl ht0 ht1 le_rfl).1
  rw [h.rectangle_mass_cdf hs1 ht1,
    h.populationCDF_u_one (s := 1) (by norm_num) le_rfl,
    h.populationCDF_u_one hs0 hs1, h.populationCDF_one_v ht0 ht1] at hlo
  exact hlo

/-- The filter retains every true deep-interior point on the existing good
event. The self-count subtraction is included before taking the degree bound. -/
theorem deep_point_degree_retained {n m : ℕ} {rho : DiamondPoint → ℝ}
    (hK : InDensityClass rho) (hn : 0 < n) {r h : ℝ}
    (hr : 0 < r) (hh : 0 ≤ h) (hSquare : h ^ 2 = r)
    (hmr : (m : ℝ) * r = 1) (hnr : 1 / (n : ℝ) ≤ r)
    {sample : Fin n → DiamondPoint} (hg : SampleGood rho m r sample)
    (i : Fin n) (hi : 7 * h ≤ (sample i).1 ∧ (sample i).1 ≤ 1 - 7 * h ∧
      7 * h ≤ (sample i).2 ∧ (sample i).2 ≤ 1 - 7 * h) :
    DegreeRetained (Chronological (fun j => (sample j).1) (fun j => (sample j).2)) r i := by
  obtain ⟨hIn, hu, hv, _, hGrid⟩ := hg
  have hGU := grid_vertices_marginalU hK hr hmr (fun j => (hIn j).2.2) hGrid
  have hGV := grid_vertices_marginalV hK hr hmr (fun j => (hIn j).1.2) hGrid
  have hU := abs_le.mp (grid_marginal_accuracy_uniform hr hmr hGU
    (sample i).1 (hIn i).1.1 (hIn i).1.2)
  have hV := abs_le.mp (grid_marginal_accuracy_uniform hr hmr hGV
    (sample i).2 (hIn i).2.1 (hIn i).2.2)
  have hCDF := abs_le.mp (grid_vertices_empiricalCDF_unit hK hr hmr hGrid
    (sample i).1 (sample i).2 (hIn i).1.1 (hIn i).1.2 (hIn i).2.1 (hIn i).2.2)
  have hSW := hK.populationCDF_lower (hIn i).1.1 (hIn i).1.2 (hIn i).2.1 (hIn i).2.2
  have hNE := hK.northeastCDF_lower (hIn i).1.1 (hIn i).1.2 (hIn i).2.1 (hIn i).2.2
  have hSWarea : 49 * r ≤ (sample i).1 * (sample i).2 := by
    have hp := mul_le_mul hi.1 hi.2.2.1 (by positivity : 0 ≤ 7 * h) (hIn i).1.1
    nlinarith only [hp, hSquare]
  have hNEarea : 49 * r ≤ (1 - (sample i).1) * (1 - (sample i).2) := by
    have hxu : 7 * h ≤ 1 - (sample i).1 := by linarith [hi.2.1]
    have hxv : 7 * h ≤ 1 - (sample i).2 := by linarith [hi.2.2.2]
    have hp := mul_le_mul hxu hxv (by positivity : 0 ≤ 7 * h)
      (sub_nonneg.mpr (hIn i).1.2)
    nlinarith only [hp, hSquare]
  have hPred := chronological_predecessor_fraction hu hv i
  have hSucc := chronological_successor_fraction hn
    (fun j => (sample j).1) (fun j => (sample j).2) i
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · apply (lt_div_iff₀ hnR).mp
    rw [hPred]
    nlinarith only [hCDF.1, hSW, hSWarea, hnr, hr]
  · apply (lt_div_iff₀ hnR).mp
    rw [hSucc]
    nlinarith only [hCDF.1, hU.2, hV.2, hNE, hNEarea, hr]

#print axioms InDensityClass.rectangle_mass_bounds
#print axioms InDensityClass.populationCDF_lower
#print axioms InDensityClass.northeastCDF_lower
#print axioms deep_point_degree_retained

end QuantyraNullCone
