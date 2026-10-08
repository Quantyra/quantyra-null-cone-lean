import QuantyraNullCone.DKWFiniteTail
import QuantyraNullCone.GridAccuracy
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms

namespace QuantyraNullCone

open MeasureTheory

def ceilBinNat (q : ℕ) (hq : 0 < q) (c : ℕ) : Fin q :=
  ⟨min (q - 1) (c - 1), by have h := min_le_left (q - 1) (c - 1); omega⟩

noncomputable def uniformCeilBin (q : ℕ) (hq : 0 < q) (x : ℝ) : Fin q :=
  ceilBinNat q hq (Nat.ceil ((q : ℝ) * x))

theorem uniform_ceil_bin_measurable (q : ℕ) (hq : 0 < q) :
    Measurable (uniformCeilBin q hq) :=
  (measurable_of_countable (ceilBinNat q hq)).comp
    ((measurable_const.mul measurable_id).nat_ceil)

theorem uniform_ceil_bin_val {q : ℕ} (hq : 0 < q) {x : ℝ} (hx : x ∈ Set.Ioc 0 1) :
    (uniformCeilBin q hq x).val = Nat.ceil ((q : ℝ) * x) - 1 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hCeil : Nat.ceil ((q : ℝ) * x) ≤ q := Nat.ceil_le.mpr (by nlinarith [hx.2])
  simp only [uniformCeilBin, ceilBinNat]
  exact min_eq_right (Nat.sub_le_sub_right hCeil 1)

/-- Exact inclusive threshold identity, including positive grid ties. -/
theorem uniform_ceil_bin_grid_iff {q k : ℕ} (hq : 0 < q) {x : ℝ}
    (hx : x ∈ Set.Ioc 0 1) :
    (uniformCeilBin q hq x).val < k ↔ x ≤ (k : ℝ) / q := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hPositive : 1 ≤ Nat.ceil ((q : ℝ) * x) :=
    Nat.one_le_ceil_iff.mpr (mul_pos hqR hx.1)
  rw [uniform_ceil_bin_val hq hx]
  have hNat : Nat.ceil ((q : ℝ) * x) - 1 < k ↔ Nat.ceil ((q : ℝ) * x) ≤ k := by omega
  rw [hNat, Nat.ceil_le]
  simpa only [mul_comm] using (le_div_iff₀ hqR).symm

def uniformBinCell {q : ℕ} (b : Fin q) : Set ℝ :=
  Set.Ioc ((b.val : ℝ) / q) (((b.val : ℝ) + 1) / q)

theorem uniform_bin_cell_subset {q : ℕ} (hq : 0 < q) (b : Fin q) :
    uniformBinCell b ⊆ Set.Ioc 0 1 := by
  intro x hx
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hL : 0 ≤ (b.val : ℝ) / q := by positivity
  have hB : (b.val : ℝ) + 1 ≤ q := by exact_mod_cast Nat.succ_le_of_lt b.isLt
  exact ⟨hL.trans_lt hx.1, hx.2.trans ((div_le_one hqR).mpr hB)⟩

theorem uniform_ceil_bin_eq_iff {q : ℕ} (hq : 0 < q) {x : ℝ}
    (hx : x ∈ Set.Ioc 0 1) (b : Fin q) :
    uniformCeilBin q hq x = b ↔ x ∈ uniformBinCell b := by
  have hL := uniform_ceil_bin_grid_iff (k := b.val) hq hx
  have hU := uniform_ceil_bin_grid_iff (k := b.val + 1) hq hx
  simp only [Nat.cast_add, Nat.cast_one] at hU
  constructor
  · intro h
    have hVal := congrArg Fin.val h
    have hNot : ¬ (uniformCeilBin q hq x).val < b.val := by omega
    have hUpper : (uniformCeilBin q hq x).val < b.val + 1 := by omega
    exact ⟨lt_of_not_ge (hL.not.mp hNot), hU.mp hUpper⟩
  · rintro ⟨hLower, hUpper⟩
    have hNot : ¬ (uniformCeilBin q hq x).val < b.val :=
      hL.not.mpr (not_le_of_gt hLower)
    have hUpper' := hU.mpr hUpper
    exact Fin.ext (by omega)

theorem uniform_bin_preimage_inter {q : ℕ} (hq : 0 < q) (b : Fin q) :
    (uniformCeilBin q hq ⁻¹' {b}) ∩ Set.Ioc 0 1 = uniformBinCell b := by
  ext x
  constructor
  · rintro ⟨hBin, hx⟩
    exact (uniform_ceil_bin_eq_iff hq hx b).mp hBin
  · intro hx
    have hSupport := uniform_bin_cell_subset hq b hx
    exact ⟨(uniform_ceil_bin_eq_iff hq hSupport b).mpr hx, hSupport⟩

noncomputable def uniform01Measure : Measure ℝ := volume.restrict (Set.Ioc 0 1)

instance uniform01_isProbabilityMeasure : IsProbabilityMeasure uniform01Measure := by
  constructor
  simp [uniform01Measure]

theorem uniform01_closed_interval : uniform01Measure = volume.restrict (Set.Icc (0 : ℝ) 1) :=
  restrict_Ioc_eq_restrict_Icc

theorem uniform_bin_preimage_mass {q : ℕ} (hq : 0 < q) (b : Fin q) :
    uniform01Measure (uniformCeilBin q hq ⁻¹' {b}) = ENNReal.ofReal (1 / (q : ℝ)) := by
  rw [uniform01Measure, Measure.restrict_apply
    ((measurableSet_singleton b).preimage (uniform_ceil_bin_measurable q hq)),
    uniform_bin_preimage_inter hq b, uniformBinCell, Real.volume_Ioc]
  congr 1
  ring

noncomputable def uniformSampleMeasure (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => uniform01Measure)

instance uniformSample_isProbabilityMeasure (n : ℕ) : IsProbabilityMeasure (uniformSampleMeasure n) := by
  unfold uniformSampleMeasure
  infer_instance

noncomputable def uniformQuantizedProfile {n : ℕ} (q : ℕ) (hq : 0 < q) (w : Fin n → ℝ) : BinProfile n q :=
  fun i => uniformCeilBin q hq (w i)

theorem uniform_quantized_profile_measurable {n : ℕ} (q : ℕ) (hq : 0 < q) :
    Measurable (uniformQuantizedProfile (n := n) q hq) :=
  measurable_pi_lambda _ (fun i => (uniform_ceil_bin_measurable q hq).comp (measurable_pi_apply i))

theorem uniform_quantized_profile_singleton {n q : ℕ} (hq : 0 < q) (b : BinProfile n q) :
    ((uniformSampleMeasure n).map (uniformQuantizedProfile q hq)) {b} =
      ENNReal.ofReal (1 / (q : ℝ)) ^ n := by
  have hPre : uniformQuantizedProfile q hq ⁻¹' {b} =
      Set.univ.pi (fun i => uniformCeilBin q hq ⁻¹' {b i}) := by
    ext w
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_pi, Set.mem_univ,
      forall_true_left, uniformQuantizedProfile, funext_iff]
  rw [Measure.map_apply (uniform_quantized_profile_measurable q hq) (measurableSet_singleton b),
    hPre, uniformSampleMeasure, Measure.pi_pi]
  simp_rw [uniform_bin_preimage_mass hq]
  simp

/-- Exact product-law bridge from continuous uniform samples to finite counting. -/
theorem uniform_quantized_profile_real_mass {n q : ℕ} (hq : 0 < q) (E : Finset (BinProfile n q)) :
    ((uniformSampleMeasure n).map (uniformQuantizedProfile q hq)).real E =
      (E.card : ℝ) / (q : ℝ) ^ n := by
  let ν := (uniformSampleMeasure n).map (uniformQuantizedProfile q hq)
  letI : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map (uniform_quantized_profile_measurable q hq).aemeasurable
  have hSingle : ∀ b : BinProfile n q, ν.real {b} = 1 / (q : ℝ) ^ n := by
    intro b
    rw [Measure.real, uniform_quantized_profile_singleton hq, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (by positivity), one_div, inv_pow, one_div]
  change ν.real E = _
  rw [← sum_measureReal_singleton]
  simp_rw [hSingle]
  simp [div_eq_mul_inv]

theorem uniform_quantized_CDF {n q k : ℕ} (hq : 0 < q) (w : Fin n → ℝ)
    (hw : ∀ i, w i ∈ Set.Ioc 0 1) :
    finiteBinCDF (uniformQuantizedProfile q hq w) k = marginalCDF w ((k : ℝ) / q) := by
  classical
  have hCount : Finset.univ.filter (fun i => ((uniformQuantizedProfile q hq w) i).val < k) =
      cumulativeCount w ((k : ℝ) / q) := by
    ext i
    simp only [cumulativeCount, Finset.mem_filter, Finset.mem_univ, true_and,
      uniformQuantizedProfile]
    exact uniform_ceil_bin_grid_iff hq (hw i)
  unfold finiteBinCDF finiteBinCount
  rw [hCount]
  rfl

#print axioms uniform_ceil_bin_grid_iff
#print axioms uniform_quantized_profile_real_mass
#print axioms uniform_quantized_CDF

end QuantyraNullCone
