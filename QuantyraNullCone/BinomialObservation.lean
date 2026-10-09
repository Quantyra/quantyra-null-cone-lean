import QuantyraNullCone.MarkedThinning
import QuantyraNullCone.DKWUniform
import QuantyraNullCone.QuotientTV
import Mathlib.Data.Finset.Powerset

namespace QuantyraNullCone

open MeasureTheory

noncomputable def membershipCode {Omega : Type*} {n : ℕ} (S : Set Omega)
    (sample : Fin n → Omega) : Fin n → Bool :=
  fun i => @decide (sample i ∈ S) (Classical.propDecidable _)

theorem membership_code_measurable {Omega : Type*} [MeasurableSpace Omega] {n : ℕ}
    {S : Set Omega} (hS : MeasurableSet S) : Measurable (@membershipCode Omega n S) := by
  classical
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_to_bool
  have hEq : (fun sample : Fin n → Omega => membershipCode S sample i) ⁻¹' {true} =
      (Function.eval i) ⁻¹' S := by ext sample; simp [membershipCode]
  rw [hEq]
  exact hS.preimage (measurable_pi_apply i)

noncomputable def membershipLaw {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (n : ℕ) (S : Set Omega) : Measure (Fin n → Bool) :=
  (Measure.pi (fun _ : Fin n => mu)).map (membershipCode S)

theorem membership_law_probability {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] (n : ℕ) {S : Set Omega}
    (hS : MeasurableSet S) : IsProbabilityMeasure (membershipLaw mu n S) :=
  Measure.isProbabilityMeasure_map (membership_code_measurable hS).aemeasurable

def trueBits {n : ℕ} (code : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun i => code i = true)

def bitCount {n : ℕ} (code : Fin n → Bool) : ℕ := (trueBits code).card

theorem bit_count_le {n : ℕ} (code : Fin n → Bool) : bitCount code ≤ n := by
  simpa [bitCount, trueBits] using Finset.card_filter_le (Finset.univ : Finset (Fin n))
    (fun i => code i = true)

def boundedBitCount {n : ℕ} (code : Fin n → Bool) : Fin (n+1) :=
  ⟨bitCount code, Nat.lt_succ_of_le (bit_count_le code)⟩

noncomputable def binomialMass (n k : ℕ) (p : ℝ) : ℝ :=
  (n.choose k : ℝ) * p^k * (1-p)^(n-k)

theorem membership_law_atom {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] {n : ℕ} {S : Set Omega}
    (hS : MeasurableSet S) (code : Fin n → Bool) :
    (membershipLaw mu n S).real {code} =
      (mu.real S)^(bitCount code) * (1-mu.real S)^(n-bitCount code) := by
  classical
  let cells (i : Fin n) : Set Omega := if code i then S else Sᶜ
  have hPre : membershipCode S ⁻¹' {code} = Set.univ.pi cells := by
    ext sample
    simp only [Set.mem_preimage, Set.mem_singleton_iff, funext_iff, Set.mem_pi,
      Set.mem_univ, forall_const]
    apply forall_congr'
    intro i
    cases h : code i <;> simp [membershipCode, cells, h]
  rw [membershipLaw, map_measureReal_apply (membership_code_measurable hS)
    (measurableSet_singleton code), hPre, Measure.real, Measure.pi_pi, ENNReal.toReal_prod]
  have hCell (i : Fin n) : (mu (cells i)).toReal =
      if code i then mu.real S else 1-mu.real S := by
    change mu.real (cells i) = if code i then mu.real S else 1-mu.real S
    cases h : code i <;> simp [cells, h, measureReal_compl hS]
  simp_rw [hCell]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  have hCards := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun i : Fin n => code i = true)
  have hFalse : (Finset.univ.filter (fun i : Fin n => ¬code i = true)).card = n-bitCount code := by
    simp only [Finset.card_univ, Fintype.card_fin] at hCards
    change (Finset.univ.filter (fun i : Fin n => ¬code i = true)).card =
      n-(Finset.univ.filter (fun i : Fin n => code i = true)).card
    omega
  rw [hFalse]
  rfl

theorem bit_count_fiber_card (n k : ℕ) :
    (Finset.univ.filter (fun code : Fin n → Bool => bitCount code = k)).card = n.choose k := by
  classical
  have hCard : (Finset.univ.filter (fun code : Fin n → Bool => bitCount code = k)).card =
      ((Finset.univ : Finset (Fin n)).powersetCard k).card := by
    apply Finset.card_bij (fun code _ => trueBits code)
    · intro code hcode
      exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, (Finset.mem_filter.mp hcode).2⟩
    · intro c hc d hd heq
      funext i
      have hi := Finset.ext_iff.mp heq i
      simp only [trueBits, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      cases hci : c i <;> cases hdi : d i <;> simp_all
    · intro s hs
      let code : Fin n → Bool := fun i => decide (i ∈ s)
      have hEq : trueBits code = s := by ext i; simp [trueBits, code]
      refine ⟨code, ?_, hEq⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, bitCount, hEq]
      exact (Finset.mem_powersetCard.mp hs).2
  simpa using hCard

noncomputable def membershipCountLaw {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (n : ℕ) (S : Set Omega) : Measure (Fin (n+1)) :=
  (membershipLaw mu n S).map boundedBitCount

theorem membership_count_probability {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] (n : ℕ) {S : Set Omega}
    (hS : MeasurableSet S) : IsProbabilityMeasure (membershipCountLaw mu n S) := by
  letI := membership_law_probability mu n hS
  exact Measure.isProbabilityMeasure_map (measurable_of_countable boundedBitCount).aemeasurable

theorem membership_count_atom {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] {n : ℕ} {S : Set Omega}
    (hS : MeasurableSet S) (k : Fin (n+1)) :
    (membershipCountLaw mu n S).real {k} = binomialMass n k (mu.real S) := by
  classical
  letI := membership_law_probability mu n hS
  rw [membershipCountLaw, finite_map_real_singleton]
  have hFilter : Finset.univ.filter (fun code : Fin n → Bool => boundedBitCount code = k) =
      Finset.univ.filter (fun code : Fin n → Bool => bitCount code = k.val) := by
    ext code
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Fin.ext_iff
  rw [hFilter]
  calc
    _ = ∑ _code ∈ Finset.univ.filter (fun code : Fin n → Bool => bitCount code = k.val),
        (mu.real S)^k.val * (1-mu.real S)^(n-k.val) := by
      apply Finset.sum_congr rfl
      intro code hcode
      rw [membership_law_atom mu hS, (Finset.mem_filter.mp hcode).2]
    _ = binomialMass n k (mu.real S) := by
      simp [binomialMass, bit_count_fiber_card, nsmul_eq_mul, mul_assoc]

noncomputable def binomialCountLaw (n : ℕ) (p : ℝ) : Measure (Fin (n+1)) :=
  membershipCountLaw uniform01Measure n (Set.Iic p)

instance binomialCountLaw_probability (n : ℕ) (p : ℝ) : IsProbabilityMeasure (binomialCountLaw n p) :=
  membership_count_probability uniform01Measure n measurableSet_Iic

theorem binomial_count_atom {n : ℕ} {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) (k : Fin (n+1)) :
    (binomialCountLaw n p).real {k} = binomialMass n k p := by
  rw [binomialCountLaw, membership_count_atom uniform01Measure measurableSet_Iic,
    uniform_population_CDF, uniform_population_CDF_unit hp]

theorem membership_count_eq_binomial {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] (n : ℕ) {S : Set Omega}
    (hS : MeasurableSet S) : membershipCountLaw mu n S = binomialCountLaw n (mu.real S) := by
  letI := membership_count_probability mu n hS
  apply Measure.ext_of_singleton
  intro k
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  exact (membership_count_atom mu hS k).trans
    (binomial_count_atom ⟨measureReal_nonneg, measureReal_le_one⟩ k).symm

theorem threshold_count_mono {n : ℕ} {p q : ℝ} (hpq : p ≤ q) (sample : Fin n → ℝ) :
    boundedBitCount (membershipCode (Set.Iic p) sample) ≤
      boundedBitCount (membershipCode (Set.Iic q) sample) := by
  change bitCount _ ≤ bitCount _
  apply Finset.card_le_card
  intro i hi
  simp only [trueBits, Finset.mem_filter, Finset.mem_univ, true_and, membershipCode,
    decide_eq_true_eq, Set.mem_Iic] at hi ⊢
  exact hi.trans hpq

theorem binomial_upper_tail_mono {n : ℕ} (k : Fin (n+1)) {p q : ℝ} (hpq : p ≤ q) :
    (binomialCountLaw n p).real (Set.Ici k) ≤ (binomialCountLaw n q).real (Set.Ici k) := by
  simp only [binomialCountLaw, membershipCountLaw, membershipLaw]
  rw [map_measureReal_apply (measurable_of_countable boundedBitCount) measurableSet_Ici,
      map_measureReal_apply (measurable_of_countable boundedBitCount) measurableSet_Ici,
      map_measureReal_apply (membership_code_measurable measurableSet_Iic)
        (measurableSet_Ici.preimage (measurable_of_countable boundedBitCount)),
      map_measureReal_apply (membership_code_measurable measurableSet_Iic)
        (measurableSet_Ici.preimage (measurable_of_countable boundedBitCount))]
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro sample hs
  exact hs.trans (threshold_count_mono hpq sample)

theorem binomial_lower_tail_antitone {n : ℕ} (k : Fin (n+1)) {p q : ℝ} (hpq : p ≤ q) :
    (binomialCountLaw n q).real (Set.Iic k) ≤ (binomialCountLaw n p).real (Set.Iic k) := by
  simp only [binomialCountLaw, membershipCountLaw, membershipLaw]
  rw [map_measureReal_apply (measurable_of_countable boundedBitCount) measurableSet_Iic,
      map_measureReal_apply (measurable_of_countable boundedBitCount) measurableSet_Iic,
      map_measureReal_apply (membership_code_measurable measurableSet_Iic)
        (measurableSet_Iic.preimage (measurable_of_countable boundedBitCount)),
      map_measureReal_apply (membership_code_measurable measurableSet_Iic)
        (measurableSet_Iic.preimage (measurable_of_countable boundedBitCount))]
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro sample hs
  exact (threshold_count_mono hpq sample).trans hs

theorem marked_count_eq_binomial {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] (n : ℕ)
    (C : Omega → Omega → Prop) (p q : Omega)
    (hS : MeasurableSet (markedIntervalSet C p q)) :
    (markedIntervalLaw mu n C p q).map boundedBitCount =
      binomialCountLaw n (mu.real (markedIntervalSet C p q)) := by
  exact membership_count_eq_binomial mu n hS

end QuantyraNullCone
