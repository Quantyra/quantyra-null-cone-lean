import QuantyraNullCone.ProbabilityRate

namespace QuantyraNullCone

open MeasureTheory

def CodeRelation {n : ℕ} (code : OrderCode n) (i j : Fin n) : Prop := code i j = true

theorem sampledOrder_relation {n : ℕ} (sample : Fin n → DiamondPoint) :
    CodeRelation (sampledOrder sample) =
      Chronological (fun i => (sample i).1) (fun i => (sample i).2) := by
  funext i j
  simp [CodeRelation, sampledOrder, Chronological]

theorem chronological_realizer_exists {n : ℕ} {u v : Fin n → ℝ}
    (hu : Function.Injective u) (hv : Function.Injective v) :
    Nonempty (Realizer (Chronological u v)) := by
  refine ⟨⟨(fun i j => u i < u j), (fun i j => v i < v j), ?_, ?_, ?_⟩⟩
  · exact ⟨fun i => lt_irrefl (u i), fun h₁ h₂ => lt_trans h₁ h₂,
      fun hij => lt_or_gt_of_ne (hu.ne hij)⟩
  · exact ⟨fun i => lt_irrefl (v i), fun h₁ h₂ => lt_trans h₁ h₂,
      fun hij => lt_or_gt_of_ne (hv.ne hij)⟩
  · intro i j
    rfl

noncomputable def Realizer.rankCDF {n : ℕ} {P : Fin n → Fin n → Prop}
    (L : Realizer P) (s t : ℝ) : ℝ :=
  empiricalCDF (fun i => (rank L.first i : ℝ) / n)
    (fun i => (rank L.second i : ℝ) / n) s t

theorem Realizer.rankCDF_swap {n : ℕ} {P : Fin n → Fin n → Prop}
    (L : Realizer P) (s t : ℝ) : L.swap.rankCDF s t = L.rankCDF t s := by
  have hRect : rectangleCount (fun i => (rank L.second i : ℝ) / n)
      (fun i => (rank L.first i : ℝ) / n) s t =
      rectangleCount (fun i => (rank L.first i : ℝ) / n)
        (fun i => (rank L.second i : ℝ) / n) t s := by
    ext i
    simp [rectangleCount, and_comm]
  simpa only [Realizer.rankCDF, Realizer.swap, empiricalCDF] using
    congrArg (fun q : Finset (Fin n) => (q.card : ℝ) / n) hRect

/-- The same selector is used for every density. Invalid codes have the fixed zero output. -/
noncomputable def selectedCDF {n : ℕ} (code : OrderCode n) : ℝ → ℝ → ℝ := by
  classical
  exact if h : Nonempty (Realizer (CodeRelation code)) then
    (Classical.choice h).rankCDF else fun _ _ => 0

def orientCDF (F : ℝ → ℝ → ℝ) : Bool → ℝ → ℝ → ℝ
  | false => F
  | true => fun s t => F t s

def OrderCDFGood {n : ℕ} (rho : DiamondPoint → ℝ) (a : ℝ) (code : OrderCode n) : Prop :=
  ∃ swap : Bool, ∀ s t : ℝ,
    |orientCDF (selectedCDF code) swap s t - populationCDF rho s t| ≤ a

theorem selectedCDF_measurable (n : ℕ) (s t : ℝ) :
    Measurable (fun code : OrderCode n => selectedCDF code s t) :=
  measurable_of_countable _

theorem orderCDFGood_measurable {n : ℕ} (rho : DiamondPoint → ℝ) (a : ℝ) :
    MeasurableSet {code : OrderCode n | OrderCDFGood rho a code} :=
  Set.to_countable _ |>.measurableSet

theorem reconstructed_orderCDFGood {n : ℕ} {rho : DiamondPoint → ℝ} {a : ℝ}
    {sample : Fin n → DiamondPoint}
    (hu : Function.Injective (fun i => (sample i).1))
    (hv : Function.Injective (fun i => (sample i).2))
    (hR : SampleCDFReconstructed rho a sample) :
    OrderCDFGood rho a (sampledOrder sample) := by
  classical
  have hEq := sampledOrder_relation sample
  have hExists : Nonempty (Realizer (CodeRelation (sampledOrder sample))) := by
    rw [hEq]
    exact chronological_realizer_exists hu hv
  unfold OrderCDFGood selectedCDF
  rw [dif_pos hExists]
  have hR' : ∀ L : Realizer (CodeRelation (sampledOrder sample)), ∃ swap : Bool,
      ∀ s t : ℝ, |(L.aligned swap).rankCDF s t - populationCDF rho s t| ≤ a := by
    rw [hEq]
    exact hR
  obtain ⟨swap, hCDF⟩ := hR' (Classical.choice hExists)
  refine ⟨swap, ?_⟩
  cases swap with
  | false => exact hCDF
  | true => simpa only [orientCDF, Realizer.aligned, Realizer.rankCDF_swap] using hCDF

theorem InDensityClass.orderCDFGood_probability {rho : DiamondPoint → ℝ}
    (h : InDensityClass rho) {n : ℕ} (hn : 65536 ≤ n) :
    (9 / 10 : ℝ) ≤ (orderLaw rho n).real
      {code | OrderCDFGood rho (174 * (n : ℝ) ^ (-1 / 4 : ℝ)) code} := by
  letI : IsProbabilityMeasure (sampleMeasure rho n) := h.sample_isProbabilityMeasure n
  rw [orderLaw, map_measureReal_apply (sampledOrder_measurable n)
    (orderCDFGood_measurable _ _)]
  refine h.reconstruction_probability hn |>.trans ?_
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [h.sample_coordinates_injective n] with sample hInj
  exact fun hR => reconstructed_orderCDFGood hInj.1 hInj.2 hR

#print axioms chronological_realizer_exists
#print axioms selectedCDF_measurable
#print axioms InDensityClass.orderCDFGood_probability

end QuantyraNullCone
