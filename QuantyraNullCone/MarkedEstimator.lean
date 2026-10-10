import QuantyraNullCone.ConfoundingMarked

namespace QuantyraNullCone

open MeasureTheory

/-- The two anchor roles are retained; only sampled-event labels are forgotten. -/
noncomputable def volumeRateAnchors : Fin 2 → DiamondPoint := ![(0, 0), (1/2, 1/2)]

def markedOrderIntervalBits {n m : ℕ} (p q : Fin m) (code : MarkedOrderCode n m) :
    Fin n → Bool := fun i => code (.inr p) (.inl i) && code (.inl i) (.inr q)

theorem marked_order_interval_bits_relabel {n m : ℕ} (p q : Fin m)
    (code : MarkedOrderCode n m) (pi : Equiv.Perm (Fin n)) :
    markedOrderIntervalBits p q (relabelMarkedOrder pi code) =
      markedOrderIntervalBits p q code ∘ pi := rfl

noncomputable def markedOrderFraction {n m : ℕ} (p q : Fin m) :
    UnlabeledMarkedOrderCode n m → ℝ :=
  Quotient.lift (fun code => markedFraction (markedOrderIntervalBits p q code)) (by
    rintro code other ⟨pi, rfl⟩
    exact (marked_fraction_relabel (markedOrderIntervalBits p q code) pi).symm)

theorem marked_order_fraction_measurable {n m : ℕ} (p q : Fin m) :
    Measurable (markedOrderFraction (n := n) p q) := measurable_of_countable _

theorem sampled_marked_order_interval_bits {n m : ℕ} (p q : Fin m)
    (anchors : Fin m → DiamondPoint) (sample : Fin n → DiamondPoint) :
    markedOrderIntervalBits p q (sampledMarkedOrder anchors sample) =
      markedIntervalCode nullChronology (anchors p) (anchors q) sample := by
  classical
  funext i
  simp [markedOrderIntervalBits, sampledMarkedOrder, markedLocation, markedIntervalCode]
  rfl

theorem sampled_marked_order_fraction {n m : ℕ} (p q : Fin m)
    (anchors : Fin m → DiamondPoint) (sample : Fin n → DiamondPoint) :
    markedOrderFraction p q (sampledUnlabeledMarkedOrder anchors sample) =
      markedFraction (markedIntervalCode nullChronology (anchors p) (anchors q) sample) := by
  change markedFraction (markedOrderIntervalBits p q (sampledMarkedOrder anchors sample)) = _
  rw [sampled_marked_order_interval_bits]

theorem marked_order_fraction_unit {n m : ℕ} (hn : 0 < n) (p q : Fin m)
    (code : UnlabeledMarkedOrderCode n m) : markedOrderFraction p q code ∈ Set.Icc (0 : ℝ) 1 := by
  induction code using Quotient.inductionOn with
  | h code => exact marked_fraction_unit hn (markedOrderIntervalBits p q code)

/-- Hoeffding calibration on the full observed quotient, without recovering latent coordinates. -/
theorem full_marked_order_fraction_hoeffding (mu : Measure DiamondPoint) [IsProbabilityMeasure mu]
    {n m : ℕ} (hn : 0 < n) (anchors : Fin m → DiamondPoint) (p q : Fin m)
    {r : ℝ} (hr : 0 ≤ r) :
    ((Measure.pi (fun _ : Fin n => mu)).map (sampledUnlabeledMarkedOrder anchors)).real
      {code | r ≤ |markedOrderFraction p q code -
        mu.real (markedIntervalSet nullChronology (anchors p) (anchors q))|} ≤
      2 * Real.exp (-2 * (n : ℝ) * r ^ 2) := by
  rw [map_measureReal_apply (sampled_unlabeled_marked_order_measurable anchors)
    (measurableSet_le measurable_const ((marked_order_fraction_measurable p q).sub_const _).abs)]
  simpa only [Set.preimage_setOf_eq, sampled_marked_order_fraction, marked_fraction_indicator,
    Measure.real] using iid_indicator_hoeffding mu hn
      (null_interval_measurable (anchors p) (anchors q)) hr

end QuantyraNullCone
