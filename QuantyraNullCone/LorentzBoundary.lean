import QuantyraNullCone.LorentzVolumeCoordinates
import QuantyraNullCone.LorentzMeasures

namespace QuantyraNullCone

open Set

noncomputable section

/-- Closed, future-directed Lorentz causal relation, including equality. -/
def causal3 (p q : LorentzPoint3) : Prop := spatialRadius3 (q - p) ≤ q 0 - p 0

def lorentzBottom3 : LorentzPoint3 := lorentzPoint3 (-1) 0 0
def lorentzTop3 : LorentzPoint3 := lorentzPoint3 1 0 0
def lorentzWaist3 : Set LorentzPoint3 := {p | p 0 = 0 ∧ spatialRadius3 p = 1}
def causalDiamond3 (p q : LorentzPoint3) : Set LorentzPoint3 :=
  {z | causal3 p z ∧ causal3 z q}

def timeShift3 (p : LorentzPoint3) (s : ℝ) : LorentzPoint3 :=
  lorentzPoint3 (p 0 + s) (p 1) (p 2)

theorem lorentz_waist_subset_closed3 : lorentzWaist3 ⊆ closedLorentzDiamond3 := by
  intro p hp
  change p 0 = 0 ∧ spatialRadius3 p = 1 at hp
  change |p 0| + spatialRadius3 p ≤ 1
  rw [hp.1, hp.2]
  norm_num

theorem isClosed_lorentzWaist3 : IsClosed lorentzWaist3 := by
  change IsClosed ({p : LorentzPoint3 | p 0 = 0} ∩ {p | spatialRadius3 p = 1})
  exact (isClosed_eq (by fun_prop) continuous_const).inter
    (isClosed_eq continuous_spatial_radius3 continuous_const)

theorem isCompact_lorentzWaist3 : IsCompact lorentzWaist3 :=
  isCompact_closedLorentzDiamond3.of_isClosed_subset isClosed_lorentzWaist3
    lorentz_waist_subset_closed3

theorem time_shift_time3 (p : LorentzPoint3) (s : ℝ) : timeShift3 p s 0 = p 0 + s := rfl
theorem time_shift_radius3 (p : LorentzPoint3) (s : ℝ) :
    spatialRadius3 (timeShift3 p s) = spatialRadius3 p := rfl

theorem time_shift_sub_radius3 (p q : LorentzPoint3) (s : ℝ) :
    spatialRadius3 (q - timeShift3 p s) = spatialRadius3 (q - p) := rfl

theorem time_shift_radius_sub3 (p q : LorentzPoint3) (s : ℝ) :
    spatialRadius3 (timeShift3 p s - q) = spatialRadius3 (p - q) := rfl

theorem spatial_radius_sub_symm3 (p q : LorentzPoint3) :
    spatialRadius3 (p - q) = spatialRadius3 (q - p) := by
  unfold spatialRadius3
  congr 1
  simp only [spatialSquared3, PiLp.sub_apply]
  ring

theorem spatial_radius_self_sub3 (p : LorentzPoint3) : spatialRadius3 (p - p) = 0 := by
  simp [spatialRadius3, spatialSquared3]

theorem causal3_refl (p : LorentzPoint3) : causal3 p p := by
  unfold causal3
  rw [spatial_radius_self_sub3, sub_self]

theorem causal3_transitive {p q r : LorentzPoint3}
    (hpq : causal3 p q) (hqr : causal3 q r) : causal3 p r := by
  unfold causal3 at *
  linarith [spatial_radius_triangle3 p q r]

theorem chronological3_trans_causal3 {p q r : LorentzPoint3}
    (hpq : chronological3 p q) (hqr : causal3 q r) : chronological3 p r := by
  unfold causal3 chronological3 at *
  linarith [spatial_radius_triangle3 p q r]

theorem causal3_trans_chronological3 {p q r : LorentzPoint3}
    (hpq : causal3 p q) (hqr : chronological3 q r) : chronological3 p r := by
  unfold causal3 chronological3 at *
  linarith [spatial_radius_triangle3 p q r]

theorem causal3_antisymmetric {p q : LorentzPoint3}
    (hpq : causal3 p q) (hqp : causal3 q p) : p = q := by
  unfold causal3 at hpq hqp
  have ht : p 0 = q 0 := by
    linarith [spatial_radius_nonneg3 (q - p), spatial_radius_nonneg3 (p - q)]
  have hr : spatialRadius3 (q - p) = 0 := by
    apply le_antisymm
    · simpa [ht] using hpq
    · exact spatial_radius_nonneg3 _
  have hs := spatial_radius_sq3 (q - p)
  rw [hr] at hs
  simp only [spatialSquared3, PiLp.sub_apply] at hs
  ext i
  fin_cases i
  · exact ht
  · change p 1 = q 1
    nlinarith [sq_nonneg (q 2 - p 2)]
  · change p 2 = q 2
    nlinarith [sq_nonneg (q 1 - p 1)]

theorem bottom_sub_radius3 (p : LorentzPoint3) :
    spatialRadius3 (p - lorentzBottom3) = spatialRadius3 p := by
  simp [spatialRadius3, spatialSquared3, lorentzBottom3, lorentzPoint3, PiLp.sub_apply]

theorem top_sub_radius3 (p : LorentzPoint3) :
    spatialRadius3 (lorentzTop3 - p) = spatialRadius3 p := by
  simp [spatialRadius3, spatialSquared3, lorentzTop3, lorentzPoint3, PiLp.sub_apply]

theorem closed_lorentz_diamond_iff_tips3 (p : LorentzPoint3) :
    p ∈ closedLorentzDiamond3 ↔ causal3 lorentzBottom3 p ∧ causal3 p lorentzTop3 := by
  change |p 0| + spatialRadius3 p ≤ 1 ↔ _
  simp only [causal3, bottom_sub_radius3, top_sub_radius3]
  change |p 0| + spatialRadius3 p ≤ 1 ↔
    spatialRadius3 p ≤ p 0 - (-1) ∧ spatialRadius3 p ≤ 1 - p 0
  constructor
  · intro h
    constructor <;> linarith [le_abs_self (p 0), neg_le_abs (p 0)]
  · rintro ⟨h1, h2⟩
    rcases le_total 0 (p 0) with ht | ht
    · rw [abs_of_nonneg ht]; linarith
    · rw [abs_of_nonpos ht]; linarith

theorem lorentz_diamond_iff_tips3 (p : LorentzPoint3) :
    p ∈ lorentzDiamond3 ↔ chronological3 lorentzBottom3 p ∧ chronological3 p lorentzTop3 := by
  change |p 0| + spatialRadius3 p < 1 ↔ _
  simp only [chronological3, bottom_sub_radius3, top_sub_radius3]
  change |p 0| + spatialRadius3 p < 1 ↔
    spatialRadius3 p < p 0 - (-1) ∧ spatialRadius3 p < 1 - p 0
  constructor
  · intro h
    constructor <;> linarith [le_abs_self (p 0), neg_le_abs (p 0)]
  · rintro ⟨h1, h2⟩
    rcases le_total 0 (p 0) with ht | ht
    · rw [abs_of_nonneg ht]; linarith
    · rw [abs_of_nonpos ht]; linarith

theorem causal_diamond_subset_closed3 {p q : LorentzPoint3}
    (hp : p ∈ closedLorentzDiamond3) (hq : q ∈ closedLorentzDiamond3) :
    causalDiamond3 p q ⊆ closedLorentzDiamond3 := by
  intro z hz
  exact (closed_lorentz_diamond_iff_tips3 z).mpr
    ⟨causal3_transitive ((closed_lorentz_diamond_iff_tips3 p).mp hp).1 hz.1,
      causal3_transitive hz.2 ((closed_lorentz_diamond_iff_tips3 q).mp hq).2⟩

theorem causal_diamond_subset_open3 {p q : LorentzPoint3}
    (hp : p ∈ lorentzDiamond3) (hq : q ∈ lorentzDiamond3) :
    causalDiamond3 p q ⊆ lorentzDiamond3 := by
  intro z hz
  exact (lorentz_diamond_iff_tips3 z).mpr
    ⟨chronological3_trans_causal3 ((lorentz_diamond_iff_tips3 p).mp hp).1 hz.1,
      causal3_trans_chronological3 hz.2 ((lorentz_diamond_iff_tips3 q).mp hq).2⟩

theorem isClosed_causalDiamond3 (p q : LorentzPoint3) : IsClosed (causalDiamond3 p q) := by
  change IsClosed ({z | spatialRadius3 (z - p) ≤ z 0 - p 0} ∩
    {z | spatialRadius3 (q - z) ≤ q 0 - z 0})
  exact (isClosed_le (by fun_prop) (by fun_prop)).inter
    (isClosed_le (by fun_prop) (by fun_prop))

theorem isCompact_causalDiamond3 {p q : LorentzPoint3}
    (hp : p ∈ closedLorentzDiamond3) (hq : q ∈ closedLorentzDiamond3) :
    IsCompact (causalDiamond3 p q) :=
  isCompact_closedLorentzDiamond3.of_isClosed_subset
    (isClosed_causalDiamond3 p q) (causal_diamond_subset_closed3 hp hq)

/-- The concrete compact-diamond property required by the smooth-base source theorem. -/
theorem open_lorentz_causal_diamond3 {p q : LorentzPoint3}
    (hp : p ∈ lorentzDiamond3) (hq : q ∈ lorentzDiamond3) :
    IsCompact (causalDiamond3 p q) ∧ causalDiamond3 p q ⊆ lorentzDiamond3 :=
  ⟨isCompact_causalDiamond3 (lorentz_diamond_subset_closed3 hp)
    (lorentz_diamond_subset_closed3 hq), causal_diamond_subset_open3 hp hq⟩

theorem past_time_shift_interior3 {p : LorentzPoint3} (hp : p ∈ closedLorentzDiamond3)
    {s : ℝ} (hs : 0 < s) (hmargin : s < 1 - spatialRadius3 p + p 0) :
    timeShift3 p (-s) ∈ lorentzDiamond3 ∧ chronological3 (timeShift3 p (-s)) p := by
  change |p 0| + spatialRadius3 p ≤ 1 at hp
  constructor
  · change |p 0 + -s| + spatialRadius3 p < 1
    have hb : |p 0 + -s| < 1 - spatialRadius3 p := by
      apply abs_lt.mpr
      constructor <;> linarith [le_abs_self (p 0)]
    linarith
  · unfold chronological3
    rw [time_shift_sub_radius3, spatial_radius_self_sub3, time_shift_time3]
    linarith

theorem future_time_shift_interior3 {p : LorentzPoint3} (hp : p ∈ closedLorentzDiamond3)
    {s : ℝ} (hs : 0 < s) (hmargin : s < 1 - spatialRadius3 p - p 0) :
    timeShift3 p s ∈ lorentzDiamond3 ∧ chronological3 p (timeShift3 p s) := by
  change |p 0| + spatialRadius3 p ≤ 1 at hp
  constructor
  · change |p 0 + s| + spatialRadius3 p < 1
    have hb : |p 0 + s| < 1 - spatialRadius3 p := by
      apply abs_lt.mpr
      constructor <;> linarith [neg_le_abs (p 0)]
    linarith
  · unfold chronological3
    rw [time_shift_radius_sub3, spatial_radius_self_sub3, time_shift_time3]
    linarith

theorem past_chronological_margin3 {p q : LorentzPoint3}
    (hq : q ∈ closedLorentzDiamond3) (hqp : chronological3 q p) :
    spatialRadius3 p - p 0 < 1 := by
  have htri : spatialRadius3 p ≤ spatialRadius3 (p - q) + spatialRadius3 q := by
    simpa using spatial_radius_triangle3 0 q p
  change |q 0| + spatialRadius3 q ≤ 1 at hq
  unfold chronological3 at hqp
  linarith [neg_le_abs (q 0)]

theorem future_chronological_margin3 {p q : LorentzPoint3}
    (hq : q ∈ closedLorentzDiamond3) (hpq : chronological3 p q) :
    spatialRadius3 p + p 0 < 1 := by
  have htri : spatialRadius3 p ≤ spatialRadius3 (q - p) + spatialRadius3 q := by
    simpa [spatial_radius_sub_symm3 p q] using spatial_radius_triangle3 0 q p
  change |q 0| + spatialRadius3 q ≤ 1 at hq
  unfold chronological3 at hpq
  linarith [le_abs_self (q 0)]

theorem lorentz_waist_no_closed_neighbors3 {p q : LorentzPoint3}
    (hp : p ∈ lorentzWaist3) (hq : q ∈ closedLorentzDiamond3) :
    ¬chronological3 p q ∧ ¬chronological3 q p := by
  change p 0 = 0 ∧ spatialRadius3 p = 1 at hp
  constructor
  · intro h
    have hm := future_chronological_margin3 hq h
    rw [hp.1, hp.2] at hm
    norm_num at hm
  · intro h
    have hm := past_chronological_margin3 hq h
    rw [hp.1, hp.2] at hm
    norm_num at hm

theorem interior_past_iff3 {p : LorentzPoint3} (hp : p ∈ closedLorentzDiamond3) :
    (∃ q ∈ lorentzDiamond3, chronological3 q p) ↔ spatialRadius3 p - p 0 < 1 := by
  constructor
  · rintro ⟨q, hq, hqp⟩
    exact past_chronological_margin3 (lorentz_diamond_subset_closed3 hq) hqp
  · intro h
    refine ⟨timeShift3 p (-((1 - spatialRadius3 p + p 0) / 2)), ?_⟩
    exact past_time_shift_interior3 hp (by linarith) (by linarith)

theorem interior_future_iff3 {p : LorentzPoint3} (hp : p ∈ closedLorentzDiamond3) :
    (∃ q ∈ lorentzDiamond3, chronological3 p q) ↔ spatialRadius3 p + p 0 < 1 := by
  constructor
  · rintro ⟨q, hq, hpq⟩
    exact future_chronological_margin3 (lorentz_diamond_subset_closed3 hq) hpq
  · intro h
    refine ⟨timeShift3 p ((1 - spatialRadius3 p - p 0) / 2), ?_⟩
    exact future_time_shift_interior3 hp (by linarith) (by linarith)

/-- The open diamond is intrinsic in the closed chronological representation. -/
theorem lorentz_interior_iff_neighbors3 {p : LorentzPoint3} (hp : p ∈ closedLorentzDiamond3) :
    p ∈ lorentzDiamond3 ↔ (∃ q ∈ lorentzDiamond3, chronological3 q p) ∧
      (∃ q ∈ lorentzDiamond3, chronological3 p q) := by
  rw [interior_past_iff3 hp, interior_future_iff3 hp]
  change |p 0| + spatialRadius3 p < 1 ↔ _
  constructor
  · intro h
    constructor <;> linarith [le_abs_self (p 0), neg_le_abs (p 0)]
  · rintro ⟨h1, h2⟩
    rcases le_total 0 (p 0) with ht | ht
    · rw [abs_of_nonneg ht]; linarith
    · rw [abs_of_nonpos ht]; linarith

theorem lorentz_waist_iff_no_neighbors3 {p : LorentzPoint3} (hp : p ∈ closedLorentzDiamond3) :
    p ∈ lorentzWaist3 ↔ (¬∃ q ∈ lorentzDiamond3, chronological3 q p) ∧
      (¬∃ q ∈ lorentzDiamond3, chronological3 p q) := by
  rw [interior_past_iff3 hp, interior_future_iff3 hp]
  change (p 0 = 0 ∧ spatialRadius3 p = 1) ↔ _
  constructor
  · rintro ⟨ht, hr⟩
    simp [ht, hr]
  · rintro ⟨h1, h2⟩
    have hr := (closed_lorentz_diamond_bounds3 hp).2
    constructor <;> linarith [not_lt.mp h1, not_lt.mp h2]

/-- Inclusion of nonempty interior pasts forces the closed causal relation. -/
theorem causal3_of_past_inclusion {p q : LorentzPoint3}
    (hp : p ∈ closedLorentzDiamond3) (hne : ∃ z ∈ lorentzDiamond3, chronological3 z p)
    (hinc : ∀ z ∈ lorentzDiamond3, chronological3 z p → chronological3 z q) : causal3 p q := by
  by_contra hn
  unfold causal3 at hn
  let d := spatialRadius3 (q - p) - (q 0 - p 0)
  have hd : 0 < d := by dsimp [d]; linarith [lt_of_not_ge hn]
  have hm : 0 < 1 - spatialRadius3 p + p 0 := by
    linarith [(interior_past_iff3 hp).mp hne]
  let s := min d (1 - spatialRadius3 p + p 0) / 2
  have hs : 0 < s := half_pos (lt_min hd hm)
  have hsm : s < 1 - spatialRadius3 p + p 0 := by
    dsimp [s]
    linarith [min_le_right d (1 - spatialRadius3 p + p 0)]
  have hsd : s < d := by
    dsimp [s]
    linarith [min_le_left d (1 - spatialRadius3 p + p 0)]
  obtain ⟨hz, hzp⟩ := past_time_shift_interior3 hp hs hsm
  have hzq := hinc _ hz hzp
  unfold chronological3 at hzq
  rw [time_shift_sub_radius3, time_shift_time3] at hzq
  dsimp [d] at hsd
  linarith

/-- The dual inclusion statement needs a nonempty interior future. -/
theorem causal3_of_future_inclusion {p q : LorentzPoint3}
    (hp : p ∈ closedLorentzDiamond3) (hne : ∃ z ∈ lorentzDiamond3, chronological3 p z)
    (hinc : ∀ z ∈ lorentzDiamond3, chronological3 p z → chronological3 q z) : causal3 q p := by
  by_contra hn
  unfold causal3 at hn
  let d := spatialRadius3 (p - q) - (p 0 - q 0)
  have hd : 0 < d := by dsimp [d]; linarith [lt_of_not_ge hn]
  have hm : 0 < 1 - spatialRadius3 p - p 0 := by
    linarith [(interior_future_iff3 hp).mp hne]
  let s := min d (1 - spatialRadius3 p - p 0) / 2
  have hs : 0 < s := half_pos (lt_min hd hm)
  have hsm : s < 1 - spatialRadius3 p - p 0 := by
    dsimp [s]
    linarith [min_le_right d (1 - spatialRadius3 p - p 0)]
  have hsd : s < d := by
    dsimp [s]
    linarith [min_le_left d (1 - spatialRadius3 p - p 0)]
  obtain ⟨hz, hpz⟩ := future_time_shift_interior3 hp hs hsm
  have hqz := hinc _ hz hpz
  unfold chronological3 at hqz
  rw [time_shift_radius_sub3, time_shift_time3] at hqz
  dsimp [d] at hsd
  linarith

def SameChronologicalProfile3 (p q : LorentzPoint3) : Prop :=
  (∀ z ∈ lorentzDiamond3, chronological3 z p ↔ chronological3 z q) ∧
    (∀ z ∈ lorentzDiamond3, chronological3 p z ↔ chronological3 q z)

/-- Exactly the waist circle is collapsed by interior chronological profiles. -/
theorem chronological_profile_eq_iff3 {p q : LorentzPoint3}
    (hp : p ∈ closedLorentzDiamond3) (hq : q ∈ closedLorentzDiamond3) :
    SameChronologicalProfile3 p q ↔ p = q ∨ (p ∈ lorentzWaist3 ∧ q ∈ lorentzWaist3) := by
  constructor
  · intro h
    by_cases hP : ∃ z ∈ lorentzDiamond3, chronological3 z p
    · have hQ : ∃ z ∈ lorentzDiamond3, chronological3 z q := by
        obtain ⟨z, hz, hzp⟩ := hP
        exact ⟨z, hz, (h.1 z hz).mp hzp⟩
      exact Or.inl (causal3_antisymmetric
        (causal3_of_past_inclusion hp hP (fun z hz => (h.1 z hz).mp))
        (causal3_of_past_inclusion hq hQ (fun z hz => (h.1 z hz).mpr)))
    · by_cases hF : ∃ z ∈ lorentzDiamond3, chronological3 p z
      · have hQ : ∃ z ∈ lorentzDiamond3, chronological3 q z := by
          obtain ⟨z, hz, hpz⟩ := hF
          exact ⟨z, hz, (h.2 z hz).mp hpz⟩
        exact Or.inl (causal3_antisymmetric
          (causal3_of_future_inclusion hq hQ (fun z hz => (h.2 z hz).mpr))
          (causal3_of_future_inclusion hp hF (fun z hz => (h.2 z hz).mp)))
      · have hQP : ¬∃ z ∈ lorentzDiamond3, chronological3 z q := by
          rintro ⟨z, hz, hzq⟩
          exact hP ⟨z, hz, (h.1 z hz).mpr hzq⟩
        have hQF : ¬∃ z ∈ lorentzDiamond3, chronological3 q z := by
          rintro ⟨z, hz, hqz⟩
          exact hF ⟨z, hz, (h.2 z hz).mpr hqz⟩
        exact Or.inr ⟨(lorentz_waist_iff_no_neighbors3 hp).mpr ⟨hP, hF⟩,
          (lorentz_waist_iff_no_neighbors3 hq).mpr ⟨hQP, hQF⟩⟩
  · rintro (rfl | ⟨hP, hQ⟩)
    · exact ⟨fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩
    · have hpN := (lorentz_waist_iff_no_neighbors3 hp).mp hP
      have hqN := (lorentz_waist_iff_no_neighbors3 hq).mp hQ
      constructor
      · intro z hz
        constructor
        · intro h; exact False.elim (hpN.1 ⟨z, hz, h⟩)
        · intro h; exact False.elim (hqN.1 ⟨z, hz, h⟩)
      · intro z hz
        constructor
        · intro h; exact False.elim (hpN.2 ⟨z, hz, h⟩)
        · intro h; exact False.elim (hqN.2 ⟨z, hz, h⟩)


#print axioms lorentz_waist_subset_closed3
#print axioms isClosed_lorentzWaist3
#print axioms isCompact_lorentzWaist3
#print axioms time_shift_time3
#print axioms time_shift_radius3
#print axioms time_shift_sub_radius3
#print axioms time_shift_radius_sub3
#print axioms spatial_radius_sub_symm3
#print axioms spatial_radius_self_sub3
#print axioms causal3_refl
#print axioms causal3_transitive
#print axioms chronological3_trans_causal3
#print axioms causal3_trans_chronological3
#print axioms causal3_antisymmetric
#print axioms bottom_sub_radius3
#print axioms top_sub_radius3
#print axioms closed_lorentz_diamond_iff_tips3
#print axioms lorentz_diamond_iff_tips3
#print axioms causal_diamond_subset_closed3
#print axioms causal_diamond_subset_open3
#print axioms isClosed_causalDiamond3
#print axioms isCompact_causalDiamond3
#print axioms open_lorentz_causal_diamond3
#print axioms past_time_shift_interior3
#print axioms future_time_shift_interior3
#print axioms past_chronological_margin3
#print axioms future_chronological_margin3
#print axioms lorentz_waist_no_closed_neighbors3
#print axioms interior_past_iff3
#print axioms interior_future_iff3
#print axioms lorentz_interior_iff_neighbors3
#print axioms lorentz_waist_iff_no_neighbors3
#print axioms causal3_of_past_inclusion
#print axioms causal3_of_future_inclusion
#print axioms chronological_profile_eq_iff3

end

end QuantyraNullCone
