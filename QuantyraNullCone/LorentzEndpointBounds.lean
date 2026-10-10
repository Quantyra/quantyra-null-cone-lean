import QuantyraNullCone.LorentzCurvePerturbation

namespace QuantyraNullCone

open MeasureTheory Set

noncomputable section

def timeMargin3 (p q : LorentzPoint3) : ℝ := q 0 - p 0 - spatialRadius3 (q - p)

theorem time_margin_pos_iff3 (p q : LorentzPoint3) :
    0 < timeMargin3 p q ↔ chronological3 p q := sub_pos

theorem abs_time_le_norm3 (v : LorentzPoint3) : |v 0| ≤ ‖v‖ :=
  PiLp.norm_apply_le v 0

theorem spatial_radius_le_norm3 (v : LorentzPoint3) : spatialRadius3 v ≤ ‖v‖ := by
  have h := lorentz_norm_sq3 v
  nlinarith [spatial_radius_sq3 v, spatial_radius_nonneg3 v, norm_nonneg v, sq_nonneg (v 0)]

theorem spatial_radius_difference3 (u v : LorentzPoint3) :
    |spatialRadius3 u - spatialRadius3 v| ≤ ‖u - v‖ := by
  have h1 := spatial_radius_triangle3 0 v u
  have h2 := spatial_radius_triangle3 0 u v
  simp only [sub_zero] at h1 h2
  rw [spatial_radius_sub_symm3 v u] at h2
  exact abs_le.mpr ⟨by linarith [spatial_radius_le_norm3 (u - v)],
    by linarith [spatial_radius_le_norm3 (u - v)]⟩

theorem time_margin_difference3 (p q p' q' : LorentzPoint3) :
    |timeMargin3 p' q' - timeMargin3 p q| ≤ 2 * ‖(q' - p') - (q - p)‖ := by
  have ht := abs_time_le_norm3 ((q' - p') - (q - p))
  have hs := spatial_radius_difference3 (q' - p') (q - p)
  have he : timeMargin3 p' q' - timeMargin3 p q =
      (((q' - p') - (q - p)) 0) - (spatialRadius3 (q' - p') - spatialRadius3 (q - p)) := by
    unfold timeMargin3
    simp only [PiLp.sub_apply]
    ring
  rw [he]
  exact (abs_sub _ _).trans (by linarith)

theorem endpoint_increment_difference3 {p q p' q' : LorentzPoint3} {eps : ℝ}
    (hp : ‖p' - p‖ ≤ eps) (hq : ‖q' - q‖ ≤ eps) :
    ‖(q' - p') - (q - p)‖ ≤ 2 * eps := by
  have he : (q' - p') - (q - p) = (q' - q) - (p' - p) := by abel
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith)

theorem endpoint_residual_future3 {p q p' q' : LorentzPoint3} {a eta : ℝ}
    (hmargin : a ≤ timeMargin3 p q) (heta : 0 ≤ eta)
    (hdelta : 2 * ‖(q' - p') - (q - p)‖ ≤ eta * a) :
    spatialRadius3 (endpointResidual3 p q p' q' (1 - eta)) ≤
      endpointResidual3 p q p' q' (1 - eta) 0 := by
  let delta := (q' - p') - (q - p)
  have he : endpointResidual3 p q p' q' (1 - eta) = delta + eta • (q - p) := by
    ext i
    change (q' i - p' i) - (1 - eta) * (q i - p i) =
      ((q' i - p' i) - (q i - p i)) + eta * (q i - p i)
    ring
  rw [he]
  have hrad := spatial_radius_add_le3 delta (eta • (q - p))
  rw [spatial_radius_smul3, abs_of_nonneg heta] at hrad
  have htime := (abs_le.mp (abs_time_le_norm3 delta)).1
  have hs := spatial_radius_le_norm3 delta
  have hm := mul_le_mul_of_nonneg_left hmargin heta
  change eta * a ≤ eta * (q 0 - p 0 - spatialRadius3 (q - p)) at hm
  change spatialRadius3 (delta + eta • (q - p)) ≤ delta 0 + eta * (q 0 - p 0)
  change 2 * ‖delta‖ ≤ eta * a at hdelta
  nlinarith

theorem weighted_time_le_two_hi3 {w : LorentzPoint3 → ℝ} {lo hi : ℝ}
    (hw : InTimeWeightClass3 w lo hi) (p q : LorentzPoint3) :
    weightedTimeSeparation3 w p q ≤ 2 * hi := by
  have hh : 0 ≤ hi := hw.lower_pos.le.trans hw.lower_le_upper
  apply csSup_le (by simp : (insert 0 (Set.range
    (fun c : FutureCurve3 p q => c.weightedLength w))).Nonempty)
  rintro x (hx | ⟨c, rfl⟩)
  · subst x
    positivity
  · have h := (c.weightedLength_bounds hw).2.trans
      (mul_le_mul_of_nonneg_left c.flatLength_le_two hh)
    linarith

/-- A uniform pointwise weight comparison for adjusted curves passes to the actual supremum. -/
theorem weighted_time_adjust_lower3 {w : LorentzPoint3 → ℝ} {lo hi delta : ℝ}
    (hw : InTimeWeightClass3 w lo hi) {p q p' q' : LorentzPoint3}
    (hpq : chronological3 p q) (hp' : p' ∈ closedLorentzDiamond3)
    (hq' : q' ∈ closedLorentzDiamond3) {k : ℝ} (hk : 0 ≤ k) (hk' : k ≤ 1)
    (he : spatialRadius3 (endpointResidual3 p q p' q' k) ≤ endpointResidual3 p q p' q' k 0)
    (hdelta : 0 ≤ delta)
    (hclose : ∀ x ∈ closedLorentzDiamond3, ∀ y ∈ closedLorentzDiamond3,
      ‖x - y‖ ≤ ‖p' - p‖ + ‖(q' - p') - (q - p)‖ + 4 * (1 - k) → |w x - w y| ≤ delta) :
    k * weightedTimeSeparation3 w p q - 2 * delta ≤ weightedTimeSeparation3 w p' q' := by
  have hn := weighted_time_separation_nonneg3 hw p' q'
  rcases hk.eq_or_lt with hk0 | hkpos
  · rw [← hk0]
    nlinarith
  have hb : weightedTimeSeparation3 w p q ≤ (weightedTimeSeparation3 w p' q' + 2 * delta) / k := by
    apply csSup_le (by simp : (insert 0 (Set.range
      (fun c : FutureCurve3 p q => c.weightedLength w))).Nonempty)
    rintro x (hx | ⟨c, rfl⟩)
    · subst x
      exact div_nonneg (by positivity) hk
    · have h := c.adjust_weightedLength_lower hpq hp' hq' hk hk' he hw hdelta (by
        intro t ht
        exact hclose _ ((c.adjust hpq hp' hq' hk he).inDiamond t ht) _ (c.inDiamond t ht)
          (c.adjust_point_distance hpq hp' hq' hk hk' he ht))
      have hupper := (c.adjust hpq hp' hq' hk he).weightedLength_le_timeSeparation hw
      apply (le_div_iff₀ hkpos).mpr
      nlinarith
  have h := (le_div_iff₀ hkpos).mp hb
  nlinarith

theorem weighted_time_endpoint_bound3 {w : LorentzPoint3 → ℝ} {lo hi a eta delta : ℝ}
    (hw : InTimeWeightClass3 w lo hi) {p q p' q' : LorentzPoint3}
    (hp : p ∈ closedLorentzDiamond3) (hq : q ∈ closedLorentzDiamond3)
    (hp' : p' ∈ closedLorentzDiamond3) (hq' : q' ∈ closedLorentzDiamond3)
    (ha : 0 < a) (hmargin : a ≤ timeMargin3 p q) (hmargin' : a ≤ timeMargin3 p' q')
    (heta : 0 ≤ eta) (heta' : eta ≤ 1) (hdelta : 0 ≤ delta)
    (hinc : 2 * ‖(q' - p') - (q - p)‖ ≤ eta * a)
    (hclose : ∀ x ∈ closedLorentzDiamond3, ∀ y ∈ closedLorentzDiamond3,
      ‖x - y‖ ≤ ‖p' - p‖ + ‖(q' - p') - (q - p)‖ + 4 * eta → |w x - w y| ≤ delta) :
    |weightedTimeSeparation3 w p' q' - weightedTimeSeparation3 w p q| ≤ 2 * hi * eta + 2 * delta := by
  have hpq := (time_margin_pos_iff3 p q).mp (ha.trans_le hmargin)
  have hpq' := (time_margin_pos_iff3 p' q').mp (ha.trans_le hmargin')
  have hforward := weighted_time_adjust_lower3 hw hpq hp' hq'
    (sub_nonneg.mpr heta') (by linarith : 1 - eta ≤ 1)
    (endpoint_residual_future3 hmargin heta hinc) hdelta (by
      intro x hx y hy hxy
      apply hclose x hx y hy
      nlinarith)
  have hinv : 2 * ‖(q - p) - (q' - p')‖ ≤ eta * a := by rwa [norm_sub_rev]
  have hback := weighted_time_adjust_lower3 hw hpq' hp hq
    (sub_nonneg.mpr heta') (by linarith : 1 - eta ≤ 1)
    (endpoint_residual_future3 hmargin' heta hinv) hdelta (by
      intro x hx y hy hxy
      rw [norm_sub_rev p p', norm_sub_rev (q - p) (q' - p')] at hxy
      apply hclose x hx y hy
      nlinarith)
  have hupper := mul_le_mul_of_nonneg_right (weighted_time_le_two_hi3 hw p q) heta
  have hupper' := mul_le_mul_of_nonneg_right (weighted_time_le_two_hi3 hw p' q') heta
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

#print axioms time_margin_pos_iff3
#print axioms abs_time_le_norm3
#print axioms spatial_radius_le_norm3
#print axioms spatial_radius_difference3
#print axioms time_margin_difference3
#print axioms endpoint_increment_difference3
#print axioms endpoint_residual_future3
#print axioms weighted_time_le_two_hi3
#print axioms weighted_time_adjust_lower3
#print axioms weighted_time_endpoint_bound3

end
end QuantyraNullCone
