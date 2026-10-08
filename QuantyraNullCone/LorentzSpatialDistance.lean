import QuantyraNullCone.LorentzVolumeCoordinates
import QuantyraNullCone.LorentzGaugeBounds

namespace QuantyraNullCone

noncomputable section

abbrev SpatialO2 := SpatialPoint3 ≃ₗᵢ[ℝ] SpatialPoint3

def spatialAction3 (R : SpatialO2) (p : LorentzPoint3) : LorentzPoint3 :=
  lorentzPoint3 (p 0) (R (splitLorentzEquiv3 p).2 0) (R (splitLorentzEquiv3 p).2 1)

theorem spatial_action_time3 (R : SpatialO2) (p : LorentzPoint3) : spatialAction3 R p 0 = p 0 := rfl

theorem spatial_action_split3 (R : SpatialO2) (p : LorentzPoint3) :
    (splitLorentzEquiv3 (spatialAction3 R p)).2 = R (splitLorentzEquiv3 p).2 := by
  ext i
  fin_cases i <;> rfl

theorem spatial_action_radius3 (R : SpatialO2) (p : LorentzPoint3) :
    spatialRadius3 (spatialAction3 R p) = spatialRadius3 p := by
  rw [← split_lorentz_radius3, spatial_action_split3, R.norm_map, split_lorentz_radius3]

theorem spatial_action_squared3 (R : SpatialO2) (p : LorentzPoint3) :
    spatialSquared3 (spatialAction3 R p) = spatialSquared3 p := by
  rw [← spatial_radius_sq3, spatial_action_radius3, spatial_radius_sq3]

theorem gauge_density_spatial_invariant3 (R : SpatialO2) (p : LorentzPoint3) :
    gaugeDensity3 (spatialAction3 R p) = gaugeDensity3 p := by
  simp only [gaugeDensity3, flowFactor3, flowDenominator3,
    spatial_action_time3, spatial_action_squared3]

def gaugeAnchor3 : LorentzPoint3 := lorentzPoint3 (1 / 2) 0 0

theorem gauge_anchor_mem3 : gaugeAnchor3 ∈ lorentzDiamond3 := by
  norm_num [gaugeAnchor3, lorentzPoint3, lorentzDiamond3, spatialRadius3, spatialSquared3,
    Matrix.cons_val_two]

theorem gauge_anchor_density_gt3 : 1 < gaugeDensity3 gaugeAnchor3 := by
  norm_num [gaugeDensity3, flowFactor3, flowDenominator3, gaugeParameter3,
    gaugeAnchor3, lorentzPoint3, spatialSquared3, Matrix.cons_val_two]

/-- Coordinate supremum after an arbitrary spatial orthogonal transformation. -/
def gaugeSpatialSupDistance3 (R : SpatialO2) : ℝ :=
  sSup ((fun p => |gaugeDensity3 (spatialAction3 R p) - flatDensity3 p|) '' lorentzDiamond3)

/-- Actual infimum over all of O(2), including reflections. -/
def gaugeO2Distance3 : ℝ := sInf (Set.range gaugeSpatialSupDistance3)

theorem gauge_spatial_sup_constant3 (R : SpatialO2) :
    gaugeSpatialSupDistance3 R =
      sSup ((fun p => |gaugeDensity3 p - 1|) '' lorentzDiamond3) := by
  simp only [gaugeSpatialSupDistance3, gauge_density_spatial_invariant3, flatDensity3]

theorem gauge_spatial_sup_positive3 :
    0 < sSup ((fun p => |gaugeDensity3 p - 1|) '' lorentzDiamond3) := by
  have hBound : BddAbove ((fun p => |gaugeDensity3 p - 1|) '' lorentzDiamond3) := by
    refine ⟨1 / 2, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨hLo, hHi⟩ := gauge_density_bounds3 (lorentz_diamond_subset_closed3 hp)
    apply abs_le.mpr
    constructor <;> linarith
  have hAnchor := le_csSup hBound (Set.mem_image_of_mem
    (fun p => |gaugeDensity3 p - 1|) gauge_anchor_mem3)
  have hStrict : 0 < |gaugeDensity3 gaugeAnchor3 - 1| := by
    rw [abs_of_pos (sub_pos.mpr gauge_anchor_density_gt3)]
    exact sub_pos.mpr gauge_anchor_density_gt3
  exact hStrict.trans_le hAnchor

theorem gauge_o2_distance_positive3 : 0 < gaugeO2Distance3 := by
  have hRange : Set.range gaugeSpatialSupDistance3 =
      {sSup ((fun p => |gaugeDensity3 p - 1|) '' lorentzDiamond3)} := by
    ext x
    constructor
    · rintro ⟨R, rfl⟩
      exact gauge_spatial_sup_constant3 R
    · intro hx
      refine ⟨LinearIsometryEquiv.refl ℝ SpatialPoint3, ?_⟩
      exact (gauge_spatial_sup_constant3 _).trans (Set.mem_singleton_iff.mp hx).symm
  unfold gaugeO2Distance3
  rw [hRange, csInf_singleton]
  exact gauge_spatial_sup_positive3

#print axioms gauge_density_spatial_invariant3
#print axioms gauge_anchor_density_gt3
#print axioms gauge_o2_distance_positive3

end

end QuantyraNullCone
