import DistinctDistances.TrackD.GeoRadial

/-! The affine-span split for nonlinear curves in dimension at least four. -/

namespace DistinctDistances.TrackD.GeoRadial

open scoped BigOperators Classical
noncomputable section
variable {d : ℕ}

theorem nonlinear_span_ge_two (Y : AffineVariety d) (hY : IsCurve Y) (hnl : ¬ IsLine Y) :
    2 ≤ Module.finrank ℂ (complexSpan Y).direction := by
  let S : AffineSubspace ℂ (Point d) := complexSpan Y
  change 2 ≤ Module.finrank ℂ S.direction
  obtain ⟨a, ha⟩ := (Bridges.curve_points_infinite Y hY.1 hY.2).nonempty
  have haS : a ∈ S := subset_affineSpan ℂ _ ha
  have hYS : Y.points ⊆ (AffineSubspace.mk' a S.direction : Set (Point d)) := by
    rw [AffineSubspace.mk'_eq haS]
    exact subset_affineSpan ℂ _
  have hle : 1 ≤ Module.finrank ℂ S.direction :=
    GeoCommon.dim_le_of_mem_flat Y 1 hY.1 hY.2 a S.direction hYS _ rfl
  by_contra htwo
  have hr : Module.finrank ℂ S.direction = 1 := by omega
  have hpts := GeoCommon.span_eq_of_dim_eq Y 1 hY.1 hY.2 ⟨a, ha⟩
    a S.direction hYS _ rfl hr.symm
  obtain ⟨v, hv⟩ : ∃ v : S.direction, v ≠ 0 :=
    Module.finrank_pos_iff_exists_ne_zero.mp (by rw [hr]; norm_num)
  have hv0 : (v : Point d) ≠ 0 := fun h => hv (Subtype.ext h)
  have hspan : (ℂ ∙ (v : Point d)) ≤ S.direction :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr v.property)
  have hspan_eq : (ℂ ∙ (v : Point d)) = S.direction :=
    Submodule.eq_of_le_of_finrank_eq hspan (by rw [finrank_span_singleton hv0, hr])
  rw [← hspan_eq] at hpts
  apply hnl
  refine ⟨a, (v : Point d), hv0, ?_⟩
  rw [hpts]
  ext x
  simp only [SetLike.mem_coe, AffineSubspace.mem_mk', vsub_eq_sub,
    Submodule.mem_span_singleton, Set.mem_setOf_eq]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    calc
      x = (x-a)+a := by abel
      _ = a + t • (v : Point d) := by rw [← ht]; abel
  · rintro ⟨t, rfl⟩
    exact ⟨t, by abel⟩

theorem projects_span (p : Pt d) (Y : AffineVariety d) (hY : IsCurve Y)
    (hnl : ¬ IsLine Y) (C : ProjectiveFamily.Family d) (hC : IsDirectionalFamily C)
    (hproj : ProjectsInto C p Y) :
    Module.finrank ℂ (complexSpan Y).direction ≤ 3 ∧
      (Module.finrank ℂ (complexSpan Y).direction = 3 → toC p ∈ complexSpan Y) := by
  obtain ⟨hmem, _⟩ := radial_member p Y hY hnl C hC hproj
  obtain ⟨W, hW, hrep⟩ := (hC _ hmem).2.2
  let S : AffineSubspace ℂ (Point d) := complexSpan Y
  let G : AffineSubspace ℂ (Point d) := AffineSubspace.mk' (toC p) W
  change Module.finrank ℂ S.direction ≤ 3 ∧
    (Module.finrank ℂ S.direction = 3 → toC p ∈ S)
  have hYG : Y.points ⊆ G := radial_subset_flat (toC p) Y W hrep
  have hSG : S ≤ G := affineSpan_le.mpr hYG
  have hdir : S.direction ≤ G.direction := AffineSubspace.direction_le hSG
  have hfin : Module.finrank ℂ S.direction ≤ Module.finrank ℂ G.direction :=
    Submodule.finrank_mono hdir
  have hG3 : Module.finrank ℂ G.direction ≤ 3 := by
    dsimp only [G]
    rw [AffineSubspace.direction_mk']
    exact hW
  refine ⟨hfin.trans hG3, ?_⟩
  intro hS3
  change Module.finrank ℂ S.direction = 3 at hS3
  have hdim : Module.finrank ℂ S.direction = Module.finrank ℂ G.direction := by omega
  have hdirs := Submodule.eq_of_le_of_finrank_eq hdir hdim
  have hSne : (S : Set (Point d)).Nonempty :=
    (Bridges.curve_points_infinite Y hY.1 hY.2).nonempty.mono (subset_affineSpan ℂ _)
  have hEq : S = G :=
    AffineSubspace.eq_of_direction_eq_of_nonempty_of_le hdirs hSne hSG
  have hpG : toC p ∈ G := AffineSubspace.self_mem_mk' _ _
  rwa [← hEq] at hpG

theorem proper_span (d : ℕ) (hd : 4 ≤ d) (Y : AffineVariety d)
    (hspan : Module.finrank ℂ (complexSpan Y).direction ≤ 3) : complexSpan Y ≠ ⊤ := by
  intro htop
  rw [htop, AffineSubspace.direction_top, finrank_top, GeoCommon.finrank_point] at hspan
  omega

theorem exterior_planar (p : Pt d) (Y : AffineVariety d) (hY : IsCurve Y)
    (hnl : ¬ IsLine Y) (C : ProjectiveFamily.Family d) (hC : IsDirectionalFamily C)
    (hproj : ProjectsInto C p Y) (hp : toC p ∉ complexSpan Y) :
    Module.finrank ℂ (complexSpan Y).direction = 2 := by
  have hge := nonlinear_span_ge_two Y hY hnl
  obtain ⟨hle, hcenter⟩ := projects_span p Y hY hnl C hC hproj
  have hne : Module.finrank ℂ (complexSpan Y).direction ≠ 3 := fun h => hp (hcenter h)
  omega

end
end DistinctDistances.TrackD.GeoRadial
