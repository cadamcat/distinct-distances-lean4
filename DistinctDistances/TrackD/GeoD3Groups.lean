import DistinctDistances.TrackD.GeoD3Degree

/-! Groups with nonlinear radial image and low center multiplicity. -/

namespace DistinctDistances.TrackD.GeoD3
open scoped BigOperators Classical
noncomputable section

 def group (Cf : Pt 3 → ProjectiveFamily.Family 3) (p : Pt 3)
    (Y : AffineVariety 3) : Option (ProjectiveVariety 3) :=
  if ProjectsInto (Cf p) p Y ∧ 2 ≤ (radialImage (toC p) Y).degree ∧
      Y.multiplicity (toC p) ≤ Y.degree / 2 then some (radialImage (toC p) Y) else none

 def mapDegree (p : Pt 3) (Y : AffineVariety 3) : ℕ := max 1 (TrackA.radialMapDegree (toC p) Y)

 theorem group_eq_some (Cf : Pt 3 → ProjectiveFamily.Family 3) (p : Pt 3)
    (Y : AffineVariety 3) (γ : ProjectiveVariety 3) : group Cf p Y = some γ ↔
    ProjectsInto (Cf p) p Y ∧ 2 ≤ (radialImage (toC p) Y).degree ∧
      Y.multiplicity (toC p) ≤ Y.degree / 2 ∧ radialImage (toC p) Y = γ := by
  constructor
  · intro h
    unfold group at h
    split_ifs at h with hc
    · exact ⟨hc.1, hc.2.1, hc.2.2, Option.some.inj h⟩
  · rintro ⟨hproj, hdeg, hmult, he⟩
    unfold group
    rw [if_pos ⟨hproj, hdeg, hmult⟩, he]

 theorem group_mem (Cf : Pt 3 → ProjectiveFamily.Family 3) (p : Pt 3)
    (Y : AffineVariety 3) (hY : IsCurve Y) (hnl : ¬ IsLine Y)
    (hC : IsDirectionalFamily (Cf p)) (γ : ProjectiveVariety 3)
    (hg : group Cf p Y = some γ) : γ ∈ Cf p := by
  obtain ⟨hproj, _, _, he⟩ := (group_eq_some Cf p Y γ).mp hg
  have h := (GeoRadial.radial_member p Y hY hnl (Cf p) hC hproj).1
  rwa [he] at h

 theorem group_mapDegree_eq (Cf : Pt 3 → ProjectiveFamily.Family 3) (p : Pt 3)
    (Y : AffineVariety 3) (hY : IsCurve Y) (hnl : ¬ IsLine Y)
    (hC : IsDirectionalFamily (Cf p)) (γ : ProjectiveVariety 3)
    (hg : group Cf p Y = some γ) : mapDegree p Y = TrackA.radialMapDegree (toC p) Y := by
  obtain ⟨hproj, _, _, _⟩ := (group_eq_some Cf p Y γ).mp hg
  have himage := (GeoRadial.radial_member p Y hY hnl (Cf p) hC hproj).2
  have hr := TrackA.dep_radial_degree_exists Y hY.1 1 (by norm_num) hY.2 (toC p) himage
  exact max_eq_right (by have h := hr.1; omega)

 theorem group_mass_le (P : Finset (Pt 3)) (𝒴 : Finset (AffineVariety 3))
    (S : AffineVariety 3 → Finset (Pt 3)) (hS : Assignment P 𝒴 S)
    (Cf : Pt 3 → ProjectiveFamily.Family 3) (p : Pt 3) (hC : IsDirectionalFamily (Cf p))
    (Y : AffineVariety 3) (hYmem : Y ∈ 𝒴) (hY : IsCurve Y) (hnl : ¬ IsLine Y)
    (γ : ProjectiveVariety 3) (hg : group Cf p Y = some γ)
    (C : ℝ) (hC0 : 0 ≤ C)
    (hsample : (massOn P Y.points : ℝ) ≤ C * (Y.degree : ℝ) * cfgM P) :
    ((S Y).card : ℝ) ≤ (2*C) * cfgM P * mapDegree p Y * GeoD4.groupDegree γ := by
  obtain ⟨hproj, hdeg, hmult, he⟩ := (group_eq_some Cf p Y γ).mp hg
  have himage := (GeoRadial.radial_member p Y hY hnl (Cf p) hC hproj).2
  have hr := TrackA.dep_radial_degree_exists Y hY.1 1 (by norm_num) hY.2 (toC p) himage
  have hf := TrackA.poly_projection_radial Y hY.1 1 (by norm_num) hY.2 (toC p) himage
    (TrackA.radialMapDegree (toC p) Y) hr
  rw [he] at hf
  have hYdeg : Y.degree ≤ 2 * (TrackA.radialMapDegree (toC p) Y : ℚ) * γ.degree := by linarith
  have heq : GeoD4.groupDegree γ = (γ.degree : ℝ) := by
    rw [GeoD4.groupDegree]
    exact max_eq_right (GeoCounting.projective_degree_ge_one γ
      (hC γ (group_mem Cf p Y hY hnl hC γ hg)).1)
  have hdegR : (Y.degree : ℝ) ≤ 2 * (mapDegree p Y : ℝ) * (γ.degree : ℝ) := by
    rw [group_mapDegree_eq Cf p Y hY hnl hC γ hg]
    exact_mod_cast hYdeg
  have hM0 : 0 ≤ cfgM P := by unfold cfgM; positivity
  calc
    _ ≤ (massOn P Y.points : ℝ) := by
      exact_mod_cast GeoCounting.assigned_mass_le P 𝒴 S hS Y hYmem
    _ ≤ _ := hsample
    _ ≤ C * (2 * (mapDegree p Y : ℝ) * (γ.degree : ℝ)) * cfgM P := by
      gcongr
    _ = _ := by rw [heq]; ring

 theorem group_sum_le (P : Finset (Pt 3)) (Cf : Pt 3 → ProjectiveFamily.Family 3)
    (hCf : ∀ p ∈ P, IsDirectionalFamily (Cf p))
    (Y : AffineVariety 3) (hY : IsCurve Y) (hnl : ¬ IsLine Y)
    (Q : Pt 3 → Prop) (C : ℝ)
    (hbound : ∑ p ∈ (P.filter Q).image toC,
      (((radialImage p Y).degree : ℝ))⁻¹ ^ 2 ≤ C) :
    (∑ p ∈ P, ∑ γ ∈ Cf p,
      if group Cf p Y = some γ ∧ Q p then (GeoD4.groupDegree γ)⁻¹ ^ 2 else 0) ≤ C := by
  have hpoint : ∀ p ∈ P, (∑ γ ∈ Cf p,
      if group Cf p Y = some γ ∧ Q p then (GeoD4.groupDegree γ)⁻¹ ^ 2 else 0) ≤
      if Q p then (((radialImage (toC p) Y).degree : ℝ))⁻¹ ^ 2 else 0 := by
    intro p hp
    cases hg : group Cf p Y with
    | none => simp [hg]; split_ifs <;> positivity
    | some γ =>
      have hγ := group_mem Cf p Y hY hnl (hCf p hp) γ hg
      rw [Finset.sum_eq_single γ]
      · have he := (group_eq_some Cf p Y γ).mp hg
        have hD : GeoD4.groupDegree γ = (γ.degree : ℝ) :=
          max_eq_right (GeoCounting.projective_degree_ge_one γ (hCf p hp γ hγ).1)
        simp [hg, hD, he.2.2.2]
      · intro γ' hγ' hne; simp [hg, Ne.symm hne]
      · intro hnot; exact (hnot hγ).elim
  calc
    _ ≤ ∑ p ∈ P, if Q p then (((radialImage (toC p) Y).degree : ℝ))⁻¹ ^ 2 else 0 :=
      Finset.sum_le_sum hpoint
    _ = ∑ p ∈ P.filter Q, (((radialImage (toC p) Y).degree : ℝ))⁻¹ ^ 2 :=
      (Finset.sum_filter ..).symm
    _ = ∑ p ∈ (P.filter Q).image toC, (((radialImage p Y).degree : ℝ))⁻¹ ^ 2 := by
      rw [Finset.sum_image]
      exact fun _ _ _ _ h => GeoCounting.toC_injective h
    _ ≤ C := hbound

end
end DistinctDistances.TrackD.GeoD3
