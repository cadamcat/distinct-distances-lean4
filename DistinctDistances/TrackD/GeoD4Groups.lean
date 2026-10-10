import DistinctDistances.TrackD.GeoCounting

/-! Groups of exterior planar curves with a common radial image. -/

namespace DistinctDistances.TrackD.GeoD4

open scoped BigOperators Classical
noncomputable section
variable {d : ℕ}

def exteriorGroup (Cf : Pt d → ProjectiveFamily.Family d) (p : Pt d)
    (Y : AffineVariety d) : Option (ProjectiveVariety d) :=
  if toC p ∉ complexSpan Y ∧ ProjectsInto (Cf p) p Y then
    some (radialImage (toC p) Y) else none

def groupDegree (γ : ProjectiveVariety d) : ℝ := max 1 (γ.degree : ℝ)

theorem group_eq_some (Cf : Pt d → ProjectiveFamily.Family d) (p : Pt d)
    (Y : AffineVariety d) (γ : ProjectiveVariety d) :
    exteriorGroup Cf p Y = some γ ↔
      toC p ∉ complexSpan Y ∧ ProjectsInto (Cf p) p Y ∧ radialImage (toC p) Y = γ := by
  constructor
  · intro h
    unfold exteriorGroup at h
    split_ifs at h with hc
    · exact ⟨hc.1, hc.2, Option.some.inj h⟩
  · rintro ⟨hp, hproj, he⟩
    simp [exteriorGroup, hp, hproj, he]

theorem group_mem (Cf : Pt d → ProjectiveFamily.Family d) (p : Pt d)
    (Y : AffineVariety d) (hY : IsCurve Y) (hnl : ¬ IsLine Y)
    (hC : IsDirectionalFamily (Cf p)) (γ : ProjectiveVariety d)
    (hgrp : exteriorGroup Cf p Y = some γ) : γ ∈ Cf p := by
  obtain ⟨_, hproj, he⟩ := (group_eq_some Cf p Y γ).mp hgrp
  have hmem := (GeoRadial.radial_member p Y hY hnl (Cf p) hC hproj).1
  rwa [he] at hmem

theorem group_degree_eq (Cf : Pt d → ProjectiveFamily.Family d) (p : Pt d)
    (Y : AffineVariety d) (hY : IsCurve Y) (hnl : ¬ IsLine Y)
    (hC : IsDirectionalFamily (Cf p)) (γ : ProjectiveVariety d)
    (hgrp : exteriorGroup Cf p Y = some γ) : groupDegree γ = (Y.degree : ℝ) := by
  obtain ⟨hp, hproj, he⟩ := (group_eq_some Cf p Y γ).mp hgrp
  have himage := (GeoRadial.radial_member p Y hY hnl (Cf p) hC hproj).2
  have hYS : Y.points ⊆ complexSpan Y := subset_affineSpan ℂ _
  have hdeg := GeoRadial.radial_degree_preserved (toC p) Y hY (complexSpan Y) hYS hp himage
  rw [he] at hdeg
  have hmem := group_mem Cf p Y hY hnl hC γ hgrp
  have hone := GeoCounting.projective_degree_ge_one γ (hC γ hmem).1
  rw [groupDegree, max_eq_right hone]
  exact_mod_cast hdeg

theorem degree_sum (C : ProjectiveFamily.Family d) (hC : IsDirectionalFamily C) :
    (∑ γ ∈ C, groupDegree γ) = (ProjectiveFamily.degree C : ℝ) := by
  calc
    _ = ∑ γ ∈ C, (γ.degree : ℝ) := by
      apply Finset.sum_congr rfl
      intro γ hγ
      exact max_eq_right (GeoCounting.projective_degree_ge_one γ (hC γ hγ).1)
    _ = _ := by simp [ProjectiveFamily.degree]

theorem group_mass_le (P : Finset (Pt d)) (𝒴 : Finset (AffineVariety d))
    (S : AffineVariety d → Finset (Pt d)) (hS : Assignment P 𝒴 S)
    (Cf : Pt d → ProjectiveFamily.Family d) (p : Pt d) (hC : IsDirectionalFamily (Cf p))
    (Y : AffineVariety d) (hYmem : Y ∈ 𝒴) (hY : IsCurve Y) (hnl : ¬ IsLine Y)
    (γ : ProjectiveVariety d) (hgrp : exteriorGroup Cf p Y = some γ)
    (C₁ : ℝ) (hsample : (massOn P Y.points : ℝ) ≤ C₁ * (Y.degree : ℝ) * cfgM P) :
    ((S Y).card : ℝ) ≤ C₁ * cfgM P * groupDegree γ := by
  calc
    _ ≤ (massOn P Y.points : ℝ) := by
      exact_mod_cast GeoCounting.assigned_mass_le P 𝒴 S hS Y hYmem
    _ ≤ _ := hsample
    _ = _ := by rw [group_degree_eq Cf p Y hY hnl hC γ hgrp]; ring

theorem pair_sum_le (P : Finset (Pt d)) (Cf : Pt d → ProjectiveFamily.Family d)
    (hCf : ∀ p ∈ P, IsDirectionalFamily (Cf p))
    (Y Y' : AffineVariety d) (hY : IsCurve Y) (hnl : ¬ IsLine Y)
    (C₂ : ℝ)
    (hfin : {p : Point d | p ∉ complexSpan Y ∧ p ∉ complexSpan Y' ∧
      radialImage p Y = radialImage p Y'}.Finite)
    (hcard : ({p : Point d | p ∉ complexSpan Y ∧ p ∉ complexSpan Y' ∧
      radialImage p Y = radialImage p Y'}.ncard : ℝ) ≤ C₂ * (Y.degree : ℝ)) :
    (∑ p ∈ P, ∑ γ ∈ Cf p,
      if exteriorGroup Cf p Y = some γ ∧ exteriorGroup Cf p Y' = some γ
      then (groupDegree γ)⁻¹ else 0) ≤ C₂ := by
  let T := {p : Point d | p ∉ complexSpan Y ∧ p ∉ complexSpan Y' ∧
    radialImage p Y = radialImage p Y'}
  have hD : (0 : ℝ) < Y.degree := by
    have h := Y.one_le_degree hY.1.ne_top
    exact_mod_cast (by linarith : (0 : ℚ) < Y.degree)
  have hpoint : ∀ p ∈ P, (∑ γ ∈ Cf p,
      if exteriorGroup Cf p Y = some γ ∧ exteriorGroup Cf p Y' = some γ
      then (groupDegree γ)⁻¹ else 0) ≤
      if toC p ∈ T then (Y.degree : ℝ)⁻¹ else 0 := by
    intro p hp
    cases hgrp : exteriorGroup Cf p Y with
    | none => simp [hgrp]; split_ifs <;> positivity
    | some γ =>
      have hγ := group_mem Cf p Y hY hnl (hCf p hp) γ hgrp
      rw [Finset.sum_eq_single γ]
      · by_cases hgrp' : exteriorGroup Cf p Y' = some γ
        · have h1 := (group_eq_some Cf p Y γ).mp hgrp
          have h2 := (group_eq_some Cf p Y' γ).mp hgrp'
          have hT : toC p ∈ T := ⟨h1.1, h2.1, h1.2.2.trans h2.2.2.symm⟩
          simp [hgrp, hgrp', hT, group_degree_eq Cf p Y hY hnl (hCf p hp) γ hgrp]
        · simp [hgrp, hgrp']; split_ifs <;> positivity
      · intro γ' hγ' hne
        simp [hgrp, Ne.symm hne]
      · intro hnot
        exact (hnot hγ).elim
  have hcount : ((P.filter (fun p => toC p ∈ T)).card : ℝ) ≤ C₂ * (Y.degree : ℝ) :=
    by
      convert GeoCounting.center_card_le P T hfin (C₂ * (Y.degree : ℝ)) hcard using 1
      congr 2
      ext p
      simp only [Finset.mem_filter]
  calc
    _ ≤ ∑ p ∈ P, if toC p ∈ T then (Y.degree : ℝ)⁻¹ else 0 :=
      Finset.sum_le_sum hpoint
    _ = ((P.filter (fun p => toC p ∈ T)).card : ℝ) * (Y.degree : ℝ)⁻¹ := by
      rw [← Finset.sum_filter]
      simp
    _ ≤ (C₂ * (Y.degree : ℝ)) * (Y.degree : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_right hcount (inv_nonneg.mpr hD.le)
    _ = C₂ := by field_simp

end
end DistinctDistances.TrackD.GeoD4
