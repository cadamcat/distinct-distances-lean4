import DistinctDistances.TrackA.ProjectiveChartFamily

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical

def coneFamily {n : ℕ} (F : ProjectiveFamily.Family n) : AffineFamily.Family n :=
  F.image ProjectiveVariety.affineCone

theorem affineCone_injective {n : ℕ} :
    Function.Injective (ProjectiveVariety.affineCone (n := n)) := by
  intro V W h
  exact ProjectiveVariety.ext (congrArg AffineVariety.ideal h)

theorem coneFamily_locus {n : ℕ} (F : ProjectiveFamily.Family n) :
    AffineFamily.locus (coneFamily F) = (ProjectiveFamily.locus F).affineCone := by
  apply AffineVariety.ext
  ext f
  change f ∈ (AffineFamily.locus (coneFamily F)).ideal ↔ f ∈ (ProjectiveFamily.locus F).ideal
  rw [chart_affine_family_mem, chart_projective_family_mem]
  constructor
  · intro h V hV
    exact h V.affineCone (Finset.mem_image.mpr ⟨V, hV, rfl⟩)
  · intro h A hA
    obtain ⟨V, hV, rfl⟩ := Finset.mem_image.mp hA
    exact h V hV

theorem coneFamily_degree {n : ℕ} (F : ProjectiveFamily.Family n) :
    AffineFamily.degree (coneFamily F) = ProjectiveFamily.degree F := by
  unfold coneFamily AffineFamily.degree ProjectiveFamily.degree
  rw [Finset.sum_image]
  · exact Finset.sum_congr rfl (fun V _ => ProjectiveVariety.degree_cone V)
  · intro V _ W _ h
    exact affineCone_injective h

theorem coneFamily_pure {n : ℕ} (F : ProjectiveFamily.Family n) (k : ℕ)
    (hF : ProjectiveFamily.IsPure F k) : AffineFamily.IsPure (coneFamily F) (k+1) := by
  intro A hA
  obtain ⟨V, hV, rfl⟩ := Finset.mem_image.mp hA
  refine ⟨(hF V hV).1, ?_⟩
  rw [ProjectiveVariety.dimension_cone V
    (ProjectiveFamily.irreducible_points_nonempty V (hF V hV).1), (hF V hV).2]

theorem coneFamily_defined {n : ℕ} (F : ProjectiveFamily.Family n) (L : ℕ)
    (hF : ProjectiveFamily.ComponentsDefinedInDegree F L) :
    AffineFamily.ComponentsDefinedInDegree (coneFamily F) L := by
  obtain ⟨E, hE, hc⟩ := hF
  refine ⟨E, ?_, ?_⟩
  · intro f hf
    obtain ⟨d, hd, hh⟩ := hE f hf
    exact hh.totalDegree_le.trans hd
  · intro A hA
    obtain ⟨V, hV, rfl⟩ := Finset.mem_image.mp hA
    exact hc V hV

theorem coneFamily_lists {n : ℕ} (F : ProjectiveFamily.Family n) (L : ℕ)
    (hF : FromProjectiveLists F L) : FromAffineLists (coneFamily F) L := by
  obtain ⟨r, lists, bounds, hdef, hunion, hsum⟩ := hF
  refine ⟨r, (fun i => coneFamily (lists i)), bounds, ?_, ?_, hsum⟩
  · intro i
    exact ⟨(hdef i).1, coneFamily_defined _ _ (hdef i).2⟩
  · intro A
    simp only [coneFamily, Finset.mem_image]
    constructor
    · rintro ⟨V, hV, rfl⟩
      obtain ⟨i, hi⟩ := (hunion V).1 hV
      exact ⟨i, V, hi, rfl⟩
    · rintro ⟨i, V, hV, rfl⟩
      exact ⟨V, (hunion V).2 ⟨i, hV⟩, rfl⟩

def projectiveBadFamily {n : ℕ} (F : ProjectiveFamily.Family n)
    (bad : AffineFamily.Family n) : ProjectiveFamily.Family n :=
  F.filter (fun V => V.affineCone ∈ bad)

theorem coneFamily_bad {n : ℕ} (F : ProjectiveFamily.Family n)
    (bad : AffineFamily.Family n) (hbad : bad ⊆ coneFamily F) :
    coneFamily (projectiveBadFamily F bad) = bad := by
  ext A
  simp only [coneFamily, projectiveBadFamily, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨V, ⟨_, hV⟩, rfl⟩
    exact hV
  · intro hA
    obtain ⟨V, hV, rfl⟩ := Finset.mem_image.mp (hbad hA)
    exact ⟨V, ⟨hV, hA⟩, rfl⟩

end
end DistinctDistances.TrackA
