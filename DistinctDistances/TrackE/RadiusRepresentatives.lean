import DistinctDistances.TrackE.RadiusFibers

/-! Radius-class representatives with distinct projections (`reduction.tex:153–155`). -/

namespace DistinctDistances

noncomputable section

namespace Reduction

open Classical in
/-- Choose one representative in each fiber of a map on a finite set. -/
theorem exists_injective_representatives {α β : Type*} (S : Finset α) (f : α → β) :
    ∃ T : Finset α, T ⊆ S ∧ (T : Set α).InjOn f ∧ T.image f = S.image f := by
  classical
  let pick : S.image f → α := fun v => (Finset.mem_image.mp v.property).choose
  have hpick : ∀ v : S.image f, pick v ∈ S ∧ f (pick v) = v.val := by
    intro v
    exact (Finset.mem_image.mp v.property).choose_spec
  let T := Finset.univ.image pick
  have hsubset : T ⊆ S := by
    intro x hx
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
    exact (hpick v).1
  have hinj : (T : Set α).InjOn f := by
    intro x hx y hy hxy
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hy
    have hvw : v = w := Subtype.ext (by rwa [(hpick v).2, (hpick w).2] at hxy)
    exact congrArg pick hvw
  refine ⟨T, hsubset, hinj, ?_⟩
  apply Finset.Subset.antisymm
  · exact Finset.image_subset_image hsubset
  · intro v hv
    refine Finset.mem_image.mpr ⟨pick ⟨v, hv⟩, ?_, (hpick ⟨v, hv⟩).2⟩
    exact Finset.mem_image.mpr ⟨⟨v, hv⟩, Finset.mem_univ _, rfl⟩

open Classical in
/-- Physical representatives in one radius class, with cardinality exactly its number
of distinct orthogonal projections. -/
theorem exists_radius_representatives {d : ℕ} (P : Finset (RPoint d)) (p : RPoint d)
    (U : Submodule ℝ (RPoint d)) (r : ℝ) :
    ∃ Z : Finset (RPoint d), Z ⊆ P.filter (fun z => dist z p = r) ∧
      Z.card = ((P.filter fun z => dist z p = r).image U.orthogonalProjectionOnto).card ∧
      ∀ z ∈ Z, ∀ z' ∈ Z, z ≠ z' →
        U.orthogonalProjectionOnto z ≠ U.orthogonalProjectionOnto z' := by
  classical
  obtain ⟨Z, hZ, hinj, himage⟩ := exists_injective_representatives
    (P.filter fun z => dist z p = r) U.orthogonalProjectionOnto
  refine ⟨Z, hZ, ?_, ?_⟩
  · calc
      Z.card = (Z.image U.orthogonalProjectionOnto).card :=
        (Finset.card_image_iff.mpr hinj).symm
      _ = _ := by
        convert congrArg Finset.card himage using 1 <;>
          congr 1 <;> ext w <;> simp only [Finset.mem_image, Finset.mem_filter]
  · intro z hz z' hz' hne heq
    exact hne (hinj hz hz' heq)

/-- Recover an ordered pair from membership in a star. -/
theorem mem_pair_of_mem_star {d : ℕ} {G : Finset (RPoint d × RPoint d)}
    {p q : RPoint d} (hq : q ∈ star G p) : (p, q) ∈ G := by
  classical
  obtain ⟨e, he, hq⟩ := Finset.mem_image.mp hq
  obtain ⟨heG, hep⟩ := Finset.mem_filter.mp he
  have heq : e = (p, q) := Prod.ext hep hq
  rwa [heq] at heG

end Reduction

end

end DistinctDistances
