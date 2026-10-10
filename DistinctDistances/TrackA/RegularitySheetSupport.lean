import DistinctDistances.TrackA.RegularityGenericVectorSupport

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical

/-- Retain component membership while supplying all original isolating
systems in one generic fiber. Overlapping lists share their sheets. -/
theorem regularity_component_generic_fiber_lists {n k s : ℕ}
    (F : AffineFamily.Family n) (hF : AffineFamily.IsPure F k)
    (φ : AffineProjection n k)
    (hnorm : ∀ V ∈ F, FiniteAffineProjection φ V ∧ ∃ r : ℕ,
      (r : ℚ) = V.degree ∧ φ.GenericallyFiniteOfDegree V r)
    (lists : Fin s → AffineFamily.Family n)
    (hunion : ∀ V, V ∈ F ↔ ∃ i, V ∈ lists i)
    (E : Fin s → Set (Poly n))
    (hcomponents : ∀ i, ∀ V ∈ lists i, V.IsComponentOf (Ideal.span (E i))) :
    ∃ (G : ComponentGenericFiber F φ) (indices : Fin s → Finset (Fin G.r)),
      (∀ j : Fin G.r, ∃ V ∈ F, G.points j ∈ affineFiberOver V φ G.t) ∧
      (∀ j : Fin G.r, ∃ i, j ∈ indices i) ∧
      ∀ i, ∀ j ∈ indices i,
        pointIdealOver (G.points j) ∈ (Ideal.span (G.equations (E i))).minimalPrimes := by
  obtain ⟨G, hG⟩ := componentGenericFiber_with_components F hF φ hnorm
  let indices (i : Fin s) : Finset (Fin G.r) := Finset.univ.filter
    (fun j => ∃ V ∈ lists i, G.points j ∈ affineFiberOver V φ G.t)
  refine ⟨G, indices, hG, ?_, ?_⟩
  · intro j
    obtain ⟨V, hV, hx⟩ := hG j
    obtain ⟨i, hi⟩ := (hunion V).mp hV
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ j, V, hi, hx⟩⟩
  · intro i j hj
    obtain ⟨V, hV, hx⟩ := (Finset.mem_filter.mp hj).2
    have hVF : V ∈ F := (hunion V).mpr ⟨i, hV⟩
    exact affineFiberOver_minimalPrime V φ (hnorm V hVF).1 (E i)
      (hcomponents i V hV) G.Ω G.t G.independent ⟨G.points j, hx⟩

/-- Every original subfamily contributes exactly its degree in distinct
sheets, using the literal generic fibers and their original point counts. -/
theorem regularity_subfamily_sheet_indices {n k : ℕ} (F bad : AffineFamily.Family n)
    (hF : AffineFamily.IsPure F k) (hbad : bad ⊆ F) (φ : AffineProjection n k)
    (hnorm : ∀ V ∈ F, FiniteAffineProjection φ V ∧ ∃ r : ℕ,
      (r : ℚ) = V.degree ∧ φ.GenericallyFiniteOfDegree V r)
    (G : ComponentGenericFiber F φ)
    (hG : ∀ j : Fin G.r, ∃ V ∈ F, G.points j ∈ affineFiberOver V φ G.t) :
    ∃ (b : ℕ) (selected : Fin b ↪ Fin G.r), (b : ℚ) = AffineFamily.degree bad ∧
      ∀ j : Fin b, ∃ V ∈ bad, G.points (selected j) ∈ affineFiberOver V φ G.t := by
  obtain ⟨S, hS, hScard⟩ := affineFamily_genericFiber_finset F hF φ hnorm
    G.Ω G.t G.independent
  obtain ⟨B, hB, hBcard⟩ := affineFamily_genericFiber_finset bad
    (fun V hV => hF V (hbad hV)) φ (fun V hV => hnorm V (hbad hV))
    G.Ω G.t G.independent
  let U : Finset (FieldPoint n G.Ω) := Finset.univ.image G.points
  have hUS : U ⊆ S := by
    intro x hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    exact (hS _).mpr (hG j)
  have hUcard : U.card = G.r := by
    simp only [U, Finset.card_image_of_injective _ G.points_injective, Finset.card_univ,
      Fintype.card_fin]
  have hSnum : S.card = G.r := by
    exact_mod_cast hScard.trans G.count_degree.symm
  have hUS_eq : U = S := Finset.eq_of_subset_of_card_le hUS (by omega)
  have hBU : B ⊆ U := by
    intro x hx
    obtain ⟨V, hV, hxV⟩ := (hB x).mp hx
    rw [hUS_eq]
    exact (hS x).mpr ⟨V, hbad hV, hxV⟩
  let indices : Finset (Fin G.r) := Finset.univ.filter (fun j => G.points j ∈ B)
  have himage : indices.image G.points = B := by
    ext x
    constructor
    · intro hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hj).2
    · intro hx
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp (hBU hx)
      exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hx⟩, rfl⟩
  have hindicescard : indices.card = B.card := by
    rw [← himage, Finset.card_image_of_injective _ G.points_injective]
  let e : Fin indices.card ≃ indices := indices.equivFin.symm
  let selected : Fin indices.card ↪ Fin G.r :=
    ⟨fun j => (e j).val, Subtype.val_injective.comp e.injective⟩
  refine ⟨indices.card, selected, ?_, ?_⟩
  · rw [hindicescard]
    exact hBcard
  · intro j
    exact (hB _).mp ((Finset.mem_filter.mp (e j).property).2)

end
end DistinctDistances.TrackA
