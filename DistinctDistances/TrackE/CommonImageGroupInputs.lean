import DistinctDistances.TrackE.CommonImageSections
import DistinctDistances.TrackE.CommonProjectionBudgets
import DistinctDistances.TrackE.CommonImageSource
import DistinctDistances.TrackE.MixedFiber

/-! Finite pooling of full original image groups, `sc:retained-products.family`,
sparse-cones.tex:158–162, 201–213. Later subfamilies do not alter the lists. -/
namespace DistinctDistances.SparseCones
open scoped BigOperators Classical
noncomputable section

/-- Every retained original target appears in exactly its complete-image group. -/
theorem common_image_group_degree_partition {d : ℕ} (i₀ : Fin d)
    (X : AffineVariety d) (F : AffineFamily.Family d)
    (J : AffineFamily.Family (d + d)) :
    (∑ Y ∈ F.filter (fun Y => commonProductImage i₀ X Y ∈ J), (Y.degree : ℝ)) =
      ∑ Z ∈ (F.image (commonProductImage i₀ X)).filter (fun Z => Z ∈ J),
        ∑ Y ∈ F.filter (fun Y => commonProductImage i₀ X Y = Z),
          (Y.degree : ℝ) := by
  classical
  have hmaps : ∀ Y ∈ F.filter (fun Y => commonProductImage i₀ X Y ∈ J),
      commonProductImage i₀ X Y ∈
        (F.image (commonProductImage i₀ X)).filter (fun Z => Z ∈ J) := by
    intro Y hY
    rw [Finset.mem_filter] at hY ⊢
    constructor
    · exact Finset.mem_image.mpr ⟨Y, hY.1, rfl⟩
    · exact hY.2
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps (fun Y => (Y.degree : ℝ))
  -- hfib : ∑ Z ∈ t, ∑ Y ∈ s.filter (g = Z), deg = ∑ Y ∈ s, deg
  symm
  rw [← hfib]
  apply Finset.sum_congr rfl
  intro Z hZ
  have hZJ : Z ∈ J := (Finset.mem_filter.mp hZ).2
  apply Finset.sum_congr _ (fun Y _ => rfl)
  -- show filter sets equal: F.filter (g = Z) = s.filter (g = Z)
  ext Y
  simp only [Finset.mem_filter]
  constructor
  · intro hY
    rcases hY with ⟨hYF, hYZ⟩
    refine ⟨⟨hYF, ?_⟩, hYZ⟩
    rw [hYZ]
    exact hZJ
  · intro hY
    rcases hY with ⟨⟨hYF, _⟩, hYZ⟩
    exact ⟨hYF, hYZ⟩

/-- Nonempty original charts recover distinct source carriers from their images. -/
theorem common_source_image_families_disjoint {d : ℕ} (i₀ : Fin d)
    (A : AffineFamily.Family d) (F : AffineVariety d → AffineFamily.Family d)
    (hA : ∀ X ∈ A, X.IsIrreducible)
    (hchart : ∀ X ∈ A, ∀ Y ∈ F X, ∃ x ∈ X, ∃ y ∈ Y, (y - x) i₀ ≠ 0) :
    ∀ X ∈ A, ∀ X' ∈ A, X ≠ X' →
      Disjoint ((F X).image (commonProductImage i₀ X))
        ((F X').image (commonProductImage i₀ X')) := by
  classical
  intro X hX X' hX' hne
  rw [Finset.disjoint_left]
  intro Z hZ hZ'
  obtain ⟨Y, hYF, hYZ⟩ := Finset.mem_image.mp hZ
  obtain ⟨Y', hY'F, hYZ'⟩ := Finset.mem_image.mp hZ'
  have himage : commonProductImage i₀ X Y = commonProductImage i₀ X' Y' := by
    rw [hYZ, hYZ']
  have hXeq := common_product_source_eq_of_image_eq i₀ X Y X' Y'
    (hA X hX) (hA X' hX') (hchart X hX Y hYF) (hchart X' hX' Y' hY'F) himage
  exact hne hXeq

/-- Pool source-wise image degrees once, using the full original image families. -/
theorem common_source_image_degree_partition {d : ℕ} (i₀ : Fin d)
    (A : AffineFamily.Family d) (F : AffineVariety d → AffineFamily.Family d)
    (J : AffineFamily.Family (d + d))
    (hdisjoint : ∀ X ∈ A, ∀ X' ∈ A, X ≠ X' →
      Disjoint ((F X).image (commonProductImage i₀ X))
        ((F X').image (commonProductImage i₀ X'))) :
    (∑ X ∈ A, ∑ Z ∈ ((F X).image (commonProductImage i₀ X)).filter
      (fun Z => Z ∈ J), (Z.degree : ℝ)) =
        ∑ Z ∈ (A.biUnion (fun X => (F X).image (commonProductImage i₀ X))).filter
          (fun Z => Z ∈ J), (Z.degree : ℝ) := by
  classical
  -- filter commutes with biUnion
  have hU : (A.biUnion (fun X => (F X).image (commonProductImage i₀ X))).filter
        (fun Z => Z ∈ J) =
      A.biUnion (fun X => ((F X).image (commonProductImage i₀ X)).filter
        (fun Z => Z ∈ J)) := by
    ext Z
    simp only [Finset.mem_filter, Finset.mem_biUnion]
    constructor
    · intro hZ
      rcases hZ with ⟨⟨X, hXA, hZX⟩, hZJ⟩
      exact ⟨X, hXA, hZX, hZJ⟩
    · intro hZ
      obtain ⟨X, hXA, hZX, hZJ⟩ := hZ
      exact ⟨⟨X, hXA, hZX⟩, hZJ⟩
  rw [hU]
  have hdisj : Set.PairwiseDisjoint (↑A : Set (AffineVariety d)) (fun X =>
      ((F X).image (commonProductImage i₀ X)).filter (fun Z => Z ∈ J)) := by
    intro X hXA X' hX'A hne
    have hX : X ∈ A := Finset.mem_coe.mp hXA
    have hX' : X' ∈ A := Finset.mem_coe.mp hX'A
    exact Disjoint.mono (Finset.filter_subset _ _)
      (Finset.filter_subset _ _) (hdisjoint X hX X' hX' hne)
  rw [Finset.sum_biUnion hdisj]

end
end DistinctDistances.SparseCones
