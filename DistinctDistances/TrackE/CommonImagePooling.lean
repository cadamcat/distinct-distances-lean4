import DistinctDistances.TrackE.CommonImageGroups

/-! Original image families pooled across all source carriers,
`sc:retained-products.family`, sparse-cones.tex:158–162, 201–213. -/
namespace DistinctDistances.SparseCones
open scoped BigOperators Classical
noncomputable section

theorem common_original_image_family_degree_bound {d k : ℕ} (i₀ : Fin d)
    (A : AffineFamily.Family d) (hA : AffineFamily.IsPure A k)
    (F L : AffineVariety d → AffineFamily.Family d)
    (hFL : ∀ X ∈ A, F X ⊆ L X) (hk : 1 ≤ k)
    (hF : ∀ X ∈ A, AffineFamily.IsPure (F X) k) (R : ℝ)
    (hchart : ∀ X ∈ A, ∀ Y ∈ F X, ∃ x ∈ X, ∃ y ∈ Y, (y - x) i₀ ≠ 0)
    (hdepth : ∀ X ∈ A, ∀ Y ∈ F X, TrackD.ForGeneralPair X Y (fun x y =>
      y - x ∉ X.tangentSpace x ∧ y - x ∉ Y.tangentSpace y ∧
      (TrackD.movingRoots (L X) x y).Finite ∧
        ((TrackD.movingRoots (L X) x y).ncard : ℝ) ≤ R))
    (J : AffineFamily.Family (d + d)) :
    (∑ X ∈ A, (X.degree : ℝ) *
      (∑ Y ∈ (F X).filter (fun Y => commonProductImage i₀ X Y ∈ J),
        (Y.degree : ℝ))) ≤
      2 * R * (∑ Z ∈ (A.biUnion
        (fun X => (F X).image (commonProductImage i₀ X))).filter
          (fun Z => Z ∈ J), (Z.degree : ℝ)) := by
  have hdisjoint := common_source_image_families_disjoint i₀ A F
    (fun X hX => (hA X hX).1) hchart
  calc
    _ ≤ ∑ X ∈ A, 2 * R *
        (∑ Z ∈ ((F X).image (commonProductImage i₀ X)).filter
          (fun Z => Z ∈ J), (Z.degree : ℝ)) := by
      apply Finset.sum_le_sum
      intro X hX
      exact common_original_image_subfamily_degree_bound i₀ X (hA X hX).1
        (hA X hX).2 (F X) (L X) (hFL X hX) hk (hF X hX) R
        (hchart X hX) (hdepth X hX) J
    _ = 2 * R * (∑ X ∈ A, ∑ Z ∈ ((F X).image (commonProductImage i₀ X)).filter
        (fun Z => Z ∈ J), (Z.degree : ℝ)) := by rw [Finset.mul_sum]
    _ = _ := by rw [common_source_image_degree_partition i₀ A F J hdisjoint]

end
end DistinctDistances.SparseCones
