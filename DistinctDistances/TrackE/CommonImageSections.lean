import DistinctDistances.TrackE.CommonSectionCounts
import DistinctDistances.TrackE.CommonImageGeometry

/-! The original source property Q remains fixed before later image subfamilies,
`sc:retained-products.family`, sparse-cones.tex:194–207. -/
namespace DistinctDistances.SparseCones
open scoped BigOperators Classical
noncomputable section

theorem common_image_mixed_section_bound {d k : ℕ} (i₀ : Fin d)
    (X Y : AffineVariety d) (hX : X.IsIrreducible) (hY : Y.IsIrreducible)
    (hk : 1 ≤ k) (hXd : X.dimension = k) (hYd : Y.dimension = k)
    (hchart : ∃ x ∈ X, ∃ y ∈ Y, (y - x) i₀ ≠ 0)
    (htrans : TrackD.ForGeneralPair X Y (fun p y => y - p ∉ Y.tangentSpace y))
    (Q : Point d → Prop) (hQ : TrackD.ForGeneralPoint X Q) :
    ∃ S : Finset (Point d), (S.card : ℚ) = X.degree ∧
      (∀ p ∈ S, p ∈ X ∧ Q p ∧ (∃ y ∈ Y, (y - p) i₀ ≠ 0) ∧
        (radialImage p Y).dimension = k) ∧
      (∑ p ∈ S, (radialImage p Y).degree) ≤ (commonProductImage i₀ X Y).degree := by
  obtain ⟨φ, s, S, _, _, hcard, _, hall⟩ := common_good_source_section i₀ X Y hX hY
    hk hXd hYd hchart htrans Q hQ
  obtain ⟨hZ, hZd₀⟩ := common_product_image_geometry i₀ X Y hX hY hchart htrans
  have hZd : (commonProductImage i₀ X Y).dimension = 2 * k := by
    rw [hZd₀, hXd, hYd]
    omega
  have hkd : k ≤ d := by
    simpa only [hXd] using TrackD.dimension_le_ambient X hX
  refine ⟨S, hcard, ?_, ?_⟩
  · intro p hp
    rcases hall p hp with ⟨hQp, hpX, _, _, hchartp, hdim, _⟩
    exact ⟨hpX, hQp, hchartp, hdim⟩
  · exact common_fixed_source_mixed_section_bound i₀ X Y hY hkd hZ hZd φ s S
      (fun p hp => (hall p hp).2)

end
end DistinctDistances.SparseCones
