import DistinctDistances.TrackE.OuterPool

/-! Generic helpers for `outer_tangent_tests`.

Only uses `OuterPool` and below (no cycle with `OuterRegularity`).
`outerPairLinear`-specific helpers live directly above 191 in
`OuterRegularity.lean`. No frozen declaration is proved here. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- Deletion budget split for the two-stage `ρ'/2 + ρ'/2 = ρ'` argument. -/
theorem tangent_deletion_split (ρ' S : ℝ) : ρ' / 2 * S ^ 2 + ρ' / 2 * S ^ 2 = ρ' * S ^ 2 := by
  ring

/-- Rank of the label-differential image from target transversality.
This is `labelDeriv_product_finrank` with `TX/TY` explicit. -/
theorem label_image_rank_of_transverse (p q : Point d) (i₀ : Fin d)
    (hchart : (q - p) i₀ ≠ 0)
    (TX TY : Submodule ℂ (Point d)) (hTY : q - p ∉ TY) :
    Module.finrank ℂ ((TX.prod TY).map (TrackD.labelDeriv (LinearMap.proj i₀) p q)) =
      Module.finrank ℂ TX + Module.finrank ℂ TY := by
  have hlam : (LinearMap.proj i₀ : Point d →ₗ[ℂ] ℂ) (q - p) ≠ 0 := by
    simpa using hchart
  exact TrackD.labelDeriv_product_finrank _ _ _ hlam TX TY hTY

/-- Tangent finrank at a smooth retained point equals the carrier dimension.
Uses `IsSmoothAt` (finrank = localDimension) and `localDimension_eq_dimension`. -/
theorem tangent_finrank_eq_dim_of_smooth {X : AffineVariety d} {p : Point d}
    (hsm : X.IsSmoothAt p) (hirr : X.IsIrreducible) (hmem : p ∈ X) :
    Module.finrank ℂ (X.tangentSpace p) = X.dimension := by
  exact hsm.2.trans (X.localDimension_eq_dimension p hirr hmem)

end
end DistinctDistances.SparseCones
