import DistinctDistances.TrackE.CommonMixedInputs

/-! Generic tangent injection for the actual finite normalization,
`sc:retained-products.family`, sparse-cones.tex:194–207. -/
namespace DistinctDistances.SparseCones
open scoped Classical
noncomputable section

theorem common_normalization_general_tangent_injective {d k : ℕ}
    (X : AffineVariety d) (hX : X.IsIrreducible) (hd : X.dimension = k)
    (φ : AffineProjection d k) (hfinite : TrackA.FiniteAffineProjection φ X) :
    TrackD.ForGeneralPoint X (fun x =>
      Function.Injective (φ.linear.domRestrict (X.tangentSpace x))) := by
  let f : Fin k → Poly d := fun i => φ.pullback (MvPolynomial.X i)
  obtain ⟨_, hgeneric⟩ := TrackD.request_rational_image_generic_tangent X hX f 1 hX.one_notMem
  have hbot := TrackA.finite_affine_projection_image_ideal_bot X hX hd φ hfinite
  apply (hgeneric.and hX (TrackD.general_tangent_finrank X hX)).mono
  intro x hx hh
  have hmap : (X.tangentSpace x).map φ.linear = ⊤ := by
    have hm := hh.1.2.1
    dsimp only [f] at hm
    rw [common_affine_projection_rational_differential,
      common_affine_projection_rational_image,
      common_zero_ideal_tangent_space (φ.image X) hbot] at hm
    exact hm
  have hdims : Module.finrank ℂ (X.tangentSpace x) = Module.finrank ℂ (Point k) := by
    simpa only [Point, Module.finrank_pi, Fintype.card_fin] using hh.2.trans hd
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdims).2
  rw [← LinearMap.range_eq_top, LinearMap.range_domRestrict]
  exact hmap

end
end DistinctDistances.SparseCones
