import DistinctDistances.TrackE.CommonImageSource

/-! Full-dimensional complete product images after transversality pruning,
`sc:retained-products.depth.dimension`, sparse-cones.tex:143–155. -/
namespace DistinctDistances.SparseCones
open scoped BigOperators Classical
noncomputable section
variable {d : ℕ}

/-- Generic target transversality makes the actual complete image irreducible
of full product dimension. The chart is required to meet that product. -/
theorem common_product_image_geometry (i₀ : Fin d) (X Y : AffineVariety d)
    (hX : X.IsIrreducible) (hY : Y.IsIrreducible)
    (hchart : ∃ x ∈ X, ∃ y ∈ Y, (y - x) i₀ ≠ 0)
    (htrans : TrackD.ForGeneralPair X Y (fun x y => y - x ∉ Y.tangentSpace y)) :
    (commonProductImage i₀ X Y).IsIrreducible ∧
      (commonProductImage i₀ X Y).dimension = X.dimension + Y.dimension := by
  let S := TrackD.productVariety X Y
  let f := TrackD.secantChartNumerator i₀
  let g := TrackD.secantChartDenominator i₀
  have hS : S.IsIrreducible := TrackD.productVariety_irreducible X Y hX hY
  have hg : g ∉ S.ideal := common_image_domain_not_mem i₀ X Y hchart
  obtain ⟨himage, hgeneric⟩ := TrackD.request_rational_image_generic_tangent S hS f g hg
  have hchartgen := common_product_chart_general i₀ X Y hchart
  have hdx := (TrackD.general_tangent_finrank X hX).on_left
    (TrackD.irreducible_points_nonempty Y hY)
  have hdy := (TrackD.general_tangent_finrank Y hY).on_right
    (TrackD.irreducible_points_nonempty X hX)
  have hrank : TrackD.ForGeneralPair X Y (fun x y => Module.finrank ℂ
      ((S.tangentSpace (TrackD.productPoint x y)).map
        (TrackD.rationalDifferential f g (TrackD.productPoint x y))) = S.dimension) := by
    apply (((htrans.and hX hY hchartgen).and hX hY hdx).and hX hY hdy).mono
    intro x hx y hy hh
    rcases hh with ⟨⟨⟨htr, hi⟩, hdx⟩, hdy⟩
    have h := TrackD.rational_secant_tangent_finrank X Y i₀ x y hx hy hi htr
    simpa only [S, f, g, TrackD.product_dimension X Y hX hY, hdx, hdy] using h
  obtain ⟨x, hx, y, hy, hgen, hrank⟩ :=
    (hgeneric.on_product.and hX hY hrank).exists
  rw [hgen.2.1, hgen.2.2] at hrank
  refine ⟨himage, ?_⟩
  simpa only [S, f, g, commonProductImage, TrackD.product_dimension X Y hX hY] using hrank

end
end DistinctDistances.SparseCones
