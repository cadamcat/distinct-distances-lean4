import DistinctDistances.TrackE.CommonRadialChartImage
import DistinctDistances.TrackE.CommonImageInputs
import DistinctDistances.TrackD.TripleViewpoint

/-! Dimension preservation from the original generic target transversality,
`sc:retained-products.family`, sparse-cones.tex:172–180. -/
namespace DistinctDistances.SparseCones
open scoped Classical
noncomputable section

theorem common_radial_dimension_from_transversality {d : ℕ}
    (Y : AffineVariety d) (hY : Y.IsIrreducible) (i₀ : Fin d) (p : Point d)
    (hchart : ∃ y ∈ Y, (y - p) i₀ ≠ 0)
    (htrans : TrackD.ForGeneralPoint Y (fun y => y - p ∉ Y.tangentSpace y)) :
    (radialImage p Y).dimension = Y.dimension := by
  let f := commonRadialNumerator p
  let g := commonRadialDenominator i₀ p
  have hg : g ∉ Y.ideal := by
    intro hmem
    obtain ⟨y, hy, hi⟩ := hchart
    have hz := (TrackD.mem_ideal_iff_eval_zero Y g).1 hmem y hy
    exact hi (by simpa [g, commonRadialDenominator, commonRadialNumerator] using hz)
  obtain ⟨_, hgeneric⟩ := TrackD.request_rational_image_generic_tangent Y hY f g hg
  have hchartgen : TrackD.ForGeneralPoint Y (fun y => (y - p) i₀ ≠ 0) := by
    refine ⟨g, ?_, ?_⟩
    · obtain ⟨y, hy, hi⟩ := hchart
      exact ⟨y, hy, by simpa [g, commonRadialDenominator, commonRadialNumerator] using hi⟩
    · intro y hy hi
      simpa [g, commonRadialDenominator, commonRadialNumerator] using hi
  have hrank : TrackD.ForGeneralPoint Y (fun y => Module.finrank ℂ
      ((Y.tangentSpace y).map (TrackD.rationalDifferential f g y)) = Y.dimension) := by
    apply ((htrans.and hY hchartgen).and hY (TrackD.general_tangent_finrank Y hY)).mono
    intro y hy hh
    rcases hh with ⟨⟨htr, hi⟩, hdim⟩
    have hr := common_radial_chart_tangent_finrank Y i₀ p y hi htr
    simpa only [f, g, hdim] using hr
  have hdim := TrackD.rational_image_dimension_eq_of_generic_rank Y hY f g hgeneric hrank
  have hactual : ∃ y ∈ Y.points, y ≠ p := by
    obtain ⟨y, hy, hi⟩ := hchart
    refine ⟨y, hy, ?_⟩
    intro he
    subst y
    simp at hi
  have hZ := radialImage_irreducible p Y hY hactual
  have hslice : (TrackA.projectiveLinearSlice (radialImage p Y)
      (MvPolynomial.X i₀)).dimension = Y.dimension := by
    rw [← common_radial_chart_image_eq_slice Y hY i₀ p hchart]
    simpa only [commonRadialChartImage, f, g] using hdim
  exact (TrackA.linearSlice_dimension (radialImage p Y) hZ (MvPolynomial.X i₀)
    (MvPolynomial.isHomogeneous_X ℂ i₀)
    (common_radial_chart_coordinate_not_mem Y i₀ p hchart)).symm.trans hslice

theorem common_product_general_radial_dimension {d : ℕ} (i₀ : Fin d)
    (X Y : AffineVariety d) (hX : X.IsIrreducible) (hY : Y.IsIrreducible)
    (hchart : ∃ x ∈ X, ∃ y ∈ Y, (y - x) i₀ ≠ 0)
    (htrans : TrackD.ForGeneralPair X Y (fun x y => y - x ∉ Y.tangentSpace y)) :
    TrackD.ForGeneralPoint X (fun x => (radialImage x Y).dimension = Y.dimension) := by
  have hchartgen := common_product_chart_general i₀ X Y hchart
  have hsource := (htrans.and hX hY hchartgen).swap.fiber_right
  apply hsource.mono
  intro x hx hgen
  have htr : TrackD.ForGeneralPoint Y (fun y => y - x ∉ Y.tangentSpace y) :=
    hgen.mono (fun y hy h => h.1)
  obtain ⟨y, hy, hh⟩ := hgen.exists
  exact common_radial_dimension_from_transversality Y hY i₀ x ⟨y, hy, hh.2⟩ htr

/-- The original finite list fixes one source open before every later image subfamily. -/
theorem common_product_family_radial_dimension {d : ℕ} (i₀ : Fin d)
    (X : AffineVariety d) (hX : X.IsIrreducible) (F : AffineFamily.Family d)
    (hF : ∀ Y ∈ F, Y.IsIrreducible)
    (hchart : ∀ Y ∈ F, ∃ x ∈ X, ∃ y ∈ Y, (y - x) i₀ ≠ 0)
    (htrans : ∀ Y ∈ F,
      TrackD.ForGeneralPair X Y (fun x y => y - x ∉ Y.tangentSpace y)) :
    TrackD.ForGeneralPoint X (fun x =>
      ∀ Y ∈ F, (radialImage x Y).dimension = Y.dimension) := by
  have hne : X.points.Nonempty := X.points_nonempty_of_isIrreducible hX
  apply TrackD.ForGeneralPoint.finset_all hX hne F _ _
  intro Y hY
  exact common_product_general_radial_dimension i₀ X Y hX (hF Y hY)
    (hchart Y hY) (htrans Y hY)

end
end DistinctDistances.SparseCones
