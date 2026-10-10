import DistinctDistances.TrackE.CommonRadialChartInputs

/-! The actual normalized image is the shared complete radial slice,
`sc:retained-products.family`, sparse-cones.tex:172–180. -/
namespace DistinctDistances.SparseCones
open scoped Classical
noncomputable section

theorem common_radial_chart_image_eq_slice {d : ℕ} (Y : AffineVariety d)
    (hY : Y.IsIrreducible) (i₀ : Fin d) (p : Point d)
    (hchart : ∃ y ∈ Y, (y - p) i₀ ≠ 0) :
    commonRadialChartImage i₀ p Y =
      TrackA.projectiveLinearSlice (radialImage p Y) (MvPolynomial.X i₀) := by
  let g := commonRadialDenominator i₀ p
  have hchartgen : TrackD.ForGeneralPoint Y (fun y => (y - p) i₀ ≠ 0) := by
    refine ⟨g, ?_, ?_⟩
    · obtain ⟨y, hy, hi⟩ := hchart
      exact ⟨y, hy, by simpa [g, commonRadialDenominator, commonRadialNumerator] using hi⟩
    · intro y hy hi
      simpa [g, commonRadialDenominator, commonRadialNumerator] using hi
  have hactual : ∃ y ∈ Y.points, y ≠ p := by
    obtain ⟨y, hy, hi⟩ := hchart
    refine ⟨y, hy, ?_⟩
    intro he
    subst y
    simp at hi
  have hZ := radialImage_irreducible p Y hY hactual
  have hℓ := MvPolynomial.isHomogeneous_X ℂ i₀
  have hℓnot := common_radial_chart_coordinate_not_mem Y i₀ p hchart
  apply AffineVariety.ext
  ext q
  constructor
  · intro hq
    apply (TrackA.chartHomogenize_mem_iff (radialImage p Y) hZ
      (MvPolynomial.X i₀) q hℓ hℓnot le_rfl).2
    apply common_radial_homogeneous_equation Y hY p _ q.totalDegree
      (TrackA.chartHomogenize_homogeneous (MvPolynomial.X i₀) q hℓ)
    apply hchartgen.mono
    intro y hy hi
    apply common_radial_chart_homogenize_zero i₀ q (y - p) hi
    have hg : MvPolynomial.eval y (commonRadialDenominator i₀ p) ≠ 0 := by
      simpa [commonRadialDenominator, commonRadialNumerator] using hi
    have hm := TrackD.rationalPoint_mem_image Y (commonRadialNumerator p)
      (commonRadialDenominator i₀ p) y hy hg
    change TrackD.rationalPoint (commonRadialNumerator p)
      (commonRadialDenominator i₀ p) y ∈ commonRadialChartImage i₀ p Y at hm
    rw [common_radial_chart_point] at hm
    exact (TrackD.mem_ideal_iff_eval_zero (commonRadialChartImage i₀ p Y) q).1
      hq _ hm
  · intro hq
    change q ∈ MvPolynomial.vanishingIdeal ℂ
      {z | ∃ y ∈ Y, MvPolynomial.eval y (commonRadialDenominator i₀ p) ≠ 0 ∧
        TrackD.rationalPoint (commonRadialNumerator p)
          (commonRadialDenominator i₀ p) y = z}
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    rintro z ⟨y, hy, hg, rfl⟩
    have hi : (y - p) i₀ ≠ 0 := by
      simpa [commonRadialDenominator, commonRadialNumerator] using hg
    have hs := common_radial_chart_point_slice Y i₀ p y hy hi
    have hz := (TrackD.mem_ideal_iff_eval_zero
      (TrackA.projectiveLinearSlice (radialImage p Y) (MvPolynomial.X i₀)) q).1 hq _ hs
    simpa only [MvPolynomial.aeval_eq_eval, common_radial_chart_point] using hz

end
end DistinctDistances.SparseCones
