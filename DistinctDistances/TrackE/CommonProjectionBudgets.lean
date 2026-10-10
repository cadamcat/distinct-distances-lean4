import DistinctDistances.TrackE.CommonCenterMultiplicity
import DistinctDistances.TrackE.CommonPointProjection

/-! Original-list projection and depth budgets for mixed sections,
`sc:retained-products.family`, sparse-cones.tex:172–191. -/
namespace DistinctDistances.SparseCones
open scoped BigOperators Classical
noncomputable section

theorem common_original_list_projection_budgets {d k : ℕ} (i₀ : Fin d)
    (X : AffineVariety d) (hX : X.IsIrreducible) (hXd : X.dimension = k)
    (F L : AffineFamily.Family d) (hFL : F ⊆ L)
    (hk : 1 ≤ k) (hF : AffineFamily.IsPure F k) (R : ℝ)
    (hchart : ∀ Y ∈ F, ∃ x ∈ X, ∃ y ∈ Y, (y - x) i₀ ≠ 0)
    (hdepth : ∀ Y ∈ F, TrackD.ForGeneralPair X Y (fun x y =>
      y - x ∉ X.tangentSpace x ∧ y - x ∉ Y.tangentSpace y ∧
      (TrackD.movingRoots L x y).Finite ∧
        ((TrackD.movingRoots L x y).ncard : ℝ) ≤ R)) :
    TrackD.ForGeneralPoint X (fun p =>
      (∀ Y ∈ F,
        (∃ y ∈ Y, (y - p) i₀ ≠ 0) ∧
        (radialImage p Y).dimension = k ∧ Y.multiplicity p ≤ 1 ∧
        1 ≤ (radialImage p Y).degree ∧
        GenericallyFiniteRadialDegree p Y (TrackA.radialMapDegree p Y) ∧
        (Y.degree : ℝ) ≤ 2 * (TrackA.radialMapDegree p Y : ℝ) *
          ((radialImage p Y).degree : ℝ)) ∧
      (∀ Y ∈ F, ∀ Y' ∈ F,
        commonProductImage i₀ X Y = commonProductImage i₀ X Y' →
          radialImage p Y = radialImage p Y') ∧
      (∀ Y ∈ F,
        ((∑ V ∈ F.filter (fun V =>
          commonProductImage i₀ X V = commonProductImage i₀ X Y),
            TrackA.radialMapDegree p V) : ℝ) ≤ R)) := by
  have hradial := common_original_list_radial_depth i₀ X hX F L hFL hk hF R hchart hdepth
  have hcharts := common_original_list_chart_witnesses i₀ X hX F hchart
  have hmult := common_original_list_center_multiplicity X hX hXd F hk hF
  apply ((hradial.and hX hcharts).and hX hmult).mono
  intro p hp hh
  refine ⟨?_, hh.1.1.2.2.1, hh.1.1.2.2.2⟩
  intro Y hY
  have hYirr := (hF Y hY).1
  have hYdim := (hF Y hY).2
  have hchartY := hh.1.2 Y hY
  have himageY := hh.1.1.1 Y hY
  have hmultY := hh.2 Y hY
  have hfinite := TrackA.dep_radial_degree_exists Y hYirr k hk hYdim p himageY
  have hprojection := common_point_projection_budget i₀ Y hYirr hk hYdim p
    hchartY himageY hmultY
  refine ⟨hchartY, himageY, hmultY,
    common_radial_degree_ge_one i₀ Y hYirr p hchartY, hfinite, ?_⟩
  exact_mod_cast hprojection

end
end DistinctDistances.SparseCones
