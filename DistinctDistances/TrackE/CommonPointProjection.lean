import DistinctDistances.TrackE.CommonProjectionInputs

/-! The point-projection budget without a flat classification or rounding,
`sc:retained-products.family`, sparse-cones.tex:184–191. -/
namespace DistinctDistances.SparseCones
open scoped Classical
noncomputable section

theorem common_point_projection_budget {d k : ℕ} (i₀ : Fin d)
    (Y : AffineVariety d) (hY : Y.IsIrreducible) (hk : 1 ≤ k)
    (hYd : Y.dimension = k) (p : Point d)
    (hchart : ∃ y ∈ Y, (y - p) i₀ ≠ 0)
    (himage : (radialImage p Y).dimension = k) (hmult : Y.multiplicity p ≤ 1) :
    Y.degree ≤ 2 * (TrackA.radialMapDegree p Y : ℚ) * (radialImage p Y).degree := by
  have hfinite := TrackA.dep_radial_degree_exists Y hY k hk hYd p himage
  have hformula := TrackA.poly_projection_radial Y hY k hk hYd p himage
    (TrackA.radialMapDegree p Y) hfinite
  have hmap : (1 : ℚ) ≤ (TrackA.radialMapDegree p Y : ℚ) := by
    exact_mod_cast hfinite.1
  have hradial := common_radial_degree_ge_one i₀ Y hY p hchart
  have hproduct : (1 : ℚ) ≤
      (TrackA.radialMapDegree p Y : ℚ) * (radialImage p Y).degree := by
    simpa only [one_mul] using mul_le_mul hmap hradial (by norm_num : (0 : ℚ) ≤ 1)
      (by positivity : (0 : ℚ) ≤ (TrackA.radialMapDegree p Y : ℚ))
  linarith

end
end DistinctDistances.SparseCones
