import DistinctDistances.TrackD.GeoSpan
import DistinctDistances.TrackD.TripleViewpoint
import DistinctDistances.TrackD.TripleTransversality

/-! The nonlinear-curve forms of the generic-viewpoint and non-tangency inputs.
The affine-span theorem merged from the geometric implementation lane supplies
the no-containing-line hypothesis, with the shared Hilbert dimension model. -/

namespace DistinctDistances.TrackD

open scoped Classical
noncomputable section
variable {d : ℕ}

theorem nonlinear_curve_not_contained_in_line (X : AffineVariety d)
    (hX : IsCurve X) (hnl : ¬ IsLine X)
    (L : AffineSubspace ℂ (Point d)) (hL : Module.finrank ℂ L.direction = 1) :
    ¬ X.points ⊆ L := by
  intro hsub
  have hspan : complexSpan X ≤ L := affineSpan_le.mpr hsub
  have hle := Submodule.finrank_mono (AffineSubspace.direction_le hspan)
  have hge := GeoRadial.nonlinear_span_ge_two X hX hnl
  rw [hL] at hle
  omega

/-- `secants.tex:442–447`, under the original nonlinear-curve hypotheses. -/
theorem nonlinear_curves_generic_nontangency (X Y : AffineVariety d)
    (hX : IsCurve X) (hY : IsCurve Y) (hnlX : ¬ IsLine X) (hnlY : ¬ IsLine Y) :
    ForGeneralPair X Y (fun x y =>
      y - x ∉ X.tangentSpace x ∧ y - x ∉ Y.tangentSpace y) := by
  exact curve_generic_nontangency X Y hX hY
    (nonlinear_curve_not_contained_in_line X hX hnlX)
    (nonlinear_curve_not_contained_in_line Y hY hnlY)

/-- `secants.tex:433–437`, with one principal open for the complete finite list. -/
theorem nonlinear_curve_general_viewpoint_centers_separated
    (X : AffineVariety 3) (hX : IsCurve X) (hnl : ¬ IsLine X) (Pc : Finset (Point 3)) :
    ForGeneralPoint X (fun v =>
      (∀ p ∈ Pc, v ≠ p) ∧ ∀ p ∈ Pc, ∀ q ∈ Pc, p ≠ q →
        ∀ (hp : p ≠ v) (hq : q ≠ v), radialProjection v p hp ≠ radialProjection v q hq) := by
  exact general_viewpoint_centers_separated X hX.1
    (Bridges.curve_points_infinite X hX.1 hX.2).nonempty
    (nonlinear_curve_not_contained_in_line X hX hnl) Pc

end
end DistinctDistances.TrackD
