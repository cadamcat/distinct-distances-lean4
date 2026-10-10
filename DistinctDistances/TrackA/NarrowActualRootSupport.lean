import DistinctDistances.TrackA.NarrowRadialCountSupport

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical BigOperators

/-- One literal target point realizes each actual-center group depth,
with every moving root on one original carrier and one line parameter. -/
theorem common_actual_radial_root_counts {n l : ℕ} (J : AffineFamily.Family n)
    (hl : 1 ≤ l) (hJ : AffineFamily.IsPure J l) (Y : AffineVariety n) (hY : Y ∈ J)
    (S : Finset (Point n)) (himage : ∀ p ∈ S, (radialImage p Y).dimension = l) :
    ∃ y ∈ Y.points, ∀ p ∈ S, ∃ hpy : y ≠ p,
      (groupMovingFiber J p Y (radialProjection p y hpy) y).Finite ∧
      (groupMovingFiber J p Y (radialProjection p y hpy) y).ncard = groupDepth p J Y - 1 ∧
      ∀ x ∈ groupMovingFiber J p Y (radialProjection p y hpy) y,
        ∃ V ∈ J, x ∈ radialFiber p V (radialProjection p y hpy) ∧
          (radialFiber p V (radialProjection p y hpy)).Finite ∧
          (∀ W ∈ J, x ∈ W.points → W = V) ∧
          ∃! t : ℂ, p = y + t • (x-y) := by
  have hgen : ∀ p ∈ S, ∀ V ∈ J, radialImage p V = radialImage p Y →
      GenericallyFiniteRadialDegree p V (radialMapDegree p V) := by
    intro p hp V hV hVz
    have hd : (radialImage p V).dimension = l := by rw [hVz]; exact himage p hp
    have hex := radial_generic_degree_exists V (hJ V hV).1 hl (hJ V hV).2 p hd
    simpa only [radialMapDegree, dif_pos hex] using hex.choose_spec
  obtain ⟨y, hy, hgood⟩ := simultaneous_radial_source_point J hl hJ Y hY S himage
    (fun p V => radialMapDegree p V) hgen
  refine ⟨y, hy, ?_⟩
  intro p hp
  obtain ⟨hpy, hcount, hdisj⟩ := hgood p hp
  obtain ⟨hfinite, hcard⟩ := groupMovingFiber_count J p y Y hY hy hpy
    (radialMapDegree p) hcount hdisj
  refine ⟨hpy, hfinite, hcard, ?_⟩
  intro x hx
  obtain ⟨hxfiber, hxny⟩ := hx
  obtain ⟨V, hxV⟩ := Set.mem_iUnion.mp hxfiber
  obtain ⟨hV, hVz⟩ := Finset.mem_filter.mp V.property
  have hxy : x ≠ y := by simpa only [Set.mem_singleton_iff] using hxny
  exact ⟨V.val, hV, hxV, (hcount V.val hV hVz).1,
    radial_fiber_unique_original_carrier J p V.val hV (radialProjection p y hpy)
      (hdisj V.val hV hVz) x hxV,
    radial_moving_root_parameter p y x hpy hxV.2.1 hxy hxV.2.2⟩

end
end DistinctDistances.TrackA
