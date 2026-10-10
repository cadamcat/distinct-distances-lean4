import DistinctDistances.TrackD.PerspectiveGroup
import DistinctDistances.TrackD.PerspectiveCentersGeometry
import DistinctDistances.TrackD.PerspectiveChartAlgebra
import DistinctDistances.TrackD.MDPerspAux

/-! The plane-chart implementation package for `secants.tex:351–370`.
The quantitative stabilizer theorem is proved independently in PerspectiveGroup. -/

namespace DistinctDistances.TrackD

open scoped Classical
noncomputable section

variable {d : ℕ}

/-- Centres of perspectives between two fixed curves, outside both chosen planes. -/
def perspectiveCenters (Y Y' : AffineVariety d)
    (Pl Pl' : AffineSubspace ℂ (Point d)) : Set (Point d) :=
  {p | p ∉ Pl ∧ p ∉ Pl' ∧ radialImage p Y = radialImage p Y'}

/-- Implementation package (`secants.tex:351–370`). Fix one perspective, identify the
projective intersection line of the two planes with the line at infinity of a chart,
and compare every other perspective with the fixed one. The comparisons are elements
of the *actual* scalar-affine stabilizer of the recharted curve. A perspective between
distinct planes determines its centre, which gives injectivity. Projective recharting
preserves the curve degree; taking its affine part can only lower it.

The nonempty centre hypothesis supplies the reference perspective. If the two affine
planes coincide, equality of radial-image closures outside that plane would force the
curves to coincide, so that case contradicts `hYY'`. No generic centre or finiteness
assumption is hidden in this statement. -/
theorem perspective_chart_stabilizer_embedding
    (Y Y' : AffineVariety d) (Pl Pl' : AffineSubspace ℂ (Point d))
    (hY : IsCurve Y) (hY' : IsCurve Y') (hline : ¬ IsLine Y) (hline' : ¬ IsLine Y')
    (hYY' : Y ≠ Y')
    (hPl : Module.finrank ℂ Pl.direction = 2)
    (hPl' : Module.finrank ℂ Pl'.direction = 2)
    (hYP : Y.points ⊆ Pl) (hYP' : Y'.points ⊆ Pl')
    (hne : (perspectiveCenters Y Y' Pl Pl').Nonempty) :
    ∃ Z : AffineVariety 2, IsCurve Z ∧ Z.points.Nonempty ∧
      (∀ L : AffineSubspace ℂ (Point 2), Module.finrank ℂ L.direction = 1 →
        ¬ Z.points ⊆ L) ∧ Z.degree ≤ Y.degree ∧
      ∃ f : perspectiveCenters Y Y' Pl Pl' → ScalarAffine.stabilizer Z,
        Function.Injective f := by
  exact PerspectiveTransport.chart_stabilizer_embedding Y Y' Pl Pl' hY hY' hline hline'
    hYY' hPl hPl' hYP hYP' (perspectiveCenters Y Y' Pl Pl') (by
      intro p hp
      exact hp) hne

/-- The proved stabilizer calculation now bounds the original centres, uniformly
in the ambient dimension and the two curves. The sole geometric implementation
input is the explicit chart-and-centre embedding above. -/
theorem perspective_centers_degree_bound
    (Y Y' : AffineVariety d) (Pl Pl' : AffineSubspace ℂ (Point d))
    (hY : IsCurve Y) (hY' : IsCurve Y') (hline : ¬ IsLine Y) (hline' : ¬ IsLine Y')
    (hYY' : Y ≠ Y')
    (hPl : Module.finrank ℂ Pl.direction = 2)
    (hPl' : Module.finrank ℂ Pl'.direction = 2)
    (hYP : Y.points ⊆ Pl) (hYP' : Y'.points ⊆ Pl') :
    (perspectiveCenters Y Y' Pl Pl').Finite ∧
      ((perspectiveCenters Y Y' Pl Pl').ncard : ℝ) ≤ (Y.degree : ℝ) := by
  classical
  by_cases hne : (perspectiveCenters Y Y' Pl Pl').Nonempty
  · obtain ⟨Z, hZ, hZne, hZline, hdegree, f, hf⟩ :=
      perspective_chart_stabilizer_embedding Y Y' Pl Pl' hY hY' hline hline'
        hYY' hPl hPl' hYP hYP' hne
    obtain ⟨hfinite, hbound⟩ := ScalarAffine.stabilizer_degree_bound Z hZ hZne hZline
    let F : Point d → ScalarAffine.stabilizer Z := fun p =>
      if hp : p ∈ perspectiveCenters Y Y' Pl Pl' then f ⟨p, hp⟩ else 1
    have hFinj : Set.InjOn F (perspectiveCenters Y Y' Pl Pl') := by
      intro p hp q hq heq
      have h : f ⟨p, hp⟩ = f ⟨q, hq⟩ := by simpa [F, hp, hq] using heq
      exact congrArg Subtype.val (hf h)
    have hfiniteS : (perspectiveCenters Y Y' Pl Pl').Finite := by
      exact hfinite.of_injOn (by intro p hp; exact Set.mem_univ _) hFinj
    refine ⟨hfiniteS, ?_⟩
    have hcard : (perspectiveCenters Y Y' Pl Pl').ncard ≤
        (Set.univ : Set (ScalarAffine.stabilizer Z)).ncard :=
      Set.ncard_le_ncard_of_injOn F (by simp) hFinj hfinite
    have hcardR : ((perspectiveCenters Y Y' Pl Pl').ncard : ℝ) ≤
        ((Set.univ : Set (ScalarAffine.stabilizer Z)).ncard : ℝ) := by exact_mod_cast hcard
    exact hcardR.trans (hbound.trans (by exact_mod_cast hdegree))
  · have hempty : perspectiveCenters Y Y' Pl Pl' = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    refine ⟨by rw [hempty]; exact Set.finite_empty, ?_⟩
    rw [hempty, Set.ncard_empty, Nat.cast_zero]
    exact_mod_cast (le_trans (by norm_num : (0 : ℚ) ≤ 1) (Y.one_le_degree hY.1.ne_top))

end
end DistinctDistances.TrackD
