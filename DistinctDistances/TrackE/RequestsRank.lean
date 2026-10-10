import DistinctDistances.TrackE.SkewPoint
import DistinctDistances.Bridges.PairFlatEnvelope

/-! Affine-model input consumed by the global rank assembly. -/

namespace DistinctDistances.Request
open scoped BigOperators Classical
noncomputable section

/-- Track A, `FA.model` and `poly:envelope`, specialized to the physical pair flats
in `red:main-contradiction` (reduction.tex:467–470). Each nonempty affine pair flat
lies in an irreducible component of the envelope, of dimension at least C(d,2).
The family consists of components of the same equations of degree at most D. -/
theorem pair_flat_envelope_carriers (d : ℕ) (W : Finset (RPoint d × RPoint d)) (D : ℕ) :
    ∃ F : AffineFamily.Family (Fintype.card (SkewIdx (d + 1))),
      (∀ V ∈ F, V.IsIrreducible) ∧ AffineFamily.ComponentsDefinedInDegree F D ∧
      AffineFamily.locus F = envelope (skewToPoint '' (⋃ x ∈ W, Reduction.pairFlat x.1 x.2)) D ∧
      ∀ x ∈ W, ∃ V ∈ F,
        skewToPoint '' Reduction.pairFlat x.1 x.2 ⊆ V.points ∧ Nat.choose d 2 ≤ V.dimension :=
  Bridges.pair_flat_envelope_carriers d W D

end
end DistinctDistances.Request
