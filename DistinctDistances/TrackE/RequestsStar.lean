import DistinctDistances.TrackE.Directional
import DistinctDistances.Bridges.ProjectiveEnvelope
import DistinctDistances.Bridges.HomogeneousEnvelope

/-! Shared projective-model input for the independent-star reduction. -/

namespace DistinctDistances.Request
open scoped BigOperators Classical
noncomputable section

/-- Track A, `FA.model` and `poly:envelope`, specialized to the homogeneous
degree-D envelope used in reduction.tex:214–225. Its projective components cover
the entire envelope and have dimension at most the number of vector coordinates.
No count, Hilbert bound or rank bound is assumed here. -/
theorem homogeneous_envelope_carriers (d : ℕ) (hd : 3 ≤ d) (D : ℕ) (E : Set (Poly d))
    (hE : ∀ f ∈ E, f.IsHomogeneous D) (V : ProjectiveVariety d)
    (hpoints : V.points = {z | ∀ f ∈ E, MvPolynomial.eval z.rep f = 0}) :
    ∃ F : ProjectiveFamily.Family d,
      (∀ Y ∈ F, Y.IsIrreducible ∧ Y.IsComponentOf V ∧ Y.dimension ≤ d) ∧
      ProjectiveFamily.locus F = V :=
  Bridges.homogeneous_envelope_carriers d hd D E hE V hpoints

end
end DistinctDistances.Request
