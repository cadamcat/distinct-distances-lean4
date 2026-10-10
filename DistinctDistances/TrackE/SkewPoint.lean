import DistinctDistances.TrackE.PairFlats
import DistinctDistances.Foundations

/-! Enumeration of skew-form entries in the shared affine-variety model. -/

namespace DistinctDistances

noncomputable section

/-- Skew-form coordinates on `ℂ^e` as track A's `Point n`, `n = C(e,2)`, through
`Fintype.equivFin`. -/
def skewToPoint {e : ℕ} (z : SkewIdx e → ℂ) : Point (Fintype.card (SkewIdx e)) :=
  fun i => z ((Fintype.equivFin (SkewIdx e)).symm i)

end

end DistinctDistances
