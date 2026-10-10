import DistinctDistances.TrackD.Basic

namespace DistinctDistances
namespace TrackD

open scoped BigOperators
open scoped Classical
noncomputable section
variable {d : ℕ}

/-- The generic degree `t` of the radial projection `π_p : Y ⇢ closure(π_p Y)` (shared model:
`GenericallyFiniteRadialDegree`); zero when undefined. -/
def radialMapDegree (p : Point d) (Y : AffineVariety d) : ℕ :=
  if h : ∃ r, GenericallyFiniteRadialDegree p Y r then Nat.find h else 0

/-- Validity of an ordered triple of curves at a center `p ∈ ℂ^3` (`secants.tex:417–432`): the
three curves have the same nonlinear projection `γ`, multiplicity at most half the degree at `p`,
and each curve occurs at most its map degree times. -/
def CurveTripleValid (p : Point 3) (Y₁ Y₂ Y₃ : AffineVariety 3) : Prop :=
  radialImage p Y₁ = radialImage p Y₂ ∧ radialImage p Y₁ = radialImage p Y₃ ∧
  (radialImage p Y₁).dimension = 1 ∧ 2 ≤ (radialImage p Y₁).degree ∧
  (∀ Y ∈ ({Y₁, Y₂, Y₃} : Finset (AffineVariety 3)), Y.multiplicity p ≤ Y.degree / 2) ∧
  ∀ Y ∈ ({Y₁, Y₂, Y₃} : Finset (AffineVariety 3)),
    ((if Y₁ = Y then 1 else 0) + (if Y₂ = Y then 1 else 0) + (if Y₃ = Y then 1 else 0) : ℕ) ≤
      radialMapDegree p Y

end
end TrackD
end DistinctDistances
