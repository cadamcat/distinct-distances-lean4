import DistinctDistances.TrackE.Basic
import DistinctDistances.Foundations

/-!
# Directions and directional curve families in track A's model

`π_p(q) = [q - p] ∈ ℙ^{d-1}` is track A's `radialProjection` of the complexified points
(`ProjectivePoint d = ℙ(ℂ^d)`). The definitions below have the same bodies as track D's
`TrackD.SpansAtMostPlane`, `TrackD.IsDirectionalFamily`, `TrackD.familyPoints` and
`TrackD.DirIn` (lane `lead-d`, uncommitted at the time of writing); one copy should be kept when
both reach `main`.
-/

namespace DistinctDistances

open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-- `π_p(q) ∈ Y` for real points `q ≠ p` (`reduction.tex:70-72`). -/
def DirMem (Y : ProjectiveVariety d) (p q : RPoint d) : Prop :=
  ∃ h : cplx q ≠ cplx p, radialProjection (cplx p) (cplx q) h ∈ Y.points

/-- A projective variety in `ℙ^{d-1}` spans a projective subspace of dimension at most two. -/
def SpansAtMostPlane (γ : ProjectiveVariety d) : Prop :=
  ∃ W : Submodule ℂ (Point d), Module.finrank ℂ W ≤ 3 ∧ ∀ z ∈ γ.points, z.submodule ≤ W

/-- A directional curve family (`sparse-cones.tex:5-8`): finitely many distinct irreducible
projective curves in `ℙ^{d-1}`, each spanning projective dimension at most two. Its total degree
is `ProjectiveFamily.degree`. -/
def IsDirectionalFamily (C : ProjectiveFamily.Family d) : Prop :=
  ∀ γ ∈ C, γ.IsIrreducible ∧ γ.dimension = 1 ∧ SpansAtMostPlane γ

/-- `π_p(q) ∈ C_p`: membership in the union of the family. -/
def DirCovered (C : RPoint d → ProjectiveFamily.Family d) (p q : RPoint d) : Prop :=
  ∃ γ ∈ C p, DirMem γ p q

open Classical in
/-- The ordered pairs `(p,q)`, `p ≠ q`, covered in neither orientation:
`π_p(q) ∉ C_p` and `π_q(p) ∉ C_q`. -/
def uncoveredPairs (P : Finset (RPoint d)) (C : RPoint d → ProjectiveFamily.Family d) :
    Finset (RPoint d × RPoint d) :=
  P.offDiag.filter fun e => ¬ DirCovered C e.1 e.2 ∧ ¬ DirCovered C e.2 e.1

end

end DistinctDistances
