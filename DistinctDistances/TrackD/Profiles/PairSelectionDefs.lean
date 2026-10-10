import DistinctDistances.TrackD.Profiles.Defs

namespace DistinctDistances
namespace TrackD
open scoped BigOperators Classical
noncomputable section
variable {d : ℕ}

/-- Ordered pairs `(p, q)`, `p ≠ q`, covered in at least one orientation:
`π_p(q) ∈ C_p` or `π_q(p) ∈ C_q` (`profiles.tex:519–521`). -/
def coveredPairs (P : Finset (Pt d)) (Cf : Pt d → ProjectiveFamily.Family d) :
    Finset (Pt d × Pt d) :=
  (P ×ˢ P).filter (fun pq => pq.1 ≠ pq.2 ∧ (DirIn (Cf pq.1) pq.1 pq.2 ∨ DirIn (Cf pq.2) pq.2 pq.1))

/-- The global terminal assignment (`profiles.tex:540–560`): each point of each non-core piece is
assigned to at most one carrier curve after the `(d-1)`st cut of its own piece; line members are
real; at most `θ n` points of each piece are left unassigned. -/
structure TerminalAssignment (Q : Partition d) (θ : ℝ) (τ : Pt d → Option (AffineVariety d)) :
    Prop where
  carrier : ∀ X ∈ Q.pieces, ∀ q ∈ X.pts, ∀ Y, τ q = some Y →
    X.path.IsCarrier (d - 1) Y ∧ toC q ∈ Y
  realLines : ∀ q Y, τ q = some Y → IsLine Y → IsRealFlat Y
  unassigned : ∀ X ∈ Q.pieces, ((X.pts.filter (fun q => τ q = none)).card : ℝ) ≤ θ * X.pts.card

/-- A selected incidence (`profiles.tex:540–544, 536–538`): `p ≠ q`, `π_p(q) ∈ C_p`, the target's
terminal curve does not project into `C_p` (global terminal deletion), and the line `pq` carries
at most `B^ρ` sample points (light lines). -/
def SelectedIncidence (P : Finset (Pt d)) (Cf : Pt d → ProjectiveFamily.Family d)
    (τ : Pt d → Option (AffineVariety d)) (ρ : ℝ) (p q : Pt d) : Prop :=
  p ≠ q ∧ DirIn (Cf p) p q ∧ (∀ Y, τ q = some Y → ¬ ProjectsInto (Cf p) p Y) ∧
    (occ P (affineSpan ℝ {p, q}) : ℝ) ≤ cfgB P ^ ρ

/-- The window alternatives of `prof:pair-selection` for the selected source and target pools,
at precision `ρ` (`profiles.tex:525–535`):
* common: two single pieces of one width `s < log B`;
* separated: two single pieces with width ratio at least `1/ρ`, both widths at most `ρ log B`;
* outer: one pool of pieces of width `log B`, used as both factors, of size at least `N √δ`. -/
def WindowAlternative (P : Finset (Pt d)) (δ ρ : ℝ) (plx ply : Finset (Piece d)) : Prop :=
  (∃ X Y : Piece d, plx = {X} ∧ ply = {Y} ∧ X.width = Y.width ∧
      X.width < Real.log (cfgB P)) ∨
  (∃ X Y : Piece d, plx = {X} ∧ ply = {Y} ∧
      (X.width ≤ ρ * Y.width ∨ Y.width ≤ ρ * X.width) ∧
      X.width ≤ ρ * Real.log (cfgB P) ∧ Y.width ≤ ρ * Real.log (cfgB P)) ∨
  (plx = ply ∧ (∀ X ∈ plx, X.width = Real.log (cfgB P)) ∧
      cfgN P * Real.sqrt δ ≤ (poolPts plx).card)

end
end TrackD
end DistinctDistances
