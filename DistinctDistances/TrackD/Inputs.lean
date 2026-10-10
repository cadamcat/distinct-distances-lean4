import DistinctDistances.TrackD.Basic
import DistinctDistances.Bridges.CIncidence
import DistinctDistances.Bridges.CurveSamples

/-!
# Inputs of track D from other tracks

The exact forms track D consumes, as `Prop`s. Abstract track D lemmas take them as explicit
hypotheses, so their proofs are independent of the other tracks; the bridges supply each input
from the owning track's theorem.
-/

namespace DistinctDistances
namespace TrackD

open scoped BigOperators
open scoped Classical

noncomputable section

/-- Real affine lines of `ℝ^m`. -/
def IsRealLine {m : ℕ} (ℓ : AffineSubspace ℝ (Pt m)) : Prop :=
  Module.finrank ℝ ℓ.direction = 1

/-- Real affine planes of `ℝ^m`. -/
def IsRealPlane {m : ℕ} (H : AffineSubspace ℝ (Pt m)) : Prop :=
  Module.finrank ℝ H.direction = 2

/-- Number of points of `Q` on a real affine subspace. -/
def occ {m : ℕ} (Q : Finset (Pt m)) (F : AffineSubspace ℝ (Pt m)) : ℕ :=
  (Q.filter (· ∈ F)).card

/-- Szemerédi–Trotter point–line incidence bound in `ℝ^m` (`ci:st`,
`classical-incidence.tex:48–94`, "also in `ℝ^s`"). -/
def STIncidence (m : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (Q : Finset (Pt m)) (L : Finset (AffineSubspace ℝ (Pt m))),
    (∀ ℓ ∈ L, IsRealLine ℓ) →
      (((Q ×ˢ L).filter (fun x => x.1 ∈ x.2)).card : ℝ) ≤
        C * (((Q.card : ℝ) * L.card) ^ ((2 : ℝ) / 3) + Q.card + L.card)

/-- The rich-line form of Szemerédi–Trotter in `ℝ^m` (`ci:st`): at most `C (n^2/t^3 + n/t)`
lines contain at least `t ≥ 2` points of an `n`-point set. -/
def STRichLines (m : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (Q : Finset (Pt m)) (L : Finset (AffineSubspace ℝ (Pt m))) (t : ℝ),
    2 ≤ t → (∀ ℓ ∈ L, IsRealLine ℓ ∧ t ≤ occ Q ℓ) →
      (L.card : ℝ) ≤ C * ((Q.card : ℝ) ^ 2 / t ^ 3 + Q.card / t)

/-- `poly:separators` for curves (`polynomial.tex:66–113`, the case `u = 1`): an irreducible
complex affine curve of degree `a` contains at most `C a M` real sample points. Used as
`geo:curve-mass` (`secants.tex:246–250`). -/
def CurveSampleBound (d : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset (Pt d)) (Y : AffineVariety d), IsCurve Y →
    (massOn P Y.points : ℝ) ≤ C * (Y.degree : ℝ) * cfgM P

/-- Track C, `ci:st` (point–line incidences in `ℝ^m`). Placeholder until track C's statement is
on `main`. -/
theorem ci_st_incidence (m : ℕ) : STIncidence m := by
  obtain ⟨C, hC, h⟩ := Bridges.ci_st_affine
  exact ⟨C, hC, h m⟩

/-- Track C, `ci:st` (rich lines in `ℝ^m`). Placeholder until track C's statement is on `main`. -/
theorem ci_st_rich (m : ℕ) : STRichLines m := by
  exact Bridges.ci_st_rich_real m

/-- Track A, `poly:separators` (curve case). Placeholder until track A's statement is on `main`. -/
theorem poly_separators_curve (d : ℕ) : CurveSampleBound d := by
  exact Bridges.curve_sample_bound d

end

end TrackD
end DistinctDistances
