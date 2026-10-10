import DistinctDistances.TrackE.ComplexSpan
import DistinctDistances.Bridges.DirectionSections

/-!
# Projective geometry inputs requested from track A

Exact forms consumed by `red:directions.count` at `reduction.tex:145–146,166–178,197–201`.
These reuse track A's projective variety model. The placeholder theorems are external inputs,
not track E proofs.
-/

namespace DistinctDistances

noncomputable section

namespace Request

open scoped BigOperators

/-- Degree positivity and the ambient projective dimension bound. -/
def DirectionVarietyBasics (d : ℕ) : Prop :=
  ∀ Y : ProjectiveVariety d, Y.IsIrreducible →
    1 ≤ (Y.degree : ℝ) ∧ Y.dimension < d

/-- The finite-locus bound in the base case of the dimension induction. -/
def ZeroDimDirectionLocus (d : ℕ) : Prop :=
  ∀ Y : ProjectiveVariety d, Y.IsIrreducible → Y.dimension = 0 →
    ∃ F : Finset (ProjectivePoint d), Y.points ⊆ (F : Set (ProjectivePoint d)) ∧
      (F.card : ℝ) ≤ (Y.degree : ℝ)

/-- Proper hyperplane sections, specialized to real normal vectors. -/
def DirectionHyperplaneSections (d : ℕ) : Prop :=
  ∀ Y : ProjectiveVariety d, Y.IsIrreducible → 1 ≤ Y.dimension →
    ∀ n : RPoint d, (∃ v ∈ Y.affineCone.points, ∑ i, v i * cplx n i ≠ 0) →
      ∃ F : ProjectiveFamily.Family d,
        (∀ V ∈ F, V.IsIrreducible ∧ V.dimension + 1 = Y.dimension) ∧
        (∑ V ∈ F, (V.degree : ℝ)) ≤ (Y.degree : ℝ) ∧
        ∀ p q : RPoint d, DirMem Y p q → inner ℝ (q - p) n = 0 →
          ∃ V ∈ F, DirMem V p q

/-- An irreducible curve is contained in a linear subspace or meets it in a finite
locus of cardinality at most its degree. The consumer needs subspace dimension at most three. -/
def CurveLinearSections (d : ℕ) : Prop :=
  ∀ Y : ProjectiveVariety d, Y.IsIrreducible → Y.dimension = 1 →
    ∀ W : Submodule ℂ (Point d), Module.finrank ℂ W ≤ 3 →
      (∀ z ∈ Y.points, z.submodule ≤ W) ∨
      ∃ F : Finset (ProjectivePoint d), (F.card : ℝ) ≤ (Y.degree : ℝ) ∧
        ∀ z ∈ Y.points, z.submodule ≤ W → z ∈ F

/-- Placeholder for track A's `FA.model` degree/dimension facts. -/
theorem directionVarietyBasics (d : ℕ) : DirectionVarietyBasics d :=
  Bridges.direction_variety_basics d

/-- Placeholder for track A's zero-dimensional projective locus bound. -/
theorem zeroDimDirectionLocus (d : ℕ) : ZeroDimDirectionLocus d :=
  Bridges.zero_dim_direction_locus d

/-- Placeholder for track A's `FA.bezout` with a degree-one cut. -/
theorem directionHyperplaneSections (d : ℕ) : DirectionHyperplaneSections d :=
  Bridges.direction_hyperplane_sections d

/-- Placeholder for track A's proper curve linear-section bound. -/
theorem curveLinearSections (d : ℕ) : CurveLinearSections d :=
  Bridges.curve_linear_sections d

end Request

end

end DistinctDistances
