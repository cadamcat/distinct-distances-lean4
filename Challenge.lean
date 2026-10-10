/-
The target of this formalization: JSP-000900, "What is the minimum distinct-distance count for a
prescribed number of points in fixed higher dimension?" (TheJustinSunPrize/awards at 16877004,
catalog section JSP-000900). The catalog's review note reads the solution as: for each fixed
`d ≥ 3`, every `n`-point set in `ℝ^d` determines at least `c_d n^(2/d)` distinct distances, which
matches the lattice order, with no exact leading constant. The source proof is OpenAI, "The
higher-dimensional Erdős distinct-distances conjecture" (2026-09-23).

`jsp_000900` states both halves of that answer: the lower bound for every finite point set with at
least two points, and the matching upper bound by some `n`-point set for every `n ≥ 2`.

The definitions `distanceSet` and `distinctDistances` are copied verbatim from Formal Conjectures,
`FormalConjecturesForMathlib/Geometry/Metric.lean` at commit
660712921cf75e22b926536e8430cb613517e3ff (Copyright 2025 The Formal Conjectures Authors,
Apache-2.0); only the module-system wrappers are dropped. Formal Conjectures' `Erdos1083.erdos_1083`
(`FormalConjectures/ErdosProblems/1083.lean`, same commit) asks for the weaker `n^(2/d - o(1))`
form. This file imports Mathlib alone and is not imported by the proof.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- BEGIN FORMAL CONJECTURES DEFINITIONS
open scoped Finset

variable {X : Type*} [MetricSpace X]

/-- The set of distances determined by a finite set of points in a metric space. -/
noncomputable def distanceSet (points : Finset X) : Finset ℝ :=
  points.offDiag.image fun (pair : X × X) => dist pair.1 pair.2

/--
Given a finite set of points in a metric space, we define the number of distinct distances
between pairs of points.
-/
noncomputable def distinctDistances (points : Finset X) : ℕ :=
  #(distanceSet points)
-- END FORMAL CONJECTURES DEFINITIONS

namespace DistinctDistances

/-- For every dimension `d ≥ 3` there are constants `0 < c` and `0 < C` such that every finite set
`P` of at least two points of Euclidean `d`-space determines at least `c |P|^(2/d)` distinct
distances, and for every `n ≥ 2` some `n`-point set determines at most `C n^(2/d)` distinct
distances. -/
theorem jsp_000900 :
    ∀ d : ℕ, 3 ≤ d →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
        (∀ P : Finset (EuclideanSpace ℝ (Fin d)), 2 ≤ P.card →
          c * (P.card : ℝ) ^ ((2 : ℝ) / (d : ℝ)) ≤ (distinctDistances P : ℝ)) ∧
        (∀ n : ℕ, 2 ≤ n → ∃ P : Finset (EuclideanSpace ℝ (Fin d)), P.card = n ∧
          (distinctDistances P : ℝ) ≤ C * (n : ℝ) ^ ((2 : ℝ) / (d : ℝ))) := by
  sorry

end DistinctDistances
