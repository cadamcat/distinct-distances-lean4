import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
The definitions of the target, `Challenge.lean`, restated for the proof. They are copied verbatim
from Formal Conjectures, `FormalConjecturesForMathlib/Geometry/Metric.lean` at commit
660712921cf75e22b926536e8430cb613517e3ff (Copyright 2025 The Formal Conjectures Authors,
Apache-2.0), as in `Challenge.lean`.
-/

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
