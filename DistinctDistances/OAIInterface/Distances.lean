import DistinctDistances.Defs
import OAI.Combinatorics.Distances.PolynomialIsolation

/-! The local distinct-distance interface to the original OAI regime theorem. -/

open Filter
open scoped Topology

namespace DistinctDistances.OAIInterface

/-- `TOP.regime`: restatement of
`OAI.ErdosDistinctDistances.failure_gives_regime`,
OAI/Combinatorics/Distances/PolynomialIsolation.lean:59–112.
`distinctDistances` is the cardinality of exactly the same off-diagonal image. -/
theorem failure_gives_regime {d : ℕ} (hd : 3 ≤ d)
    (hfail : ¬ ∃ c : ℝ, 0 < c ∧
      ∀ P : Finset (EuclideanSpace ℝ (Fin d)), 2 ≤ P.card →
        c * (P.card : ℝ) ^ (2 / (d : ℝ)) ≤ (distinctDistances P : ℝ)) :
    ∃ P : ℕ → Finset (EuclideanSpace ℝ (Fin d)),
      (∀ k, 2 ≤ (P k).card) ∧
      Tendsto (fun k => (P k).card) atTop atTop ∧
      Tendsto (fun k => (1 + (distinctDistances (P k) : ℝ)) /
        ((P k).card : ℝ) ^ (2 / (d : ℝ))) atTop (𝓝 0) := by
  -- `distanceSet` and OAI's `distances` are definitionally equal off-diagonal images.
  exact OAI.ErdosDistinctDistances.failure_gives_regime hd hfail

end DistinctDistances.OAIInterface
