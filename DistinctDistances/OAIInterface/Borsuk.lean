import OAI.Geometry.Borsuk.Simplicial.UnitRadial

/-! Exact wrapper for the prebuilt OAI theorem
OAI.BorsukNine.SimplicialChains.odd_sphere_dimension_bound,
OAI/Geometry/Borsuk/Simplicial/UnitRadial.lean. -/

namespace DistinctDistances.OAIInterface

theorem odd_sphere_dimension_bound (n m : ℕ) (hn : 0 < n)
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hf : ContinuousOn f {x | ‖x‖ = 1}) (hfn : ∀ x, ‖x‖ = 1 → ‖f x‖ = 1)
    (hfo : ∀ x, ‖x‖ = 1 → f (-x) = -f x) : n ≤ m := by
  exact OAI.BorsukNine.SimplicialChains.odd_sphere_dimension_bound n m hn f hf hfn hfo

end DistinctDistances.OAIInterface
