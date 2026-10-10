import DistinctDistances.TrackD.Basic

namespace DistinctDistances.TrackD
noncomputable section
variable {d : ℕ}

/-- The chart `φ(u) = λ(u)⁻¹ • u` of directions. -/
def dirChart (lam : Point d →ₗ[ℂ] ℂ) (u : Point d) : Point d := (lam u)⁻¹ • u

/-- The derivative of `dirChart` at `u`: `w ↦ λ(u)⁻¹ • w - (λ(w) / λ(u)^2) • u`. -/
def dirChartDeriv (lam : Point d →ₗ[ℂ] ℂ) (u : Point d) : Point d →ₗ[ℂ] Point d :=
  (lam u)⁻¹ • LinearMap.id - ((lam u) ^ 2)⁻¹ • (lam.smulRight u)

/-- The derivative of the label map `ψ(x, y) = (x, φ(y - x))` at `(x, y)`:
`(ξ, η) ↦ (ξ, Dφ_{y-x}(η - ξ))`. -/
def labelDeriv (lam : Point d →ₗ[ℂ] ℂ) (x y : Point d) :
    (Point d × Point d) →ₗ[ℂ] (Point d × Point d) :=
  LinearMap.prod (LinearMap.fst ℂ (Point d) (Point d))
    ((dirChartDeriv lam (y - x)).comp
      (LinearMap.snd ℂ (Point d) (Point d) - LinearMap.fst ℂ (Point d) (Point d)))

end
end DistinctDistances.TrackD
