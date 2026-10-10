import DistinctDistances.TrackC.SurfaceNormals

open Filter
open scoped Topology BigOperators

namespace DistinctDistances.TrackC

/-- Equal normalized normal directions have the same tangent kernel. -/
theorem normalRatio_equal_tangent (f : Poly 3) (x y : E 3) (i : Fin 3)
    (hxi : gradient f x i ≠ 0) (hyi : gradient f y i ≠ 0)
    (hN : ∀ j : Fin 3, normalRatio f i j y = normalRatio f i j x)
    (v : E 3) (hv : polynomialDifferential f y v = 0) :
    polynomialDifferential f x v = 0 := by
  have hcross (j : Fin 3) : gradient f y j * gradient f x i =
      gradient f x j * gradient f y i :=
    (div_eq_div_iff hyi hxi).mp (hN j)
  have hsum : gradient f y i * polynomialDifferential f x v =
      gradient f x i * polynomialDifferential f y v := by
    simp only [polynomialDifferential_apply]
    simp only [gradient] at hcross ⊢
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have h := congrArg (fun t : ℝ => t * v j) (hcross j)
    simpa [mul_assoc, mul_comm, mul_left_comm] using h.symm
  rw [hv, mul_zero] at hsum
  exact (mul_eq_zero.mp hsum).resolve_left hyi

/-- Derivatives of a local zero-set parametrization lie in the moving tangent kernel. -/
theorem surfaceParam_derivative_tangent (f : Poly 3) (x : E 3) (hx : regularPoint f x)
    (u : (polynomialDifferential f x).ker)
    (hψ : DifferentiableAt ℝ (polynomialSurfaceParam f x hx) u)
    (hzero : ∀ᶠ w in 𝓝 u, evalR f (polynomialSurfaceParam f x hx w) = 0)
    (v : (polynomialDifferential f x).ker) :
    polynomialDifferential f (polynomialSurfaceParam f x hx u)
      (fderiv ℝ (polynomialSurfaceParam f x hx) u v) = 0 := by
  let ψ := polynomialSurfaceParam f x hx
  have hchain := (polynomial_hasFDerivAt 3 f (ψ u)).comp u hψ.hasFDerivAt
  have hconst : HasFDerivAt (𝕜 := ℝ) (fun w => evalR f (ψ w)) 0 u :=
    (hasFDerivAt_const (0 : ℝ) u).congr_of_eventuallyEq hzero
  have hD : (polynomialDifferential f (ψ u)).comp (fderiv ℝ ψ u) = 0 :=
    hchain.unique hconst
  have h := congrArg (fun D : (polynomialDifferential f x).ker →L[ℝ] ℝ => D v) hD
  simpa using h

end DistinctDistances.TrackC
