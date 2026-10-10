import DistinctDistances.TrackC.SurfacePatch
import DistinctDistances.TrackC.NormalRatios

open Filter
open scoped Topology

namespace DistinctDistances.TrackC

/-- The chain rule turns flatness into zero derivative of the normal ratios
along the local polynomial surface parametrization. -/
theorem surfaceParam_normalRatio_hasFDerivAt_zero (f : Poly 3) (x : E 3)
    (hx : regularPoint f x) (u : (polynomialDifferential f x).ker) (i j : Fin 3)
    (hψ : DifferentiableAt ℝ (polynomialSurfaceParam f x hx) u)
    (hzero : ∀ᶠ v in 𝓝 u, evalR f (polynomialSurfaceParam f x hx v) = 0)
    (hflat : flatPoint f (polynomialSurfaceParam f x hx u))
    (hi : gradient f (polynomialSurfaceParam f x hx u) i ≠ 0) :
    HasFDerivAt (𝕜 := ℝ) (fun v => normalRatio f i j (polynomialSurfaceParam f x hx v)) 0 u := by
  let ψ := polynomialSurfaceParam f x hx
  let z := ψ u
  have hψderiv : HasFDerivAt (𝕜 := ℝ) ψ (fderiv ℝ ψ u) u := hψ.hasFDerivAt
  have hchain := (polynomial_hasFDerivAt 3 f z).comp u hψderiv
  have hconst : HasFDerivAt (𝕜 := ℝ) (fun v => evalR f (ψ v)) 0 u :=
    (hasFDerivAt_const (0 : ℝ) u).congr_of_eventuallyEq hzero
  have hkernel : (polynomialDifferential f z).comp (fderiv ℝ ψ u) = 0 :=
    hchain.unique hconst
  have hnormal := (normalRatio_hasFDerivAt f z i j hi).comp u hψderiv
  have hnormalzero : (normalRatioDifferential f i j z).comp (fderiv ℝ ψ u) = 0 := by
    apply ContinuousLinearMap.ext
    intro v
    apply normalRatioDifferential_tangent_zero f z hflat i j hi
    have h := congrArg (fun D : (polynomialDifferential f x).ker →L[ℝ] ℝ => D v) hkernel
    simpa using h
  simpa only [hnormalzero, Function.comp_def] using hnormal

end DistinctDistances.TrackC
