import DistinctDistances.TrackC.ConstantNormal
import DistinctDistances.TrackC.FixedTangents

open Filter
open scoped Topology

namespace DistinctDistances.TrackC

/-- A regular flat patch lies in its tangent affine plane, CI:194–200. -/
theorem surface_param_in_tangent_plane (f : Poly 3) (x : E 3)
    (hx : regularPoint f x) (i : Fin 3) (r : ℝ) (hr : 0 < r)
    (hψ : ∀ u ∈ Metric.ball (0 : (polynomialDifferential f x).ker) r,
      DifferentiableAt ℝ (polynomialSurfaceParam f x hx) u)
    (hflat : ∀ u ∈ Metric.ball (0 : (polynomialDifferential f x).ker) r,
      flatPoint f (polynomialSurfaceParam f x hx u))
    (hi : ∀ u ∈ Metric.ball (0 : (polynomialDifferential f x).ker) r,
      gradient f (polynomialSurfaceParam f x hx u) i ≠ 0) :
    ∀ u ∈ Metric.ball (0 : (polynomialDifferential f x).ker) r,
      polynomialDifferential f x (polynomialSurfaceParam f x hx u - x) = 0 := by
  let s := Metric.ball (0 : (polynomialDifferential f x).ker) r
  let q := fun u => polynomialDifferential f x (polynomialSurfaceParam f x hx u)
  have hxi : gradient f x i ≠ 0 := by
    simpa using hi 0 (Metric.mem_ball_self hr)
  have hN (j : Fin 3) := surface_normalRatio_const_on_ball f x hx i j r hr hψ hflat hi
  have hderiv (u) (hu : u ∈ s) : HasFDerivAt (𝕜 := ℝ) q 0 u := by
    have hzero : ∀ᶠ w in 𝓝 u, evalR f (polynomialSurfaceParam f x hx w) = 0 := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hu] with w hw
      exact (hflat w hw).1.1
    have hcomp := (polynomialDifferential f x).hasFDerivAt.comp u (hψ u hu).hasFDerivAt
    have hD : (polynomialDifferential f x).comp
        (fderiv ℝ (polynomialSurfaceParam f x hx) u) = 0 := by
      apply ContinuousLinearMap.ext
      intro v
      apply normalRatio_equal_tangent f x (polynomialSurfaceParam f x hx u) i hxi (hi u hu)
        (fun j => hN j u hu)
      exact surfaceParam_derivative_tangent f x hx u (hψ u hu) hzero v
    simpa only [hD, Function.comp_def] using hcomp
  have hdiff : DifferentiableOn ℝ q s := fun u hu =>
    (hderiv u hu).differentiableAt.differentiableWithinAt
  have hzero : ∀ u ∈ s, fderivWithin ℝ q s u = 0 := by
    intro u hu
    exact (hderiv u hu).hasFDerivWithinAt.fderivWithin (Metric.isOpen_ball.uniqueDiffWithinAt hu)
  intro u hu
  have hconst := (convex_ball (0 : (polynomialDifferential f x).ker) r).is_const_of_fderivWithin_eq_zero
    hdiff hzero hu (Metric.mem_ball_self hr)
  change polynomialDifferential f x (polynomialSurfaceParam f x hx u) =
    polynomialDifferential f x (polynomialSurfaceParam f x hx 0) at hconst
  rw [polynomialSurfaceParam_zero] at hconst
  rw [map_sub, hconst, sub_self]

/-- The fixed tangent projection makes a flat parametrization an affine inclusion. -/
theorem surface_param_eq_add_on_ball (f : Poly 3) (x : E 3)
    (hx : regularPoint f x) (i : Fin 3) (r : ℝ) (hr : 0 < r)
    (hψ : ∀ u ∈ Metric.ball (0 : (polynomialDifferential f x).ker) r,
      DifferentiableAt ℝ (polynomialSurfaceParam f x hx) u)
    (hflat : ∀ u ∈ Metric.ball (0 : (polynomialDifferential f x).ker) r,
      flatPoint f (polynomialSurfaceParam f x hx u))
    (hi : ∀ u ∈ Metric.ball (0 : (polynomialDifferential f x).ker) r,
      gradient f (polynomialSurfaceParam f x hx u) i ≠ 0)
    (hproj : ∀ u ∈ Metric.ball (0 : (polynomialDifferential f x).ker) r,
      (polynomialSurfaceData f x hx).rightFun (polynomialSurfaceParam f x hx u) = u) :
    ∀ u ∈ Metric.ball (0 : (polynomialDifferential f x).ker) r,
      polynomialSurfaceParam f x hx u = x + (u : E 3) := by
  intro u hu
  have hT := surface_param_in_tangent_plane f x hx i r hr hψ hflat hi u hu
  let w : (polynomialDifferential f x).ker :=
    ⟨polynomialSurfaceParam f x hx u - x, hT⟩
  have hright := hproj u hu
  change (polynomialSurfaceData f x hx).rightDeriv (w : E 3) = u at hright
  have hId := congrArg (fun D : (polynomialDifferential f x).ker →L[ℝ]
      (polynomialDifferential f x).ker => D w)
    (polynomialSurfaceData_rightDeriv_subtype f x hx)
  change (polynomialSurfaceData f x hx).rightDeriv (w : E 3) = w at hId
  have hw : w = u := hId.symm.trans hright
  have hval := congrArg (fun v : (polynomialDifferential f x).ker => (v : E 3)) hw
  change polynomialSurfaceParam f x hx u - x = (u : E 3) at hval
  simpa only [add_comm] using sub_eq_iff_eq_add.mp hval

end DistinctDistances.TrackC
