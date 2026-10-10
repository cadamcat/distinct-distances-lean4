import DistinctDistances.TrackC.SurfaceNormals

open Filter
open scoped Topology

namespace DistinctDistances.TrackC

/-- A flat regular surface patch has constant normalized normal direction,
the mean-value step used in CI:194–198. -/
theorem surface_normalRatio_const_on_ball (f : Poly 3) (x : E 3)
    (hx : regularPoint f x) (i j : Fin 3) (r : ℝ) (hr : 0 < r)
    (hψ : ∀ u ∈ Metric.ball (0 : (polynomialDifferential f x).ker) r,
      DifferentiableAt ℝ (polynomialSurfaceParam f x hx) u)
    (hflat : ∀ u ∈ Metric.ball (0 : (polynomialDifferential f x).ker) r,
      flatPoint f (polynomialSurfaceParam f x hx u))
    (hi : ∀ u ∈ Metric.ball (0 : (polynomialDifferential f x).ker) r,
      gradient f (polynomialSurfaceParam f x hx u) i ≠ 0) :
    ∀ u ∈ Metric.ball (0 : (polynomialDifferential f x).ker) r,
      normalRatio f i j (polynomialSurfaceParam f x hx u) = normalRatio f i j x := by
  let s := Metric.ball (0 : (polynomialDifferential f x).ker) r
  let N := fun u => normalRatio f i j (polynomialSurfaceParam f x hx u)
  have hderiv (u) (hu : u ∈ s) : HasFDerivAt (𝕜 := ℝ) N 0 u := by
    apply surfaceParam_normalRatio_hasFDerivAt_zero f x hx u i j (hψ u hu)
    · filter_upwards [Metric.isOpen_ball.mem_nhds hu] with v hv
      exact (hflat v hv).1.1
    · exact hflat u hu
    · exact hi u hu
  have hdiff : DifferentiableOn ℝ N s := fun u hu =>
    (hderiv u hu).differentiableAt.differentiableWithinAt
  have hzero : ∀ u ∈ s, fderivWithin ℝ N s u = 0 := by
    intro u hu
    exact (hderiv u hu).hasFDerivWithinAt.fderivWithin (Metric.isOpen_ball.uniqueDiffWithinAt hu)
  intro u hu
  have hconst := (convex_ball (0 : (polynomialDifferential f x).ker) r).is_const_of_fderivWithin_eq_zero hdiff hzero hu (Metric.mem_ball_self hr)
  simpa [N] using hconst

end DistinctDistances.TrackC
