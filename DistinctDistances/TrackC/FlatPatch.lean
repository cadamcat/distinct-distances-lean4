import DistinctDistances.TrackC.AffinePatch

open Filter
open scoped Topology ContDiff

namespace DistinctDistances.TrackC

/-- A neighborhood of regular flat zeros contains an open tangent-plane patch.
This supplies the analytic input to the factor argument in CI:188–206. -/
theorem flat_surface_tangent_patch (f : Poly 3) (x : E 3) (hx : regularPoint f x)
    (hflat : ∀ᶠ y in 𝓝 x, regularPoint f y → flatPoint f y) :
    ∃ r : ℝ, 0 < r ∧ ∀ u ∈ Metric.ball (0 : (polynomialDifferential f x).ker) r,
      evalR f (x + (u : E 3)) = 0 := by
  obtain ⟨i, hi⟩ := hx.2
  let ψ := polynomialSurfaceParam f x hx
  have hψcont : ContinuousAt ψ 0 :=
    (polynomialSurfaceParam_hasStrictFDerivAt f x hx).continuousAt
  have hψtendsto : Tendsto ψ (𝓝 0) (𝓝 x) := by
    simpa [ψ] using hψcont.tendsto
  have hC1 : ContDiffAt ℝ 1 ψ 0 :=
    (polynomialSurfaceParam_contDiffAt f x hx).of_le (by simp)
  have hψdiff : ∀ᶠ u in 𝓝 (0 : (polynomialDifferential f x).ker),
      DifferentiableAt ℝ ψ u :=
    (hC1.eventually (by simp)).mono (fun u hu => hu.differentiableAt one_ne_zero)
  have hgcont : ContinuousAt (fun u => gradient f (ψ u) i) 0 := by
    change ContinuousAt ((evalR (MvPolynomial.pderiv i f)) ∘ ψ) 0
    exact (polynomial_contDiff 3 (MvPolynomial.pderiv i f) 0).continuous.continuousAt.comp hψcont
  have hg : ∀ᶠ u in 𝓝 (0 : (polynomialDifferential f x).ker), gradient f (ψ u) i ≠ 0 :=
    hgcont.eventually_ne (by simpa [ψ] using hi)
  have hz := polynomialSurfaceParam_eventually_zero f x hx
  have hproj := polynomialSurfaceParam_eventually_rightFun f x hx
  have hflatmap := hψtendsto.eventually hflat
  have hall : ∀ᶠ u in 𝓝 (0 : (polynomialDifferential f x).ker),
      DifferentiableAt ℝ ψ u ∧ flatPoint f (ψ u) ∧ gradient f (ψ u) i ≠ 0 ∧
      (polynomialSurfaceData f x hx).rightFun (ψ u) = u := by
    filter_upwards [hψdiff, hg, hz, hproj, hflatmap] with u hdu hgu hzu hpu hfu
    refine ⟨hdu, hfu ⟨hzu, i, hgu⟩, hgu, hpu⟩
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hall
  refine ⟨r, hr, ?_⟩
  intro u hu
  have heq := surface_param_eq_add_on_ball f x hx i r hr
    (fun v hv => (hball hv).1)
    (fun v hv => (hball hv).2.1)
    (fun v hv => (hball hv).2.2.1)
    (fun v hv => (hball hv).2.2.2) u hu
  have hzero := (hball hu).2.1.1.1
  change evalR f (polynomialSurfaceParam f x hx u) = 0 at hzero
  rw [heq] at hzero
  exact hzero

end DistinctDistances.TrackC
