import DistinctDistances.TrackC.SurfaceCharts

open Filter
open scoped Topology ContDiff

namespace DistinctDistances.TrackC

@[simp] theorem polynomialSurfaceData_rightFun_self (f : Poly 3) (x : E 3)
    (hx : regularPoint f x) : (polynomialSurfaceData f x hx).rightFun x = 0 := by
  simp [polynomialSurfaceData, HasStrictFDerivAt.implicitFunctionDataOfComplemented]

/-- Local zero-level parametrization by the fixed tangent plane. -/
noncomputable def polynomialSurfaceParam (f : Poly 3) (x : E 3) (hx : regularPoint f x) :
    (polynomialDifferential f x).ker → E 3 :=
  (polynomialSurfaceData f x hx).implicitFunction 0

@[simp] theorem polynomialSurfaceParam_zero (f : Poly 3) (x : E 3) (hx : regularPoint f x) :
    polynomialSurfaceParam f x hx 0 = x := by
  have h := (polynomialSurfaceData f x hx).implicitFunction_apply_image.self_of_nhds
  simpa [polynomialSurfaceParam, hx.1] using h

/-- Its derivative at the base point is the tangent inclusion. -/
theorem polynomialSurfaceParam_hasStrictFDerivAt (f : Poly 3) (x : E 3)
    (hx : regularPoint f x) : HasStrictFDerivAt (polynomialSurfaceParam f x hx)
      (polynomialDifferential f x).ker.subtypeL 0 := by
  let φ := polynomialSurfaceData f x hx
  have hright : φ.rightDeriv.comp (polynomialDifferential f x).ker.subtypeL =
      ContinuousLinearMap.id ℝ (polynomialDifferential f x).ker :=
    polynomialSurfaceData_rightDeriv_subtype f x hx
  have hleft : φ.leftDeriv.comp (polynomialDifferential f x).ker.subtypeL = 0 := by
    ext u
    exact u.property
  have h := φ.hasStrictFDerivAt_implicitFunction _ hright hleft
  simpa [φ, polynomialSurfaceParam, hx.1] using h

/-- Nearby tangent parameters give actual zeros of the original polynomial. -/
theorem polynomialSurfaceParam_eventually_zero (f : Poly 3) (x : E 3)
    (hx : regularPoint f x) : ∀ᶠ u in 𝓝 (0 : (polynomialDifferential f x).ker),
      evalR f (polynomialSurfaceParam f x hx u) = 0 := by
  let φ := polynomialSurfaceData f x hx
  have hbase : φ.prodFun φ.pt = (0, 0) := by
    simp [φ, ImplicitFunctionData.prodFun, hx.1]
  have h := φ.leftFun_implicitFunction
  rw [hbase] at h
  have ht : Tendsto (fun u : (polynomialDifferential f x).ker => ((0 : ℝ), u))
      (𝓝 0) (𝓝 (0, 0)) := by
    simpa only [nhds_prod_eq, id_eq] using
      (tendsto_const_nhds.prodMk (tendsto_id : Tendsto (fun u : (polynomialDifferential f x).ker => u)
        (𝓝 0) (𝓝 0)))
  simpa [φ, polynomialSurfaceParam] using ht.eventually h

/-- The chart projection recovers nearby tangent parameters. -/
theorem polynomialSurfaceParam_eventually_rightFun (f : Poly 3) (x : E 3)
    (hx : regularPoint f x) : ∀ᶠ u in 𝓝 (0 : (polynomialDifferential f x).ker),
      (polynomialSurfaceData f x hx).rightFun (polynomialSurfaceParam f x hx u) = u := by
  let φ := polynomialSurfaceData f x hx
  have hbase : φ.prodFun φ.pt = (0, 0) := by
    simp [φ, ImplicitFunctionData.prodFun, hx.1]
  have h := φ.rightFun_implicitFunction
  rw [hbase] at h
  have ht : Tendsto (fun u : (polynomialDifferential f x).ker => ((0 : ℝ), u))
      (𝓝 0) (𝓝 (0, 0)) := by
    simpa only [nhds_prod_eq, id_eq] using
      (tendsto_const_nhds.prodMk (tendsto_id : Tendsto (fun u : (polynomialDifferential f x).ker => u)
        (𝓝 0) (𝓝 0)))
  simpa [φ, polynomialSurfaceParam] using ht.eventually h

/-- The parametrization inherits polynomial smoothness near the base point. -/
theorem polynomialSurfaceParam_contDiffAt (f : Poly 3) (x : E 3)
    (hx : regularPoint f x) :
    ContDiffAt ℝ ∞ (polynomialSurfaceParam f x hx) 0 := by
  let φ := polynomialSurfaceData f x hx
  have hrightFun : φ.rightFun = (fun y : E 3 => φ.rightDeriv (y-x)) := rfl
  have hright : ContDiff ℝ ∞ φ.rightFun := by
    rw [hrightFun]
    have hshift : ContDiff ℝ ∞ (fun y : E 3 => y-x) :=
      (contDiff_id : ContDiff ℝ ∞ (id : E 3 → E 3)).sub contDiff_const
    exact φ.rightDeriv.contDiff.comp hshift
  have hsmooth : ContDiff ℝ ∞ φ.prodFun := by
    change ContDiff ℝ ∞ (fun y : E 3 => (evalR f y, φ.rightFun y))
    exact (polynomial_contDiff 3 f ∞).prodMk hright
  let L := φ.leftDeriv.equivProdOfSurjectiveOfIsCompl φ.rightDeriv
    φ.range_leftDeriv φ.range_rightDeriv φ.isCompl_ker
  have hderiv : HasFDerivAt φ.prodFun (L : E 3 →L[ℝ] ℝ × (polynomialDifferential f x).ker) x :=
    φ.hasStrictFDerivAt.hasFDerivAt
  have hbase : φ.prodFun x = (0, 0) := by
    simp [φ, ImplicitFunctionData.prodFun, hx.1]
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hinv := hsmooth.contDiffAt.to_localInverse hderiv hn
  rw [hbase] at hinv
  have hpair : ContDiffAt ℝ ∞
      (fun u : (polynomialDifferential f x).ker => ((0 : ℝ), u)) 0 :=
    contDiff_const.contDiffAt.prodMk contDiff_id.contDiffAt
  have hcomp := hinv.comp 0 hpair
  convert! hcomp using 1

end DistinctDistances.TrackC
