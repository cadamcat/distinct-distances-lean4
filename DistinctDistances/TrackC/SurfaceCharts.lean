import DistinctDistances.TrackC.PolynomialCalculus

open scoped Topology

namespace DistinctDistances.TrackC

/-- A surjective scalar functional has a continuous projection to its kernel. -/
private theorem scalar_kernel_complemented (D : E 3 →L[ℝ] ℝ)
    (hD : Function.Surjective D) : D.ker.ClosedComplemented := by
  obtain ⟨w, hw⟩ := hD 1
  let P : E 3 →L[ℝ] E 3 := ContinuousLinearMap.id ℝ (E 3) - D.smulRight w
  have hP (v : E 3) : P v ∈ D.ker := by
    change D (P v) = 0
    simp [P, hw]
  refine ⟨P.codRestrict D.ker hP, ?_⟩
  intro v
  apply Subtype.ext
  change P v = v
  have hv : D v = 0 := v.property
  simp [P, hv]

/-- Concrete implicit-function data for the regular polynomial surface,
consumed by the constant-normal argument at CI:188–206. -/
noncomputable def polynomialSurfaceData (f : Poly 3) (x : E 3)
    (hx : regularPoint f x) :
    ImplicitFunctionData ℝ (E 3) ℝ (polynomialDifferential f x).ker :=
  HasStrictFDerivAt.implicitFunctionDataOfComplemented (evalR f) (polynomialDifferential f x)
    (polynomial_hasStrictFDerivAt 3 f x)
    (LinearMap.range_eq_top.mpr (regular_polynomial_differential_surjective f x hx))
    (scalar_kernel_complemented _ (regular_polynomial_differential_surjective f x hx))

@[simp] theorem polynomialSurfaceData_pt (f : Poly 3) (x : E 3) (hx : regularPoint f x) :
    (polynomialSurfaceData f x hx).pt = x := rfl

@[simp] theorem polynomialSurfaceData_leftFun (f : Poly 3) (x : E 3) (hx : regularPoint f x) :
    (polynomialSurfaceData f x hx).leftFun = evalR f := rfl

/-- The chart's fixed projection is the identity on the tangent kernel. -/
theorem polynomialSurfaceData_rightDeriv_subtype (f : Poly 3) (x : E 3)
    (hx : regularPoint f x) :
    (polynomialSurfaceData f x hx).rightDeriv.comp (polynomialDifferential f x).ker.subtypeL =
      ContinuousLinearMap.id ℝ (polynomialDifferential f x).ker := by
  apply ContinuousLinearMap.ext
  intro u
  change (Classical.choose (scalar_kernel_complemented (polynomialDifferential f x)
    (regular_polynomial_differential_surjective f x hx))) u = u
  exact Classical.choose_spec (scalar_kernel_complemented (polynomialDifferential f x)
    (regular_polynomial_differential_surjective f x hx)) u

/-- The regular zero belongs to the implicit chart's source. -/
theorem polynomial_surface_chart_source (f : Poly 3) (x : E 3) (hx : regularPoint f x) :
    x ∈ (polynomialSurfaceData f x hx).toOpenPartialHomeomorph.source :=
  (polynomialSurfaceData f x hx).pt_mem_toOpenPartialHomeomorph_source

end DistinctDistances.TrackC
