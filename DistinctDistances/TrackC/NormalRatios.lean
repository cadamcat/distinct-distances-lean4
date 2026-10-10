import DistinctDistances.TrackC.FlatDifferential

namespace DistinctDistances.TrackC

/-- A normal direction normalized by one nonzero coordinate. -/
noncomputable def normalRatio (f : Poly 3) (i j : Fin 3) (x : E 3) : ℝ :=
  gradient f x j / gradient f x i

noncomputable def normalRatioDifferential (f : Poly 3) (i j : Fin 3) (x : E 3) :
    E 3 →L[ℝ] ℝ :=
  (gradient f x i)⁻¹ • polynomialDifferential (MvPolynomial.pderiv j f) x +
    (-(gradient f x j) / (gradient f x i)^2) •
      polynomialDifferential (MvPolynomial.pderiv i f) x

/-- The normalized normal coordinates have the quotient-rule differential. -/
theorem normalRatio_hasFDerivAt (f : Poly 3) (x : E 3) (i j : Fin 3)
    (hi : gradient f x i ≠ 0) :
    HasFDerivAt (normalRatio f i j) (normalRatioDifferential f i j x) x := by
  have hnum := polynomial_hasFDerivAt 3 (MvPolynomial.pderiv j f) x
  have hden := polynomial_hasFDerivAt 3 (MvPolynomial.pderiv i f) x
  have hinv := (hasFDerivAt_inv hi).comp x hden
  have h := hnum.mul hinv
  convert! h using 1
  ext v
  simp [normalRatioDifferential, gradient, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, div_eq_mul_inv, Function.comp_def]
  simp only [Fin.sum_univ_succ]
  ring

/-- Flatness kills every tangent derivative of a normalized normal coordinate. -/
theorem normalRatioDifferential_tangent_zero (f : Poly 3) (x : E 3)
    (hflat : flatPoint f x) (i j : Fin 3) (hi : gradient f x i ≠ 0)
    (v : E 3) (hv : polynomialDifferential f x v = 0) :
    normalRatioDifferential f i j x v = 0 := by
  have h := flat_differential_normal f x hflat v hv i j
  simp only [normalRatioDifferential, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  field_simp [hi]
  nlinarith [h]

end DistinctDistances.TrackC
