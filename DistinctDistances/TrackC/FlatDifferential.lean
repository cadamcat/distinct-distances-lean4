import DistinctDistances.TrackC.PolynomialCalculus

open scoped BigOperators

namespace DistinctDistances.TrackC

/-- Hessian row evaluated on a tangent vector. -/
noncomputable def hessianRow (f : Poly 3) (x : E 3) (i : Fin 3) (v : Fin 3 → ℝ) : ℝ :=
  ∑ j : Fin 3, v j * evalR (MvPolynomial.pderiv i (MvPolynomial.pderiv j f)) x

private theorem hessian_sub_left (f : Poly 3) (x : E 3) (u w v : Fin 3 → ℝ) :
    hessian f x (u-w) v = hessian f x u v - hessian f x w v := by
  simp [hessian, sub_mul, Finset.sum_sub_distrib]

private theorem hessian_smul_left (f : Poly 3) (x : E 3) (a : ℝ) (u v : Fin 3 → ℝ) :
    hessian f x (a • u) v = a * hessian f x u v := by
  simp [hessian, Finset.mul_sum, mul_assoc]

private theorem hessian_single_left (f : Poly 3) (x : E 3) (i : Fin 3) (v : Fin 3 → ℝ) :
    hessian f x (Pi.single i 1) v = hessianRow f x i v := by
  simp [hessian, hessianRow, Pi.single_apply, ite_mul]

/-- Flatness makes the Hessian of a tangent vector parallel to the normal;
this is the linear algebra step in CI:188–206's constant-normal argument. -/
theorem flat_hessian_normal (f : Poly 3) (x : E 3) (hflat : flatPoint f x)
    (v : Fin 3 → ℝ) (hv : ∑ k : Fin 3, gradient f x k * v k = 0) (i j : Fin 3) :
    gradient f x i * hessianRow f x j v = gradient f x j * hessianRow f x i v := by
  classical
  let u : Fin 3 → ℝ := gradient f x i • Pi.single j 1 - gradient f x j • Pi.single i 1
  have hu : ∑ k : Fin 3, gradient f x k * u k = 0 := by
    simp [u, Pi.single_apply, mul_sub, sub_mul, mul_ite, ite_mul, Finset.sum_sub_distrib,
      mul_assoc, mul_comm]
  have h := hflat.2 u v hu hv
  rw [show u = gradient f x i • Pi.single j 1 - gradient f x j • Pi.single i 1 from rfl,
    hessian_sub_left, hessian_smul_left, hessian_smul_left,
    hessian_single_left, hessian_single_left] at h
  exact sub_eq_zero.mp h

/-- Rewrite that relation using the analytic coordinate differentials. -/
theorem flat_differential_normal (f : Poly 3) (x : E 3) (hflat : flatPoint f x)
    (v : E 3) (hv : polynomialDifferential f x v = 0) (i j : Fin 3) :
    gradient f x i * polynomialDifferential (MvPolynomial.pderiv j f) x v =
      gradient f x j * polynomialDifferential (MvPolynomial.pderiv i f) x v := by
  have h := flat_hessian_normal f x hflat v
    (by simpa [polynomialDifferential_apply, gradient, mul_comm] using hv) i j
  simpa [polynomialDifferential_apply, hessianRow, polynomial_pderiv_commute, mul_comm] using h

end DistinctDistances.TrackC
