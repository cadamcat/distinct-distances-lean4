import DistinctDistances.TrackC.Basic

namespace DistinctDistances.TrackC

/-- Restriction of a real three-variable polynomial to an affine vector line. -/
noncomputable def polynomialVectorRestriction (f : Poly 3) (x v : E 3) : Polynomial ℝ :=
  MvPolynomial.eval₂Hom Polynomial.C
    (fun i => Polynomial.C (x i) + Polynomial.C (v i) * Polynomial.X) f

/-- The restriction is a genuine polynomial in the real line parameter. -/
theorem eval_polynomialVectorRestriction (f : Poly 3) (x v : E 3) (t : ℝ) :
    (polynomialVectorRestriction f x v).eval t = evalR f (x + t • v) := by
  let χ : Fin 3 → Polynomial ℝ :=
    fun i => Polynomial.C (x i) + Polynomial.C (v i) * Polynomial.X
  have h : (Polynomial.evalRingHom t).comp (MvPolynomial.eval₂Hom Polynomial.C χ) =
      MvPolynomial.eval (x + t • v) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro i
      simp [χ]
      ring
  exact congrArg (fun H : Poly 3 →+* ℝ => H f) h

end DistinctDistances.TrackC
