import DistinctDistances.TrackC.Basic

open scoped BigOperators

namespace DistinctDistances.TrackC

/-- Polynomial restriction to an affine vector line in every partition dimension. -/
noncomputable def linePolynomial (d : ℕ) (f : Poly d) (x v : E d) : Polynomial ℝ :=
  MvPolynomial.eval₂Hom Polynomial.C
    (fun i => Polynomial.C (x i) + Polynomial.C (v i) * Polynomial.X) f

theorem linePolynomial_eval (d : ℕ) (f : Poly d) (x v : E d) (t : ℝ) :
    (linePolynomial d f x v).eval t = evalR f (x + t • v) := by
  let χ : Fin d → Polynomial ℝ := fun i => Polynomial.C (x i) + Polynomial.C (v i) * Polynomial.X
  have h : (Polynomial.evalRingHom t).comp (MvPolynomial.eval₂Hom Polynomial.C χ) =
      MvPolynomial.eval (x + t • v) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro i
      simp [χ]
      ring
  exact congrArg (fun H : Poly d →+* ℝ => H f) h

/-- Affine substitution cannot increase total degree. -/
theorem linePolynomial_natDegree_le (d : ℕ) (f : Poly d) (x v : E d) :
    (linePolynomial d f x v).natDegree ≤ f.totalDegree := by
  classical
  let χ : Fin d → Polynomial ℝ := fun i => Polynomial.C (x i) + Polynomial.C (v i) * Polynomial.X
  have hχ (i : Fin d) : (χ i).natDegree ≤ 1 := by
    exact (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) <|
      (Polynomial.natDegree_mul_le).trans (by simp))
  change (MvPolynomial.eval₂Hom Polynomial.C χ f).natDegree ≤ f.totalDegree
  conv_lhs => rw [MvPolynomial.as_sum f]
  rw [map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial]
  calc
    (Polynomial.C (f.coeff m) * m.prod (fun i n => χ i ^ n)).natDegree ≤
        (Polynomial.C (f.coeff m)).natDegree + (m.prod (fun i n => χ i ^ n)).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ ∑ i ∈ m.support, m i := by
      simp only [Polynomial.natDegree_C, zero_add, Finsupp.prod]
      exact (Polynomial.natDegree_prod_le _ _).trans (Finset.sum_le_sum
        (fun i hi => by simpa using Polynomial.natDegree_pow_le_of_le (m i) (hχ i)))
    _ ≤ f.totalDegree := MvPolynomial.le_totalDegree hm

end DistinctDistances.TrackC
