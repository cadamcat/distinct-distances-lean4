import DistinctDistances.Foundations.Projective

/-! Original graded evaluation API lowered for chart-local comparisons.
Names, binders and proof bodies are relocated verbatim. -/

namespace DistinctDistances
open scoped BigOperators
noncomputable section
namespace GenericFiber

section Graded

variable {σ R : Type*} [CommRing R] [Algebra ℂ R]

theorem aeval_monomial_graded (w : σ → ℕ) (a : σ → R) (d : σ →₀ ℕ) (c : ℂ) :
    MvPolynomial.aeval (fun s => (Polynomial.X ^ w s * Polynomial.C (a s) : Polynomial R))
        (MvPolynomial.monomial d c) =
      Polynomial.C (MvPolynomial.aeval a (MvPolynomial.monomial d c)) *
        Polynomial.X ^ (Finsupp.weight w d) := by
  classical
  rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial, Finsupp.weight_apply,
    Polynomial.algebraMap_apply]
  simp only [Finsupp.prod, Finsupp.sum, mul_pow, Finset.prod_mul_distrib, ← pow_mul,
    Finset.prod_pow_eq_pow_sum, smul_eq_mul, map_mul, map_prod, map_pow]
  have hexp : (∑ s ∈ d.support, w s * d s) = ∑ s ∈ d.support, d s * w s :=
    Finset.sum_congr rfl (fun s _ => Nat.mul_comm _ _)
  rw [hexp]
  ring

theorem coeff_aeval_graded (w : σ → ℕ) (a : σ → R) (Φ : MvPolynomial σ ℂ) (D : ℕ) :
    (MvPolynomial.aeval (fun s => (Polynomial.X ^ w s * Polynomial.C (a s) : Polynomial R))
        Φ).coeff D =
      MvPolynomial.aeval a (MvPolynomial.weightedHomogeneousComponent w D Φ) := by
  classical
  conv_lhs => rw [Φ.as_sum]
  rw [MvPolynomial.weightedHomogeneousComponent_apply, map_sum, map_sum,
    Polynomial.finset_sum_coeff, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [aeval_monomial_graded, Polynomial.coeff_C_mul_X_pow]
  by_cases h : Finsupp.weight w d = D
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (fun h' => h h'.symm), if_neg h]

theorem aeval_graded_of_isWeightedHomogeneous {w : σ → ℕ} {Φ : MvPolynomial σ ℂ} {D : ℕ}
    (hΦ : Φ.IsWeightedHomogeneous w D) (a : σ → R) :
    MvPolynomial.aeval (fun s => (Polynomial.X ^ w s * Polynomial.C (a s) : Polynomial R)) Φ =
      Polynomial.C (MvPolynomial.aeval a Φ) * Polynomial.X ^ D := by
  ext k
  rw [coeff_aeval_graded, Polynomial.coeff_C_mul_X_pow]
  by_cases hk : k = D
  · subst hk
    rw [if_pos rfl, hΦ.weightedHomogeneousComponent_same]
  · rw [if_neg hk, hΦ.weightedHomogeneousComponent_ne k hk, map_zero]

theorem eval_aeval_polynomial (v : σ → Polynomial R) (c : R) (Φ : MvPolynomial σ ℂ) :
    (MvPolynomial.aeval v Φ).eval c = MvPolynomial.aeval (fun s => (v s).eval c) Φ := by
  induction Φ using MvPolynomial.induction_on with
  | C r =>
      simp only [MvPolynomial.aeval_C, Polynomial.algebraMap_apply, Polynomial.eval_C]
  | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]
  | mul_X p s hp => simp only [map_mul, Polynomial.eval_mul, hp, MvPolynomial.aeval_X]

/-- Weighted homogeneous polynomials scale with the weights. -/
theorem aeval_scale_of_isWeightedHomogeneous {w : σ → ℕ} {Φ : MvPolynomial σ ℂ} {D : ℕ}
    (hΦ : Φ.IsWeightedHomogeneous w D) (b : σ → R) (c : R) :
    MvPolynomial.aeval (fun s => c ^ w s * b s) Φ = c ^ D * MvPolynomial.aeval b Φ := by
  have h := congrArg (Polynomial.eval c) (aeval_graded_of_isWeightedHomogeneous (R := R) hΦ b)
  rw [eval_aeval_polynomial] at h
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X] at h
  rw [h, mul_comm]

end Graded

end GenericFiber
end
end DistinctDistances
