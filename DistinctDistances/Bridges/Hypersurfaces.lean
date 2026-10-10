import DistinctDistances.Foundations.Affine

/-! The shared affine dimension of a prime hypersurface, from its explicit Hilbert function. -/

namespace DistinctDistances.Bridges

noncomputable section

theorem totalDegree_pos_of_not_isUnit {n : ℕ} (f : Poly n) (hf : f ≠ 0)
    (hunit : ¬ IsUnit f) : 0 < f.totalDegree := by
  by_contra h
  have hdeg : f.totalDegree = 0 := Nat.eq_zero_of_not_pos h
  have he : f = MvPolynomial.C (f.coeff 0) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdeg
  have hc : f.coeff 0 ≠ 0 := by
    intro hz
    apply hf
    rw [he, hz, map_zero]
  apply hunit
  rw [he]
  exact (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C

def primeHypersurface {n : ℕ} (f : Poly (n + 1))
    (hp : (Ideal.span {f}).IsPrime) : AffineVariety (n + 1) :=
  ⟨Ideal.span {f}, hp.isRadical⟩

theorem primeHypersurface_irreducible {n : ℕ} (f : Poly (n + 1))
    (hp : (Ideal.span {f}).IsPrime) : (primeHypersurface f hp).IsIrreducible := hp

theorem primeHypersurface_hilbertPolynomial {n : ℕ} (f : Poly (n + 1))
    (hp : (Ideal.span {f}).IsPrime) (hf : f ≠ 0) :
    (primeHypersurface f hp).hilbertPolynomial =
      OAI.QuarticPowerFree.hypersurfaceHilbertPolynomial n f.totalDegree := by
  apply OAI.QuarticPowerFree.polynomial_eq_of_eventually_nat_eval_eq
  filter_upwards [(primeHypersurface f hp).hilbert_eventually,
    Filter.eventually_ge_atTop f.totalDegree] with D hD hdeg
  exact hD.symm.trans (OAI.QuarticPowerFree.hypersurface_hilbert_polynomial f hf D hdeg)

theorem primeHypersurface_dimension {n : ℕ} (f : Poly (n + 1))
    (hp : (Ideal.span {f}).IsPrime) (hf : f ≠ 0) (hdeg : 0 < f.totalDegree) :
    (primeHypersurface f hp).dimension = n := by
  change (primeHypersurface f hp).hilbertPolynomial.natDegree = n
  rw [primeHypersurface_hilbertPolynomial f hp hf]
  apply le_antisymm (OAI.QuarticPowerFree.hypersurfaceHilbertPolynomial_degree n f.totalDegree)
  apply Polynomial.le_natDegree_of_ne_zero
  rw [OAI.QuarticPowerFree.hypersurfaceHilbertPolynomial_coeff]
  exact div_ne_zero (by exact_mod_cast hdeg.ne') (by exact_mod_cast Nat.factorial_ne_zero n)

end
end DistinctDistances.Bridges
