import DistinctDistances.TrackA.Definitions
import OAI.NumberTheory.PowerFree.Jacobians

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical
open UniqueFactorizationMonoid

/-- The finite-dimensional space of first polars of the equation. -/
def firstPolar {n : ℕ} (f : Poly n) : (Fin n → ℂ) →ₗ[ℂ] Poly n where
  toFun w := ∑ i, w i • MvPolynomial.pderiv i f
  map_add' w v := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c w := by simp [Finset.smul_sum, smul_smul]

theorem prime_factor_detected_by_partial {n : ℕ} (f q : Poly n)
    (hsquare : Squarefree f) (hq : Prime q) (hqf : q ∣ f) :
    ∃ i : Fin n, ¬ q ∣ MvPolynomial.pderiv i f := by
  have hvars : q.vars.Nonempty := by
    by_contra hn
    have hconstant := MvPolynomial.vars_eq_empty_iff_eq_C.mp
      (Finset.not_nonempty_iff_eq_empty.mp hn)
    have hc : q.coeff 0 ≠ 0 := by
      intro hz
      apply hq.ne_zero
      rw [hconstant, hz, map_zero]
    exact hq.not_unit (hconstant.symm ▸
      ((isUnit_iff_ne_zero.mpr hc).map (MvPolynomial.C : ℂ →+* Poly n)))
  obtain ⟨i, hi⟩ := hvars
  have hpartial := OAI.QuarticPowerFree.pderiv_ne_zero_of_mem_vars i q hi
  have hnotpartial : ¬ q ∣ MvPolynomial.pderiv i q := by
    intro hdvd
    exact (not_le_of_gt (OAI.QuarticPowerFree.pderiv_totalDegree_lt i q hpartial))
      (MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdvd hpartial)
  obtain ⟨a, rfl⟩ := hqf
  have hnotqa : ¬ q ∣ a := by
    rintro ⟨b, rfl⟩
    exact hq.not_unit (hsquare q ⟨b, by ring⟩)
  refine ⟨i, ?_⟩
  intro hdvd
  have hterm := dvd_sub hdvd (dvd_mul_right q (MvPolynomial.pderiv i a))
  have heq : MvPolynomial.pderiv i (q*a) - q*MvPolynomial.pderiv i a =
      a*MvPolynomial.pderiv i q := by
    simp only [Derivation.leibniz, smul_eq_mul]
    ring
  rw [heq] at hterm
  exact (hq.dvd_mul.mp hterm).elim hnotqa hnotpartial

theorem firstPolar_degree {n : ℕ} (f : Poly n) (w : Fin n → ℂ) :
    (firstPolar f w).totalDegree ≤ f.totalDegree - 1 := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  apply (MvPolynomial.totalDegree_smul_le (w i) _).trans
  by_cases hzero : MvPolynomial.pderiv i f = 0
  · simp [hzero]
  · have hlt := OAI.QuarticPowerFree.pderiv_totalDegree_lt i f hzero
    omega

/-- Finite linear avoidance chooses a first polar having no nonunit common
divisor with a nonzero squarefree equation. -/
theorem exists_coprime_firstPolar {n : ℕ} (f : Poly n) (hf : f ≠ 0)
    (hsquare : Squarefree f) :
    ∃ w : Fin n → ℂ, ∀ d : Poly n, d ∣ f → d ∣ firstPolar f w → IsUnit d := by
  let F := (factors f).toFinset
  let bad (q : F) : Submodule ℂ (Fin n → ℂ) :=
    ((Ideal.span ({q.val} : Set (Poly n))).restrictScalars ℂ).comap (firstPolar f)
  have hbad (q : F) : bad q ≠ ⊤ := by
    have hqmem : q.val ∈ factors f := Multiset.mem_toFinset.mp q.property
    have hqprime : Prime q.val := prime_of_factor q.val hqmem
    obtain ⟨i, hi⟩ := prime_factor_detected_by_partial f q.val hsquare hqprime
      (dvd_of_mem_factors hqmem)
    intro htop
    have hmem : (Pi.single i 1 : Fin n → ℂ) ∈ bad q := by rw [htop]; trivial
    have hdiv : q.val ∣ firstPolar f (Pi.single i 1) := Ideal.mem_span_singleton.mp hmem
    apply hi
    simpa [firstPolar, Pi.single_apply] using hdiv
  obtain ⟨w, hw⟩ := Submodule.exists_forall_notMem_of_forall_ne_top bad hbad
  refine ⟨w, ?_⟩
  intro d hdf hdg
  by_contra hnotunit
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hf hdf
  obtain ⟨q, hqirreducible, hqd⟩ := WfDvdMonoid.exists_irreducible_factor hnotunit hd0
  obtain ⟨a, ha, hqa⟩ := exists_mem_factors_of_dvd hf hqirreducible (hqd.trans hdf)
  have hag : a ∣ firstPolar f w := hqa.symm.dvd.trans (hqd.trans hdg)
  exact hw ⟨a, Multiset.mem_toFinset.mpr ha⟩ (Ideal.mem_span_singleton.mpr hag)

end
end DistinctDistances.TrackA
