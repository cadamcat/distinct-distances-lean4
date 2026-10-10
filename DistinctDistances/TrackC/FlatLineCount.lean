import DistinctDistances.TrackC.LineAlgebra

open scoped BigOperators
open Classical

noncomputable section

namespace DistinctDistances.TrackC

variable [NormalizationMonoid (Poly 3)]

/-- The factor-wise counting assembly in CI:188–210, with its shared Bézout input explicit. -/
theorem flat_line_bound_of_bezout (f : Poly 3) (hf : f ≠ 0) (hsq : Squarefree f)
    (T : Fin 9 → Poly 3) (hdegree : ∀ j, (T j).totalDegree ≤ 3*f.totalDegree)
    (hT : ∀ x, regularPoint f x → (flatPoint f x ↔ ∀ j, evalR (T j) x = 0))
    (hBezout : ∀ a b : Poly 3, a ≠ 0 → b ≠ 0 → IsRelPrime a b →
      FiniteCardBound {l : Line 3 | onPolynomial a l ∧ onPolynomial b l}
        ((a.totalDegree : ℝ)*b.totalDegree)) :
    FiniteCardBound {l : Line 3 | flatLine f l ∧ ¬ inPlaneComponent f l}
      (3*(f.totalDegree:ℝ)^2) := by
  let F := (UniqueFactorizationMonoid.normalizedFactors f).toFinset.filter
    (fun g => ∃ l : Line 3, flatLine f l ∧ ¬ inPlaneComponent f l ∧ onPolynomial g l)
  have hfactor : ∀ g ∈ F, g ∈ UniqueFactorizationMonoid.normalizedFactors f := by
    intro g hg
    exact Multiset.mem_toFinset.mp (Finset.mem_filter.mp hg).1
  have htest : ∀ g ∈ F, ∃ j : Fin 9, ¬ g ∣ T j := by
    intro g hg
    have hgp := UniqueFactorizationMonoid.prime_of_normalized_factor g (hfactor g hg)
    have hgf := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (hfactor g hg)
    obtain ⟨l,hl,hplane,hgl⟩ := (Finset.mem_filter.mp hg).2
    have hdeg0 : g.totalDegree ≠ 0 := by
      intro hz
      have heq := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hz
      have hcoeff : g.coeff 0 ≠ 0 := by
        intro hc
        apply hgp.ne_zero
        rw [heq,hc]
        simp
      apply hgp.not_isUnit
      exact MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mpr ⟨isUnit_iff_ne_zero.mpr hcoeff,hz⟩
    have hdeg1 : g.totalDegree ≠ 1 := by
      intro hg1
      exact hplane ⟨g,hg1,hgf,hgl⟩
    obtain ⟨x,hxl,hx⟩ := flatLine_regular_point f l hl
    obtain ⟨h,hfg⟩ := hgf
    exact nonlinear_factor_flat_test_not_divisible f g h hfg hgp.irreducible (by omega)
      x hx (hgl x hxl) T hT
  let J : Poly 3 → Fin 9 := fun g => if hg : g ∈ F then (htest g hg).choose else 0
  have hJ : ∀ g ∈ F, ¬ g ∣ T (J g) := by
    intro g hg
    simpa [J,hg] using (htest g hg).choose_spec
  let A : Poly 3 → Set (Line 3) := fun g => {l | onPolynomial g l ∧ onPolynomial (T (J g)) l}
  have hcount : ∀ g ∈ F, FiniteCardBound (A g) (3*(f.totalDegree:ℝ)*g.totalDegree) := by
    intro g hg
    have hgp := UniqueFactorizationMonoid.prime_of_normalized_factor g (hfactor g hg)
    have ht : T (J g) ≠ 0 := by intro hz; exact hJ g hg (hz ▸ dvd_zero g)
    have hc := hBezout g (T (J g)) hgp.ne_zero ht (hgp.irreducible.isRelPrime_iff_not_dvd.mpr (hJ g hg))
    refine ⟨hc.1, hc.2.trans ?_⟩
    have hd : ((T (J g)).totalDegree : ℝ) ≤ 3*(f.totalDegree:ℝ) := by exact_mod_cast hdegree (J g)
    nlinarith [mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg g.totalDegree)]
  have hsub : {l : Line 3 | flatLine f l ∧ ¬ inPlaneComponent f l} ⊆ ⋃ g ∈ F, A g := by
    intro l hl
    obtain ⟨g,hg,hgl⟩ := line_supported_by_factor f hf l hl.1.1
    have hgF : g ∈ F := Finset.mem_filter.mpr
      ⟨Multiset.mem_toFinset.mpr hg,l,hl.1,hl.2,hgl⟩
    exact Set.mem_iUnion.mpr ⟨g,Set.mem_iUnion.mpr
      ⟨hgF,hgl,flatLine_on_tests f l hl.1 T hT (J g)⟩⟩
  have hfinite : (⋃ g ∈ F, A g).Finite :=
    F.finite_toSet.biUnion (fun g hg => (hcount g hg).1)
  refine ⟨hfinite.subset hsub, ?_⟩
  have hsumdegree : ∑ g ∈ F, g.totalDegree ≤ f.totalDegree := by
    calc
      _ ≤ ∑ g ∈ (UniqueFactorizationMonoid.normalizedFactors f).toFinset, g.totalDegree :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = _ := squarefree_factor_degree_sum f hf hsq
  have hsumdegreeR : (∑ g ∈ F, (g.totalDegree:ℝ)) ≤ f.totalDegree := by exact_mod_cast hsumdegree
  calc
    _ ≤ ((⋃ g ∈ F, A g).ncard : ℝ) := by exact_mod_cast Set.ncard_le_ncard hsub hfinite
    _ ≤ ∑ g ∈ F, ((A g).ncard : ℝ) := by exact_mod_cast F.set_ncard_biUnion_le A
    _ ≤ ∑ g ∈ F, 3*(f.totalDegree:ℝ)*g.totalDegree :=
      Finset.sum_le_sum (fun g hg => (hcount g hg).2)
    _ = 3*(f.totalDegree:ℝ)*(∑ g ∈ F, (g.totalDegree:ℝ)) := by simp only [Finset.mul_sum]
    _ ≤ 3*(f.totalDegree:ℝ)^2 := by
      calc
        _ ≤ 3*(f.totalDegree:ℝ)*(f.totalDegree:ℝ) :=
          mul_le_mul_of_nonneg_left hsumdegreeR (by positivity)
        _ = _ := by ring

end DistinctDistances.TrackC
