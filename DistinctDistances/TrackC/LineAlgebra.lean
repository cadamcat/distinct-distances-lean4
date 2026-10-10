import DistinctDistances.TrackC.LineParameter
import DistinctDistances.TrackC.FlatFactorObstruction

open scoped BigOperators
open Classical

noncomputable section

namespace DistinctDistances.TrackC

variable [NormalizationMonoid (Poly 3)]

/-- Affine substitution along a real vector line. -/
def lineRestrictionMap (x v : E 3) : Poly 3 →+* Polynomial ℝ :=
  MvPolynomial.eval₂Hom Polynomial.C
    (fun i => Polynomial.C (x i) + Polynomial.C (v i) * Polynomial.X)

theorem onPolynomial_iff_restriction_zero (f : Poly 3) (l : Line 3) (x v : E 3)
    (hrange : Set.range (fun t : ℝ => x+t • v) = (l.1 : Set (E 3))) :
    onPolynomial f l ↔ lineRestrictionMap x v f = 0 := by
  constructor
  · intro hf
    apply Polynomial.funext
    intro t
    change (linePolynomial 3 f x v).eval t = (0 : Polynomial ℝ).eval t
    rw [linePolynomial_eval]
    have ht : x+t • v ∈ (l.1 : Set (E 3)) := by
      rw [← hrange]
      exact Set.mem_range_self t
    simpa using hf _ ht
  · intro hf y hy
    obtain ⟨t,rfl⟩ := (hrange.symm ▸ hy : y ∈ Set.range (fun t : ℝ => x+t • v))
    rw [← linePolynomial_eval]
    change Polynomial.eval t (lineRestrictionMap x v f) = 0
    rw [hf]
    simp

/-- One irreducible factor supports each line in a nonzero polynomial zero set. -/
theorem line_supported_by_factor (f : Poly 3) (hf : f ≠ 0) (l : Line 3)
    (hl : onPolynomial f l) :
    ∃ g ∈ UniqueFactorizationMonoid.normalizedFactors f, onPolynomial g l := by
  obtain ⟨x,v,hv,hrange,hinj⟩ := affine_line_parameter 3 l
  let I := RingHom.ker (lineRestrictionMap x v)
  have hI : I.IsPrime := RingHom.ker_isPrime _
  have hfI : f ∈ I := (onPolynomial_iff_restriction_zero f l x v hrange).mp hl
  have hprod : (UniqueFactorizationMonoid.normalizedFactors f).prod ∈ I := by
    obtain ⟨u,hu⟩ := UniqueFactorizationMonoid.prod_normalizedFactors hf
    rwa [← hu, Ideal.mul_unit_mem_iff_mem I u.isUnit] at hfI
  obtain ⟨g,hg,hgI⟩ := (hI.multiset_prod_mem_iff_exists_mem _).mp hprod
  exact ⟨g,hg,(onPolynomial_iff_restriction_zero g l x v hrange).mpr hgI⟩

/-- A noncritical line contains a regular point. -/
theorem flatLine_regular_point (f : Poly 3) (l : Line 3) (hl : flatLine f l) :
    ∃ x ∈ l.1, regularPoint f x := by
  by_contra! h
  apply hl.2.1
  intro x hx
  refine ⟨hl.1 x hx, ?_⟩
  intro i
  by_contra hi
  exact h x hx ⟨hl.1 x hx,i,hi⟩

/-- The tests vanish on an entire flat line, including its critical points. -/
theorem flatLine_on_tests (f : Poly 3) (l : Line 3) (hl : flatLine f l)
    (T : Fin 9 → Poly 3)
    (hT : ∀ x, regularPoint f x → (flatPoint f x ↔ ∀ j, evalR (T j) x = 0)) :
    ∀ j, onPolynomial (T j) l := by
  obtain ⟨z,hzl,hz⟩ := flatLine_regular_point f l hl
  obtain ⟨i,hi⟩ := hz.2
  obtain ⟨x,v,hv,hrange,hinj⟩ := affine_line_parameter 3 l
  have hd : lineRestrictionMap x v (MvPolynomial.pderiv i f) ≠ 0 := by
    intro hd
    have hline := (onPolynomial_iff_restriction_zero _ l x v hrange).mpr hd
    exact hi (hline z hzl)
  intro j
  have hprod : onPolynomial (MvPolynomial.pderiv i f * T j) l := by
    intro y hy
    by_cases hreg : regularPoint f y
    · have htest := (hT y hreg).mp (hl.2.2 y hy hreg) j
      change MvPolynomial.eval y (T j) = 0 at htest
      simp only [evalR, map_mul]
      rw [htest, mul_zero]
    · have hderiv : gradient f y i = 0 := by
        by_contra hi
        exact hreg ⟨hl.1 y hy,i,hi⟩
      change MvPolynomial.eval y (MvPolynomial.pderiv i f) = 0 at hderiv
      simp only [evalR, map_mul]
      rw [hderiv, zero_mul]
  have hp := (onPolynomial_iff_restriction_zero _ l x v hrange).mp hprod
  rw [map_mul] at hp
  exact (onPolynomial_iff_restriction_zero _ l x v hrange).mpr
    ((mul_eq_zero.mp hp).resolve_left hd)

/-- Total degree is unchanged by multiplication by a unit. -/
theorem real_totalDegree_associated (f g : Poly 3) (h : Associated f g) :
    f.totalDegree = g.totalDegree := by
  by_cases hf : f = 0
  · have hg : g = 0 := h.eq_zero_iff.mp hf
    simp [hf,hg]
  · obtain ⟨u,hu⟩ := h
    have hdeg : (u : Poly 3).totalDegree = 0 :=
      (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp u.isUnit).2
    rw [← hu, MvPolynomial.totalDegree_mul_of_isDomain hf u.ne_zero, hdeg, add_zero]

theorem real_totalDegree_multiset_prod (s : Multiset (Poly 3)) (hs : ∀ p ∈ s, p ≠ 0) :
    s.prod.totalDegree = (s.map MvPolynomial.totalDegree).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons p s ih =>
    have hp : p ≠ 0 := hs p (by simp)
    have hs' : ∀ q ∈ s, q ≠ 0 := fun q hq => hs q (by simp [hq])
    have hprod : s.prod ≠ 0 := Multiset.prod_ne_zero (fun hz => hs' 0 hz rfl)
    rw [Multiset.prod_cons, MvPolynomial.totalDegree_mul_of_isDomain hp hprod,
      ih hs']
    simp

/-- The squarefree irreducible factors have total degree exactly the degree of f. -/
theorem squarefree_factor_degree_sum (f : Poly 3) (hf : f ≠ 0) (hsq : Squarefree f) :
    ∑ g ∈ (UniqueFactorizationMonoid.normalizedFactors f).toFinset, g.totalDegree = f.totalDegree := by
  let s := UniqueFactorizationMonoid.normalizedFactors f
  have hn : s.Nodup := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hf).mp hsq
  have hs : ∀ p ∈ s, p ≠ 0 := fun p hp => (UniqueFactorizationMonoid.prime_of_normalized_factor p hp).ne_zero
  have heq := real_totalDegree_multiset_prod s hs
  have hass := real_totalDegree_associated s.prod f (UniqueFactorizationMonoid.prod_normalizedFactors hf)
  change (s.toFinset.val.map MvPolynomial.totalDegree).sum = f.totalDegree
  change (s.dedup.map MvPolynomial.totalDegree).sum = f.totalDegree
  rw [Multiset.dedup_eq_self.mpr hn, ← heq, hass]

end DistinctDistances.TrackC
