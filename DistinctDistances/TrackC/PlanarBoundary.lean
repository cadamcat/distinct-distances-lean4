import DistinctDistances.TrackC.PlanarLineFactor
import DistinctDistances.TrackC.PairIncidence

open scoped BigOperators
open Classical

noncomputable section

namespace DistinctDistances.TrackC

private theorem planar_totalDegree_associated (f g : Poly 2) (h : Associated f g) :
    f.totalDegree = g.totalDegree := by
  by_cases hf : f = 0
  · have hg : g = 0 := h.eq_zero_iff.mp hf
    simp [hf,hg]
  · obtain ⟨u,hu⟩ := h
    have hdeg : (u : Poly 2).totalDegree = 0 :=
      (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp u.isUnit).2
    rw [← hu, MvPolynomial.totalDegree_mul_of_isDomain hf u.ne_zero, hdeg, add_zero]

private theorem planar_totalDegree_multiset_prod (s : Multiset (Poly 2)) (hs : ∀ p ∈ s, p ≠ 0) :
    s.prod.totalDegree = (s.map MvPolynomial.totalDegree).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons p s ih =>
    have hp : p ≠ 0 := hs p (by simp)
    have hs' : ∀ q ∈ s, q ≠ 0 := fun q hq => hs q (by simp [hq])
    have hprod : s.prod ≠ 0 := Multiset.prod_ne_zero (fun hz => hs' 0 hz rfl)
    rw [Multiset.prod_cons, MvPolynomial.totalDegree_mul_of_isDomain hp hprod, ih hs']
    simp

private theorem planar_degree_sum_toFinset_le (s : Multiset (Poly 2)) :
    (∑ p ∈ s.toFinset,p.totalDegree) ≤ (s.map MvPolynomial.totalDegree).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons p s ih =>
    simp only [Multiset.toFinset_cons, Multiset.map_cons, Multiset.sum_cons]
    by_cases hp : p ∈ s.toFinset
    · rw [Finset.insert_eq_of_mem hp]
      omega
    · rw [Finset.sum_insert hp]
      omega

private theorem planar_factor_degree_sum_le [NormalizationMonoid (Poly 2)]
    (f : Poly 2) (hf : f ≠ 0) :
    ∑ g ∈ (UniqueFactorizationMonoid.normalizedFactors f).toFinset,g.totalDegree ≤ f.totalDegree := by
  let s := UniqueFactorizationMonoid.normalizedFactors f
  have hs : ∀ p ∈ s,p ≠ 0 := fun p hp => (UniqueFactorizationMonoid.prime_of_normalized_factor p hp).ne_zero
  have heq := planar_totalDegree_multiset_prod s hs
  have hass := planar_totalDegree_associated s.prod f (UniqueFactorizationMonoid.prod_normalizedFactors hf)
  calc
    _ ≤ (s.map MvPolynomial.totalDegree).sum := planar_degree_sum_toFinset_le s
    _ = _ := heq.symm.trans hass

private theorem planar_linear_irreducible (p : Poly 2) (hp : p.totalDegree = 1) : Irreducible p := by
  apply MvPolynomial.irreducible_of_totalDegree_eq_one hp
  intro a ha
  apply isUnit_iff_ne_zero.mpr
  intro hz
  subst a
  have hp0 : p = 0 := by
    apply MvPolynomial.ext
    intro m
    simpa using ha m
  rw [hp0,MvPolynomial.totalDegree_zero] at hp
  omega

private theorem planar_zeroSet_associated (p q : Poly 2) (h : Associated p q) : zeroSet p = zeroSet q := by
  have hsubset : ∀ p q : Poly 2, p ∣ q → zeroSet p ⊆ zeroSet q := by
    intro p q hdiv x hx
    obtain ⟨r,rfl⟩ := hdiv
    change MvPolynomial.eval x p = 0 at hx
    change MvPolynomial.eval x (p*r) = 0
    rw [map_mul,hx,zero_mul]
  exact Set.Subset.antisymm (hsubset p q h.dvd) (hsubset q p h.symm.dvd)

/-- A nonzero planar degree-D polynomial contains at most D distinct affine lines. -/
theorem planar_contained_line_count (f : Poly 2) (hf : f ≠ 0) :
    FiniteCardBound {l : Line 2 | onPolynomial f l} f.totalDegree := by
  letI : StrongNormalizationMonoid (Poly 2) := UniqueFactorizationMonoid.strongNormalizationMonoid
  let F := (UniqueFactorizationMonoid.normalizedFactors f).toFinset.filter (fun p => p.totalDegree = 1)
  let A : Poly 2 → Set (Line 2) := fun p => {l | zeroSet p = (l.1:Set (E 2))}
  have hA : ∀ p, FiniteCardBound (A p) 1 := by
    intro p
    have hss : (A p).Subsingleton := by
      intro l hl l' hl'
      exact Subtype.ext (SetLike.coe_injective (hl.symm.trans hl'))
    exact ⟨hss.finite,by exact_mod_cast (Set.ncard_le_one hss.finite).mpr hss⟩
  have hsub : {l : Line 2 | onPolynomial f l} ⊆ ⋃ p ∈ F,A p := by
    intro l hl
    obtain ⟨p,hp,hpf,hzero⟩ := planar_line_factor f l hl
    obtain ⟨q,hq,hass⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hf
      (planar_linear_irreducible p hp) hpf
    have hqdegree : q.totalDegree = 1 := (planar_totalDegree_associated p q hass).symm.trans hp
    have hqF : q ∈ F := Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hq,hqdegree⟩
    exact Set.mem_iUnion.mpr ⟨q,Set.mem_iUnion.mpr ⟨hqF,(planar_zeroSet_associated p q hass).symm.trans hzero⟩⟩
  have hfinite : (⋃ p ∈ F,A p).Finite := F.finite_toSet.biUnion (fun p hp => (hA p).1)
  have hcard : F.card ≤ f.totalDegree := by
    calc
      F.card = ∑ p ∈ F,p.totalDegree := by
        symm
        simpa using Finset.sum_const_nat (s := F) (m := 1) (f := MvPolynomial.totalDegree)
          (fun p hp => (Finset.mem_filter.mp hp).2)
      _ ≤ ∑ p ∈ (UniqueFactorizationMonoid.normalizedFactors f).toFinset,p.totalDegree :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ ≤ _ := planar_factor_degree_sum_le f hf
  refine ⟨hfinite.subset hsub,?_⟩
  calc
    _ ≤ ((⋃ p ∈ F,A p).ncard:ℝ) := by exact_mod_cast Set.ncard_le_ncard hsub hfinite
    _ ≤ ∑ p ∈ F,((A p).ncard:ℝ) := by exact_mod_cast F.set_ncard_biUnion_le A
    _ ≤ ∑ _p ∈ F,(1:ℝ) := Finset.sum_le_sum (fun p hp => (hA p).2)
    _ = (F.card:ℝ) := by simp
    _ ≤ _ := by exact_mod_cast hcard

/-- Boundary components contribute n+D² incidences, independently of their point multiplicities. -/
theorem planar_contained_line_incidence (f : Poly 2) (hf : f ≠ 0) (X : Finset (E 2))
    (L : Finset (Line 2)) (hL : ∀ l ∈ L,onPolynomial f l) :
    relationMass X L (fun x l => x ∈ l.1) ≤ X.card+(f.totalDegree:ℝ)^2 := by
  have hb := planar_contained_line_count f hf
  have hcard : (L.card:ℝ) ≤ f.totalDegree :=
    (Nat.cast_le.mpr (finset_card_le_ncard L _ hb.1 hL)).trans hb.2
  apply (line_pair_incidence_bound X L).trans
  gcongr

end DistinctDistances.TrackC
