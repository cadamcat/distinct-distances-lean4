import DistinctDistances.Bridges.Hypersurfaces
import OAI.NumberTheory.PowerFree.SurfaceCounting
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

/-!
Irreducible components of an affine hypersurface.

A nonzero polynomial is a unit times the product of its normalized prime factors.
The distinct factors define irreducible hypersurfaces of dimension one less than
the ambient space, and the sum of their degrees is at most the total degree.
A nonempty affine subspace on which the polynomial vanishes lies in one factor,
because its vanishing ideal is prime.
-/

namespace DistinctDistances.Bridges

noncomputable section
open scoped BigOperators Classical
open UniqueFactorizationMonoid AffineSubspace

variable {n m : ℕ}

/-- Pull a polynomial back along an affine-linear parametrization. -/
def affineLinearPullback (a : Point n) (φ : Point m →ₗ[ℂ] Point n) :
    Poly n →ₐ[ℂ] Poly m :=
  MvPolynomial.aeval (fun i => MvPolynomial.C (a i) +
    ∑ j : Fin m, MvPolynomial.C (φ (Pi.single j 1) i) * MvPolynomial.X j)

theorem eval_affineLinearPullback (a : Point n) (φ : Point m →ₗ[ℂ] Point n)
    (t : Point m) (f : Poly n) :
    MvPolynomial.aeval t (affineLinearPullback a φ f) =
      MvPolynomial.aeval (a + φ t) f := by
  have ht : (∑ j : Fin m, t j • Pi.single j (1 : ℂ)) = t := by
    simpa using (Pi.basisFun ℂ (Fin m)).sum_repr t
  have hφ (i : Fin n) : φ t i = ∑ j : Fin m, φ (Pi.single j 1) i * t j := by
    conv_lhs => rw [← ht, map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [affineLinearPullback, MvPolynomial.comp_aeval_apply]
  apply congrArg (fun g : Point n => MvPolynomial.aeval g f)
  funext i
  simp [hφ, Pi.add_apply]

theorem vanishingIdeal_affineLinearImage_prime (a : Point n)
    (φ : Point m →ₗ[ℂ] Point n) :
    (MvPolynomial.vanishingIdeal ℂ {x | ∃ t : Point m, x = a + φ t}).IsPrime := by
  let ψ := affineLinearPullback a φ
  have hmem (f : Poly n) :
      f ∈ MvPolynomial.vanishingIdeal ℂ {x | ∃ t : Point m, x = a + φ t} ↔ ψ f = 0 := by
    constructor
    · intro hf
      apply MvPolynomial.funext
      intro t
      change MvPolynomial.aeval t (ψ f) = MvPolynomial.aeval t 0
      rw [eval_affineLinearPullback]
      simpa using hf (a + φ t) ⟨t, rfl⟩
    · intro hf x hx
      obtain ⟨t, rfl⟩ := hx
      have hz := congrArg (MvPolynomial.aeval t) hf
      simpa only [ψ, eval_affineLinearPullback, map_zero] using hz
  have hI : MvPolynomial.vanishingIdeal ℂ {x | ∃ t : Point m, x = a + φ t} =
      RingHom.ker ψ.toRingHom := by
    ext f
    exact hmem f
  rw [hI]
  exact RingHom.ker_isPrime _

/-- In zero variables every polynomial is constant, so its total degree vanishes. -/
theorem totalDegree_poly_zero (f : Poly 0) : f.totalDegree = 0 := by
  rw [MvPolynomial.totalDegree]
  apply le_antisymm
  · refine Finset.sup_le ?_
    intro s _
    rw [Finsupp.sum]
    have hsup : s.support = ∅ := by
      ext i
      exact i.elim0
    rw [hsup, Finset.sum_empty]
  · exact Nat.zero_le _

theorem isUnit_poly_zero (f : Poly 0) (hf : f ≠ 0) : IsUnit f := by
  have hdeg : f.totalDegree = 0 := totalDegree_poly_zero f
  rw [MvPolynomial.isUnit_iff_totalDegree_of_isReduced]
  refine ⟨?_, hdeg⟩
  have heq : f = MvPolynomial.C (f.coeff 0) :=
    (MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp hdeg
  have hc : f.coeff 0 ≠ 0 := by
    intro hz
    exact hf (heq.trans (by rw [hz, map_zero]))
  exact isUnit_iff_ne_zero.mpr hc

theorem totalDegree_associated (f g : Poly n) (h : Associated f g) :
    f.totalDegree = g.totalDegree := by
  by_cases hf : f = 0
  · have hg : g = 0 := h.eq_zero_iff.mp hf
    simp [hf, hg]
  · obtain ⟨u, hu⟩ := h
    have hdeg : (u : Poly n).totalDegree = 0 :=
      (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp u.isUnit).2
    rw [← hu, MvPolynomial.totalDegree_mul_of_isDomain hf u.ne_zero, hdeg, add_zero]

theorem totalDegree_multiset_prod (s : Multiset (Poly n)) (hs : ∀ p ∈ s, p ≠ 0) :
    s.prod.totalDegree = (s.map MvPolynomial.totalDegree).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons p s ih =>
    have hp : p ≠ 0 := hs p (by simp)
    have hs' : ∀ q ∈ s, q ≠ 0 := fun q hq => hs q (by simp [hq])
    have hprod : s.prod ≠ 0 := Multiset.prod_ne_zero (fun hz => hs' 0 hz rfl)
    rw [Multiset.prod_cons, MvPolynomial.totalDegree_mul_of_isDomain hp hprod, ih hs']
    simp

theorem degree_sum_toFinset_le [DecidableEq (Poly n)] (s : Multiset (Poly n)) :
    (∑ p ∈ s.toFinset, p.totalDegree) ≤ (s.map MvPolynomial.totalDegree).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons p s ih =>
    simp only [Multiset.toFinset_cons, Multiset.map_cons, Multiset.sum_cons]
    by_cases hp : p ∈ s.toFinset
    · rw [Finset.insert_eq_of_mem hp]
      omega
    · rw [Finset.sum_insert hp]
      omega

theorem factor_degree_sum_le [NormalizationMonoid (Poly n)] [DecidableEq (Poly n)]
    (f : Poly n) (hf : f ≠ 0) :
    ∑ g ∈ (normalizedFactors f).toFinset, g.totalDegree ≤ f.totalDegree := by
  let s := normalizedFactors f
  have hs : ∀ p ∈ s, p ≠ 0 := fun p hp => (prime_of_normalized_factor p hp).ne_zero
  have heq := totalDegree_multiset_prod s hs
  have hass := totalDegree_associated s.prod f (prod_normalizedFactors hf)
  calc
    _ ≤ (s.map MvPolynomial.totalDegree).sum := degree_sum_toFinset_le s
    _ = _ := heq.symm.trans hass

/-- A nonempty affine subspace is a translate of its direction. -/
theorem affineSubspace_param (L : AffineSubspace ℂ (Point n)) {a : Point n} (ha : a ∈ L) :
    ∃ (φ : Point (Module.finrank ℂ L.direction) →ₗ[ℂ] Point n),
      (L : Set (Point n)) =
        {x | ∃ t : Point (Module.finrank ℂ L.direction), x = a + φ t} := by
  have _ : Module.Finite ℂ (Point n) := Module.Finite.of_basis (Pi.basisFun ℂ (Fin n))
  have _ : Module.Finite ℂ L.direction := inferInstance
  let W := L.direction
  let b := Module.finBasis ℂ W
  let φ : Point (Module.finrank ℂ W) →ₗ[ℂ] Point n :=
    W.subtype.comp b.equivFun.symm.toLinearMap
  refine ⟨φ, ?_⟩
  ext x
  constructor
  · intro hx
    have hdir : x - a ∈ W := by
      simpa [W, vsub_eq_sub] using vsub_mem_direction hx ha
    let k : W := ⟨x - a, hdir⟩
    refine ⟨b.equivFun k, ?_⟩
    have hφ : φ (b.equivFun k) = x - a := by
      change (b.equivFun.symm (b.equivFun k) : Point n) = x - a
      rw [LinearEquiv.symm_apply_apply]
    rw [hφ]
    abel
  · rintro ⟨t, rfl⟩
    have ht : φ t ∈ W := by
      simpa [φ] using (b.equivFun.symm t).property
    have hmem : φ t +ᵥ a ∈ L := vadd_mem_of_mem_direction ht ha
    simpa [vadd_eq_add, add_comm] using hmem

theorem hypersurface_components (n : ℕ) :
    ∀ g : Poly n, g ≠ 0 → ∃ F : Finset (AffineVariety n),
      (∀ V ∈ F, V.IsIrreducible ∧ V.dimension + 1 = n ∧
        ∀ x ∈ V.points, MvPolynomial.eval x g = 0) ∧
      (∑ V ∈ F, (V.degree : ℝ)) ≤ g.totalDegree ∧
      ∀ L : AffineSubspace ℂ (Point n), (L : Set (Point n)).Nonempty →
        (∀ x ∈ L, MvPolynomial.eval x g = 0) → ∃ V ∈ F, (L : Set (Point n)) ⊆ V.points := by
  intro g hg
  by_cases hunit : IsUnit g
  · refine ⟨∅, ?_, ?_, ?_⟩
    · intro V hV
      cases hV
    · simp
    · intro L hL hvanish
      obtain ⟨x, hx⟩ := hL
      have h0 : MvPolynomial.eval x g = 0 := hvanish x hx
      have hu : IsUnit (MvPolynomial.eval x g) := by
        simpa [MvPolynomial.aeval_eq_eval] using IsUnit.map (MvPolynomial.aeval x) hunit
      exact (hu.ne_zero h0).elim
  · have hn : n ≠ 0 := by
      rintro rfl
      exact hunit (isUnit_poly_zero g hg)
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    let _ : DecidableEq (Poly (m + 1)) := Classical.decEq _
    let _ : StrongNormalizationMonoid (Poly (m + 1)) :=
      UniqueFactorizationMonoid.strongNormalizationMonoid
    let s := (normalizedFactors g).toFinset
    let componentOf : {f : Poly (m + 1) // f ∈ s} → AffineVariety (m + 1) := fun f =>
      primeHypersurface f.1 (Ideal.isPrime_span_singleton_of_prime
        (prime_of_normalized_factor f.1 (Multiset.mem_toFinset.mp f.2)))
    let _ : DecidableEq (AffineVariety (m + 1)) := Classical.decEq _
    let F := s.attach.image componentOf
    have degree_eq (f : {f : Poly (m + 1) // f ∈ s}) :
        (componentOf f).degree = (f.1.totalDegree : ℚ) := by
      have hp := prime_of_normalized_factor f.1 (Multiset.mem_toFinset.mp f.2)
      change OAI.QuarticPowerFree.affineDegree (Ideal.span {f.1}) = _
      exact OAI.QuarticPowerFree.affineDegree_hypersurface f.1 hp.ne_zero
        (totalDegree_pos_of_not_isUnit f.1 hp.ne_zero hp.not_isUnit)
    refine ⟨F, ?_, ?_, ?_⟩
    · intro V hV
      obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hV
      have hp := prime_of_normalized_factor f.1 (Multiset.mem_toFinset.mp f.2)
      refine ⟨Ideal.isPrime_span_singleton_of_prime hp, ?_, ?_⟩
      · have hdim : (componentOf f).dimension = m :=
          primeHypersurface_dimension f.1 (Ideal.isPrime_span_singleton_of_prime hp)
            hp.ne_zero (totalDegree_pos_of_not_isUnit f.1 hp.ne_zero hp.not_isUnit)
        simp [hdim]
      · intro x hx
        have hgmem : g ∈ Ideal.span {f.1} :=
          (Ideal.mem_span_singleton).2
            (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp f.2))
        simpa [MvPolynomial.aeval_eq_eval] using hx g hgmem
    · have hinj : Set.InjOn componentOf s.attach := by
        intro a _ b _ hab
        apply Subtype.ext
        have hideal : Ideal.span {a.1} = Ideal.span {b.1} := by
          simpa [componentOf, primeHypersurface] using congrArg AffineVariety.ideal hab
        have hba : b.1 ∣ a.1 := (Ideal.mem_span_singleton).1 <| by
          rw [← hideal]
          exact Ideal.mem_span_singleton_self a.1
        exact (normalizedFactors_eq_of_dvd g b.1 (Multiset.mem_toFinset.mp b.2) a.1
          (Multiset.mem_toFinset.mp a.2) hba).symm
      rw [Finset.sum_image hinj]
      have hterm : ∀ f ∈ s.attach, ((componentOf f).degree : ℝ) = (f.1.totalDegree : ℝ) := by
        intro f _
        exact_mod_cast degree_eq f
      rw [Finset.sum_congr rfl hterm]
      rw [Finset.sum_attach s (fun p => (p.totalDegree : ℝ))]
      exact_mod_cast factor_degree_sum_le g hg
    · intro L hL hvanish
      obtain ⟨a, ha⟩ := hL
      obtain ⟨φ, hset⟩ := affineSubspace_param L ha
      have hprime :
          (MvPolynomial.vanishingIdeal ℂ (L : Set (Point (m + 1)))).IsPrime := by
        rw [hset]
        exact vanishingIdeal_affineLinearImage_prime a φ
      have hgI : g ∈ MvPolynomial.vanishingIdeal ℂ (L : Set (Point (m + 1))) := by
        intro x hx
        simpa [MvPolynomial.aeval_eq_eval] using hvanish x hx
      have hprod : (normalizedFactors g).prod ∈
          MvPolynomial.vanishingIdeal ℂ (L : Set (Point (m + 1))) := by
        obtain ⟨u, hu⟩ := prod_normalizedFactors hg
        rw [← Ideal.mul_unit_mem_iff_mem _ u.isUnit, hu]
        exact hgI
      obtain ⟨p, hp, hpI⟩ :=
        (hprime.multiset_prod_mem_iff_exists_mem (normalizedFactors g)).mp hprod
      have hps : p ∈ s := (Multiset.mem_toFinset).2 hp
      refine ⟨componentOf ⟨p, hps⟩, ?_, ?_⟩
      · exact Finset.mem_image_of_mem componentOf (Finset.mem_attach s ⟨p, hps⟩)
      · show (L : Set (Point (m + 1))) ⊆ MvPolynomial.zeroLocus ℂ (Ideal.span {p})
        rw [MvPolynomial.le_zeroLocus_iff_le_vanishingIdeal, Ideal.span_singleton_le_iff_mem]
        exact hpI

end
end DistinctDistances.Bridges
