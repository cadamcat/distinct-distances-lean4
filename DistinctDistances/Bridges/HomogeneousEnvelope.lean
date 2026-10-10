import DistinctDistances.Foundations.Projective
import DistinctDistances.Bridges.AmbientHilbert
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.Ideal.Colon

/-!
Irreducible projective components of a homogeneous envelope.

`V` is already a projective variety, so its ideal is radical, homogeneous, and
saturated. The minimal primes over that ideal are the ideals of its irreducible
components. Each one is homogeneous, misses some coordinate, and therefore
defines a projective variety. The cone of that variety has dimension at most the
number of coordinates, so the projective dimension is at most `d`. Their locus
is `V` because a radical ideal is the intersection of its minimal primes.
-/

attribute [local instance] MvPolynomial.gradedAlgebra

namespace DistinctDistances.Bridges
noncomputable section
open scoped Classical

/-- Minimal primes over a homogeneous ideal are homogeneous. -/
theorem homogeneous_minimal_prime {n : ℕ} (I Q : Ideal (Poly n))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) ℂ))
    (hQ : Q ∈ I.minimalPrimes) :
    Q.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) ℂ) := by
  let A := MvPolynomial.homogeneousSubmodule (Fin n) ℂ
  have hIQ : I ≤ Q := hQ.le
  have hcore : I ≤ (Q.homogeneousCore A).toIdeal := by
    rw [← hI.toIdeal_homogeneousCore_eq_self]
    exact Ideal.homogeneousCore_mono A hIQ
  have hback : Q ≤ (Q.homogeneousCore A).toIdeal :=
    hQ.2 ⟨hQ.isPrime.homogeneousCore, hcore⟩ (Ideal.toIdeal_homogeneousCore_le A Q)
  have heq : (Q.homogeneousCore A).toIdeal = Q :=
    le_antisymm (Ideal.toIdeal_homogeneousCore_le A Q) hback
  rw [← heq]
  exact (Q.homogeneousCore A).isHomogeneous

/-- A homogeneous prime that misses a coordinate is a projective variety. -/
def projectiveVarietyOfHomogeneousPrime {n : ℕ} (Q : Ideal (Poly n))
    (hQ : Q.IsPrime)
    (hhom : Q.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) ℂ))
    (hcoord : ∃ i : Fin n, MvPolynomial.X i ∉ Q) : ProjectiveVariety n where
  ideal := Q
  isRadical := hQ.isRadical
  isHomogeneous := hhom
  isSaturated := by
    intro f hf
    obtain ⟨i, hi⟩ := hcoord
    obtain ⟨r, hr⟩ := hf i
    exact (hQ.mem_or_mem hr).resolve_left (fun hpow => hi (hQ.mem_of_pow_mem r hpow))

/-- A minimal prime over a saturated ideal cannot contain every coordinate. -/
theorem exists_coordinate_not_mem_minimal_prime {n : ℕ} (I Q : Ideal (Poly n))
    (hI : IrrelevantSaturated I) (hQ : Q ∈ I.minimalPrimes) :
    ∃ i : Fin n, MvPolynomial.X i ∉ Q := by
  by_contra hcoord
  have hvars : ∀ i : Fin n, MvPolynomial.X i ∈ Q := by
    intro i
    by_contra hi
    exact hcoord ⟨i, hi⟩
  have : Module.Finite (Poly n) (Poly n ⧸ I) :=
    Module.Finite.of_surjective I.mkQ (Submodule.mkQ_surjective I)
  have hmem : Q ∈ associatedPrimes (Poly n) (Poly n ⧸ I) := by
    have hsub :=
      Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
        (Poly n) (Poly n ⧸ I)
    rw [Ideal.annihilator_quotient] at hsub
    exact hsub hQ
  have hassoc : ∃ x : Poly n ⧸ I,
      Q = (⊥ : Submodule (Poly n) (Poly n ⧸ I)).colon {x} :=
    (isAssociatedPrime_iff.mp (AssociatedPrimes.mem_iff.mp hmem)).2
  obtain ⟨x, hx⟩ := hassoc
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective x
  have hmul (i : Fin n) : MvPolynomial.X i * a ∈ I := by
    have hXi : (MvPolynomial.X i : Poly n) • x = 0 := by
      have hcol : (MvPolynomial.X i : Poly n) ∈
          (⊥ : Submodule (Poly n) (Poly n ⧸ I)).colon {x} := by
        rw [← hx]
        exact hvars i
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot] at hcol
      exact hcol
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    calc
      Ideal.Quotient.mk I (MvPolynomial.X i * a)
          = Ideal.Quotient.mk I ((MvPolynomial.X i : Poly n) • a) := by rw [smul_eq_mul]
      _ = (MvPolynomial.X i : Poly n) • Ideal.Quotient.mk I a := by
            rw [← Ideal.Quotient.mk_eq_mk, Submodule.Quotient.mk_smul,
              Ideal.Quotient.mk_eq_mk]
      _ = (MvPolynomial.X i : Poly n) • x := by rw [ha]
      _ = 0 := hXi
  have haI : a ∈ I := hI a (fun i => ⟨1, by rw [pow_one]; exact hmul i⟩)
  have hx0 : x = 0 := by
    rw [← ha, Ideal.Quotient.eq_zero_iff_mem]
    exact haI
  have hcolon : (⊥ : Submodule (Poly n) (Poly n ⧸ I)).colon
      {(0 : Poly n ⧸ I)} = ⊤ := by
    ext r
    simp [Submodule.mem_colon_singleton]
  have hQtop : Q = ⊤ := by
    rw [hx, hx0, hcolon]
  exact hQ.isPrime.ne_top hQtop

set_option linter.unusedVariables false in
/-- The irreducible components of a homogeneous projective envelope cover it
and have dimension at most the number of coordinates. -/
theorem homogeneous_envelope_carriers (d : ℕ) (hd : 3 ≤ d) (D : ℕ) (E : Set (Poly d))
    (hE : ∀ f ∈ E, f.IsHomogeneous D) (V : ProjectiveVariety d)
    (hpoints : V.points = {z | ∀ f ∈ E, MvPolynomial.eval z.rep f = 0}) :
    ∃ F : ProjectiveFamily.Family d,
      (∀ Y ∈ F, Y.IsIrreducible ∧ Y.IsComponentOf V ∧ Y.dimension ≤ d) ∧
      ProjectiveFamily.locus F = V := by
  let Qs := {Q : Ideal (Poly d) // Q ∈ V.ideal.minimalPrimes}
  let : Fintype Qs :=
    (Ideal.finite_minimalPrimes_of_isNoetherianRing (Poly d) V.ideal).fintype
  let φ : Qs → ProjectiveVariety d := fun Q =>
    projectiveVarietyOfHomogeneousPrime Q.1 Q.2.isPrime
      (homogeneous_minimal_prime V.ideal Q.1 V.isHomogeneous Q.2)
      (exists_coordinate_not_mem_minimal_prime V.ideal Q.1 V.isSaturated Q.2)
  let F : ProjectiveFamily.Family d := Finset.univ.image φ
  refine ⟨F, ?_, ?_⟩
  · intro Y hY
    obtain ⟨Q, _, rfl⟩ := Finset.mem_image.mp hY
    refine ⟨Q.2.isPrime, Q.2, ?_⟩
    have hne := ProjectiveFamily.irreducible_points_nonempty (φ Q) Q.2.isPrime
    have hcone := (φ Q).dimension_cone hne
    have hle := affine_dimension_le (φ Q).affineCone
    rw [hcone] at hle
    exact (Nat.le_succ _).trans hle
  · apply ProjectiveVariety.ext
    have hloc : (ProjectiveFamily.locus F).ideal =
        ProjectiveVariety.vanishingIdeal (⋃ Y ∈ F, Y.points) := rfl
    rw [hloc]
    have hrad : sInf V.ideal.minimalPrimes = V.ideal := by
      rw [Ideal.sInf_minimalPrimes, V.isRadical.radical]
    ext f
    constructor
    · intro hf
      rw [← hrad, Ideal.mem_sInf]
      intro Q hQ
      have hY : φ ⟨Q, hQ⟩ ∈ F :=
        Finset.mem_image.mpr ⟨⟨Q, hQ⟩, Finset.mem_univ _, rfl⟩
      have hfY : f ∈ ProjectiveVariety.vanishingIdeal (φ ⟨Q, hQ⟩).points := by
        unfold ProjectiveVariety.vanishingIdeal
        rw [MvPolynomial.mem_vanishingIdeal_iff]
        intro x hx
        obtain ⟨hv, hxV⟩ := hx
        have hxU : x ∈ ProjectiveVariety.nonzeroRepresentatives (⋃ Y ∈ F, Y.points) :=
          ⟨hv, by
            simp only [Set.mem_iUnion]
            exact ⟨φ ⟨Q, hQ⟩, hY, hxV⟩⟩
        exact (MvPolynomial.mem_vanishingIdeal_iff.mp hf) x hxU
      rw [ProjectiveVariety.vanishingIdeal_points] at hfY
      exact hfY
    · intro hf
      unfold ProjectiveVariety.vanishingIdeal
      rw [MvPolynomial.mem_vanishingIdeal_iff]
      intro x hx
      obtain ⟨hx0, hxU⟩ := hx
      simp only [Set.mem_iUnion] at hxU
      obtain ⟨Y, hY, hxY⟩ := hxU
      obtain ⟨Q, _, rfl⟩ := Finset.mem_image.mp hY
      have hfY : f ∈ ProjectiveVariety.vanishingIdeal (φ Q).points := by
        rw [ProjectiveVariety.vanishingIdeal_points]
        exact Q.2.le hf
      exact (MvPolynomial.mem_vanishingIdeal_iff.mp hfY) x ⟨hx0, hxY⟩

end
end DistinctDistances.Bridges
