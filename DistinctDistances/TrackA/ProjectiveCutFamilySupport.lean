import DistinctDistances.TrackA.CutSaturationSupport
import Mathlib.RingTheory.GradedAlgebra.Radical

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Minimal primes over an actual homogeneous polynomial ideal are
homogeneous, by minimality applied to their prime homogeneous cores. -/
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

/-- A homogeneous prime with a surviving coordinate is an actual
reduced saturated projective variety in the shared model. -/
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

/-- A prime over a finite union contains at least one member's ideal.
The polynomial product argument also covers the empty union. -/
theorem projective_family_prime_over_locus {n : ℕ} (F : ProjectiveFamily.Family n)
    (Q : Ideal (Poly n)) (hQ : Q.IsPrime)
    (hIQ : (ProjectiveFamily.locus F).ideal ≤ Q) :
    ∃ V ∈ F, V.ideal ≤ Q := by
  by_contra h
  have hchoice : ∀ V : F, ∃ f : Poly n, f ∈ V.val.ideal ∧ f ∉ Q := by
    intro V
    have hnot : ¬ V.val.ideal ≤ Q := fun hle => h ⟨V.val, V.property, hle⟩
    exact SetLike.not_le_iff_exists.mp hnot
  choose f hfI hfQ using hchoice
  let t := ∏ V : F, f V
  have htI : t ∈ (ProjectiveFamily.locus F).ideal := by
    apply (chart_projective_family_mem F t).2
    intro V hV
    obtain ⟨a, ha⟩ := Finset.dvd_prod_of_mem f (Finset.mem_univ (⟨V,hV⟩ : F))
    change (∏ W : F, f W) = f ⟨V,hV⟩ * a at ha
    rw [show t = f ⟨V,hV⟩ * a from ha]
    exact V.ideal.mul_mem_right a (hfI ⟨V,hV⟩)
  have htQ : ∀ s : Finset F, (∏ V ∈ s, f V) ∉ Q := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hQ.one_notMem
    | @insert V s hV ih =>
      rw [Finset.prod_insert hV]
      exact hQ.mul_notMem (hfQ V) ih
  exact htQ Finset.univ (hIQ htI)

/-- Every minimal prime of a proper linear cut of a pure projective
family has the expected positive cone dimension. -/
theorem projective_linear_cut_minimal_prime_dimension {n : ℕ}
    (F : ProjectiveFamily.Family n) (k : ℕ) (hF : ProjectiveFamily.IsPure F (k+1))
    (ℓ : Poly n) (havoid : ∀ V ∈ F, ℓ ∉ V.ideal)
    (Q : Ideal (Poly n))
    (hQ : Q ∈ ((ProjectiveFamily.locus F).ideal ⊔ Ideal.span {ℓ}).minimalPrimes) :
    OAI.QuarticPowerFree.affineDimension Q = k+1 := by
  obtain ⟨V, hV, hVQ⟩ := projective_family_prime_over_locus F Q hQ.isPrime
    (le_sup_left.trans hQ.le)
  have hcutQ : Q ∈ (V.ideal ⊔ Ideal.span {ℓ}).minimalPrimes := by
    refine ⟨⟨hQ.isPrime, sup_le hVQ (le_sup_right.trans hQ.le)⟩, ?_⟩
    intro P hP hPQ
    apply hQ.2 ⟨hP.1, ?_⟩ hPQ
    exact sup_le ((projective_family_member_subvariety F V hV).trans
      (le_sup_left.trans hP.2)) (le_sup_right.trans hP.2)
  letI : V.ideal.IsPrime := (hF V hV).1
  letI : Q.IsPrime := hQ.isPrime
  have hdimV : OAI.QuarticPowerFree.affineDimension V.ideal = (k+1)+1 := by
    have hd := V.dimension_cone (ProjectiveFamily.irreducible_points_nonempty V (hF V hV).1)
    simpa only [AffineVariety.dimension, ProjectiveVariety.affineCone, (hF V hV).2] using hd
  exact OAI.QuarticPowerFree.proper_cut_component_dimension V.ideal Q ℓ (havoid V hV) hcutQ hdimV

/-- A positive-dimensional prime cone has a coordinate surviving in its
coordinate ring, from the original OAI independent-coordinate theorem. -/
theorem prime_coordinate_not_mem_of_positive_dimension {n : ℕ}
    (Q : Ideal (Poly n)) (hQ : Q.IsPrime)
    (hpos : 0 < OAI.QuarticPowerFree.affineDimension Q) :
    ∃ i : Fin n, MvPolynomial.X i ∉ Q := by
  obtain ⟨j, _, hj⟩ := OAI.QuarticPowerFree.affineDimension_independent_coordinates Q hQ.ne_top
  let a : Fin (OAI.QuarticPowerFree.affineDimension Q) := ⟨0,hpos⟩
  exact ⟨j a, fun hm => hj.ne_zero a (Ideal.Quotient.eq_zero_iff_mem.mpr hm)⟩

/-- A proper homogeneous linear cut has an actual finite pure projective
component family, constructed from the scheme sum ideal's minimal primes.
Reducedness of the scheme cut is not needed for this set-theoretic family. -/
theorem projective_linear_cut_family {n : ℕ} (F : ProjectiveFamily.Family n)
    (k : ℕ) (hF : ProjectiveFamily.IsPure F (k+1))
    (ℓ : Poly n) (hℓ : ℓ.IsHomogeneous 1) (havoid : ∀ V ∈ F, ℓ ∉ V.ideal) :
    ∃ W : ProjectiveFamily.Family n,
      ProjectiveFamily.IsPure W k ∧
      (ProjectiveFamily.locus W).Subvariety (ProjectiveFamily.locus F) ∧
      (∀ p, p ∈ (ProjectiveFamily.locus W).points ↔
        p ∈ (ProjectiveFamily.locus F).points ∧ MvPolynomial.eval p.rep ℓ = 0) ∧
      ℓ ∈ (ProjectiveFamily.locus W).ideal := by
  let J := (ProjectiveFamily.locus F).ideal ⊔ Ideal.span {ℓ}
  have hspan : (Ideal.span {ℓ}).IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) ℂ) := by
    apply Ideal.homogeneous_span
    rintro f (rfl : f = ℓ)
    exact ⟨1, hℓ⟩
  have hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) ℂ) :=
    (ProjectiveFamily.locus F).isHomogeneous.sup hspan
  let Qs := {Q : Ideal (Poly n) // Q ∈ J.minimalPrimes}
  letI : Fintype Qs := (Ideal.finite_minimalPrimes_of_isNoetherianRing (Poly n) J).fintype
  have hdim (Q : Qs) : OAI.QuarticPowerFree.affineDimension Q.val = k+1 :=
    projective_linear_cut_minimal_prime_dimension F k hF ℓ havoid Q.val Q.property
  let φ : Qs → ProjectiveVariety n := fun Q =>
    projectiveVarietyOfHomogeneousPrime Q.val Q.property.isPrime
      (homogeneous_minimal_prime J Q.val hJ Q.property)
      (prime_coordinate_not_mem_of_positive_dimension Q.val Q.property.isPrime (by rw [hdim Q]; omega))
  let W := Finset.univ.image φ
  have hφ (Q : Qs) : (φ Q).IsIrreducible ∧ (φ Q).dimension = k := by
    have hirr : (φ Q).IsIrreducible := Q.property.isPrime
    refine ⟨hirr, ?_⟩
    have heq := (φ Q).dimension_cone (ProjectiveFamily.irreducible_points_nonempty (φ Q) hirr)
    change OAI.QuarticPowerFree.affineDimension Q.val = (φ Q).dimension+1 at heq
    rw [hdim Q] at heq
    omega
  have hrep (U : ProjectiveVariety n) (p : ProjectivePoint n) :
      p ∈ U.points ↔ p.rep ∈ U.affineCone.points := by
    simpa only [Projectivization.mk_rep] using
      ProjectiveVariety.mem_points_mk_iff U p.rep p.rep_nonzero
  have hzero (p : ProjectivePoint n) :
      p ∈ (ProjectiveFamily.locus W).points ↔ p.rep ∈ MvPolynomial.zeroLocus ℂ J := by
    rw [ProjectiveFamily.points_locus]
    constructor
    · intro hp
      obtain ⟨U, hU⟩ := Set.mem_iUnion.mp hp
      obtain ⟨hUW, hpU⟩ := Set.mem_iUnion.mp hU
      obtain ⟨Q, _, rfl⟩ := Finset.mem_image.mp hUW
      have hxQ := (hrep (φ Q) p).1 hpU
      exact fun f hf => hxQ f (Q.property.le hf)
    · intro hp
      let P := MvPolynomial.vanishingIdeal ℂ ({p.rep} : Set (Point n))
      have hJP : J ≤ P := by
        intro f hf
        exact (MvPolynomial.mem_vanishingIdeal_singleton_iff p.rep f).2 (hp f hf)
      obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le hJP
      let c : Qs := ⟨Q,hQ⟩
      have hpφ : p ∈ (φ c).points := by
        apply (hrep (φ c) p).2
        intro f hf
        exact (MvPolynomial.mem_vanishingIdeal_singleton_iff p.rep f).1 (hQP hf)
      exact Set.mem_iUnion.mpr ⟨φ c, Set.mem_iUnion.mpr
        ⟨Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩, hpφ⟩⟩
  refine ⟨W, ?_, ?_, ?_, ?_⟩
  · intro U hU
    obtain ⟨Q, _, rfl⟩ := Finset.mem_image.mp hU
    exact hφ Q
  · intro f hf
    apply (chart_projective_family_mem W f).2
    intro U hU
    obtain ⟨Q, _, rfl⟩ := Finset.mem_image.mp hU
    exact Q.property.le (Ideal.mem_sup_left hf)
  · intro p
    rw [hzero p]
    constructor
    · intro hp
      refine ⟨(hrep (ProjectiveFamily.locus F) p).2 (fun f hf => hp f (Ideal.mem_sup_left hf)), ?_⟩
      simpa only [MvPolynomial.aeval_eq_eval] using
        hp ℓ (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton ℓ)))
    · rintro ⟨hpF, hpℓ⟩
      have hker : J ≤ RingHom.ker (MvPolynomial.aeval p.rep).toRingHom := by
        apply sup_le
        · exact fun f hf => (hrep (ProjectiveFamily.locus F) p).1 hpF f hf
        · apply Ideal.span_le.mpr
          rintro f (rfl : f = ℓ)
          exact hpℓ
      exact fun f hf => hker hf
  · apply (chart_projective_family_mem W ℓ).2
    intro U hU
    obtain ⟨Q, _, rfl⟩ := Finset.mem_image.mp hU
    exact Q.property.le (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton ℓ)))

end
end DistinctDistances.TrackA
