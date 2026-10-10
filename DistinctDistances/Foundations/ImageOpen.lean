import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
Chevalley-type image openness at the level of complex points.

`dominant_open_image` and `maximal_avoiding` are ports of
`OAI.ExactFourier.PositiveGeneration.dominant_open_image` / `maximal_avoiding`
(OAI/Computability/FourierCircuit/PositiveReach.lean), whose module is not prebuilt
in the shared OAI checkout. `polynomial_point_image_contains_open` is the general
point-level statement: for a polynomial map between affine spaces and an irreducible
source subvariety `V(P)`, the image of a nonempty principal open `V(P) ∩ {p ≠ 0}`
contains a nonempty principal open `V(Q) ∩ {h ≠ 0}` of the closure `V(Q)` of the image,
where `Q = φ⁻¹(P)`.
-/

namespace DistinctDistances

namespace ImageOpen

open Topology

section Spectrum

variable {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]

/-- The generic point of the spectrum of a domain. -/
def genericPoint (R : Type*) [CommRing R] [IsDomain R] : PrimeSpectrum R := ⟨⊥, inferInstance⟩

theorem generic_mem_open {U : Set (PrimeSpectrum R)} (hU : IsOpen U) (hne : U.Nonempty) :
    genericPoint R ∈ U := by
  obtain ⟨x, hx⟩ := hne
  rw [PrimeSpectrum.eq_biUnion_of_isOpen hU] at hx
  obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp hx
  apply hp
  change p ∉ (⊥ : Ideal R)
  intro hz
  have hpz : p = 0 := hz
  exact hxp (hpz ▸ x.asIdeal.zero_mem)

theorem constructible_generic_nhds {T : Set (PrimeSpectrum R)} (hT : IsConstructible T) :
    ∃ U : Set (PrimeSpectrum R), IsOpen U ∧ genericPoint R ∈ U ∧
      ∀ x ∈ U, (x ∈ T ↔ genericPoint R ∈ T) := by
  induction hT using IsConstructible.empty_union_induction with
  | open_retrocompact V hV hc =>
    by_cases hg : genericPoint R ∈ V
    · exact ⟨V, hV, hg, fun x hx => ⟨fun _ => hg, fun _ => hx⟩⟩
    · have hv : V = ∅ := Set.eq_empty_iff_forall_notMem.mpr
        (fun x hx => hg (generic_mem_open hV ⟨x, hx⟩))
      subst V
      exact ⟨Set.univ, isOpen_univ, Set.mem_univ _, by simp⟩
  | union V hV W hW ihV ihW =>
    obtain ⟨U, hU, hg, hue⟩ := ihV
    obtain ⟨Z, hZ, hgz, hze⟩ := ihW
    exact ⟨U ∩ Z, hU.inter hZ, ⟨hg, hgz⟩, fun x hx => or_congr (hue x hx.1) (hze x hx.2)⟩
  | compl V hV ih =>
    obtain ⟨U, hU, hg, he⟩ := ih
    exact ⟨U, hU, hg, fun x hx => not_congr (he x hx)⟩

theorem constructible_contains_basic {T : Set (PrimeSpectrum R)} (hT : IsConstructible T)
    (hg : genericPoint R ∈ T) : ∃ g : R, g ≠ 0 ∧ (PrimeSpectrum.basicOpen g : Set _) ⊆ T := by
  obtain ⟨U, hU, hu, he⟩ := constructible_generic_nhds hT
  rw [PrimeSpectrum.eq_biUnion_of_isOpen hU] at hu
  obtain ⟨g, hgU, hgg⟩ := Set.mem_iUnion₂.mp hu
  refine ⟨g, ?_, fun x hx => (he x (hgU hx)).mpr hg⟩
  simpa [genericPoint] using hgg

/-- A dominant finite-presentation map of domains: the image of a nonempty basic open
contains a nonempty basic open. -/
theorem dominant_open_image (f : R →+* S) (hf : f.FinitePresentation)
    (hinj : Function.Injective f) (p : S) (hp : p ≠ 0) :
    ∃ g : R, g ≠ 0 ∧ (PrimeSpectrum.basicOpen g : Set _) ⊆
      PrimeSpectrum.comap f '' (PrimeSpectrum.basicOpen p : Set _) := by
  apply constructible_contains_basic
    (PrimeSpectrum.isConstructible_comap_image hf PrimeSpectrum.isConstructible_basicOpen)
  refine ⟨genericPoint S, ?_, ?_⟩
  · simpa [genericPoint] using hp
  · apply PrimeSpectrum.ext
    change Ideal.comap f ⊥ = ⊥
    ext x
    change f x = 0 ↔ x = 0
    exact map_eq_zero_iff f hinj

end Spectrum

theorem maximal_avoiding {R : Type*} [CommRing R] [IsJacobsonRing R]
    (I : Ideal R) (hI : I.IsPrime) (p : R) (hp : p ∉ I) :
    ∃ J : Ideal R, J.IsMaximal ∧ I ≤ J ∧ p ∉ J := by
  by_contra h
  push_neg at h
  apply hp
  rw [← IsJacobsonRing.out (inferInstance : IsJacobsonRing R) hI.isRadical]
  rw [Ideal.jacobson, Ideal.mem_sInf]
  intro J hJ
  exact h J hJ.2 hJ.1

open MvPolynomial

/-- **Point-level Chevalley theorem.** Let `φ` be a polynomial map, `P` a prime of the
source polynomial ring (an irreducible variety `V(P)`), `p ∉ P`, and `Q = φ⁻¹ P` (the
ideal of the closure of the image). Then there is `h ∉ Q` such that every point of
`V(Q)` with `h ≠ 0` is the image of a point of `V(P)` with `p ≠ 0`. -/
theorem polynomial_point_image_contains_open {ι κ : Type} [Fintype ι] [Fintype κ]
    (φ : MvPolynomial ι ℂ →ₐ[ℂ] MvPolynomial κ ℂ) (P : Ideal (MvPolynomial κ ℂ)) [P.IsPrime]
    (p : MvPolynomial κ ℂ) (hp : p ∉ P) :
    ∃ h : MvPolynomial ι ℂ, h ∉ P.comap φ ∧
      ∀ y : ι → ℂ, (∀ f ∈ P.comap φ, aeval y f = 0) → aeval y h ≠ 0 →
        ∃ x : κ → ℂ, (∀ f ∈ P, aeval x f = 0) ∧ aeval x p ≠ 0 ∧
          ∀ i, aeval x (φ (X i)) = y i := by
  classical
  let Q : Ideal (MvPolynomial ι ℂ) := P.comap φ
  haveI : Q.IsPrime := Ideal.comap_isPrime φ P
  let ψ : (MvPolynomial ι ℂ ⧸ Q) →ₐ[ℂ] (MvPolynomial κ ℂ ⧸ P) := Ideal.quotientMapₐ P φ le_rfl
  have hinj : Function.Injective ψ := Ideal.quotientMap_injective
  have hft : ψ.toRingHom.FiniteType := by
    apply RingHom.FiniteType.of_comp_finiteType (f := algebraMap ℂ (MvPolynomial ι ℂ ⧸ Q))
    have he : ψ.toRingHom.comp (algebraMap ℂ (MvPolynomial ι ℂ ⧸ Q)) =
        algebraMap ℂ (MvPolynomial κ ℂ ⧸ P) := by
      ext1 c
      exact ψ.commutes c
    rw [he]
    haveI : Algebra.FiniteType ℂ (MvPolynomial κ ℂ ⧸ P) :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ P)
        (Ideal.Quotient.mkₐ_surjective ℂ P)
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  have hfp : ψ.toRingHom.FinitePresentation := RingHom.FinitePresentation.of_finiteType.mp hft
  have hp0 : Ideal.Quotient.mk P p ≠ 0 := fun h0 => hp (Ideal.Quotient.eq_zero_iff_mem.mp h0)
  obtain ⟨r, hr0, hr⟩ := dominant_open_image ψ.toRingHom hfp hinj _ hp0
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective r
  refine ⟨h, fun hh => hr0 (Ideal.Quotient.eq_zero_iff_mem.mpr hh), ?_⟩
  intro y hy hyh
  let M : Ideal (MvPolynomial ι ℂ) := vanishingIdeal ℂ {y}
  have hQM : Q ≤ M := fun f hf => (mem_vanishingIdeal_singleton_iff y f).mpr (hy f hf)
  have hsurj : Function.Surjective (Ideal.Quotient.mk Q) := Ideal.Quotient.mk_surjective
  have hkerM : RingHom.ker (Ideal.Quotient.mk Q) ≤ M := by
    rw [Ideal.mk_ker]
    exact hQM
  have hMmax : M.IsMaximal := inferInstance
  haveI : (M.map (Ideal.Quotient.mk Q)).IsPrime := Ideal.map_isPrime_of_surjective hsurj hkerM
  have hcomapM : (M.map (Ideal.Quotient.mk Q)).comap (Ideal.Quotient.mk Q) = M := by
    rw [Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_eq_left.mpr hQM
  let xR : PrimeSpectrum (MvPolynomial ι ℂ ⧸ Q) := ⟨M.map (Ideal.Quotient.mk Q), inferInstance⟩
  have hxR : xR ∈ (PrimeSpectrum.basicOpen (Ideal.Quotient.mk Q h) : Set _) := by
    change Ideal.Quotient.mk Q h ∉ M.map (Ideal.Quotient.mk Q)
    intro hmem
    have hhM : h ∈ M := by
      rw [← hcomapM]
      exact hmem
    exact hyh ((mem_vanishingIdeal_singleton_iff y h).mp hhM)
  obtain ⟨q, hq, hqx⟩ := hr hxR
  have hqp : Ideal.Quotient.mk P p ∉ q.asIdeal := hq
  have hqx' : q.asIdeal.comap ψ.toRingHom = M.map (Ideal.Quotient.mk Q) :=
    congrArg PrimeSpectrum.asIdeal hqx
  let q' : Ideal (MvPolynomial κ ℂ) := q.asIdeal.comap (Ideal.Quotient.mk P)
  haveI : q'.IsPrime := Ideal.comap_isPrime _ _
  have hpq' : p ∉ q' := hqp
  obtain ⟨J, hJ, hqJ, hpJ⟩ := maximal_avoiding q' inferInstance p hpq'
  have hsq : (Ideal.Quotient.mk P).comp (φ : MvPolynomial ι ℂ →+* MvPolynomial κ ℂ) =
      ψ.toRingHom.comp (Ideal.Quotient.mk Q) :=
    RingHom.ext fun _ => rfl
  have hq'M : q'.comap (φ : MvPolynomial ι ℂ →+* MvPolynomial κ ℂ) = M := by
    change (q.asIdeal.comap (Ideal.Quotient.mk P)).comap
      (φ : MvPolynomial ι ℂ →+* MvPolynomial κ ℂ) = M
    rw [Ideal.comap_comap, hsq, ← Ideal.comap_comap, hqx', hcomapM]
  have hcontract : J.comap (φ : MvPolynomial ι ℂ →+* MvPolynomial κ ℂ) = M := by
    symm
    apply Ideal.IsMaximal.eq_of_le hMmax (Ideal.comap_ne_top _ hJ.ne_top)
    rw [← hq'M]
    exact Ideal.comap_mono hqJ
  obtain ⟨x, hx⟩ := eq_vanishingIdeal_singleton_of_isMaximal ℂ hJ
  refine ⟨x, ?_, ?_, ?_⟩
  · intro f hf
    have hfq : f ∈ q' := by
      change Ideal.Quotient.mk P f ∈ q.asIdeal
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hf]
      exact q.asIdeal.zero_mem
    have hfJ := hqJ hfq
    rw [hx] at hfJ
    exact (mem_vanishingIdeal_singleton_iff x f).mp hfJ
  · intro h0
    apply hpJ
    rw [hx]
    exact (mem_vanishingIdeal_singleton_iff x p).mpr h0
  · intro i
    have hpoly : X i - C (y i) ∈ M := by
      apply (mem_vanishingIdeal_singleton_iff y _).mpr
      simp
    rw [← hcontract] at hpoly
    change φ (X i - C (y i)) ∈ J at hpoly
    rw [hx] at hpoly
    have hz := (mem_vanishingIdeal_singleton_iff x _).mp hpoly
    have hCφ : φ (C (y i)) = C (y i) := by
      rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
      rfl
    rw [map_sub, hCφ, map_sub, aeval_C] at hz
    exact sub_eq_zero.mp hz

end ImageOpen

end DistinctDistances
