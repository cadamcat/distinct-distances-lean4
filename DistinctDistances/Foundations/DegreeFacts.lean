import DistinctDistances.Foundations.GenericFiber

/-!
Shared-model facts used by B11 (`conc:deg-fiber-degree`).

* Transcendence-degree avoidance: the image of `Z(J) × ℂ^f` under a polynomial map is
  contained in a hypersurface missing any prime of larger dimension.
* Hilbert sandwich: a projective variety squeezed between a pure top-dimensional piece and
  lower-dimensional pieces has the dimension and degree of the top piece.
-/

namespace DistinctDistances

open scoped BigOperators

noncomputable section

namespace DegreeFacts

/-- A kernel of a map into a domain of smaller transcendence degree is not contained in the
kernel of a surjection onto a domain. -/
theorem exists_ker_not_ker {m : ℕ} {A B : Type} [CommRing A] [IsDomain A] [Algebra ℂ A]
    [CommRing B] [IsDomain B] [Algebra ℂ B]
    (ρ : Poly m →ₐ[ℂ] A) (π : Poly m →ₐ[ℂ] B) (hπ : Function.Surjective π)
    (h : Algebra.trdeg ℂ A < Algebra.trdeg ℂ B) :
    ∃ g : Poly m, ρ g = 0 ∧ π g ≠ 0 := by
  by_contra hcon
  push Not at hcon
  let Kρ := RingHom.ker ρ
  let Kπ := RingHom.ker π
  haveI : Kρ.IsPrime := RingHom.ker_isPrime ρ
  haveI : Kπ.IsPrime := RingHom.ker_isPrime π
  have hle : Kρ ≤ Kπ := fun g hg => hcon g hg
  have hdim := GenericFiber.affineDimension_mono hle
  have hρ : (OAI.QuarticPowerFree.affineDimension Kρ : Cardinal) ≤ Algebra.trdeg ℂ A := by
    rw [GenericFiber.affineDimension_eq_trdeg]
    exact trdeg_le_of_injective (Ideal.kerLiftAlg ρ) (Ideal.kerLiftAlg_injective ρ)
  have hπ' : (OAI.QuarticPowerFree.affineDimension Kπ : Cardinal) = Algebra.trdeg ℂ B := by
    rw [GenericFiber.affineDimension_eq_trdeg]
    exact (Ideal.quotientKerAlgEquivOfSurjective hπ).trdeg_eq
  have hcast : (OAI.QuarticPowerFree.affineDimension Kπ : Cardinal) ≤
      (OAI.QuarticPowerFree.affineDimension Kρ : Cardinal) := by exact_mod_cast hdim
  exact absurd (lt_of_le_of_lt (hπ'.symm.le.trans (hcast.trans hρ)) h) (lt_irrefl _)

/-- Substitution of the source variables into `(Poly a ⧸ N)[t]`. -/
def freeSubst (a f : ℕ) (N : Ideal (Poly a)) : Poly (a + f) →ₐ[ℂ] MvPolynomial (Fin f) (Poly a ⧸ N) :=
  MvPolynomial.aeval (Fin.append (fun j : Fin a => MvPolynomial.C (Ideal.Quotient.mk N
    (MvPolynomial.X j))) (fun j : Fin f => MvPolynomial.X j))

theorem trdeg_freeExtension (a f : ℕ) (N : Ideal (Poly a)) [N.IsPrime] :
    Algebra.trdeg ℂ (MvPolynomial (Fin f) (Poly a ⧸ N)) =
      (OAI.QuarticPowerFree.affineDimension N : Cardinal) + f := by
  haveI h1 : FaithfulSMul ℂ (Poly a ⧸ N) :=
    (faithfulSMul_iff_algebraMap_injective ℂ (Poly a ⧸ N)).mpr (algebraMap ℂ _).injective
  haveI h2 : FaithfulSMul (Poly a ⧸ N) (MvPolynomial (Fin f) (Poly a ⧸ N)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (MvPolynomial.C_injective _ _)
  have h := trdeg_add_eq ℂ (Poly a ⧸ N) (A := MvPolynomial (Fin f) (Poly a ⧸ N))
  rw [MvPolynomial.trdeg_of_isDomain] at h
  rw [← h, ← GenericFiber.affineDimension_eq_trdeg]
  simp

/-- Evaluation of `(Poly a ⧸ N)[t]` at a point of `Z(N)` and a parameter value. -/
def freeEval {a f : ℕ} (N : Ideal (Poly a)) (x : Point a)
    (hx : N ≤ RingHom.ker (MvPolynomial.aeval x : Poly a →ₐ[ℂ] ℂ).toRingHom) (t : Point f) :
    MvPolynomial (Fin f) (Poly a ⧸ N) →+* ℂ :=
  MvPolynomial.eval₂Hom (Ideal.Quotient.lift N (MvPolynomial.aeval x).toRingHom hx) t

theorem freeEval_freeSubst {a f : ℕ} (N : Ideal (Poly a)) (x : Point a)
    (hx : N ≤ RingHom.ker (MvPolynomial.aeval x : Poly a →ₐ[ℂ] ℂ).toRingHom) (t : Point f)
    (q : Poly (a + f)) :
    freeEval N x hx t (freeSubst a f N q) = MvPolynomial.aeval (Fin.append x t) q := by
  have hring : (freeEval N x hx t).comp (freeSubst a f N).toRingHom =
      (MvPolynomial.aeval (Fin.append x t) : Poly (a + f) →ₐ[ℂ] ℂ).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [freeEval, freeSubst, RingHom.coe_comp, Function.comp_apply,
        AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, MvPolynomial.aeval_C,
        MvPolynomial.algebraMap_eq, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
      rw [MvPolynomial.algebraMap_apply, MvPolynomial.eval₂_C, ← Ideal.Quotient.mk_algebraMap,
        Ideal.Quotient.lift_mk]
      simp
    · intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp [freeEval, freeSubst]
      · simp [freeEval, freeSubst]
  exact RingHom.congr_fun hring q

/-- **Image avoidance.** If every prime over `J` has dimension at most `k`, the image of
`Z(J) × ℂ^f` under a polynomial map lies in a hypersurface not containing any target domain of
transcendence degree larger than `k + f`. -/
theorem exists_vanishing_on_parametrized_image {a f m k : ℕ} (J : Ideal (Poly a))
    (hJ : ∀ N : Ideal (Poly a), N.IsPrime → J ≤ N →
      OAI.QuarticPowerFree.affineDimension N ≤ k)
    (Φ : Fin m → Poly (a + f)) {B : Type} [CommRing B] [IsDomain B] [Algebra ℂ B]
    (π : Poly m →ₐ[ℂ] B) (hπ : Function.Surjective π)
    (hB : ((k + f : ℕ) : Cardinal) < Algebra.trdeg ℂ B) :
    ∃ g : Poly m, π g ≠ 0 ∧ ∀ x ∈ MvPolynomial.zeroLocus ℂ J, ∀ t : Point f,
      MvPolynomial.aeval (fun i => MvPolynomial.aeval (Fin.append x t) (Φ i)) g = 0 := by
  classical
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing (Poly a) J
  let M := hfin.toFinset
  have hchoice : ∀ N ∈ M, ∃ g : Poly m,
      (MvPolynomial.aeval (fun i => freeSubst a f N (Φ i)) :
          Poly m →ₐ[ℂ] MvPolynomial (Fin f) (Poly a ⧸ N)) g = 0 ∧ π g ≠ 0 := by
    intro N hN
    have hNmin : N ∈ J.minimalPrimes := (Set.Finite.mem_toFinset _).mp hN
    haveI : N.IsPrime := hNmin.isPrime
    let ρ : Poly m →ₐ[ℂ] MvPolynomial (Fin f) (Poly a ⧸ N) :=
      MvPolynomial.aeval (fun i => freeSubst a f N (Φ i))
    refine exists_ker_not_ker (A := MvPolynomial (Fin f) (Poly a ⧸ N)) ρ π hπ ?_
    rw [trdeg_freeExtension]
    have hk := hJ N hNmin.isPrime hNmin.1.2
    refine lt_of_le_of_lt ?_ hB
    have : ((OAI.QuarticPowerFree.affineDimension N : ℕ) : Cardinal) + (f : Cardinal) =
        ((OAI.QuarticPowerFree.affineDimension N + f : ℕ) : Cardinal) := by push_cast; rfl
    rw [this]
    exact_mod_cast (by omega : OAI.QuarticPowerFree.affineDimension N + f ≤ k + f)
  let gs : Ideal (Poly a) → Poly m := fun N =>
    if hN : N ∈ M then Classical.choose (hchoice N hN) else 1
  refine ⟨∏ N ∈ M, gs N, ?_, ?_⟩
  · rw [map_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro N hN
    simp only [gs, dite_eq_left_of_eq_true (eq_true hN)]
    exact (Classical.choose_spec (hchoice N hN)).2
  · intro x hx t
    let mx : Ideal (Poly a) := RingHom.ker (MvPolynomial.aeval x : Poly a →ₐ[ℂ] ℂ).toRingHom
    have hmx : mx.IsPrime := RingHom.ker_isPrime _
    have hJx : J ≤ mx := fun q hq => (MvPolynomial.mem_zeroLocus_iff.mp hx) q hq
    obtain ⟨N, hNmin, hNx⟩ := Ideal.exists_minimalPrimes_le hJx
    have hN : N ∈ M := (Set.Finite.mem_toFinset _).mpr hNmin
    rw [map_prod]
    apply Finset.prod_eq_zero hN
    haveI : N.IsPrime := hNmin.isPrime
    have hspec := (Classical.choose_spec (hchoice N hN)).1
    simp only [gs, dite_eq_left_of_eq_true (eq_true hN)]
    have hcomp : (freeEval N x hNx t).comp
        ((MvPolynomial.aeval (fun i => freeSubst a f N (Φ i)) :
          Poly m →ₐ[ℂ] MvPolynomial (Fin f) (Poly a ⧸ N)).toRingHom) =
        (MvPolynomial.aeval (fun i => MvPolynomial.aeval (Fin.append x t) (Φ i)) :
          Poly m →ₐ[ℂ] ℂ).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp only [freeEval, RingHom.coe_comp, Function.comp_apply,
          AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, MvPolynomial.aeval_C,
          MvPolynomial.algebraMap_eq, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
        rw [MvPolynomial.algebraMap_apply, MvPolynomial.eval₂_C, ← Ideal.Quotient.mk_algebraMap,
          Ideal.Quotient.lift_mk]
        simp
      · intro i
        simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
          AlgHom.coe_toRingHom, MvPolynomial.aeval_X]
        exact freeEval_freeSubst N x hNx t (Φ i)
    have := RingHom.congr_fun hcomp (Classical.choose (hchoice N hN))
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom] at this
    rw [← this, hspec, map_zero]

end DegreeFacts

end

end DistinctDistances
