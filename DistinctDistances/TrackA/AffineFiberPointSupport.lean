import DistinctDistances.Foundations.Projection
import Mathlib.RingTheory.TotallySplit

set_option backward.isDefEq.respectTransparency false

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical

/-- The literal equations of one fiber of the supplied projection. -/
def affineFiberIdeal {n k : ℕ} (V : AffineVariety n) (φ : AffineProjection n k)
    (y : Point k) : Ideal (Poly n) :=
  V.ideal ⊔ Ideal.span (Set.range (fun i : Fin k =>
    φ.pullback (MvPolynomial.X i) - MvPolynomial.C (y i)))

theorem affineFiberIdeal_zeroLocus {n k : ℕ} (V : AffineVariety n)
    (φ : AffineProjection n k) (y : Point k) :
    MvPolynomial.zeroLocus ℂ (affineFiberIdeal V φ y) = φ.fiber V y := by
  ext x
  change (∀ f ∈ affineFiberIdeal V φ y, MvPolynomial.eval x f = 0) ↔
    x ∈ V.points ∧ φ.apply x = y
  constructor
  · intro h
    refine ⟨fun f hf => h f (Ideal.mem_sup_left hf), ?_⟩
    funext i
    have hi := h _ (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_range_self i)))
    change MvPolynomial.aeval x
      (φ.pullback (MvPolynomial.X i) - MvPolynomial.C (y i)) = 0 at hi
    simpa only [map_sub, MvPolynomial.aeval_C, Algebra.algebraMap_self_apply,
      φ.eval_pullback, MvPolynomial.aeval_X, sub_eq_zero] using hi
  · rintro ⟨hx, hxy⟩
    have hI : affineFiberIdeal V φ y ≤ RingHom.ker (MvPolynomial.eval x) := by
      apply sup_le
      · exact hx
      · apply Ideal.span_le.mpr
        rintro f ⟨i, rfl⟩
        change MvPolynomial.aeval x _ = 0
        simp only [map_sub, MvPolynomial.aeval_C, Algebra.algebraMap_self_apply,
          φ.eval_pullback, MvPolynomial.aeval_X, hxy, sub_self]
    exact hI

/-- The universal property of the coordinate quotient, with the actual
coordinate tuple as its inverse. No radical replacement is needed. -/
def quotientAlgHomEquivZeroLocus {n : ℕ} (I : Ideal (Poly n)) :
    ((Poly n ⧸ I) →ₐ[ℂ] ℂ) ≃ MvPolynomial.zeroLocus ℂ I where
  toFun h := ⟨fun i => h (Ideal.Quotient.mk I (MvPolynomial.X i)), by
    intro f hf
    have he : (MvPolynomial.aeval (fun i => h (Ideal.Quotient.mk I (MvPolynomial.X i)))) =
        h.comp (Ideal.Quotient.mkₐ ℂ I) := by
      apply MvPolynomial.algHom_ext
      intro i
      simp
    change MvPolynomial.aeval _ f = 0
    rw [he, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem.mpr hf, map_zero]⟩
  invFun x := Ideal.Quotient.liftₐ I (MvPolynomial.aeval x.1) x.2
  left_inv h := by
    apply AlgHom.ext
    intro z
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective z
    change (Ideal.Quotient.liftₐ I (MvPolynomial.aeval
      (fun i => h (Ideal.Quotient.mk I (MvPolynomial.X i)))) _)
        (Ideal.Quotient.mk I f) = _
    rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
    have he : (MvPolynomial.aeval (fun i => h (Ideal.Quotient.mk I (MvPolynomial.X i)))) =
        h.comp (Ideal.Quotient.mkₐ ℂ I) := by
      apply MvPolynomial.algHom_ext
      intro i
      simp
    simpa using congrArg (fun a : Poly n →ₐ[ℂ] ℂ => a f) he
  right_inv x := by
    apply Subtype.ext
    funext i
    change (Ideal.Quotient.liftₐ I (MvPolynomial.aeval x.1) x.2)
      (Ideal.Quotient.mk I (MvPolynomial.X i)) = x.1 i
    rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
    exact MvPolynomial.aeval_X x.1 i

def affineFiberAlgHomEquiv {n k : ℕ} (V : AffineVariety n)
    (φ : AffineProjection n k) (y : Point k) :
    ((Poly n ⧸ affineFiberIdeal V φ y) →ₐ[ℂ] ℂ) ≃ φ.fiber V y :=
  (quotientAlgHomEquivZeroLocus _).trans (Set.equivOfEq (affineFiberIdeal_zeroLocus V φ y))

/-- Rational points of a finite étale complex algebra are finite, and
their number equals the algebra's vector-space dimension. -/
theorem finite_etale_complex_algHom_count (A : Type*) [CommRing A] [Algebra ℂ A]
    [Algebra.Etale ℂ A] :
    Finite (A →ₐ[ℂ] ℂ) ∧ Nat.card (A →ₐ[ℂ] ℂ) = Module.finrank ℂ A := by
  let e := Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum ℂ A
  let ep := Algebra.FormallyEtale.equivPiOfIsSepClosed ℂ A
  haveI : Module.Finite ℂ A := Algebra.FormallyUnramified.finite_of_free ℂ A
  haveI : IsArtinianRing A := isArtinian_of_tower ℂ inferInstance
  letI : Fintype (PrimeSpectrum A) := Fintype.ofFinite _
  haveI : Finite (A →ₐ[ℂ] ℂ) := Finite.of_equiv (PrimeSpectrum A) e.symm
  refine ⟨inferInstance, ?_⟩
  rw [Nat.card_congr e, ep.toLinearEquiv.finrank_eq]
  simp [Module.finrank_pi, Nat.card_eq_fintype_card]

theorem affineFiber_count_of_etale {n k : ℕ} (V : AffineVariety n)
    (φ : AffineProjection n k) (y : Point k)
    [Algebra.Etale ℂ (Poly n ⧸ affineFiberIdeal V φ y)] :
    (φ.fiber V y).Finite ∧ (φ.fiber V y).ncard =
      Module.finrank ℂ (Poly n ⧸ affineFiberIdeal V φ y) := by
  let e := affineFiberAlgHomEquiv V φ y
  obtain ⟨hfinite, hcard⟩ := finite_etale_complex_algHom_count
    (Poly n ⧸ affineFiberIdeal V φ y)
  letI := hfinite
  haveI : Finite (φ.fiber V y) := Finite.of_equiv _ e
  refine ⟨Set.toFinite _, ?_⟩
  exact (Nat.card_congr e.symm).trans hcard

end
end DistinctDistances.TrackA
