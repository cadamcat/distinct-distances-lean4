import DistinctDistances.TrackA.GenericFiberFieldSupport

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical TensorProduct

/-- The supplied finite affine map has an actual principal etale base
open, including when it has a nonzero affine offset. -/
theorem affineProjection_etale_base_open {n k : ℕ} (V : AffineVariety n)
    (hV : V.IsIrreducible) (hd : V.dimension = k) (φ : AffineProjection n k)
    (hf : FiniteAffineProjection φ V) :
    letI := (affineProjectionMap V φ).toRingHom.toAlgebra
    ∃ g : Poly k, g ≠ 0 ∧ Algebra.Etale (Poly k)
      (Localization.Away (affineProjectionMap V φ g)) := by
  letI : V.ideal.IsPrime := hV
  letI := (affineProjectionMap V φ).toRingHom.toAlgebra
  letI : Module (Poly k) (Poly n ⧸ V.ideal) :=
    (affineProjectionMap V φ).toRingHom.toAlgebra.toModule
  letI : SMul (Poly k) (Poly n ⧸ V.ideal) :=
    (affineProjectionMap V φ).toRingHom.toAlgebra.toSMul
  haveI : Module.Finite (Poly k) (Poly n ⧸ V.ideal) := hf
  haveI : Module.IsTorsionFree (Poly k) (Poly n ⧸ V.ideal) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (finite_affine_projection_pullback_injective V hV hd φ hf)
  exact finite_domain_etale_base_open (Poly k) (Poly n ⧸ V.ideal)

/-- Every closed field fiber above this principal open has the same
literal point count, equal to the original affine module rank. -/
theorem affineProjection_closed_field_fibers {n k : ℕ} (V : AffineVariety n)
    (hV : V.IsIrreducible) (hd : V.dimension = k) (φ : AffineProjection n k)
    (hf : FiniteAffineProjection φ V) :
    ∃ g : Poly k, g ≠ 0 ∧ ∀ (K : Type*) [Field K] [Algebra ℂ K] [IsAlgClosed K]
      (t : Fin k → K), MvPolynomial.aeval t g ≠ 0 →
        (affineFiberOver V φ t).Finite ∧
          (affineFiberOver V φ t).ncard = affineProjectionRank V φ := by
  obtain ⟨g, hg, he⟩ := affineProjection_etale_base_open V hV hd φ hf
  refine ⟨g, hg, ?_⟩
  intro K _ _ _ t hgt
  let R := Poly k
  let B := Poly n ⧸ V.ideal
  letI := (affineProjectionMap V φ).toRingHom.toAlgebra
  letI : Module R B := (affineProjectionMap V φ).toRingHom.toAlgebra.toModule
  letI : SMul R B := (affineProjectionMap V φ).toRingHom.toAlgebra.toSMul
  letI := (MvPolynomial.aeval (R := ℂ) t).toRingHom.toAlgebra
  letI : Module R K := (MvPolynomial.aeval (R := ℂ) t).toRingHom.toAlgebra.toModule
  letI : SMul R K := (MvPolynomial.aeval (R := ℂ) t).toRingHom.toAlgebra.toSMul
  haveI : Module.Finite R B := hf
  obtain ⟨hetale, hrank⟩ := etale_base_open_field_fiber R B K g hg he hgt
  letI := hetale
  obtain ⟨hfinite, hcount⟩ := finite_etale_closed_algHom_count K (K ⊗[R] B)
  let e : (K ⊗[R] B →ₐ[K] K) ≃ affineFiberOver V φ t :=
    (AlgHom.liftEquiv R K B K).symm.trans (affineFiberOverAlgHomEquiv V φ K t)
  letI := hfinite
  haveI : Finite (affineFiberOver V φ t) := Finite.of_equiv _ e
  refine ⟨Set.toFinite _, ?_⟩
  exact (Nat.card_congr e.symm).trans (hcount.trans hrank)

/-- The degree supplied by geometric complex fibers equals the actual
module rank: choose one complex base point in both principal opens. -/
theorem affineProjectionRank_eq_genericDegree {n k r : ℕ} (V : AffineVariety n)
    (hV : V.IsIrreducible) (hd : V.dimension = k) (φ : AffineProjection n k)
    (hf : FiniteAffineProjection φ V) (hr : φ.GenericallyFiniteOfDegree V r) :
    affineProjectionRank V φ = r := by
  obtain ⟨g, hg, hfiber⟩ := affineProjection_closed_field_fibers V hV hd φ hf
  obtain ⟨_, q, hq, hqfiber⟩ := hr
  have himage := finite_affine_projection_image_ideal_bot V hV hd φ hf
  have hq0 : q ≠ 0 := by simpa only [himage, Ideal.mem_bot] using hq
  obtain ⟨y, hy⟩ : ∃ y : Point k, MvPolynomial.eval y (g * q) ≠ 0 := by
    by_contra h
    push Not at h
    exact mul_ne_zero hg hq0 (MvPolynomial.funext (by simpa using h))
  have hgy : MvPolynomial.aeval y g ≠ 0 := (mul_ne_zero_iff.mp (by simpa using hy)).1
  have hqy : MvPolynomial.aeval y q ≠ 0 := (mul_ne_zero_iff.mp (by simpa using hy)).2
  have hyimage : y ∈ (φ.image V).points := by
    intro f hf
    rw [himage, Ideal.mem_bot] at hf
    simp only [hf, map_zero]
  exact (hfiber ℂ y hgy).2.symm.trans
    ((congrArg Set.ncard (affineFiberOver_complex V φ y)).trans (hqfiber y hyimage hqy).2)

/-- Algebraic independence puts the literal generic point in every
nonzero principal base open, so its point count is the supplied degree. -/
theorem affineFiberOver_generic_count {n k r : ℕ} (V : AffineVariety n)
    (hV : V.IsIrreducible) (hd : V.dimension = k) (φ : AffineProjection n k)
    (hf : FiniteAffineProjection φ V) (hr : φ.GenericallyFiniteOfDegree V r)
    (K : Type*) [Field K] [Algebra ℂ K] [IsAlgClosed K]
    (t : Fin k → K) (ht : AlgebraicIndependent ℂ t) :
    (affineFiberOver V φ t).Finite ∧ (affineFiberOver V φ t).ncard = r := by
  obtain ⟨g, hg, hfiber⟩ := affineProjection_closed_field_fibers V hV hd φ hf
  have hgt : MvPolynomial.aeval t g ≠ 0 := by
    intro h
    exact hg ((algebraicIndependent_iff_injective_aeval.mp ht) (by simpa using h))
  obtain ⟨hfin, hcount⟩ := hfiber K t hgt
  exact ⟨hfin, hcount.trans (affineProjectionRank_eq_genericDegree V hV hd φ hf hr)⟩

/-- A rational point above an independent base tuple embeds the original
component coordinate domain; nonzero elements divide a nonzero base scalar. -/
theorem finite_domain_field_map_injective (R B K : Type*) [CommRing R] [IsDomain R]
    [CommRing B] [IsDomain B] [Algebra R B] [Module.Finite R B]
    [Field K] [Algebra R K] (hRK : Function.Injective (algebraMap R K))
    (h : B →ₐ[R] K) : Function.Injective h := by
  apply (RingHom.injective_iff_ker_eq_bot h.toRingHom).mpr
  apply eq_bot_iff.mpr
  intro b hb
  change b = 0
  by_contra hb0
  obtain ⟨g, hg, c, hgc⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := R) b).exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero hb0)
  have he : algebraMap R K g = 0 := by
    rw [← h.commutes, hgc, map_mul]
    change h b = 0 at hb
    rw [hb, zero_mul]
  exact hg (hRK (by simpa using he))

/-- The original equations vanishing on a generic sheet are exactly its
component ideal. This identifies contractions used for isolation and
prevents sheets of distinct selected components from coinciding. -/
theorem affineFiberOver_eval_ker {n k : ℕ} (V : AffineVariety n)
    (hV : V.IsIrreducible) (φ : AffineProjection n k) (hf : FiniteAffineProjection φ V)
    (K : Type*) [Field K] [Algebra ℂ K] (t : Fin k → K)
    (ht : AlgebraicIndependent ℂ t) (x : affineFiberOver V φ t) :
    RingHom.ker (MvPolynomial.aeval (R := ℂ) x.1).toRingHom = V.ideal := by
  let R := Poly k
  let B := Poly n ⧸ V.ideal
  letI : V.ideal.IsPrime := hV
  letI := (affineProjectionMap V φ).toRingHom.toAlgebra
  letI : Module R B := (affineProjectionMap V φ).toRingHom.toAlgebra.toModule
  letI : SMul R B := (affineProjectionMap V φ).toRingHom.toAlgebra.toSMul
  letI := (MvPolynomial.aeval (R := ℂ) t).toRingHom.toAlgebra
  letI : Module R K := (MvPolynomial.aeval (R := ℂ) t).toRingHom.toAlgebra.toModule
  letI : SMul R K := (MvPolynomial.aeval (R := ℂ) t).toRingHom.toAlgebra.toSMul
  let h := (affineFiberOverAlgHomEquiv V φ K t).symm x
  haveI : Module.Finite R B := hf
  have hi : Function.Injective h := finite_domain_field_map_injective R B K
    (algebraicIndependent_iff_injective_aeval.mp ht) h
  ext f
  change MvPolynomial.aeval x.1 f = 0 ↔ f ∈ V.ideal
  have he : h (Ideal.Quotient.mk V.ideal f) = MvPolynomial.aeval x.1 f := by
    change (Ideal.Quotient.liftₐ V.ideal (MvPolynomial.aeval (R := ℂ) x.1) x.2.1)
      (Ideal.Quotient.mk V.ideal f) = _
    set_option backward.isDefEq.respectTransparency false in
      rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
    rfl
  rw [← he, map_eq_zero_iff h hi, Ideal.Quotient.eq_zero_iff_mem]

end
end DistinctDistances.TrackA
