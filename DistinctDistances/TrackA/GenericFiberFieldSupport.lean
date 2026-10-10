import DistinctDistances.TrackA.AffineEtaleFiberSupport
import DistinctDistances.TrackA.AffineFiberPointSupport
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.Algebra.MvPolynomial.Funext

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical TensorProduct

/-- The original affine projection, including its supplied offset. -/
def affineProjectionMap {n k : ℕ} (V : AffineVariety n) (φ : AffineProjection n k) :
    Poly k →ₐ[ℂ] (Poly n ⧸ V.ideal) :=
  (Ideal.Quotient.mkₐ ℂ V.ideal).comp φ.pullback

def affineProjectionRank {n k : ℕ} (V : AffineVariety n) (φ : AffineProjection n k) : ℕ :=
  letI := (affineProjectionMap V φ).toRingHom.toAlgebra
  letI : Module (Poly k) (Poly n ⧸ V.ideal) :=
    (affineProjectionMap V φ).toRingHom.toAlgebra.toModule
  Module.finrank (Poly k) (Poly n ⧸ V.ideal)

/-- Literal points of the original fiber over a complex field extension. -/
def affineFiberOver {n k : ℕ} (V : AffineVariety n) (φ : AffineProjection n k)
    {K : Type*} [Field K] [Algebra ℂ K] (t : Fin k → K) : Set (Fin n → K) :=
  {x | (∀ f ∈ V.ideal, MvPolynomial.aeval x f = 0) ∧
    ∀ j, MvPolynomial.aeval x (φ.pullback (MvPolynomial.X j)) = t j}

theorem affineFiberOver_complex {n k : ℕ} (V : AffineVariety n)
    (φ : AffineProjection n k) (y : Point k) : affineFiberOver V φ y = φ.fiber V y := by
  ext x
  change ((∀ f ∈ V.ideal, MvPolynomial.aeval x f = 0) ∧
    ∀ j, MvPolynomial.aeval x (φ.pullback (MvPolynomial.X j)) = y j) ↔
      x ∈ V.points ∧ φ.apply x = y
  simp only [φ.eval_pullback, MvPolynomial.aeval_X, funext_iff]
  rfl

/-- The quotient/base-change universal property retains the original
coordinate tuple and the original projection equations. -/
def affineFiberOverAlgHomEquiv {n k : ℕ} (V : AffineVariety n)
    (φ : AffineProjection n k) (K : Type*) [Field K] [Algebra ℂ K] (t : Fin k → K) :
    letI := (affineProjectionMap V φ).toRingHom.toAlgebra
    letI : Module (Poly k) (Poly n ⧸ V.ideal) :=
      (affineProjectionMap V φ).toRingHom.toAlgebra.toModule
    letI : SMul (Poly k) (Poly n ⧸ V.ideal) :=
      (affineProjectionMap V φ).toRingHom.toAlgebra.toSMul
    letI := (MvPolynomial.aeval (R := ℂ) t).toRingHom.toAlgebra
    letI : Module (Poly k) K := (MvPolynomial.aeval (R := ℂ) t).toRingHom.toAlgebra.toModule
    letI : SMul (Poly k) K := (MvPolynomial.aeval (R := ℂ) t).toRingHom.toAlgebra.toSMul
    ((Poly n ⧸ V.ideal) →ₐ[Poly k] K) ≃ affineFiberOver V φ t := by
  let R := Poly k
  let B := Poly n ⧸ V.ideal
  letI := (affineProjectionMap V φ).toRingHom.toAlgebra
  letI : Module R B := (affineProjectionMap V φ).toRingHom.toAlgebra.toModule
  letI : SMul R B := (affineProjectionMap V φ).toRingHom.toAlgebra.toSMul
  haveI : IsScalarTower ℂ R B := IsScalarTower.of_algHom (affineProjectionMap V φ)
  letI := (MvPolynomial.aeval (R := ℂ) t).toRingHom.toAlgebra
  letI : Module R K := (MvPolynomial.aeval (R := ℂ) t).toRingHom.toAlgebra.toModule
  letI : SMul R K := (MvPolynomial.aeval (R := ℂ) t).toRingHom.toAlgebra.toSMul
  haveI : IsScalarTower ℂ R K := IsScalarTower.of_algHom (MvPolynomial.aeval (R := ℂ) t)
  let point (h : B →ₐ[R] K) : Fin n → K :=
    fun i => h (Ideal.Quotient.mk V.ideal (MvPolynomial.X i))
  have hpoint (h : B →ₐ[R] K) : MvPolynomial.aeval (R := ℂ) (point h) =
      (h.restrictScalars ℂ).comp (Ideal.Quotient.mkₐ ℂ V.ideal) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [MvPolynomial.aeval_X, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
    rfl
  let fromPoint (x : affineFiberOver V φ t) : B →ₐ[R] K :=
    { __ := (Ideal.Quotient.liftₐ V.ideal (MvPolynomial.aeval (R := ℂ) x.1) x.2.1).toRingHom
      commutes' p := by
        have he : (MvPolynomial.aeval (R := ℂ) x.1).comp φ.pullback =
            MvPolynomial.aeval (R := ℂ) t := by
          apply MvPolynomial.algHom_ext
          intro j
          simpa only [AlgHom.comp_apply, MvPolynomial.aeval_X] using x.2.2 j
        change (Ideal.Quotient.liftₐ V.ideal (MvPolynomial.aeval (R := ℂ) x.1) x.2.1)
          ((affineProjectionMap V φ) p) = MvPolynomial.aeval t p
        simp only [affineProjectionMap, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
          Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
        exact AlgHom.congr_fun he p }
  refine
    { toFun := fun h => ⟨point h, ?_⟩
      invFun := fromPoint
      left_inv := ?_
      right_inv := ?_ }
  · constructor
    · intro f hf
      rw [hpoint, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem.mpr hf, map_zero]
    · intro j
      rw [hpoint, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
      set_option backward.isDefEq.respectTransparency false in
        change h (algebraMap R B (MvPolynomial.X j)) = t j
      rw [h.commutes]
      exact MvPolynomial.aeval_X t j
  · intro h
    apply AlgHom.ext
    intro b
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective b
    change (Ideal.Quotient.liftₐ V.ideal (MvPolynomial.aeval (R := ℂ) (point h)) _)
      (Ideal.Quotient.mk V.ideal f) = _
    set_option backward.isDefEq.respectTransparency false in
      rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk, hpoint]
    rfl
  · intro x
    apply Subtype.ext
    funext i
    change (Ideal.Quotient.liftₐ V.ideal (MvPolynomial.aeval (R := ℂ) x.1) x.2.1)
      (Ideal.Quotient.mk V.ideal (MvPolynomial.X i)) = x.1 i
    set_option backward.isDefEq.respectTransparency false in
      rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
    exact MvPolynomial.aeval_X x.1 i

/-- All components use the same algebraically closed generic base field. -/
abbrev GenericBaseField (k : ℕ) := AlgebraicClosure (FractionRing (Poly k))

def genericBasePoint (k : ℕ) : Fin k → GenericBaseField k :=
  fun j => algebraMap (Poly k) (GenericBaseField k) (MvPolynomial.X j)

theorem genericBasePoint_independent (k : ℕ) :
    AlgebraicIndependent ℂ (genericBasePoint k) := by
  exact (MvPolynomial.algebraicIndependent_X (Fin k) ℂ).map'
    (f := IsScalarTower.toAlgHom ℂ (Poly k) (GenericBaseField k))
    ((RingHom.injective (algebraMap (FractionRing (Poly k)) (GenericBaseField k))).comp
      (IsFractionRing.injective (Poly k) (FractionRing (Poly k))))

/-- Finite etale algebras over the chosen closed field have exactly as
many rational points as their vector-space dimension. -/
theorem finite_etale_closed_algHom_count (K A : Type*) [Field K] [IsAlgClosed K]
    [CommRing A] [Algebra K A] [Algebra.Etale K A] :
    Finite (A →ₐ[K] K) ∧ Nat.card (A →ₐ[K] K) = Module.finrank K A := by
  let e := Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum K A
  let ep := Algebra.FormallyEtale.equivPiOfIsSepClosed K A
  haveI : Module.Finite K A := Algebra.FormallyUnramified.finite_of_free K A
  haveI : IsArtinianRing A := isArtinian_of_tower K inferInstance
  letI : Fintype (PrimeSpectrum A) := Fintype.ofFinite _
  haveI : Finite (A →ₐ[K] K) := Finite.of_equiv (PrimeSpectrum A) e.symm
  refine ⟨inferInstance, ?_⟩
  rw [Nat.card_congr e, ep.toLinearEquiv.finrank_eq]
  simp [Module.finrank_pi, Nat.card_eq_fintype_card]

end
end DistinctDistances.TrackA
