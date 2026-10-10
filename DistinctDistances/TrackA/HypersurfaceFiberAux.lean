import DistinctDistances.TrackA.NormalizationRankSupport
import DistinctDistances.TrackA.Hilbert
import DistinctDistances.TrackA.AlgebraicFieldFiberSupport
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Ideal.GoingUp
import OAI.NumberTheory.PowerFree.ProjectionDegrees
import Mathlib.RingTheory.Flat.Rank
import DistinctDistances.TrackA.LocalPolynomialComparisonSupport

namespace DistinctDistances.TrackA
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical BigOperators

/-- Integrality bounds each coordinate of every fiber by a nonzero
one-variable polynomial. -/
theorem hyp_finite_affine_fiber {n m : ℕ} (V : AffineVariety n)
    (φ : AffineProjection n m) (hf : FiniteAffineProjection φ V) (y : Point m) :
    (φ.fiber V y).Finite := by
  let B := Poly n ⧸ V.ideal
  let g : Poly m →+* B := (Ideal.Quotient.mk V.ideal).comp φ.pullback.toRingHom
  have hfinite : g.Finite := hf
  have hcoordinate (i : Fin n) : ∃ Q : Polynomial ℂ, Q ≠ 0 ∧
      ∀ v ∈ φ.fiber V y, Q.eval (v i) = 0 := by
    obtain ⟨P, hP, hPzero⟩ := hfinite.to_isIntegral
      (Ideal.Quotient.mk V.ideal (MvPolynomial.X i))
    let ε : Poly m →+* ℂ := MvPolynomial.eval y
    let Q := P.map ε
    refine ⟨Q, (hP.map ε).ne_zero, ?_⟩
    rintro v ⟨hv, hφv⟩
    let ev : B →+* ℂ := Ideal.Quotient.lift V.ideal (MvPolynomial.eval v)
      (fun f hf => by simpa only [MvPolynomial.aeval_eq_eval] using hv f hf)
    have hev (f : Poly n) : ev (Ideal.Quotient.mk V.ideal f) = MvPolynomial.eval v f :=
      Ideal.Quotient.lift_mk _ _ _
    have hevg : ev.comp g = ε := by
      apply MvPolynomial.ringHom_ext
      · intro c
        change ev (Ideal.Quotient.mk V.ideal (φ.pullback (MvPolynomial.C c))) = _
        rw [hev]
        simp [AffineProjection.pullback, ε]
      · intro j
        change ev (Ideal.Quotient.mk V.ideal (φ.pullback (MvPolynomial.X j))) = _
        rw [hev]
        change MvPolynomial.aeval v (φ.pullback (MvPolynomial.X j)) = _
        rw [φ.eval_pullback, hφv]
        rfl
    have h := congrArg ev hPzero
    rw [map_zero, Polynomial.hom_eval₂, hevg, hev, MvPolynomial.eval_X] at h
    simpa only [Q, Polynomial.eval_map] using h
  choose Q hQ hroots using hcoordinate
  let roots (i : Fin n) : Set ℂ := {a | (Q i).IsRoot a}
  have hrootsfinite (i : Fin n) : (roots i).Finite :=
    Polynomial.finite_setOfPred_isRoot (hQ i)
  letI (i : Fin n) : Finite (roots i) := hrootsfinite i
  let f : φ.fiber V y → ((i : Fin n) → roots i) := fun v i =>
    ⟨v.val i, hroots i v.val v.property⟩
  have hf : Function.Injective f := by
    intro v w h
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun h i)
  haveI : Finite (φ.fiber V y) := Finite.of_injective f hf
  exact Set.toFinite _

/-- Finitely many nonzero polynomials over an extension field can be
simultaneously nonzero at a scalar in the infinite base field. -/
theorem hyp_avoid_polynomial_roots {K L ι : Type*}
    [Field K] [Infinite K] [Field L] [Algebra K L] [Fintype ι]
    (P : ι → Polynomial L) (hP : ∀ i, P i ≠ 0) :
    ∃ a : K, ∀ i, (P i).eval (algebraMap K L a) ≠ 0 := by
  let bad (i : ι) : Set K := (algebraMap K L) ⁻¹' {b | (P i).IsRoot b}
  have hbad (i : ι) : (bad i).Finite :=
    (Polynomial.finite_setOfPred_isRoot (hP i)).preimage
      (algebraMap K L).injective.injOn
  let S : Finset K := Finset.univ.biUnion (fun i => (hbad i).toFinset)
  obtain ⟨a, ha⟩ := S.exists_notMem
  refine ⟨a, ?_⟩
  intro i hai
  apply ha
  apply Finset.mem_biUnion.mpr
  refine ⟨i, Finset.mem_univ i, ?_⟩
  exact (hbad i).mem_toFinset.mpr hai

/-- Encoding a vector as coefficients gives a nonzero polynomial
whenever the vector is nonzero. -/
def hyp_momentPolynomial {n : ℕ} {L : Type*} [Field L] (v : Fin n → L) :
    Polynomial L := ∑ i : Fin n, Polynomial.C (v i) * Polynomial.X ^ i.val

theorem hyp_momentPolynomial_coeff {n : ℕ} {L : Type*} [Field L]
    (v : Fin n → L) (j : Fin n) : (hyp_momentPolynomial v).coeff j.val = v j := by
  rw [hyp_momentPolynomial, Polynomial.finsetSum_coeff, Finset.sum_eq_single j]
  · simp
  · intro i hi hij
    rw [Polynomial.coeff_C_mul_X_pow]
    exact if_neg (fun h => hij (Fin.ext h.symm))
  · simp

theorem hyp_momentPolynomial_ne_zero {n : ℕ} {L : Type*} [Field L]
    (v : Fin n → L) (hv : v ≠ 0) : hyp_momentPolynomial v ≠ 0 := by
  intro h
  apply hv
  funext j
  have hc := hyp_momentPolynomial_coeff v j
  rw [h, Polynomial.coeff_zero] at hc
  exact hc.symm

/-- One scalar supplies coefficients of a linear form nonzero on each
of finitely many vectors, including vectors over an extension field. -/
theorem hyp_separating_coefficients {n : ℕ} {K L : Type*}
    [Field K] [Infinite K] [Field L] [Algebra K L]
    (S : Finset (Fin n → L)) (hS : ∀ v ∈ S, v ≠ 0) :
    ∃ c : Fin n → K, ∀ v ∈ S, (∑ i, algebraMap K L (c i) * v i) ≠ 0 := by
  obtain ⟨a, ha⟩ := hyp_avoid_polynomial_roots (K := K)
    (fun v : S => hyp_momentPolynomial v.val)
    (fun v => hyp_momentPolynomial_ne_zero v.val (hS v.val v.property))
  refine ⟨fun i => a ^ i.val, ?_⟩
  intro v hv
  have h := ha ⟨v, hv⟩
  simpa only [hyp_momentPolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X, map_pow, mul_comm] using h

/-- An affine projection may be extended by an arbitrary linear
coordinate while retaining its finite algebra map. -/
def hyp_extend_projection {n k : ℕ} (φ : AffineProjection n k)
    (ℓ : Point n →ₗ[ℂ] ℂ) : AffineProjection n (k+1) where
  linear := LinearMap.pi (Fin.cons ℓ (fun j => (LinearMap.proj j).comp φ.linear))
  offset := Fin.cons 0 φ.offset

theorem hyp_extend_projection_apply {n k : ℕ} (φ : AffineProjection n k)
    (ℓ : Point n →ₗ[ℂ] ℂ) (p : Point n) :
    (hyp_extend_projection φ ℓ).apply p = Fin.cons (ℓ p) (φ.apply p) := by
  ext j
  cases j using Fin.cases <;> simp [hyp_extend_projection, AffineProjection.apply]

theorem hyp_extend_projection_pullback_succ {n k : ℕ} (φ : AffineProjection n k)
    (ℓ : Point n →ₗ[ℂ] ℂ) (j : Fin k) :
    (hyp_extend_projection φ ℓ).pullback (MvPolynomial.X j.succ) =
      φ.pullback (MvPolynomial.X j) := by
  simp [AffineProjection.pullback, hyp_extend_projection, linearCoordinate]

theorem hyp_extend_projection_finite {n k : ℕ} (V : AffineVariety n)
    (φ : AffineProjection n k) (ℓ : Point n →ₗ[ℂ] ℂ)
    (hf : FiniteAffineProjection φ V) :
    FiniteAffineProjection (hyp_extend_projection φ ℓ) V := by
  let g := affineProjectionMap V (hyp_extend_projection φ ℓ)
  have he : g.comp (MvPolynomial.rename Fin.succ) = affineProjectionMap V φ := by
    ext j
    simp only [g, affineProjectionMap, AlgHom.comp_apply, MvPolynomial.rename_X,
      Ideal.Quotient.mkₐ_eq_mk, hyp_extend_projection_pullback_succ]
  have h : (g.comp (MvPolynomial.rename Fin.succ)).Finite := by
    rw [he]
    exact hf
  exact AlgHom.Finite.of_comp_finite h

/-- The reduced image coordinate ring is the actual pullback subalgebra. -/
def hyp_imageMap {n m : ℕ} (V : AffineVariety n) (φ : AffineProjection n m) :
    (Poly m ⧸ (φ.image V).ideal) →ₐ[ℂ] (Poly n ⧸ V.ideal) :=
  Ideal.Quotient.liftₐ (φ.image V).ideal (affineProjectionMap V φ)
    (fun f hf => Ideal.Quotient.eq_zero_iff_mem.mpr hf)

theorem hyp_imageMap_mk {n m : ℕ} (V : AffineVariety n)
    (φ : AffineProjection n m) (f : Poly m) :
    hyp_imageMap V φ (Ideal.Quotient.mk (φ.image V).ideal f) =
      Ideal.Quotient.mk V.ideal (φ.pullback f) := rfl

theorem hyp_imageMap_injective {n m : ℕ} (V : AffineVariety n)
    (φ : AffineProjection n m) : Function.Injective (hyp_imageMap V φ) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [hyp_imageMap_mk, Ideal.Quotient.eq_zero_iff_mem] at ha
  exact Ideal.Quotient.eq_zero_iff_mem.mpr ha

theorem hyp_imageMap_finite {n m : ℕ} (V : AffineVariety n)
    (φ : AffineProjection n m) (hf : FiniteAffineProjection φ V) :
    (hyp_imageMap V φ).Finite := by
  have he : (hyp_imageMap V φ).comp (Ideal.Quotient.mkₐ ℂ (φ.image V).ideal) =
      affineProjectionMap V φ := by
    ext j
    rfl
  have h : ((hyp_imageMap V φ).comp
      (Ideal.Quotient.mkₐ ℂ (φ.image V).ideal)).Finite := by
    rw [he]
    exact hf
  exact AlgHom.Finite.of_comp_finite h

def hyp_imageEvaluation {n m : ℕ} (V : AffineVariety n)
    (φ : AffineProjection n m) (K : Type*) [Field K] [Algebra ℂ K]
    (y : Fin m → K) (hy : ∀ f ∈ (φ.image V).ideal, MvPolynomial.aeval y f = 0) :
    (Poly m ⧸ (φ.image V).ideal) →ₐ[ℂ] K :=
  Ideal.Quotient.liftₐ (φ.image V).ideal (MvPolynomial.aeval (R := ℂ) y) hy

/-- Fiber points correspond to algebra homomorphisms over the actual
image coordinate ring, including when its ideal is nonzero. -/
def hyp_imageFiberAlgHomEquiv {n m : ℕ} (V : AffineVariety n)
    (φ : AffineProjection n m) (K : Type*) [Field K] [Algebra ℂ K]
    (y : Fin m → K) (hy : ∀ f ∈ (φ.image V).ideal, MvPolynomial.aeval y f = 0) :
    let A := Poly m ⧸ (φ.image V).ideal
    let B := Poly n ⧸ V.ideal
    letI : Algebra A B := (hyp_imageMap V φ).toRingHom.toAlgebra
    letI : Module A B := (hyp_imageMap V φ).toRingHom.toAlgebra.toModule
    letI : SMul A B := (hyp_imageMap V φ).toRingHom.toAlgebra.toSMul
    letI : Algebra A K := (hyp_imageEvaluation V φ K y hy).toRingHom.toAlgebra
    letI : Module A K := (hyp_imageEvaluation V φ K y hy).toRingHom.toAlgebra.toModule
    letI : SMul A K := (hyp_imageEvaluation V φ K y hy).toRingHom.toAlgebra.toSMul
    (B →ₐ[A] K) ≃ affineFiberOver V φ y := by
  let A := Poly m ⧸ (φ.image V).ideal
  let B := Poly n ⧸ V.ideal
  letI : Algebra A B := (hyp_imageMap V φ).toRingHom.toAlgebra
  letI : Module A B := (hyp_imageMap V φ).toRingHom.toAlgebra.toModule
  letI : SMul A B := (hyp_imageMap V φ).toRingHom.toAlgebra.toSMul
  letI : Algebra A K := (hyp_imageEvaluation V φ K y hy).toRingHom.toAlgebra
  letI : Module A K := (hyp_imageEvaluation V φ K y hy).toRingHom.toAlgebra.toModule
  letI : SMul A K := (hyp_imageEvaluation V φ K y hy).toRingHom.toAlgebra.toSMul
  haveI : IsScalarTower ℂ A B := IsScalarTower.of_algHom (hyp_imageMap V φ)
  haveI : IsScalarTower ℂ A K := IsScalarTower.of_algHom (hyp_imageEvaluation V φ K y hy)
  let point (h : B →ₐ[A] K) : Fin n → K :=
    fun i => h (Ideal.Quotient.mk V.ideal (MvPolynomial.X i))
  have hpoint (h : B →ₐ[A] K) : MvPolynomial.aeval (R := ℂ) (point h) =
      (h.restrictScalars ℂ).comp (Ideal.Quotient.mkₐ ℂ V.ideal) := by
    ext i
    simp only [MvPolynomial.aeval_X, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
    rfl
  let fromPoint (x : affineFiberOver V φ y) : B →ₐ[A] K :=
    { __ := (Ideal.Quotient.liftₐ V.ideal (MvPolynomial.aeval (R := ℂ) x.1) x.2.1).toRingHom
      commutes' a := by
        obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
        have he : (MvPolynomial.aeval (R := ℂ) x.1).comp φ.pullback =
            MvPolynomial.aeval (R := ℂ) y := by
          ext j
          simpa only [AlgHom.comp_apply, MvPolynomial.aeval_X] using x.2.2 j
        change (Ideal.Quotient.liftₐ V.ideal (MvPolynomial.aeval (R := ℂ) x.1) x.2.1)
          (hyp_imageMap V φ (Ideal.Quotient.mk (φ.image V).ideal f)) =
            hyp_imageEvaluation V φ K y hy (Ideal.Quotient.mk (φ.image V).ideal f)
        rw [hyp_imageMap_mk]
        simp only [hyp_imageEvaluation, Ideal.Quotient.liftₐ_apply,
          Ideal.Quotient.lift_mk]
        exact AlgHom.congr_fun he f }
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
      change h (algebraMap A B (Ideal.Quotient.mk (φ.image V).ideal (MvPolynomial.X j))) = y j
      rw [h.commutes]
      exact MvPolynomial.aeval_X y j
  · intro h
    apply AlgHom.ext
    intro b
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective b
    change (Ideal.Quotient.liftₐ V.ideal (MvPolynomial.aeval (R := ℂ) (point h)) _)
      (Ideal.Quotient.mk V.ideal f) = _
    rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk, hpoint]
    rfl
  · intro x
    apply Subtype.ext
    funext i
    change (Ideal.Quotient.liftₐ V.ideal (MvPolynomial.aeval (R := ℂ) x.1) x.2.1)
      (Ideal.Quotient.mk V.ideal (MvPolynomial.X i)) = x.1 i
    rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
    exact MvPolynomial.aeval_X x.1 i

/-- A singleton fiber over an injective generic field point forces
degree one on a nonempty principal open of the actual image. -/
theorem hyp_generic_degree_one {n m : ℕ} (V : AffineVariety n)
    (hV : V.IsIrreducible) (φ : AffineProjection n m) (hf : FiniteAffineProjection φ V)
    (K : Type) [Field K] [Algebra ℂ K] [IsAlgClosed K]
    (y : Fin m → K) (u : Fin n → K)
    (hufiber : affineFiberOver V φ y = {u})
    (hker : RingHom.ker (MvPolynomial.aeval (R := ℂ) u).toRingHom = V.ideal) :
    φ.GenericallyFiniteOfDegree V 1 := by
  have hu : u ∈ affineFiberOver V φ y := by rw [hufiber]; exact Set.mem_singleton u
  have heval : (MvPolynomial.aeval (R := ℂ) u).comp φ.pullback =
      MvPolynomial.aeval (R := ℂ) y := by
    ext j
    simpa only [AlgHom.comp_apply, MvPolynomial.aeval_X] using hu.2 j
  have hy : ∀ f ∈ (φ.image V).ideal, MvPolynomial.aeval y f = 0 := by
    intro f hf
    rw [← heval]
    exact hu.1 _ hf
  let A := Poly m ⧸ (φ.image V).ideal
  let B := Poly n ⧸ V.ideal
  letI : V.ideal.IsPrime := hV
  letI : (φ.image V).ideal.IsPrime := φ.image_irreducible V hV
  haveI : CharZero A := Algebra.charZero_of_charZero ℂ A
  letI : Algebra A B := (hyp_imageMap V φ).toRingHom.toAlgebra
  letI : Module A B := (hyp_imageMap V φ).toRingHom.toAlgebra.toModule
  letI : SMul A B := (hyp_imageMap V φ).toRingHom.toAlgebra.toSMul
  haveI : Module.Finite A B := hyp_imageMap_finite V φ hf
  haveI : Algebra.IsIntegral A B := ⟨(hyp_imageMap_finite V φ hf).to_isIntegral⟩
  haveI : Algebra.FiniteType A B := Module.Finite.finiteType B
  haveI : Algebra.IsAlgebraic A B := Algebra.IsIntegral.isAlgebraic
  haveI : Module.IsTorsionFree A B :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (hyp_imageMap_injective V φ)
  obtain ⟨g, hg, r, hr, hcount⟩ := algebraic_finiteType_field_hom_fibers A B
  letI : Algebra A K := (hyp_imageEvaluation V φ K y hy).toRingHom.toAlgebra
  letI : Module A K := (hyp_imageEvaluation V φ K y hy).toRingHom.toAlgebra.toModule
  letI : SMul A K := (hyp_imageEvaluation V φ K y hy).toRingHom.toAlgebra.toSMul
  have hinj : Function.Injective (hyp_imageEvaluation V φ K y hy) := by
    let e : B →ₐ[ℂ] K := Ideal.Quotient.liftₐ V.ideal (MvPolynomial.aeval (R := ℂ) u) hu.1
    have hei : Function.Injective e := by
      apply (injective_iff_map_eq_zero _).mpr
      intro b hb
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective b
      change MvPolynomial.aeval u f = 0 at hb
      have hf : f ∈ V.ideal := by rw [← hker]; exact hb
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hf
    have he : e.comp (hyp_imageMap V φ) = hyp_imageEvaluation V φ K y hy := by
      apply Ideal.Quotient.algHom_ext
      apply AlgHom.ext
      intro f
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
      rw [hyp_imageMap_mk]
      simp only [e, hyp_imageEvaluation, Ideal.Quotient.liftₐ_apply,
        Ideal.Quotient.lift_mk]
      exact AlgHom.congr_fun heval f
    rw [← he]
    exact hei.comp (hyp_imageMap_injective V φ)
  have hgK : algebraMap A K g ≠ 0 := by
    intro h
    rw [RingHom.algebraMap_toAlgebra] at h
    have hzero : hyp_imageEvaluation V φ K y hy g = 0 := h
    exact hg (hinj (hzero.trans (map_zero _).symm))
  have hrone : r = 1 := by
    have hc := (hcount K hgK).2
    let e := hyp_imageFiberAlgHomEquiv V φ K y hy
    have hcard : Nat.card (B →ₐ[A] K) = 1 := by
      rw [Nat.card_congr e]
      change (affineFiberOver V φ y).ncard = 1
      rw [hufiber, Set.ncard_singleton]
    exact hc.symm.trans hcard
  subst r
  obtain ⟨G, hG⟩ := Ideal.Quotient.mk_surjective g
  refine ⟨by decide, G, ?_, ?_⟩
  · intro hGmem
    exact hg (hG ▸ Ideal.Quotient.eq_zero_iff_mem.mpr hGmem)
  · intro z hz hGz
    letI : Algebra A ℂ := (hyp_imageEvaluation V φ ℂ z hz).toRingHom.toAlgebra
    have hgℂ : algebraMap A ℂ g ≠ 0 := by
      rw [← hG]
      exact hGz
    obtain ⟨hfin, hcard⟩ := hcount ℂ hgℂ
    let e := (hyp_imageFiberAlgHomEquiv V φ ℂ z hz).trans
      (Set.equivOfEq (affineFiberOver_complex V φ z))
    letI := hfin
    haveI : Finite (φ.fiber V z) := Finite.of_equiv _ e
    exact ⟨Set.toFinite _, (Nat.card_congr e.symm).trans hcard⟩

/-- Finite affine projections have closed complex-point images. -/
theorem hyp_finite_image_lift {n m : ℕ} (V : AffineVariety n)
    (φ : AffineProjection n m) (hf : FiniteAffineProjection φ V)
    (y : Point m) (hy : y ∈ (φ.image V).points) :
    ∃ p ∈ V.points, φ.apply p = y := by
  let A := Poly m ⧸ (φ.image V).ideal
  let B := Poly n ⧸ V.ideal
  let i := hyp_imageMap V φ
  let e := hyp_imageEvaluation V φ ℂ y hy
  letI : Algebra A B := i.toRingHom.toAlgebra
  letI : Module A B := i.toRingHom.toAlgebra.toModule
  letI : SMul A B := i.toRingHom.toAlgebra.toSMul
  haveI : Module.Finite A B := hyp_imageMap_finite V φ hf
  haveI : Algebra.IsIntegral A B := ⟨(hyp_imageMap_finite V φ hf).to_isIntegral⟩
  let P : Ideal A := RingHom.ker e.toRingHom
  have he : Function.Surjective e := fun c => ⟨algebraMap ℂ A c, e.commutes c⟩
  letI : P.IsMaximal := RingHom.ker_isMaximal_of_surjective e.toRingHom he
  have hkeri : RingHom.ker (algebraMap A B) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp (hyp_imageMap_injective V φ)
  obtain ⟨Q, hQ, hQA⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (R := A) (S := B) P
    (by rw [hkeri]; exact bot_le)
  letI : Q.IsMaximal := hQ
  let J : Ideal (Poly n) := Q.comap (Ideal.Quotient.mk V.ideal)
  have hJ : J.IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨p, hp⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal ℂ hJ
  have hJpoint : ∀ f ∈ J, MvPolynomial.eval p f = 0 := by
    intro f hf
    rw [hp, MvPolynomial.mem_vanishingIdeal_singleton_iff] at hf
    exact hf
  refine ⟨p, ?_, ?_⟩
  · intro f hf
    apply hJpoint f
    change Ideal.Quotient.mk V.ideal f ∈ Q
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hf]
    exact Q.zero_mem
  · funext j
    have hj : Ideal.Quotient.mk (φ.image V).ideal
        (MvPolynomial.X j - MvPolynomial.C (y j)) ∈ P := by
      change MvPolynomial.aeval y (MvPolynomial.X j - MvPolynomial.C (y j)) = 0
      simp
    rw [← hQA] at hj
    have hjJ : φ.pullback (MvPolynomial.X j) - MvPolynomial.C (y j) ∈ J := by
      change Ideal.Quotient.mk V.ideal _ ∈ Q
      change hyp_imageMap V φ (Ideal.Quotient.mk (φ.image V).ideal
        (MvPolynomial.X j - MvPolynomial.C (y j))) ∈ Q at hj
      rw [hyp_imageMap_mk] at hj
      simpa only [map_sub, AffineProjection.pullback, MvPolynomial.aeval_C,
        MvPolynomial.algebraMap_eq] using hj
    have hzero := hJpoint _ hjJ
    change MvPolynomial.aeval p (φ.pullback (MvPolynomial.X j) - MvPolynomial.C (y j)) = 0 at hzero
    simpa only [map_sub, MvPolynomial.aeval_C, Algebra.algebraMap_self_apply,
      φ.eval_pullback, MvPolynomial.aeval_X, sub_eq_zero] using hzero

def hyp_linearForm {n : ℕ} (c : Fin n → ℂ) : Point n →ₗ[ℂ] ℂ :=
  ∑ i, c i • LinearMap.proj i

theorem hyp_linearForm_apply {n : ℕ} (c : Fin n → ℂ) (p : Point n) :
    hyp_linearForm c p = ∑ i, c i * p i := by
  simp [hyp_linearForm]

theorem hyp_extended_head_eval {n k : ℕ} (φ : AffineProjection n k)
    (c : Fin n → ℂ) {K : Type*} [Field K] [Algebra ℂ K] (u : Fin n → K) :
    MvPolynomial.aeval u
      ((hyp_extend_projection φ (hyp_linearForm c)).pullback (MvPolynomial.X 0)) =
        ∑ i, algebraMap ℂ K (c i) * u i := by
  have hc (i : Fin n) : hyp_linearForm c (Pi.single i 1) = c i := by
    simp [hyp_linearForm_apply, Pi.single_apply]
  simp only [AffineProjection.pullback, MvPolynomial.aeval_X,
    hyp_extend_projection, Fin.cons_zero, MvPolynomial.C_0, add_zero,
    linearCoordinate, LinearMap.pi_apply, Fin.cons_zero, hc,
    map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X]

/-- The same complex linear coefficients separate a finite actual set
and a finite set of generic vectors in a complex field extension. -/
theorem hyp_simultaneous_linear_separation {n : ℕ} {K : Type*}
    [Field K] [Algebra ℂ K] (T : Finset (Point n)) (U : Finset (Fin n → K)) :
    ∃ c : Fin n → ℂ,
      Set.InjOn (hyp_linearForm c) T ∧
      Set.InjOn (fun u : Fin n → K => ∑ i, algebraMap ℂ K (c i) * u i) U := by
  let embed : Point n → (Fin n → K) := fun p i => algebraMap ℂ K (p i)
  have hembed : Function.Injective embed := by
    intro p q h
    funext i
    exact (algebraMap ℂ K).injective (congrFun h i)
  let W := T.image embed ∪ U
  let D := ((W ×ˢ W).filter (fun pq => pq.1 ≠ pq.2)).image (fun pq => pq.1 - pq.2)
  have hD : ∀ v ∈ D, v ≠ 0 := by
    intro v hv
    obtain ⟨⟨p, q⟩, hpq, rfl⟩ := Finset.mem_image.mp hv
    exact sub_ne_zero.mpr (Finset.mem_filter.mp hpq).2
  obtain ⟨c, hc⟩ := hyp_separating_coefficients (K := ℂ) D hD
  let L : (Fin n → K) → K := fun u => ∑ i, algebraMap ℂ K (c i) * u i
  have hL : Set.InjOn L W := by
    intro p hp q hq heq
    by_contra hne
    have hd : p - q ∈ D := Finset.mem_image.mpr
      ⟨(p, q), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp, hq⟩, hne⟩, rfl⟩
    apply hc (p-q) hd
    simpa only [L, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, heq, sub_self]
  refine ⟨c, ?_, ?_⟩
  · intro p hp q hq heq
    apply hembed
    apply hL (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩))
      (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨q, hq, rfl⟩))
    change (∑ i, algebraMap ℂ K (c i) * algebraMap ℂ K (p i)) =
      ∑ i, algebraMap ℂ K (c i) * algebraMap ℂ K (q i)
    simpa only [hyp_linearForm_apply, map_sum, map_mul] using congrArg (algebraMap ℂ K) heq
  · exact hL.mono (by intro p hp; exact Finset.mem_union_right _ hp)

/-- Extend a finite normalization so that its generic fiber and each
specified actual fiber are separated by the new coordinate. -/
theorem hyp_affine_birational_projection {n k : ℕ} (V : AffineVariety n)
    (hV : V.IsIrreducible) (hdim : V.dimension = k) (hk : k ≤ n)
    (S : Finset (Point n)) (hS : ∀ p ∈ S, p ∈ V.points)
    (x : Point n) (hx : x ∉ V.points) :
    ∃ φ : AffineProjection n (k+1), FiniteAffineProjection φ V ∧
      φ.GenericallyFiniteOfDegree V 1 ∧ φ.apply x ∉ (φ.image V).points ∧
      ∀ p ∈ S, φ.fiber V (φ.apply p) = {p} := by
  let F : AffineFamily.Family n := {V}
  have hF : AffineFamily.IsPure F k := by
    intro W hW
    rw [Finset.mem_singleton.mp hW]
    exact ⟨hV, hdim⟩
  obtain ⟨ψ, hψ, hnorm⟩ := poly_hilbert_normalization F k hk hF
  obtain ⟨hfinite, r, hdegree, hgeneric⟩ := hnorm V (Finset.mem_singleton_self _)
  let K := GenericBaseField k
  let t := genericBasePoint k
  have ht := genericBasePoint_independent k
  obtain ⟨hUfinite, hUcount⟩ := affineFiberOver_generic_count V hV hdim ψ hfinite
    hgeneric K t ht
  let U := hUfinite.toFinset
  have hUcard : U.card = r := by
    rw [← hUcount]
    exact (Set.ncard_eq_toFinset_card _ hUfinite).symm
  obtain ⟨u, hu⟩ := Finset.card_pos.mp (by rw [hUcard]; exact hgeneric.1)
  have hu' : u ∈ affineFiberOver V ψ t := hUfinite.mem_toFinset.mp hu
  let actual (p : Point n) : Finset (Point n) :=
    (hyp_finite_affine_fiber V ψ hfinite (ψ.apply p)).toFinset
  let T := insert x (actual x ∪ S.biUnion actual)
  have hactual (p q : Point n) : q ∈ actual p ↔ q ∈ ψ.fiber V (ψ.apply p) :=
    (hyp_finite_affine_fiber V ψ hfinite (ψ.apply p)).mem_toFinset
  have hxT : x ∈ T := Finset.mem_insert_self _ _
  have hfiberT (p : Point n) (hp : p ∈ S) (q : Point n)
      (hq : q ∈ ψ.fiber V (ψ.apply p)) : q ∈ T := by
    apply Finset.mem_insert_of_mem
    apply Finset.mem_union_right
    exact Finset.mem_biUnion.mpr ⟨p, hp, (hactual p q).mpr hq⟩
  obtain ⟨c, hsepT, hsepU⟩ := hyp_simultaneous_linear_separation T U
  let ℓ := hyp_linearForm c
  let φ := hyp_extend_projection ψ ℓ
  have hφfinite : FiniteAffineProjection φ V :=
    hyp_extend_projection_finite V ψ ℓ hfinite
  let y : Fin (k+1) → K := Fin.cons (∑ i, algebraMap ℂ K (c i) * u i) t
  have hφfiber : affineFiberOver V φ y = {u} := by
    ext v
    constructor
    · intro hv
      have hvbase : v ∈ affineFiberOver V ψ t := by
        refine ⟨hv.1, ?_⟩
        intro j
        have hh := hv.2 j.succ
        simpa only [φ, hyp_extend_projection_pullback_succ, y, Fin.cons_succ] using hh
      have hvU : v ∈ U := hUfinite.mem_toFinset.mpr hvbase
      have hh := hv.2 (0 : Fin (k+1))
      have heq : (∑ i, algebraMap ℂ K (c i) * v i) =
          ∑ i, algebraMap ℂ K (c i) * u i := by
        simpa only [φ, ℓ, hyp_extended_head_eval, y, Fin.cons_zero] using hh
      exact Set.mem_singleton_iff.mpr (hsepU hvU hu heq)
    · intro hv
      have hvu : v = u := Set.mem_singleton_iff.mp hv
      subst v
      refine ⟨hu'.1, ?_⟩
      intro j
      cases j using Fin.cases with
      | zero => exact hyp_extended_head_eval ψ c u
      | succ j =>
        simpa only [φ, hyp_extend_projection_pullback_succ, y, Fin.cons_succ] using hu'.2 j
  have hker := affineFiberOver_eval_ker V hV ψ hfinite K t ht ⟨u, hu'⟩
  have hφgeneric := hyp_generic_degree_one V hV φ hφfinite K y u hφfiber hker
  have hcoords (p q : Point n) (heq : φ.apply p = φ.apply q) :
      ℓ p = ℓ q ∧ ψ.apply p = ψ.apply q := by
    rw [hyp_extend_projection_apply, hyp_extend_projection_apply] at heq
    exact ⟨congrFun heq 0, funext (fun j => congrFun heq j.succ)⟩
  refine ⟨φ, hφfinite, hφgeneric, ?_, ?_⟩
  · intro hximage
    obtain ⟨p, hp, heq⟩ := hyp_finite_image_lift V φ hφfinite (φ.apply x) hximage
    obtain ⟨hℓ, hψ⟩ := hcoords p x heq
    have hpT : p ∈ T := Finset.mem_insert_of_mem (Finset.mem_union_left _
      ((hactual x p).mpr ⟨hp, hψ⟩))
    exact hx (hsepT hpT hxT hℓ ▸ hp)
  · intro p hp
    ext q
    constructor
    · rintro ⟨hq, heq⟩
      obtain ⟨hℓ, hψ⟩ := hcoords q p heq
      have hqT := hfiberT p hp q ⟨hq, hψ⟩
      have hpT := hfiberT p hp p ⟨hS p hp, rfl⟩
      exact Set.mem_singleton_iff.mpr (hsepT hqT hpT hℓ)
    · intro hq
      have hqp : q = p := Set.mem_singleton_iff.mp hq
      subst q
      exact ⟨hS p hp, rfl⟩

theorem hyp_finite_image_dimension {n m : ℕ} (V : AffineVariety n)
    (hV : V.IsIrreducible) (φ : AffineProjection n m) (hf : FiniteAffineProjection φ V) :
    (φ.image V).dimension = V.dimension := by
  have hi := OAI.PiExponentJets.W24.ringKrullDim_eq_of_integral_injective
    (hyp_imageMap V φ).toRingHom (hyp_imageMap_injective V φ)
    (hyp_imageMap_finite V φ hf).to_isIntegral
  rw [prime_coordinate_krull_dimension V.ideal hV,
    prime_coordinate_krull_dimension (φ.image V).ideal (φ.image_irreducible V hV)] at hi
  exact_mod_cast hi.symm

/-- A codimension-one prime in a polynomial ring is principal. -/
theorem hyp_codimension_one_principal {k : ℕ} (P : Ideal (Poly (k+1)))
    (hP : P.IsPrime) (hdim : OAI.QuarticPowerFree.affineDimension P = k) :
    ∃ f : Poly (k+1), f ≠ 0 ∧ P = Ideal.span {f} := by
  letI : P.IsPrime := hP
  have hsum := affineDimension_add_height (Q := P)
  rw [hdim] at hsum
  have hheight : P.height = 1 := by
    have hne : P.height ≠ ⊤ := by
      intro htop
      rw [htop, add_top] at hsum
      exact ENat.top_ne_natCast (k+1) hsum
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hne
    rw [← hm, ← Nat.cast_add] at hsum
    have hnat : k+m = k+1 := Nat.cast_injective hsum
    have hm1 : m = 1 := by omega
    rw [← hm, hm1, Nat.cast_one]
  obtain ⟨f, hf⟩ := UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hheight
  refine ⟨f, ?_, hf⟩
  intro hfzero
  have hbot : P = ⊥ := by rw [hf, hfzero, Ideal.span_singleton_eq_bot]
  have hheight0 : P.height = 0 := by rw [hbot, Ideal.height_eq_zero_iff_eq_bot.mpr rfl]
  rw [hheight] at hheight0
  exact one_ne_zero hheight0

/-- The equation of a finite affine hypersurface projection has degree
at most the degree of the source, by OAI's projection Hilbert bound. -/
theorem hyp_affine_projection_equation {n k : ℕ} (V : AffineVariety n)
    (hV : V.IsIrreducible) (hdim : V.dimension = k)
    (φ : AffineProjection n (k+1)) (hf : FiniteAffineProjection φ V) :
    ∃ f : Poly (k+1), f ≠ 0 ∧ (φ.image V).ideal = Ideal.span {f} ∧
      (f.totalDegree : ℚ) ≤ V.degree := by
  have hYdim : (φ.image V).dimension = k :=
    (hyp_finite_image_dimension V hV φ hf).trans hdim
  obtain ⟨f, hfzero, hprincipal⟩ := hyp_codimension_one_principal
    (φ.image V).ideal (φ.image_irreducible V hV) hYdim
  refine ⟨f, hfzero, hprincipal, ?_⟩
  have hbound := OAI.QuarticPowerFree.polynomial_projection_equation_degree_bound
    V.ideal V.hilbertPolynomial (by change V.dimension ≤ k; rw [hdim]) V.hilbert_eventually
    (fun j => φ.pullback (MvPolynomial.X j)) 1 (by decide) (projection_base_degree φ)
    f hfzero (fun g => by
      have hpb : MvPolynomial.aeval (fun j => φ.pullback (MvPolynomial.X j)) = φ.pullback := by
        ext j
        simp
      rw [hpb, Ideal.Quotient.eq_zero_iff_mem]
      change g ∈ (φ.image V).ideal ↔ f ∣ g
      rw [hprincipal, Ideal.mem_span_singleton])
  have hdim' : OAI.QuarticPowerFree.affineDimension V.ideal = k := hdim
  simpa only [Nat.cast_one, one_pow, mul_one, one_mul, AffineVariety.degree,
    AffineVariety.hilbertPolynomial,
    OAI.QuarticPowerFree.affineDegree, hdim', mul_comm] using hbound

/-- An affine polynomial substitution does not increase total degree. -/
theorem hyp_affine_pullback_degree {n m : ℕ} (φ : AffineProjection n m)
    (f : Poly m) : (φ.pullback f).totalDegree ≤ f.totalDegree := by
  have hpullback : MvPolynomial.aeval (fun j => φ.pullback (MvPolynomial.X j)) = φ.pullback := by
    ext j
    simp
  have h := OAI.QuarticPowerFree.totalDegree_linear_substitute_le
    (fun j => φ.pullback (MvPolynomial.X j)) (projection_base_degree φ) f
  have h' : (MvPolynomial.aeval (fun j => φ.pullback (MvPolynomial.X j)) f).totalDegree ≤
      f.totalDegree := by
    simpa only [MvPolynomial.aeval_def, MvPolynomial.algebraMap_eq] using h
  rw [hpullback] at h'
  exact h'

/-- Polynomial pullback preserves membership in point-ideal powers. -/
theorem hyp_affine_pullback_order {n m : ℕ} (φ : AffineProjection n m)
    (f : Poly m) (p : Point n) (r : ℕ)
    (h : OrderAtLeast f (φ.apply p) r) : OrderAtLeast (φ.pullback f) p r := by
  have hmap : (pointIdealOver (φ.apply p)).map φ.pullback.toRingHom ≤ pointIdealOver p := by
    rw [Ideal.map_le_iff_le_comap]
    intro g hg
    change φ.pullback g ∈ pointIdealOver p
    rw [pointIdealOver, MvPolynomial.mem_vanishingIdeal_singleton_iff]
    change MvPolynomial.aeval p (φ.pullback g) = 0
    rw [φ.eval_pullback]
    exact (MvPolynomial.mem_vanishingIdeal_singleton_iff _ g).mp hg
  have hh := Ideal.mem_map_of_mem φ.pullback.toRingHom h
  rw [Ideal.map_pow] at hh
  exact (pow_le_pow_left' hmap r) hh

/-- Artin–Rees controls division by a regular element for any ideal. -/
theorem hyp_colon_shift {R : Type*} [CommRing R] [IsNoetherianRing R]
    (J : Ideal R) (x : R) (hx : x ∈ nonZeroDivisors R) :
    ∃ c : ℕ, ∀ t ≥ c, (J ^ t).colon {x} ≤ J ^ (t-c) := by
  obtain ⟨c, hc⟩ := J.exists_pow_inf_eq_pow_smul
    (↑(Ideal.span {x}) : Submodule R R)
  refine ⟨c, fun t ht r hr => ?_⟩
  have hrx : r * x ∈ J ^ t := (Submodule.mem_colon_singleton).mp hr
  have htop : ((J ^ t : Ideal R) : Submodule R R) ≤ J ^ t • (⊤ : Submodule R R) := by
    intro a ha
    have hh := Submodule.smul_mem_smul ha
      (Submodule.mem_top : (1 : R) ∈ (⊤ : Submodule R R))
    simpa using hh
  have hinter : r * x ∈ J ^ t • (⊤ : Submodule R R) ⊓
      (↑(Ideal.span {x}) : Submodule R R) :=
    ⟨htop hrx, Ideal.mem_span_singleton'.mpr ⟨r, rfl⟩⟩
  rw [hc t ht] at hinter
  have hle : J ^ (t-c) • (J ^ c • (⊤ : Submodule R R) ⊓
      (↑(Ideal.span {x}) : Submodule R R)) ≤
      ((J ^ (t-c) * Ideal.span {x} : Ideal R) : Submodule R R) := by
    apply (smul_mono_right _ inf_le_right).trans
    apply Submodule.smul_le.mpr
    intro a ha b hb
    exact Ideal.mul_mem_mul ha hb
  obtain ⟨s, hs, he⟩ := Ideal.mem_mul_span_singleton.mp (hle hinter)
  have hrs : r = s := by
    apply sub_eq_zero.mp
    apply (mem_nonZeroDivisors_iff_right.mp hx)
    rw [sub_mul, he, sub_self]
  rwa [hrs]

/-- A conductor identifies multiplication into the source of an injective map. -/
def hyp_conductorMap {K A B : Type*} [Field K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] (f : A →ₐ[K] B) (hf : Function.Injective f)
    (x : B) (hx : ∀ b : B, ∃ a : A, f a = x*b) : B →ₗ[K] A where
  toFun b := (hx b).choose
  map_add' b d := hf (by
    rw [map_add, (hx (b+d)).choose_spec, (hx b).choose_spec, (hx d).choose_spec,
      mul_add])
  map_smul' k b := hf (by
    rw [map_smul, (hx (k • b)).choose_spec, (hx b).choose_spec]
    simp [Algebra.smul_def, mul_left_comm])

theorem hyp_conductorMap_spec {K A B : Type*} [Field K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] (f : A →ₐ[K] B) (hf : Function.Injective f)
    (x : B) (hx : ∀ b : B, ∃ a : A, f a = x*b) (b : B) :
    f (hyp_conductorMap f hf x hx b) = x*b := (hx b).choose_spec

/-- A conductor and Artin–Rees bound the source point jets by shifted target jets. -/
theorem hyp_conductor_length_bound {K A B : Type*} [Field K]
    [CommRing A] [CommRing B] [Algebra K A] [Algebra K B] [IsNoetherianRing B]
    (f : A →ₐ[K] B) (hf : Function.Injective f) (M : Ideal A) (N : Ideal B)
    (hMN : M.map f.toRingHom ≤ N) (x : B) (hxreg : x ∈ nonZeroDivisors B)
    (hx : ∀ b : B, ∃ a : A, f a = x*b) :
    ∃ c : ℕ, ∀ t ≥ c,
      Module.length K (B ⧸ N ^ (t-c)) ≤ Module.length K (A ⧸ M ^ t) := by
  obtain ⟨c, hc⟩ := hyp_colon_shift N x hxreg
  refine ⟨c, fun t ht => ?_⟩
  let μ : B →ₗ[K] A ⧸ M ^ t :=
    (Ideal.Quotient.mkₐ K (M ^ t)).toLinearMap.comp (hyp_conductorMap f hf x hx)
  have hker : LinearMap.ker μ ≤ (N ^ (t-c)).restrictScalars K := by
    intro b hb
    have hμ : hyp_conductorMap f hf x hx b ∈ M ^ t :=
      Ideal.Quotient.eq_zero_iff_mem.mp hb
    have hxb : x*b ∈ N ^ t := by
      have hh := Ideal.mem_map_of_mem f.toRingHom hμ
      change f (hyp_conductorMap f hf x hx b) ∈ (M ^ t).map f.toRingHom at hh
      rw [hyp_conductorMap_spec, Ideal.map_pow] at hh
      exact (pow_le_pow_left' hMN t) hh
    exact hc t ht ((Submodule.mem_colon_singleton).mpr (by simpa [mul_comm] using hxb))
  calc Module.length K (B ⧸ N ^ (t-c))
      ≤ Module.length K (B ⧸ LinearMap.ker μ) :=
        Module.length_le_of_surjective (Submodule.factor hker) (Submodule.factor_surjective hker)
    _ = Module.length K (LinearMap.range μ) := μ.quotKerEquivRange.length_eq
    _ ≤ Module.length K (A ⧸ M ^ t) :=
        Module.length_le_of_injective (LinearMap.range μ).subtype (Submodule.subtype_injective _)

/-- A quotient supported at one point is unchanged by point localization. -/
def hyp_pointQuotientEquiv {n : ℕ} (p : Point n) (I : Ideal (Poly n))
    (t : ℕ) (ht : pointIdeal p ^ t ≤ I) :
    (PointLocalRing p ⧸ localizedIdeal I p) ≃ₐ[ℂ] (Poly n ⧸ I) := by
  let j : Poly n →ₐ[ℂ] (Poly n ⧸ I) := Ideal.Quotient.mkₐ ℂ I
  have hu (s : (pointIdeal p).primeCompl) : IsUnit (j s) := by
    have hh := Ideal.Quotient.isUnit_mk_pow_of_notMem (pointIdeal p) (n := t)
      (Ideal.mem_primeCompl_iff.mp s.property)
    exact hh.map (Ideal.Quotient.factor ht)
  let l : PointLocalRing p →ₐ[ℂ] (Poly n ⧸ I) :=
    IsLocalization.liftAlgHom (f := j) hu
  have hl (f : Poly n) : l (algebraMap (Poly n) (PointLocalRing p) f) = j f :=
    IsLocalization.lift_eq hu f
  have hI : localizedIdeal I p ≤ RingHom.ker l.toRingHom := by
    rw [localizedIdeal, Ideal.map_le_iff_le_comap]
    intro f hf
    change l (algebraMap (Poly n) (PointLocalRing p) f) = 0
    rw [hl]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hf
  let a : (PointLocalRing p ⧸ localizedIdeal I p) →ₐ[ℂ] (Poly n ⧸ I) :=
    Ideal.Quotient.liftₐ _ l hI
  let b : (Poly n ⧸ I) →ₐ[ℂ] (PointLocalRing p ⧸ localizedIdeal I p) :=
    Ideal.Quotient.liftₐ I
      ((Ideal.Quotient.mkₐ ℂ _).comp (IsScalarTower.toAlgHom ℂ (Poly n) (PointLocalRing p)))
      (fun f hf => Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hf))
  refine AlgEquiv.ofAlgHom a b ?_ ?_
  · apply Ideal.Quotient.algHom_ext
    apply AlgHom.ext
    intro f
    change l (algebraMap (Poly n) (PointLocalRing p) f) = j f
    exact hl f
  · apply Ideal.Quotient.algHom_ext
    apply IsLocalization.algHom_ext (W := (pointIdeal p).primeCompl)
    apply AlgHom.ext
    intro f
    change b (l (algebraMap (Poly n) (PointLocalRing p) f)) = _
    rw [hl]
    rfl

/-- Global coordinate point jets give the original local Hilbert lengths. -/
theorem hyp_coordinate_jet_length {n : ℕ} (V : AffineVariety n)
    (p : Point n) (t : ℕ) :
    Module.length ℂ ((Poly n ⧸ V.ideal) ⧸
      ((pointIdeal p).map (Ideal.Quotient.mk V.ideal)) ^ (t+1)) =
      V.localHilbert p t := by
  let J := pointIdeal p ^ (t+1)
  let e : ((Poly n ⧸ V.ideal) ⧸ J.map (Ideal.Quotient.mk V.ideal)) ≃ₐ[ℂ]
      (Poly n ⧸ V.ideal ⊔ J) :=
    { __ := DoubleQuot.quotQuotEquivQuotSup V.ideal J
      commutes' := by intro c; rfl }
  rw [← Ideal.map_pow]
  change Module.length ℂ ((Poly n ⧸ V.ideal) ⧸ J.map _) = _
  rw [e.toLinearEquiv.length_eq]
  unfold AffineVariety.localHilbert localLengthAt
  rw [point_local_length_eq_complex_length p]
  exact (hyp_pointQuotientEquiv p (V.ideal ⊔ J) (t+1) le_sup_right).toLinearEquiv.length_eq.symm

/-- Finite generation makes a common denominator from individual denominators. -/
theorem hyp_common_denominator (A B : Type*) [CommRing A] [IsDomain A]
    [CommRing B] [Algebra A B] [Module.Finite A B] (g : A) (hg : g ≠ 0)
    (h : ∀ b : B, ∃ k : ℕ, ∃ a : A, algebraMap A B a = g ^ k • b) :
    ∃ a : A, a ≠ 0 ∧ ∀ b : B, ∃ r : A, algebraMap A B r = a • b := by
  obtain ⟨d, v, hv⟩ := Module.Finite.exists_fin (R := A) (M := B)
  choose k a ha using fun i : Fin d => h (v i)
  let N : ℕ := ∑ i : Fin d, k i
  have hk (i : Fin d) : k i ≤ N :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (k j)) (Finset.mem_univ i)
  refine ⟨g ^ N, pow_ne_zero _ hg, fun b => ?_⟩
  have hb : b ∈ Submodule.span A (Set.range v) := hv.symm ▸ Submodule.mem_top
  induction hb using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    refine ⟨g ^ (N-k i) * a i, ?_⟩
    rw [map_mul, ha i, Algebra.smul_def, ← mul_assoc, ← map_mul,
      ← pow_add, Nat.sub_add_cancel (hk i)]
    rw [Algebra.smul_def]
  | zero => exact ⟨0, by simp⟩
  | add y z hy hz iy iz =>
    obtain ⟨r, hr⟩ := iy
    obtain ⟨s, hs⟩ := iz
    exact ⟨r+s, by rw [map_add, hr, hs, smul_add]⟩
  | smul c y hy iy =>
    obtain ⟨r, hr⟩ := iy
    refine ⟨c*r, ?_⟩
    rw [map_mul, hr, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def]
    ring

/-- A rank-one etale principal open supplies a global conductor.
The abstract rings keep localization instances independent of polynomial quotients. -/
theorem hyp_conductor_of_etale_point (A B : Type*) [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B]
    [Module.IsTorsionFree A B] (g : A) (hg : g ≠ 0)
    (hf : Module.Finite (Localization (Submonoid.powers g))
      (Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers g))))
    (he : Algebra.Etale (Localization (Submonoid.powers g))
      (Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers g))))
    (e : A →+* ℂ) (heg : e g ≠ 0)
    (hone : letI : Algebra A ℂ := e.toAlgebra; Nat.card (B →ₐ[A] ℂ) = 1) :
    ∃ x : B, x ≠ 0 ∧ ∀ b : B, ∃ a : A, algebraMap A B a = x*b := by
  let Ag := Localization (Submonoid.powers g)
  let Bg := Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers g))
  have hM : Submonoid.powers g ≤ nonZeroDivisors A :=
    Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero hg)
  have hMB : Algebra.algebraMapSubmonoid B (Submonoid.powers g) ≤ nonZeroDivisors B :=
    Submonoid.map_le_of_le_comap _ (hM.trans
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (FaithfulSMul.algebraMap_injective A B)))
  haveI : IsDomain Ag := IsLocalization.isDomain_of_le_nonZeroDivisors Ag hM
  haveI : IsDomain Bg := IsLocalization.isDomain_of_le_nonZeroDivisors Bg hMB
  haveI : Module.IsTorsionFree Ag Bg := Module.IsTorsionFree.of_isLocalization A B hM
  haveI : IsLocalization.Away (algebraMap A B g) Bg := by
    change IsLocalization (Submonoid.powers (algebraMap A B g)) Bg
    rw [show Submonoid.powers (algebraMap A B g) =
      Algebra.algebraMapSubmonoid B (Submonoid.powers g) by
      simp [Algebra.algebraMapSubmonoid, Submonoid.map_powers]]
    infer_instance
  haveI : Module.Finite Ag Bg := hf
  haveI : Algebra.Etale Ag Bg := he
  letI : Algebra A ℂ := e.toAlgebra
  letI : Module A ℂ := e.toAlgebra.toModule
  letI : SMul A ℂ := e.toAlgebra.toSMul
  let hu : IsUnit (algebraMap A ℂ g) := isUnit_iff_ne_zero.mpr heg
  letI : Algebra Ag ℂ := (IsLocalization.Away.lift (S := Ag) g hu).toAlgebra
  haveI : IsScalarTower A Ag ℂ := IsScalarTower.of_algebraMap_eq fun a =>
    (IsLocalization.Away.lift_eq g hu a).symm
  obtain ⟨_, _, hcard⟩ := finite_etale_domain_field_hom_count Ag Bg ℂ
  have hrank : Module.finrank Ag Bg = 1 := by
    rw [← hcard, Nat.card_congr (localized_base_field_hom_equiv A B Ag Bg ℂ g heg)]
    exact hone
  have hsurj : Function.Surjective (algebraMap Ag Bg) := by
    apply Module.algebraMap_surjective_of_rankAtStalk_le_one
    intro q
    rw [Module.rankAtStalk_eq, Ideal.finrank_fiber_eq_finrank, hrank]
  have hdenom (b : B) : ∃ k : ℕ, ∃ a : A, algebraMap A B a = g ^ k • b := by
    obtain ⟨u, hu⟩ := hsurj (algebraMap B Bg b)
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers g) u
    obtain ⟨k, hk⟩ := s.property
    refine ⟨k, a, ?_⟩
    apply IsLocalization.injective Bg hMB
    have hh := congrArg (algebraMap Ag Bg) hs
    simp only [map_mul, ← IsScalarTower.algebraMap_apply, hu] at hh
    simpa only [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply A B Bg,
      hk, mul_comm] using hh.symm
  obtain ⟨a, ha, hcond⟩ := hyp_common_denominator A B g hg hdenom
  refine ⟨algebraMap A B a, ?_, ?_⟩
  · exact fun h => ha ((FaithfulSMul.algebraMap_injective A B) (h.trans (map_zero _).symm))
  · intro b
    obtain ⟨r, hr⟩ := hcond b
    exact ⟨r, by simpa only [Algebra.smul_def] using hr⟩

/-- Geometric degree one supplies a nonzero global conductor. -/
theorem hyp_birational_conductor {n m : ℕ} (V : AffineVariety n)
    (hV : V.IsIrreducible) (φ : AffineProjection n m)
    (hf : FiniteAffineProjection φ V) (hbir : φ.GenericallyFiniteOfDegree V 1) :
    ∃ x : (Poly n ⧸ V.ideal), x ≠ 0 ∧
      ∀ b : (Poly n ⧸ V.ideal), ∃ a : (Poly m ⧸ (φ.image V).ideal),
        hyp_imageMap V φ a = x*b := by
  let A := Poly m ⧸ (φ.image V).ideal
  let B := Poly n ⧸ V.ideal
  letI : V.ideal.IsPrime := hV
  letI : (φ.image V).ideal.IsPrime := φ.image_irreducible V hV
  haveI : CharZero A := Algebra.charZero_of_charZero ℂ A
  letI : Algebra A B := (hyp_imageMap V φ).toRingHom.toAlgebra
  letI : Module A B := (hyp_imageMap V φ).toRingHom.toAlgebra.toModule
  letI : SMul A B := (hyp_imageMap V φ).toRingHom.toAlgebra.toSMul
  haveI : Module.Finite A B := hyp_imageMap_finite V φ hf
  haveI : Algebra.IsIntegral A B := ⟨(hyp_imageMap_finite V φ hf).to_isIntegral⟩
  haveI : Algebra.FiniteType A B := Module.Finite.finiteType B
  haveI : Algebra.IsAlgebraic A B := Algebra.IsIntegral.isAlgebraic
  haveI : Module.IsTorsionFree A B :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (hyp_imageMap_injective V φ)
  obtain ⟨g, hg, hfg, heg⟩ := algebraic_finiteType_finite_etale_base_open A B
  obtain ⟨G, hG⟩ := Ideal.Quotient.mk_surjective g
  obtain ⟨_, H, hH, hcount⟩ := hbir
  have hGnot : G ∉ (φ.image V).ideal := by
    intro h
    exact hg (hG ▸ Ideal.Quotient.eq_zero_iff_mem.mpr h)
  have hGH : G*H ∉ (φ.image V).ideal := fun h =>
    ((φ.image_irreducible V hV).mem_or_mem h).elim hGnot hH
  rw [← AffineVariety.vanishingIdeal_points, MvPolynomial.mem_vanishingIdeal_iff] at hGH
  push Not at hGH
  obtain ⟨y, hy, hyGH⟩ := hGH
  have hyG : MvPolynomial.aeval y G ≠ 0 := fun h => hyGH (by simp [map_mul, h])
  have hyH : MvPolynomial.aeval y H ≠ 0 := fun h => hyGH (by simp [map_mul, h])
  let e : A →ₐ[ℂ] ℂ := hyp_imageEvaluation V φ ℂ y hy
  have hegpoint : e g ≠ 0 := by rw [← hG]; exact hyG
  have hone : letI : Algebra A ℂ := e.toRingHom.toAlgebra;
      Nat.card (B →ₐ[A] ℂ) = 1 := by
    letI : Algebra A ℂ := e.toRingHom.toAlgebra
    letI : Module A ℂ := e.toRingHom.toAlgebra.toModule
    letI : SMul A ℂ := e.toRingHom.toAlgebra.toSMul
    let ep := (hyp_imageFiberAlgHomEquiv V φ ℂ y hy).trans
      (Set.equivOfEq (affineFiberOver_complex V φ y))
    rw [Nat.card_congr ep]
    exact (hcount y hy hyH).2
  exact hyp_conductor_of_etale_point A B g hg hfg heg e.toRingHom hegpoint hone

/-- The conductor bounds the original local Hilbert function by a fixed shift. -/
theorem hyp_projection_localHilbert_bound {n m : ℕ} (V : AffineVariety n)
    (hV : V.IsIrreducible) (φ : AffineProjection n m)
    (hf : FiniteAffineProjection φ V) (hbir : φ.GenericallyFiniteOfDegree V 1)
    (p : Point n) :
    ∃ c : ℕ, ∀ t : ℕ, V.localHilbert p t ≤ (φ.image V).localHilbert (φ.apply p) (t+c) := by
  let A := Poly m ⧸ (φ.image V).ideal
  let B := Poly n ⧸ V.ideal
  letI : V.ideal.IsPrime := hV
  let M : Ideal A := (pointIdeal (φ.apply p)).map (Ideal.Quotient.mk (φ.image V).ideal)
  let N : Ideal B := (pointIdeal p).map (Ideal.Quotient.mk V.ideal)
  let f : A →ₐ[ℂ] B := hyp_imageMap V φ
  have hMN : M.map f.toRingHom ≤ N := by
    rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
    intro F hF
    change Ideal.Quotient.mk V.ideal (φ.pullback F) ∈ N
    apply Ideal.mem_map_of_mem
    rw [pointIdeal, MvPolynomial.mem_vanishingIdeal_singleton_iff, φ.eval_pullback]
    exact (MvPolynomial.mem_vanishingIdeal_singleton_iff _ F).mp hF
  obtain ⟨x, hx, hcond⟩ := hyp_birational_conductor V hV φ hf hbir
  obtain ⟨c, hc⟩ := hyp_conductor_length_bound f (hyp_imageMap_injective V φ)
    M N hMN x (mem_nonZeroDivisors_of_ne_zero hx) hcond
  refine ⟨c, fun t => ?_⟩
  have hh := hc (t+c+1) (by omega)
  have hsub : t+c+1-c = t+1 := by omega
  rw [hsub] at hh
  change Module.length ℂ ((Poly n ⧸ V.ideal) ⧸
    ((pointIdeal p).map (Ideal.Quotient.mk V.ideal)) ^ (t+1)) ≤
    Module.length ℂ ((Poly m ⧸ (φ.image V).ideal) ⧸
      ((pointIdeal (φ.apply p)).map (Ideal.Quotient.mk (φ.image V).ideal)) ^ ((t+c)+1)) at hh
  simpa only [hyp_coordinate_jet_length] using hh

/-- A shift of local Hilbert lengths preserves their leading coefficient. -/
theorem hyp_multiplicity_le_of_shift {n m : ℕ} (V : AffineVariety n)
    (p : Point n) (W : AffineVariety m) (q : Point m)
    (hd : V.localDimension p = W.localDimension q) (c : ℕ)
    (h : ∀ t : ℕ, V.localHilbert p t ≤ W.localHilbert q (t+c)) :
    V.multiplicity p ≤ W.multiplicity q := by
  let P := V.localHilbertPolynomial p
  let Q := W.localHilbertPolynomial q
  let S : Polynomial ℚ := Q.comp (Polynomial.X + Polynomial.C (c : ℚ))
  have hdeg : P.natDegree = Q.natDegree := hd
  have hSdeg : S.natDegree = Q.natDegree := by
    rw [Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one]
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (localHilbertPolynomial_eventually V p)
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp (localHilbertPolynomial_eventually W q)
  have heval : ∀ᶠ t : ℕ in Filter.atTop, P.eval (t : ℚ) ≤ S.eval (t : ℚ) := by
    apply Filter.eventually_atTop.mpr
    refine ⟨max N₀ N₁, fun t ht => ?_⟩
    have hP := hN₀ t (le_trans (Nat.le_max_left _ _) ht)
    have hQ := hN₁ (t+c) (by omega)
    have hfinite : W.localHilbert q (t+c) ≠ ⊤ := by
      obtain ⟨a, ha, _⟩ := localHilbert_finite_value W q (t+c)
      rw [ha]
      exact ENat.natCast_ne_top a
    have hh : ((V.localHilbert p t).toNat : ℚ) ≤ ((W.localHilbert q (t+c)).toNat : ℚ) := by
      exact_mod_cast ENat.toNat_le_toNat (h t) hfinite
    change (V.localHilbertPolynomial p).eval (t : ℚ) ≤ _
    rw [hP]
    change _ ≤ (Q.comp (Polynomial.X + Polynomial.C (c : ℚ))).eval (t : ℚ)
    rw [Polynomial.eval_comp]
    simpa [Q, Nat.cast_add] using hh.trans_eq hQ.symm
  have hcoeff : P.coeff Q.natDegree ≤ S.coeff Q.natDegree :=
    OAI.QuarticPowerFree.coeff_le_of_eventually_nat_eval_le P S Q.natDegree
      hdeg.le hSdeg.le heval
  have hScoeff : S.coeff Q.natDegree = Q.coeff Q.natDegree := by
    calc S.coeff Q.natDegree = S.leadingCoeff := by
          rw [← hSdeg, Polynomial.coeff_natDegree]
      _ = Q.leadingCoeff := by
          rw [Polynomial.leadingCoeff_comp (by rw [Polynomial.natDegree_X_add_C]; norm_num),
            Polynomial.leadingCoeff_X_add_C, one_pow, mul_one]
      _ = Q.coeff Q.natDegree := Polynomial.coeff_natDegree.symm
  rw [hScoeff] at hcoeff
  unfold AffineVariety.multiplicity
  rw [hd]
  apply mul_le_mul_of_nonneg_left
  · exact hcoeff
  · positivity

end
end DistinctDistances.TrackA
