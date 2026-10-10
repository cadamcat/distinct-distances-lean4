import DistinctDistances.TrackA.AffineGenericRankSupport
import Mathlib.RingTheory.Ideal.GoingUp

set_option backward.isDefEq.respectTransparency true

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical

/-- The original equations, with coefficient extension and literal
projection-fiber equations. Omitted components remain in this system. -/
def genericFiberEquations {n k : ℕ} (φ : AffineProjection n k)
    {K : Type*} [Field K] [Algebra ℂ K] (t : Fin k → K) (E : Set (Poly n)) :
    Set (FieldPoly n K) :=
  (MvPolynomial.map (algebraMap ℂ K) '' E) ∪
    Set.range (fun j : Fin k =>
      MvPolynomial.map (algebraMap ℂ K) (φ.pullback (MvPolynomial.X j)) -
        MvPolynomial.C (t j))

/-- Transfer integrality through an original finite algebra map and the
field scalar tower, without reducing a concrete polynomial quotient. -/
theorem finite_algebra_map_integral (R B K A : Type*) [CommRing R] [CommRing B]
    [CommRing K] [CommRing A] [Algebra R B] [Module.Finite R B]
    [Algebra R K] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
    (β : B →ₐ[R] A) (b : B) : IsIntegral K (β b) := by
  have hi : IsIntegral R b := Algebra.IsIntegral.isIntegral b
  exact (hi.map β).tower_top

/-- A literal fiber of a finite original coordinate map is integral over
the fiber field. This uses its original coordinate quotient and equations. -/
theorem finite_affine_fiber_quotient_integral {n k : ℕ} (V : AffineVariety n)
    (φ : AffineProjection n k) (hf : FiniteAffineProjection φ V)
    (K : Type*) [Field K] [Algebra ℂ K] (t : Fin k → K)
    (Q : Ideal (FieldPoly n K))
    (hVQ : ∀ f ∈ V.ideal, MvPolynomial.map (algebraMap ℂ K) f ∈ Q)
    (hbase : ∀ j, MvPolynomial.map (algebraMap ℂ K)
      (φ.pullback (MvPolynomial.X j)) - MvPolynomial.C (t j) ∈ Q) :
    Algebra.IsIntegral K (FieldPoly n K ⧸ Q) := by
  let R := Poly k
  let B := Poly n ⧸ V.ideal
  let A := FieldPoly n K ⧸ Q
  letI := (affineProjectionMap V φ).toRingHom.toAlgebra
  letI : Module R B := (affineProjectionMap V φ).toRingHom.toAlgebra.toModule
  letI : SMul R B := (affineProjectionMap V φ).toRingHom.toAlgebra.toSMul
  haveI : Module.Finite R B := hf
  letI := (MvPolynomial.aeval (R := ℂ) t).toRingHom.toAlgebra
  letI : Module R K := (MvPolynomial.aeval (R := ℂ) t).toRingHom.toAlgebra.toModule
  letI : SMul R K := (MvPolynomial.aeval (R := ℂ) t).toRingHom.toAlgebra.toSMul
  letI : Algebra R A :=
    ((algebraMap K A).comp (MvPolynomial.aeval (R := ℂ) t).toRingHom).toAlgebra
  letI : Module R A :=
    ((algebraMap K A).comp (MvPolynomial.aeval (R := ℂ) t).toRingHom).toAlgebra.toModule
  letI : SMul R A :=
    ((algebraMap K A).comp (MvPolynomial.aeval (R := ℂ) t).toRingHom).toAlgebra.toSMul
  haveI : IsScalarTower R K A := IsScalarTower.of_algebraMap_eq
    (R := R) (S := K) (A := A) fun _ => rfl
  let m : Poly n →ₐ[ℂ] FieldPoly n K := MvPolynomial.mapAlgHom (Algebra.ofId ℂ K)
  let e : Poly n →ₐ[ℂ] A :=
    ((Ideal.Quotient.mkₐ K Q).restrictScalars ℂ).comp m
  have he (f : Poly n) : e f =
      Ideal.Quotient.mk Q (MvPolynomial.map (algebraMap ℂ K) f) := rfl
  let β : B →ₐ[ℂ] A := Ideal.Quotient.liftₐ V.ideal e (fun f hf => by
    rw [he, Ideal.Quotient.eq_zero_iff_mem]
    exact hVQ f hf)
  have hβ (f : Poly n) : β (Ideal.Quotient.mk V.ideal f) = e f :=
    Ideal.Quotient.lift_mk _ _ _
  have hβbase : β.comp (affineProjectionMap V φ) =
      ((Algebra.ofId K A).restrictScalars ℂ).comp (MvPolynomial.aeval (R := ℂ) t) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply, affineProjectionMap, Ideal.Quotient.mkₐ_eq_mk,
      MvPolynomial.aeval_X]
    change β (Ideal.Quotient.mk V.ideal (φ.pullback (MvPolynomial.X j))) =
      algebraMap K A (t j)
    rw [hβ, he]
    change Ideal.Quotient.mk Q (MvPolynomial.map (algebraMap ℂ K)
      (φ.pullback (MvPolynomial.X j))) = Ideal.Quotient.mk Q (MvPolynomial.C (t j))
    apply eq_of_sub_eq_zero
    rw [← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact hbase j
  let βR : B →ₐ[R] A :=
    { __ := β.toRingHom
      commutes' p := AlgHom.congr_fun hβbase p }
  have hX (j : Fin n) : IsIntegral K (Ideal.Quotient.mk Q (MvPolynomial.X j)) := by
    have hi : IsIntegral K (βR (Ideal.Quotient.mk V.ideal (MvPolynomial.X j) : B)) :=
      finite_algebra_map_integral R B K A βR _
    have hβX : βR (Ideal.Quotient.mk V.ideal (MvPolynomial.X j)) =
        Ideal.Quotient.mk Q (MvPolynomial.X j) := by
      change β (Ideal.Quotient.mk V.ideal (MvPolynomial.X j)) = _
      rw [hβ, he, MvPolynomial.map_X]
    rw [hβX] at hi
    exact hi
  constructor
  intro a
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  induction p using MvPolynomial.induction_on with
  | C c => exact isIntegral_algebraMap
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | mul_X p j hp => simpa only [map_mul] using hp.mul (hX j)

/-- A selected original minimal component yields isolated generic sheets
in the WHOLE original fiber system, irrespective of omitted dimensions. -/
theorem affineFiberOver_minimalPrime {n k : ℕ} (V : AffineVariety n)
    (φ : AffineProjection n k) (hf : FiniteAffineProjection φ V)
    (E : Set (Poly n)) (hV : V.IsComponentOf (Ideal.span E))
    (K : Type*) [Field K] [Algebra ℂ K] (t : Fin k → K)
    (ht : AlgebraicIndependent ℂ t) (x : affineFiberOver V φ t) :
    pointIdealOver x.1 ∈ (Ideal.span (genericFiberEquations φ t E)).minimalPrimes := by
  let m : Poly n →+* FieldPoly n K := MvPolynomial.map (algebraMap ℂ K)
  have hvan (f : Poly n) : MvPolynomial.eval x.1 (m f) = MvPolynomial.aeval x.1 f := by
    exact (MvPolynomial.eval₂_eq_eval_map _ _ f).symm
  have hker : (pointIdealOver x.1).comap m = V.ideal := by
    ext f
    change m f ∈ pointIdealOver x.1 ↔ f ∈ V.ideal
    rw [pointIdealOver, MvPolynomial.mem_vanishingIdeal_singleton_iff,
      MvPolynomial.aeval_eq_eval, hvan]
    exact SetLike.ext_iff.mp (affineFiberOver_eval_ker V hV.isPrime φ hf K t ht x) f
  have hEP : Ideal.span (genericFiberEquations φ t E) ≤ pointIdealOver x.1 := by
    apply Ideal.span_le.mpr
    rintro f (⟨f, hf, rfl⟩ | ⟨j, rfl⟩)
    · change m f ∈ pointIdealOver x.1
      rw [pointIdealOver, MvPolynomial.mem_vanishingIdeal_singleton_iff]
      rw [MvPolynomial.aeval_eq_eval]
      exact (hvan f).trans (x.2.1 f (hV.le (Ideal.subset_span hf)))
    · change m (φ.pullback (MvPolynomial.X j)) - MvPolynomial.C (t j) ∈ pointIdealOver x.1
      rw [pointIdealOver, MvPolynomial.mem_vanishingIdeal_singleton_iff]
      change MvPolynomial.eval x.1 (m (φ.pullback (MvPolynomial.X j)) -
        MvPolynomial.C (t j)) = 0
      simp only [map_sub, MvPolynomial.eval_C, hvan, x.2.2, sub_self]
  refine ⟨⟨inferInstance, hEP⟩, ?_⟩
  intro Q hQ hQP
  letI : Q.IsPrime := hQ.1
  have hQE : Ideal.span E ≤ Q.comap m := by
    apply Ideal.span_le.mpr
    intro f hf
    exact hQ.2 (Ideal.subset_span (Or.inl ⟨f, hf, rfl⟩))
  have hQV : Q.comap m ≤ V.ideal := by
    rw [← hker]
    exact Ideal.comap_mono hQP
  have hVQ : V.ideal ≤ Q.comap m := hV.2 ⟨Ideal.IsPrime.comap m, hQE⟩ hQV
  have hbase (j : Fin k) : MvPolynomial.map (algebraMap ℂ K)
      (φ.pullback (MvPolynomial.X j)) - MvPolynomial.C (t j) ∈ Q :=
    hQ.2 (Ideal.subset_span (Or.inr (Set.mem_range_self j)))
  haveI : Algebra.IsIntegral K (FieldPoly n K ⧸ Q) :=
    finite_affine_fiber_quotient_integral V φ hf K t Q hVQ hbase
  have hQmax : Q.IsMaximal := (Ideal.Quotient.maximal_ideal_iff_isField_quotient Q).mpr
    (isField_of_isIntegral_of_isField' (R := K) (S := FieldPoly n K ⧸ Q) (Field.toIsField K))
  exact (hQmax.eq_of_le (inferInstance : (pointIdealOver x.1).IsPrime).ne_top hQP).symm.le

/-- Different original components have disjoint literal generic fibers. -/
theorem affineFiberOver_disjoint {n k : ℕ} (V W : AffineVariety n)
    (hV : V.IsIrreducible) (hW : W.IsIrreducible) (hne : V ≠ W)
    (φ : AffineProjection n k) (hfV : FiniteAffineProjection φ V)
    (hfW : FiniteAffineProjection φ W) (K : Type*) [Field K] [Algebra ℂ K]
    (t : Fin k → K) (ht : AlgebraicIndependent ℂ t) :
    Disjoint (affineFiberOver V φ t) (affineFiberOver W φ t) := by
  apply Set.disjoint_left.mpr
  intro x hxV hxW
  apply hne
  apply AffineVariety.ext
  exact (affineFiberOver_eval_ker V hV φ hfV K t ht ⟨x, hxV⟩).symm.trans
    (affineFiberOver_eval_ker W hW φ hfW K t ht ⟨x, hxW⟩)

end
end DistinctDistances.TrackA
