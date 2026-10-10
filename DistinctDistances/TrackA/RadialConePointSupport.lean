import DistinctDistances.TrackA.RadialConeAlgebraSupport
import DistinctDistances.TrackA.RadialRootCountSupport

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical

/-- Evaluation at the supplied literal point of the original radial image cone. -/
def radialConePoint {n : ℕ} (V : AffineVariety n) (p v : Point n)
    (hv : v ∈ (radialImage p V).affineCone.points) : RadialConeBase V p →ₐ[ℂ] ℂ :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval v) (by
    intro f hf
    exact hv f (radialCone_ker_le_image_ideal V p hf))

theorem radialConePoint_mk {n : ℕ} (V : AffineVariety n) (p v : Point n)
    (hv : v ∈ (radialImage p V).affineCone.points) (f : Poly n) :
    radialConePoint V p v hv (Ideal.Quotient.mk _ f) = MvPolynomial.aeval v f := by
  rw [radialConePoint, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  rfl

@[instance_reducible]
def radialConePointAlgebra {n : ℕ} (V : AffineVariety n) (p v : Point n)
    (hv : v ∈ (radialImage p V).affineCone.points) : Algebra (RadialConeBase V p) ℂ := by
  with_unfolding_all
    exact RingHom.toAlgebra (R := RadialConeBase V p) (S := ℂ)
      (radialConePoint V p v hv).toRingHom

/-- Literal pairs retain both the original source point and the cone scalar. -/
def radialConePairs {n : ℕ} (V : AffineVariety n) (p v : Point n) :
    Set (Point n × ℂ) := {q | q.1 ∈ V.points ∧ q.2 • (q.1-p) = v}

/-- Original base-linear cone homomorphisms are exactly literal source/scalar pairs. -/
def radialConeHomEquivPairs {n : ℕ} (V : AffineVariety n) (p v : Point n)
    (hv : v ∈ (radialImage p V).affineCone.points) :
    letI := radialConeAlgebra V p
    letI := radialConePointAlgebra V p v hv
    (Polynomial (Poly n ⧸ V.ideal) →ₐ[RadialConeBase V p] ℂ) ≃ radialConePairs V p v := by
  let R := RadialConeBase V p
  let A := Poly n ⧸ V.ideal
  let B := Polynomial A
  letI := radialConeAlgebra V p
  letI := radialConePointAlgebra V p v hv
  letI : SMul ℂ R := (inferInstance : Algebra ℂ R).toSMul
  haveI : IsScalarTower ℂ R B := by
    refine IsScalarTower.of_algebraMap_eq (R := ℂ) (S := R) (A := B) ?_
    intro c
    change algebraMap ℂ B c = radialConeInclusion V p (algebraMap ℂ R c)
    exact (radialConeInclusion V p).commutes c |>.symm
  haveI : IsScalarTower ℂ R ℂ := by
    refine IsScalarTower.of_algebraMap_eq (R := ℂ) (S := R) (A := ℂ) ?_
    intro c
    change c = radialConePoint V p v hv (algebraMap ℂ R c)
    exact (radialConePoint V p v hv).commutes c |>.symm
  let point (h : B →ₐ[R] ℂ) : Point n :=
    fun i => h (Polynomial.C (Ideal.Quotient.mk V.ideal (MvPolynomial.X i)))
  have hpoint (h : B →ₐ[R] ℂ) : MvPolynomial.aeval (point h) =
      ((h.restrictScalars ℂ).comp Polynomial.CAlgHom).comp (Ideal.Quotient.mkₐ ℂ V.ideal) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [MvPolynomial.aeval_X, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
    rfl
  let evaluation (q : radialConePairs V p v) : B →ₐ[ℂ] ℂ :=
    Polynomial.aevalTower (Ideal.Quotient.liftₐ V.ideal (MvPolynomial.aeval q.1.1) q.2.1) q.1.2
  have heval (q : radialConePairs V p v) :
      (evaluation q).comp (radialConePullback V p) = MvPolynomial.aeval v := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply, radialConePullback_X, MvPolynomial.aeval_X]
    change evaluation q (Polynomial.X * Polynomial.C (Ideal.Quotient.mk V.ideal
      (radialCoordinate p i))) = v i
    rw [map_mul, Polynomial.aevalTower_X, Polynomial.aevalTower_C,
      Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
    change q.1.2 * MvPolynomial.aeval q.1.1 (radialCoordinate p i) = v i
    have h := congrFun q.2.2 i
    simpa only [radialCoordinate, map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
      Algebra.algebraMap_self_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] using h
  let fromPair (q : radialConePairs V p v) : B →ₐ[R] ℂ :=
    { __ := (evaluation q).toRingHom
      commutes' a := by
        obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
        change evaluation q (radialConeInclusion V p (Ideal.Quotient.mk _ f)) =
          radialConePoint V p v hv (Ideal.Quotient.mk _ f)
        rw [radialConePoint_mk]
        change evaluation q (radialConePullback V p f) = _
        exact AlgHom.congr_fun (heval q) f }
  refine
    { toFun := fun h => ⟨(point h, h Polynomial.X), ?_⟩
      invFun := fromPair
      left_inv := ?_
      right_inv := ?_ }
  · constructor
    · intro f hf
      rw [hpoint, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem.mpr hf, map_zero]
    · funext i
      have hc := h.commutes (Ideal.Quotient.mk (RingHom.ker (radialConePullback V p))
        (MvPolynomial.X i))
      change h (radialConePullback V p (MvPolynomial.X i)) =
        radialConePoint V p v hv (Ideal.Quotient.mk _ (MvPolynomial.X i)) at hc
      rw [radialConePullback_X, map_mul, radialConePoint_mk, MvPolynomial.aeval_X] at hc
      have hp := AlgHom.congr_fun (hpoint h) (radialCoordinate p i)
      change MvPolynomial.aeval (point h) (radialCoordinate p i) =
        h (Polynomial.C (Ideal.Quotient.mk V.ideal (radialCoordinate p i))) at hp
      rw [← hp] at hc
      simpa only [radialCoordinate, map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
        Algebra.algebraMap_self_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] using hc
  · intro h
    apply AlgHom.coe_ringHom_injective
    apply Polynomial.ringHom_ext
    · intro a
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
      change evaluation _ (Polynomial.C (Ideal.Quotient.mk V.ideal f)) = _
      rw [Polynomial.aevalTower_C, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk,
        hpoint]
      rfl
    · change evaluation _ Polynomial.X = h Polynomial.X
      exact Polynomial.aevalTower_X _ _
  · intro q
    apply Subtype.ext
    apply Prod.ext
    · funext i
      change evaluation q (Polynomial.C (Ideal.Quotient.mk V.ideal (MvPolynomial.X i))) = q.1.1 i
      rw [Polynomial.aevalTower_C, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
      exact MvPolynomial.aeval_X q.1.1 i
    · change evaluation q Polynomial.X = q.1.2
      exact Polynomial.aevalTower_X _ _

end
end DistinctDistances.TrackA
