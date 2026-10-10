import DistinctDistances.TrackA.FixedCoordinateNormalizationSupport
import DistinctDistances.TrackA.NormalizationProjectionSupport
import DistinctDistances.TrackA.ProjectionSourceSupport

set_option backward.isDefEq.respectTransparency false

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The literal cone quotient cut by one coordinate agrees with the
literal ambient sum-ideal quotient, including its nonreduced structure. -/
def homogeneousCoordinateCutQuotientEquiv {n : ℕ} (I : Ideal (Poly n)) (t : Poly n) :
    ((Poly n ⧸ I) ⧸ Ideal.span {Ideal.Quotient.mk I t}) ≃+*
      Poly n ⧸ (I ⊔ Ideal.span {t}) := by
  have he : (Ideal.span ({t} : Set (Poly n))).map (Ideal.Quotient.mk I) =
      Ideal.span {Ideal.Quotient.mk I t} := by
    rw [Ideal.map_span, Set.image_singleton]
  exact (Ideal.quotEquivOfEq he.symm).trans
    (DoubleQuot.quotQuotEquivQuotSup I (Ideal.span {t}))

theorem homogeneousCoordinateCutQuotientEquiv_mk {n : ℕ}
    (I : Ideal (Poly n)) (t f : Poly n) :
    homogeneousCoordinateCutQuotientEquiv I t
      (Ideal.Quotient.mk _ (Ideal.Quotient.mk I f)) =
        Ideal.Quotient.mk (I ⊔ Ideal.span {t}) f := by
  simp only [homogeneousCoordinateCutQuotientEquiv, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk]
  rfl

/-- Finite parameters on the actual infinity sum-ideal quotient lift to
finite cone parameters while retaining the original chosen coordinate. -/
theorem homogeneous_finite_parameters_from_coordinate_cut {n s : ℕ}
    (I : Ideal (Poly n))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) ℂ))
    (t : Poly n) (ht : t.IsHomogeneous 1)
    (f : Fin s → Poly n) (hf : ∀ i, (f i).IsHomogeneous 1)
    (hfinite : (MvPolynomial.aeval (R := ℂ)
      (fun i => Ideal.Quotient.mk (I ⊔ Ideal.span {t}) (f i))).Finite) :
    (MvPolynomial.aeval (R := ℂ)
      (Fin.cons (Ideal.Quotient.mk I t) (fun i => Ideal.Quotient.mk I (f i)))).Finite := by
  let z : Fin s → Poly n ⧸ I := fun i => Ideal.Quotient.mk I (f i)
  let q := DoubleQuot.quotLeftToQuotSupₐ ℂ I (Ideal.span {t})
  have hq : Function.Surjective q := Ideal.Quotient.factor_surjective le_sup_left
  have hker : RingHom.ker q.toRingHom ≤ Ideal.span {Ideal.Quotient.mk I t} := by
    change RingHom.ker (DoubleQuot.quotLeftToQuotSup I (Ideal.span {t})) ≤ _
    rw [DoubleQuot.ker_quotLeftToQuotSup,
      Ideal.map_span, Set.image_singleton]
  let : GradedAlgebra (OAI.PiExponentJets.W64.quotientSection I) := homogeneousQuotientGrading I hI
  exact graded_finite_parameters_lift_through_coordinate_cut
    (OAI.PiExponentJets.W64.quotientSection I) (Ideal.Quotient.mk I t) ⟨t, ht, rfl⟩
    z (fun i => ⟨f i, hf i, rfl⟩) q hq hker hfinite

/-- The original projective-closure quotient maps to the affine
coordinate quotient by setting the original X0 to one. -/
def projectiveClosureDehomogenization {n : ℕ} (V : AffineVariety n) :
    (Poly (n+1) ⧸ (projectiveClosure V).ideal) →ₐ[ℂ] (Poly n ⧸ V.ideal) :=
  Ideal.Quotient.liftₐ (projectiveClosure V).ideal
    ((Ideal.Quotient.mkₐ ℂ V.ideal).comp
      (MvPolynomial.aeval (Fin.cons (1 : Poly n) MvPolynomial.X)))
    (fun f hf => Ideal.Quotient.eq_zero_iff_mem.mpr (projectiveClosure_aeval_mem V f hf))

theorem projectiveClosureDehomogenization_mk {n : ℕ} (V : AffineVariety n)
    (f : Poly (n+1)) :
    projectiveClosureDehomogenization V (Ideal.Quotient.mk (projectiveClosure V).ideal f) =
      Ideal.Quotient.mk V.ideal (MvPolynomial.aeval (Fin.cons (1 : Poly n) MvPolynomial.X) f) := rfl

theorem projectiveClosureDehomogenization_surjective {n : ℕ} (V : AffineVariety n) :
    Function.Surjective (projectiveClosureDehomogenization V) := by
  intro a
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  refine ⟨Ideal.Quotient.mk (projectiveClosure V).ideal (MvPolynomial.rename Fin.succ f), ?_⟩
  rw [projectiveClosureDehomogenization_mk, MvPolynomial.aeval_rename]
  simp only [Function.comp_def, Fin.cons_succ, MvPolynomial.aeval_X_left_apply]

/-- Finite cone parameters with the literal original X0 give finite
affine parameters after dehomogenization. -/
theorem affine_finite_parameters_from_projective_cone {n s : ℕ}
    (V : AffineVariety n) (f : Fin s → Poly (n+1))
    (hfinite : (MvPolynomial.aeval (R := ℂ)
      (Fin.cons (Ideal.Quotient.mk (projectiveClosure V).ideal (MvPolynomial.X 0))
        (fun i => Ideal.Quotient.mk (projectiveClosure V).ideal (f i)))).Finite) :
    (MvPolynomial.aeval (R := ℂ) (fun i => Ideal.Quotient.mk V.ideal
      (MvPolynomial.aeval (Fin.cons (1 : Poly n) MvPolynomial.X) (f i)))).Finite := by
  have ht : projectiveClosureDehomogenization V
      (Ideal.Quotient.mk (projectiveClosure V).ideal (MvPolynomial.X 0)) = 1 := by
    rw [projectiveClosureDehomogenization_mk, MvPolynomial.aeval_X, Fin.cons_zero, map_one]
  have h := finite_parameters_specialize_fixed_coordinate_one
    (Ideal.Quotient.mk (projectiveClosure V).ideal (MvPolynomial.X 0))
    (fun i => Ideal.Quotient.mk (projectiveClosure V).ideal (f i)) hfinite
    (projectiveClosureDehomogenization V) (projectiveClosureDehomogenization_surjective V) ht
  simpa only [projectiveClosureDehomogenization_mk] using h

/-- A finite polynomial parameter map on the actual infinity quotient
gives the same finite zero-offset affine linear projection on the original
variety. No radicalization of the infinity cut is used. -/
theorem finite_affine_projection_of_infinity_parameters {n s : ℕ}
    (V : AffineVariety n) (ψ : LinearProjection n s)
    (hfinite : (MvPolynomial.aeval (R := ℂ) (fun i =>
      Ideal.Quotient.mk ((projectiveClosure V).ideal ⊔ Ideal.span {MvPolynomial.X 0})
        (MvPolynomial.rename Fin.succ (linearCoordinate ψ i)))).Finite) :
    FiniteAffineProjection (⟨ψ, 0⟩ : AffineProjection n s) V := by
  let f : Fin s → Poly (n+1) := fun i =>
    MvPolynomial.rename Fin.succ (linearCoordinate ψ i)
  have hf (i : Fin s) : (f i).IsHomogeneous 1 :=
    (linearCoordinate_homogeneous ψ i).rename_isHomogeneous
  have hcone := homogeneous_finite_parameters_from_coordinate_cut
    (projectiveClosure V).ideal (projectiveClosure V).isHomogeneous
    (MvPolynomial.X 0) (MvPolynomial.isHomogeneous_X ℂ 0) f hf hfinite
  have haffine := affine_finite_parameters_from_projective_cone V f hcone
  have he (i : Fin s) :
      MvPolynomial.aeval (Fin.cons (1 : Poly n) MvPolynomial.X) (f i) =
        linearCoordinate ψ i := by
    rw [MvPolynomial.aeval_rename]
    simp only [Function.comp_def, Fin.cons_succ, MvPolynomial.aeval_X_left_apply]
  apply finite_affine_projection_of_quotient_parameters V
    (fun i => Ideal.Quotient.mk V.ideal (linearCoordinate ψ i)) ψ (fun _ => rfl)
  simpa only [he] using haffine

end
end DistinctDistances.TrackA
