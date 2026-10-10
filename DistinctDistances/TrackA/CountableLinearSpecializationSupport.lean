import DistinctDistances.TrackA.ReducedScalarExtensionSupport
import DistinctDistances.OAIInterface.CountableLinearSpecialization

set_option backward.isDefEq.respectTransparency.types false

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical TensorProduct
attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- An injective parameter specialization extends to the coefficient
fraction field. Cancelling that base change transfers geometric reducedness
to the actual specialized universal-incidence quotient. -/
theorem universalLinearEquation_injective_specialization_reduced
    {R A K σ : Type} [Field R] [CharZero R] [CommRing A] [Algebra R A]
    [IsReduced A] [Algebra.FiniteType R A] [Field K] [Algebra R K] [Fintype σ]
    (v : σ → A) (i : σ) (hv : IsUnit (v i))
    (f : MvPolynomial σ R →ₐ[R] K) (hf : Function.Injective f) :
    let := f.toRingHom.toAlgebra
    IsReduced (K ⊗[MvPolynomial σ R]
      (MvPolynomial σ A ⧸ Ideal.span {universalLinearEquation v})) := by
  let P := MvPolynomial σ R
  let F := FractionRing P
  let Q := MvPolynomial σ A ⧸ Ideal.span {universalLinearEquation v}
  let : Algebra P K := f.toRingHom.toAlgebra
  let g : F →ₐ[R] K := IsFractionRing.liftAlgHom hf
  let : Algebra F K := g.toRingHom.toAlgebra
  let : IsScalarTower P F K := IsScalarTower.of_algebraMap_eq fun p => by
    exact (IsFractionRing.lift_algebraMap hf p).symm
  let : IsReduced (universalLinearGeometricRing (K := R) v K) :=
    universalLinearEquation_geometric_generic_reduced v i hv K
  let e := Algebra.TensorProduct.cancelBaseChange P F K K Q
  exact isReduced_of_injective e.symm e.symm.injective

/-- Parameter tensor and tensor quotient comparisons identify the reduced
specialization with the literal principal ideal in the scalar model. -/
theorem universalLinearEquation_specialized_tensor_radical
    {R A K σ : Type} [Field R] [CharZero R] [CommRing A] [Algebra R A]
    [IsReduced A] [Algebra.FiniteType R A] [Field K] [Algebra R K] [Fintype σ]
    (v : σ → A) (i : σ) (hv : IsUnit (v i))
    (f : MvPolynomial σ R →ₐ[R] K) (hf : Function.Injective f) :
    (Ideal.span {∑ j, f (MvPolynomial.X j) ⊗ₜ[R] v j} :
      Ideal (K ⊗[R] A)).IsRadical := by
  let P := MvPolynomial σ R
  let B := MvPolynomial σ A
  let I : Ideal B := Ideal.span {universalLinearEquation v}
  let : Algebra P K := f.toRingHom.toAlgebra
  let : IsScalarTower R P K :=
    IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  let : IsReduced (K ⊗[P] (B ⧸ I)) :=
    universalLinearEquation_injective_specialization_reduced v i hv f hf
  obtain ⟨e, heC, heX⟩ :=
    OAI.MaximalSeshadri.BertiniIntegral.mvPolynomial_parameter_tensor (R := R) (K := K) (A := A) (σ := σ)
  let J : Ideal (K ⊗[R] A) := Ideal.span {∑ j, f (MvPolynomial.X j) ⊗ₜ[R] v j}
  have he : e (1 ⊗ₜ[P] universalLinearEquation v) =
      ∑ j, f (MvPolynomial.X j) ⊗ₜ[R] v j := by
    rw [universalLinearEquation, TensorProduct.tmul_sum, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [show (1 : K) ⊗ₜ[P] (MvPolynomial.X j * MvPolynomial.C (v j)) =
      ((1 : K) ⊗ₜ[P] (MvPolynomial.X j : B)) *
        ((1 : K) ⊗ₜ[P] MvPolynomial.C (v j)) by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]]
    rw [map_mul, heX, heC, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    rfl
  have hJ : J = (I.map
      (Algebra.TensorProduct.includeRight : B →ₐ[P] K ⊗[P] B).toRingHom).map e.toRingHom := by
    rw [Ideal.map_map, Ideal.map_span, Set.image_singleton]
    change J = Ideal.span {e (1 ⊗ₜ[P] universalLinearEquation v)}
    rw [he]
  let q := (Algebra.TensorProduct.tensorQuotientEquiv K B K I).trans
    (Ideal.quotientEquivAlg _ J e hJ)
  rw [Ideal.isRadical_iff_quotient_reduced]
  exact isReduced_of_injective q.symm q.symm.injective

/-- The scalar model equivalence carries the specialized equation to the
given coordinates, so reducedness concerns their actual sum ideal. -/
theorem reduced_linear_equation_over_model
    {R A K B σ : Type} [Field R] [CharZero R] [CommRing A] [Algebra R A]
    [IsReduced A] [Algebra.FiniteType R A] [Field K] [Algebra R K]
    [CommRing B] [Algebra K B] [Fintype σ]
    (e : (K ⊗[R] A) ≃ₐ[K] B) (v₀ : σ → A) (v : σ → B)
    (hcoords : ∀ j, e (1 ⊗ₜ[R] v₀ j) = v j)
    (i : σ) (hv : IsUnit (v₀ i))
    (f : MvPolynomial σ R →ₐ[R] K) (hf : Function.Injective f) :
    (Ideal.span {∑ j, algebraMap K B (f (MvPolynomial.X j)) * v j}).IsRadical := by
  have hr := universalLinearEquation_specialized_tensor_radical v₀ i hv f hf
  let I : Ideal (K ⊗[R] A) := Ideal.span {∑ j, f (MvPolynomial.X j) ⊗ₜ[R] v₀ j}
  let J : Ideal B := Ideal.span {∑ j, algebraMap K B (f (MvPolynomial.X j)) * v j}
  have he (a : K) (b : A) : e (a ⊗ₜ[R] b) = algebraMap K B a * e (1 ⊗ₜ[R] b) := by
    rw [show a ⊗ₜ[R] b = a • ((1 : K) ⊗ₜ[R] b) by
      rw [TensorProduct.smul_tmul']; simp]
    rw [map_smul, Algebra.smul_def]
  have hJ : J = I.map e.toRingHom := by
    rw [Ideal.map_span, Set.image_singleton]
    change J = Ideal.span {e (∑ j, f (MvPolynomial.X j) ⊗ₜ[R] v₀ j)}
    have hsum : e (∑ j, f (MvPolynomial.X j) ⊗ₜ[R] v₀ j) =
        ∑ j, algebraMap K B (f (MvPolynomial.X j)) * v j := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [he, hcoords]
    rw [hsum]
  let : IsReduced ((K ⊗[R] A) ⧸ I) := (Ideal.isRadical_iff_quotient_reduced I).mp hr
  let q := Ideal.quotientEquivAlg I J e hJ
  rw [Ideal.isRadical_iff_quotient_reduced]
  exact isReduced_of_injective q.symm q.symm.injective

end
end DistinctDistances.TrackA
