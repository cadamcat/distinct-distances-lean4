import DistinctDistances.TrackA.AffineFiberPointSupport
import DistinctDistances.TrackA.NormalizationSpecializationSupport
import Mathlib.RingTheory.TensorProduct.Maps

set_option backward.isDefEq.respectTransparency true

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical TensorProduct

/-- The original fiber equations give the literal scalar specialization
of the original affine coordinate algebra. -/
def affineFiberTensorEquiv {n k : ℕ} (V : AffineVariety n) (ψ : LinearProjection n k)
    (y : Point k) :
    let Q := Poly n ⧸ affineFiberIdeal V (⟨ψ, 0⟩ : AffineProjection n k) y
    let qAlg : Algebra ℂ Q := inferInstance
    letI := (affineNormalizationMap V ψ).toRingHom.toAlgebra
    letI : Module (Poly k) (Poly n ⧸ V.ideal) :=
      (affineNormalizationMap V ψ).toRingHom.toAlgebra.toModule
    letI : SMul (Poly k) (Poly n ⧸ V.ideal) :=
      (affineNormalizationMap V ψ).toRingHom.toAlgebra.toSMul
    letI := (MvPolynomial.aeval (R := ℂ) y).toRingHom.toAlgebra
    letI : Module (Poly k) ℂ :=
      (MvPolynomial.aeval (R := ℂ) y).toRingHom.toAlgebra.toModule
    letI : SMulCommClass (Poly k) ℂ ℂ := ⟨fun _ _ _ => by
      simp only [Algebra.smul_def, smul_eq_mul]
      ring⟩
    letI : Algebra ℂ Q := qAlg
    letI : Module ℂ Q := qAlg.toModule
    letI : SMul ℂ Q := qAlg.toSMul
    (ℂ ⊗[Poly k] (Poly n ⧸ V.ideal)) ≃ₐ[ℂ]
      Q := by
  let R := Poly k
  let B := Poly n ⧸ V.ideal
  let J := affineFiberIdeal V (⟨ψ, 0⟩ : AffineProjection n k) y
  let Q := Poly n ⧸ J
  let qAlg : Algebra ℂ Q := inferInstance
  letI := (affineNormalizationMap V ψ).toRingHom.toAlgebra
  letI : Module R B := (affineNormalizationMap V ψ).toRingHom.toAlgebra.toModule
  letI : SMul R B := (affineNormalizationMap V ψ).toRingHom.toAlgebra.toSMul
  letI := (MvPolynomial.aeval (R := ℂ) y).toRingHom.toAlgebra
  letI : Module R ℂ := (MvPolynomial.aeval (R := ℂ) y).toRingHom.toAlgebra.toModule
  letI : SMulCommClass R ℂ ℂ := ⟨fun _ _ _ => by
    simp only [Algebra.smul_def, smul_eq_mul]
    ring⟩
  letI : Algebra ℂ Q := qAlg
  letI : Module ℂ Q := qAlg.toModule
  letI : SMul ℂ Q := qAlg.toSMul
  letI : Algebra R Q := ((algebraMap ℂ Q).comp (MvPolynomial.aeval (R := ℂ) y).toRingHom).toAlgebra
  letI : Module R Q :=
    ((algebraMap ℂ Q).comp (MvPolynomial.aeval (R := ℂ) y).toRingHom).toAlgebra.toModule
  letI : SMul R Q :=
    ((algebraMap ℂ Q).comp (MvPolynomial.aeval (R := ℂ) y).toRingHom).toAlgebra.toSMul
  haveI : IsScalarTower R ℂ Q :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := ℂ) (A := Q) fun _ => rfl
  let T := ℂ ⊗[R] B
  letI : CommRing T := inferInstance
  letI : Algebra ℂ T := Algebra.TensorProduct.leftAlgebra
  let β : B →ₐ[ℂ] Q := Ideal.Quotient.liftₐ V.ideal (Ideal.Quotient.mkₐ ℂ J)
    (fun f hf => Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left hf))
  have hβmk (f : Poly n) : β (Ideal.Quotient.mk V.ideal f) = Ideal.Quotient.mk J f :=
    Ideal.Quotient.lift_mk _ _ _
  have hβ : β.comp (affineNormalizationMap V ψ) =
      (Algebra.ofId ℂ Q).comp (MvPolynomial.aeval y) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, affineNormalizationMap, MvPolynomial.aeval_X,
      β, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk, Algebra.ofId_apply]
    set_option backward.isDefEq.respectTransparency false in
      change Ideal.Quotient.mk J (linearCoordinate ψ i) =
        Ideal.Quotient.mk J (MvPolynomial.C (y i))
    apply eq_of_sub_eq_zero
    rw [← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    have hi : (⟨ψ, 0⟩ : AffineProjection n k).pullback (MvPolynomial.X i) -
        MvPolynomial.C (y i) ∈ J :=
      Ideal.mem_sup_right (Ideal.subset_span (Set.mem_range_self i))
    simpa only [J, affineFiberIdeal, AffineProjection.pullback, MvPolynomial.aeval_X,
      Pi.zero_apply, MvPolynomial.C_0, add_zero] using hi
  let βR : B →ₐ[R] Q :=
    { __ := β.toRingHom
      commutes' r := AlgHom.congr_fun hβ r }
  let forward : T →ₐ[ℂ] Q := Algebra.TensorProduct.lift
    (Algebra.ofId ℂ Q) βR (fun _ _ => Commute.all _ _)
  have hforward (a : ℂ) (b : B) : forward (a ⊗ₜ[R] b) = algebraMap ℂ Q a * β b := rfl
  let ev : Poly n →ₐ[ℂ] T :=
    ((Algebra.TensorProduct.includeRight : B →ₐ[R] T).restrictScalars ℂ).comp
      (Ideal.Quotient.mkₐ ℂ V.ideal)
  have hev (f : Poly n) : ev f = (1 : ℂ) ⊗ₜ[R] Ideal.Quotient.mk V.ideal f := rfl
  have hcoord (i : Fin k) : ev (linearCoordinate ψ i) = algebraMap ℂ T (y i) := by
    have hi := (Algebra.TensorProduct.includeRight : B →ₐ[R] T).commutes (MvPolynomial.X i)
    change Algebra.TensorProduct.includeRight
      (affineNormalizationMap V ψ (MvPolynomial.X i)) = algebraMap R T (MvPolynomial.X i) at hi
    simp only [affineNormalizationMap, MvPolynomial.aeval_X,
      IsScalarTower.algebraMap_apply R ℂ T] at hi
    have hR : algebraMap R ℂ (MvPolynomial.X i) = y i :=
      MvPolynomial.aeval_X y i
    rw [hR] at hi
    rw [hev]
    exact hi
  have hJ : ∀ f ∈ J, ev f = 0 := by
    have hle : J ≤ RingHom.ker ev.toRingHom := by
      apply sup_le
      · intro f hf
        change ev f = 0
        rw [hev, Ideal.Quotient.eq_zero_iff_mem.mpr hf, TensorProduct.tmul_zero]
      · apply Ideal.span_le.mpr
        rintro f ⟨i, rfl⟩
        change ev _ = 0
        set_option backward.isDefEq.respectTransparency false in
          simp only [AffineProjection.pullback, MvPolynomial.aeval_X, Pi.zero_apply,
            MvPolynomial.C_0, add_zero, map_sub, hcoord, MvPolynomial.C_eq_algebraMap,
            AlgHom.commutes, map_zero, sub_self]
    exact hle
  let backward : Q →ₐ[ℂ] T := Ideal.Quotient.liftₐ J ev hJ
  have hback (f : Poly n) : backward (Ideal.Quotient.mk J f) = ev f :=
    Ideal.Quotient.lift_mk _ _ _
  apply AlgEquiv.ofAlgHom forward backward
  · apply AlgHom.ext
    intro z
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective z
    change forward (backward (Ideal.Quotient.mk J f)) = Ideal.Quotient.mk J f
    rw [hback]
    have he : forward.comp ev = Ideal.Quotient.mkₐ ℂ J := by
      apply MvPolynomial.algHom_ext
      intro i
      change forward (ev (MvPolynomial.X i)) = Ideal.Quotient.mk J (MvPolynomial.X i)
      rw [hev, hforward, map_one, one_mul, hβmk]
    exact AlgHom.congr_fun he f
  · apply Algebra.TensorProduct.ext'
    intro a b
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective b
    change backward (forward (a ⊗ₜ[R] Ideal.Quotient.mk V.ideal f)) =
      a ⊗ₜ[R] Ideal.Quotient.mk V.ideal f
    rw [hforward, map_mul, backward.commutes, hβmk, hback, hev]
    set_option backward.isDefEq.respectTransparency false in
      change (a ⊗ₜ[R] (1 : B)) * ((1 : ℂ) ⊗ₜ[R] Ideal.Quotient.mk V.ideal f) =
        a ⊗ₜ[R] Ideal.Quotient.mk V.ideal f
    set_option backward.isDefEq.respectTransparency false in
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

end
end DistinctDistances.TrackA
