import DistinctDistances.TrackD.DifferentialConstants
import DistinctDistances.TrackD.GenericCotangent
import DistinctDistances.TrackD.GenericTangent
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Derivation extension for the generic rational-image tangent step
(`secants.tex:63–81`). No differential rank or transcendence-degree formula is used. -/

namespace DistinctDistances.TrackD

open scoped TensorProduct BigOperators Classical
noncomputable section

set_option maxHeartbeats 600000

/-- A derivation which kills the kernel descends along a surjective algebra map.
The target module may lie in a further algebra in the tower. -/
theorem derivation_descends (R A B M : Type*)
    [CommRing R] [CommRing A] [CommRing B] [AddCommGroup M]
    [Algebra R A] [Algebra R B] [Module R M] [Module A M] [Module B M]
    [IsScalarTower R A M] [IsScalarTower R B M]
    (q : A →ₐ[R] B) (hq : Function.Surjective q)
    (hsmul : ∀ a : A, ∀ m : M, a • m = q a • m)
    (δ : Derivation R A M) (hδ : ∀ a : A, q a = 0 → δ a = 0) :
    ∃ ε : Derivation R B M, ∀ a : A, ε (q a) = δ a := by
  let f := q.toLinearMap
  have hker : LinearMap.ker f ≤ LinearMap.ker (δ : A →ₗ[R] M) := by
    intro a ha
    exact hδ a ha
  let e := f.quotKerEquivOfSurjective hq
  let L : B →ₗ[R] M :=
    ((LinearMap.ker f).liftQ (δ : A →ₗ[R] M) hker).comp e.symm.toLinearMap
  have hL : ∀ a : A, L (q a) = δ a := by
    intro a
    change (LinearMap.ker f).liftQ (δ : A →ₗ[R] M) hker (e.symm (f a)) = δ a
    have he : e.symm (f a) = Submodule.Quotient.mk a :=
      f.quotKerEquivOfSurjective_symm_apply hq a
    rw [he]
    rfl
  refine ⟨{ toLinearMap := L, map_one_eq_zero' := ?_, leibniz' := ?_ }, hL⟩
  · rw [← map_one q, hL, δ.map_one_eq_zero]
  · intro b c
    obtain ⟨a, rfl⟩ := hq b
    obtain ⟨a', rfl⟩ := hq c
    rw [← map_mul q, hL, hL, hL, δ.leibniz, hsmul, hsmul]

/-- Localizing the source extends derivations with values in any module over the
localization. The étale differential comparison supplies the extension. -/
theorem derivation_extends_localization (R A E M : Type*)
    [CommRing R] [CommRing A] [CommRing E] [AddCommGroup M]
    [Algebra R A] [Algebra R E] [Algebra A E] [IsScalarTower R A E]
    [Module R M] [Module A M] [Module E M]
    [IsScalarTower R A M] [IsScalarTower R E M] [IsScalarTower A E M]
    [Algebra.FormallyEtale A E] (δ : Derivation R A M) :
    ∃ ε : Derivation R E M, ∀ a : A, ε (algebraMap A E a) = δ a := by
  let L := (δ.liftKaehlerDifferential.liftBaseChange E).comp
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A E).symm.toLinearMap
  refine ⟨L.compDer (KaehlerDifferential.D R E), ?_⟩
  intro a
  simp [L, KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    LinearMap.liftBaseChange_tmul]

/-- A formally smooth field extension admits extension of every derivation with
values in the larger field. This proves tangent surjectivity without computing rank. -/
theorem derivation_extends_smooth_field (R E K : Type*)
    [CommRing R] [Field E] [Field K]
    [Algebra R E] [Algebra R K] [Algebra E K] [IsScalarTower R E K]
    [Algebra.FormallySmooth E K] (δ : Derivation R E K) :
    ∃ ε : Derivation R K K, ∀ a : E, ε (algebraMap E K a) = δ a := by
  let f := KaehlerDifferential.mapBaseChange R E K
  have hf : LinearMap.ker f = ⊥ := LinearMap.ker_eq_bot.mpr
    (mapBaseChange_injective_of_smooth R E K)
  let L := (δ.liftKaehlerDifferential.liftBaseChange K).comp f.leftInverse
  refine ⟨L.compDer (KaehlerDifferential.D R K), ?_⟩
  intro a
  have heq : KaehlerDifferential.D R K (algebraMap E K a) =
      f (1 ⊗ₜ[E] KaehlerDifferential.D R E a) := by
    simp [f]
  change (δ.liftKaehlerDifferential.liftBaseChange K)
    (f.leftInverse (KaehlerDifferential.D R K (algebraMap E K a))) = δ a
  rw [heq, LinearMap.leftInverse_apply_of_inj hf,
    LinearMap.liftBaseChange_tmul, one_smul, Derivation.liftKaehlerDifferential_comp_D]

/-- Every function-field vector satisfying the ideal's tangent equations is the
coordinate velocity of a derivation of the actual coordinate function field. -/
theorem coordinate_tangent_derivation {n : ℕ} (I : Ideal (Poly n))
    (K : Type*) [Field K] [Algebra ℂ K] [Algebra (Poly n ⧸ I) K]
    [IsScalarTower ℂ (Poly n ⧸ I) K] [IsFractionRing (Poly n ⧸ I) K]
    (v : Fin n → K)
    (hv : ∀ p ∈ I, ∑ i : Fin n, coordinateFieldMap I K (MvPolynomial.pderiv i p) * v i = 0) :
    ∃ δ : Derivation ℂ K K,
      ∀ i : Fin n, δ (coordinateFieldMap I K (MvPolynomial.X i)) = v i := by
  let φ := coordinateFieldMap I K
  letI : Algebra (Poly n) K := φ.toRingHom.toAlgebra
  letI : Module (Poly n) K := (φ.toRingHom.toAlgebra).toModule
  letI : IsScalarTower ℂ (Poly n) K := IsScalarTower.of_algHom φ
  let δ := MvPolynomial.mkDerivation ℂ v
  have hδ : ∀ p : Poly n, δ p = ∑ i : Fin n, φ (MvPolynomial.pderiv i p) * v i := by
    intro p
    simpa [δ, φ, coordinateFieldMap, Algebra.smul_def, RingHom.algebraMap_toAlgebra] using
      mk_derivation_sum K v p
  obtain ⟨ε, hε⟩ := derivation_descends ℂ (Poly n) (Poly n ⧸ I) K
    (Ideal.Quotient.mkₐ ℂ I) Ideal.Quotient.mk_surjective
    (by
      intro p z
      simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
      rfl) δ (by
      intro p hp
      rw [hδ]
      exact hv p (Ideal.Quotient.eq_zero_iff_mem.mp hp))
  letI : Algebra.FormallyEtale (Poly n ⧸ I) K :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors (Poly n ⧸ I))
  obtain ⟨ζ, hζ⟩ := derivation_extends_localization ℂ (Poly n ⧸ I) K K ε
  refine ⟨ζ, ?_⟩
  intro i
  change ζ (algebraMap (Poly n ⧸ I) K (Ideal.Quotient.mk I (MvPolynomial.X i))) = v i
  exact (hζ (Ideal.Quotient.mk I (MvPolynomial.X i))).trans
    ((hε (MvPolynomial.X i)).trans (MvPolynomial.mkDerivation_X _ _ i))

end
end DistinctDistances.TrackD
