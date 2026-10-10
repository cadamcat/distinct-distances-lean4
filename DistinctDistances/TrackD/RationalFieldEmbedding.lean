import DistinctDistances.TrackD.RationalFunctionField
import DistinctDistances.TrackD.FieldTangent

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section

set_option maxHeartbeats 800000

/-- The rational-image coordinate function field embeds in the source function
field. The only geometric input is the explicit pullback-kernel lemma. -/
theorem rational_function_field_embedding {n m : ℕ}
    (X : AffineVariety n) (hX : X.IsIrreducible)
    (f : Fin m → Poly n) (g : Poly n) (hg : g ∉ X.ideal)
    (E K : Type*) [Field E] [Field K]
    [Algebra ℂ E] [Algebra ℂ K]
    [Algebra (Poly n ⧸ X.ideal) K] [IsScalarTower ℂ (Poly n ⧸ X.ideal) K]
    [IsFractionRing (Poly n ⧸ X.ideal) K]
    [Algebra (Poly m ⧸ (rationalImage X f g).ideal) E]
    [IsScalarTower ℂ (Poly m ⧸ (rationalImage X f g).ideal) E]
    [IsFractionRing (Poly m ⧸ (rationalImage X f g).ideal) E] :
    ∃ η : E →ₐ[ℂ] K, ∀ p : Poly m,
      η (coordinateFieldMap (rationalImage X f g).ideal E p) =
        rationalFieldPullback K (coordinateFieldMap X.ideal K) f g p := by
  let Y := rationalImage X f g
  let ψ := rationalFieldPullback K (coordinateFieldMap X.ideal K) f g
  have hker : RingHom.ker ψ = Y.ideal := rationalFieldPullback_kernel X hX K f g hg
  have hz : ∀ p ∈ Y.ideal, ψ p = 0 := by
    intro p hp
    exact RingHom.mem_ker.mp (hker.symm ▸ hp)
  let q : (Poly m ⧸ Y.ideal) →ₐ[ℂ] K := Ideal.Quotient.liftₐ Y.ideal ψ hz
  have hqp (p : Poly m) : q (Ideal.Quotient.mk Y.ideal p) = ψ p := by
    change Ideal.Quotient.lift Y.ideal ψ.toRingHom hz
      (Ideal.Quotient.mk Y.ideal p) = ψ p
    exact Ideal.Quotient.lift_mk Y.ideal ψ.toRingHom hz
  have hq : Function.Injective q := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    have hp : ψ p = 0 := (hqp p).symm.trans ha
    exact hker ▸ RingHom.mem_ker.mpr hp
  let η : E →ₐ[ℂ] K := IsFractionRing.liftAlgHom hq
  refine ⟨η, ?_⟩
  intro p
  change η (algebraMap (Poly m ⧸ Y.ideal) E (Ideal.Quotient.mk Y.ideal p)) = ψ p
  have hlift : η (algebraMap (Poly m ⧸ Y.ideal) E (Ideal.Quotient.mk Y.ideal p)) =
      q (Ideal.Quotient.mk Y.ideal p) := by
    exact IsFractionRing.lift_algebraMap hq _
  exact hlift.trans (hqp p)

/-- Function-field surjectivity for the actual rational-image closure. No rank
or transcendence-degree axiom is used. Denominator charts are chosen before
specializing at any source point. -/
theorem rational_function_field_tangent_surjective {n m : ℕ}
    (X : AffineVariety n) (hX : X.IsIrreducible)
    (f : Fin m → Poly n) (g : Poly n) (hg : g ∉ X.ideal)
    (K : Type*) [Field K] [Algebra ℂ K]
    [Algebra (Poly n ⧸ X.ideal) K] [IsScalarTower ℂ (Poly n ⧸ X.ideal) K]
    [IsFractionRing (Poly n ⧸ X.ideal) K] :
    fieldTangent (rationalImage X f g).ideal K
        (rationalFieldPullback K (coordinateFieldMap X.ideal K) f g) ≤
      (fieldTangent X.ideal K (coordinateFieldMap X.ideal K)).map
        (fieldRationalDifferential K (coordinateFieldMap X.ideal K) f g) := by
  let Y := rationalImage X f g
  letI : Y.ideal.IsPrime := rational_image_irreducible X hX f g hg
  let E := FractionRing (Poly m ⧸ Y.ideal)
  obtain ⟨η, hη⟩ := rational_function_field_embedding X hX f g hg E K
  letI : Algebra E K := η.toRingHom.toAlgebra
  letI : IsScalarTower ℂ E K := IsScalarTower.of_algHom η
  letI : Algebra (Poly m ⧸ Y.ideal) K :=
    ((η.toRingHom).comp (algebraMap (Poly m ⧸ Y.ideal) E)).toAlgebra
  letI : IsScalarTower (Poly m ⧸ Y.ideal) E K :=
    IsScalarTower.of_algebraMap_eq' (R := Poly m ⧸ Y.ideal) (S := E) (A := K) rfl
  letI : IsScalarTower ℂ (Poly m ⧸ Y.ideal) K :=
    IsScalarTower.of_algebraMap_eq (R := ℂ) (S := Poly m ⧸ Y.ideal) (A := K) (by
      intro z
      change algebraMap ℂ K z = η (algebraMap (Poly m ⧸ Y.ideal) E
        (algebraMap ℂ (Poly m ⧸ Y.ideal) z))
      rw [← IsScalarTower.algebraMap_apply ℂ (Poly m ⧸ Y.ideal) E]
      exact (η.commutes z).symm)
  letI : Algebra.EssFiniteType (Poly n ⧸ X.ideal) K :=
    Algebra.EssFiniteType.of_isLocalization K (nonZeroDivisors (Poly n ⧸ X.ideal))
  letI : Algebra.EssFiniteType ℂ K := Algebra.EssFiniteType.comp ℂ (Poly n ⧸ X.ideal) K
  letI : Algebra.EssFiniteType E K := Algebra.EssFiniteType.of_comp ℂ E K
  letI : CharZero E := charZero_of_inj_zero (by
    intro a ha
    have hc : (a : ℂ) = 0 := (algebraMap ℂ E).injective (by simpa using ha)
    exact_mod_cast hc)
  have hψ : (IsScalarTower.toAlgHom ℂ E K).comp (coordinateFieldMap Y.ideal E) =
      rationalFieldPullback K (coordinateFieldMap X.ideal K) f g := by
    apply AlgHom.ext
    intro p
    change η (coordinateFieldMap Y.ideal E p) = _
    exact hη p
  have hgne : coordinateFieldMap X.ideal K g ≠ 0 := by
    intro hzero
    apply hg
    exact coordinateFieldMap_kernel X.ideal K ▸ RingHom.mem_ker.mpr hzero
  have hcoords : ∀ i : Fin m,
      algebraMap E K (coordinateFieldMap Y.ideal E (MvPolynomial.X i)) =
        coordinateFieldMap X.ideal K (f i) / coordinateFieldMap X.ideal K g := by
    intro i
    change η (coordinateFieldMap Y.ideal E (MvPolynomial.X i)) = _
    simpa [rationalFieldPullback] using hη (MvPolynomial.X i)
  have h := field_rational_tangent_surjective X.ideal Y.ideal E K f g hgne hcoords
  simpa only [hψ] using h

end
end DistinctDistances.TrackD
