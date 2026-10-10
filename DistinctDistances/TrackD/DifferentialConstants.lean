import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Analysis.Complex.Polynomial.Basic

namespace DistinctDistances.TrackD

open scoped TensorProduct
noncomputable section

open KaehlerDifferential

/-- The Jacobi–Zariski sequence injects differentials from the base of a formally smooth
field extension. -/
theorem mapBaseChange_injective_of_smooth
    (R E K : Type*) [CommRing R] [CommRing E] [CommRing K]
    [Algebra R E] [Algebra R K] [Algebra E K] [IsScalarTower R E K]
    [Algebra.FormallySmooth E K] : Function.Injective (mapBaseChange R E K) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨u, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange R E K x).mp hx
  rw [Subsingleton.elim u 0, map_zero]

/-- Differentiation of the transcendental coordinate in the rational function field,
obtained by the étale localization comparison. -/
def rationalCoordinateDifferential :
    KaehlerDifferential ℂ (FractionRing (Polynomial ℂ)) →ₗ[FractionRing (Polynomial ℂ)]
      FractionRing (Polynomial ℂ) :=
  (((Algebra.linearMap (Polynomial ℂ) (FractionRing (Polynomial ℂ))).comp
      (polynomialEquiv ℂ).toLinearMap).liftBaseChange (FractionRing (Polynomial ℂ))).comp
    (tensorKaehlerEquivOfFormallyEtale ℂ (Polynomial ℂ)
      (FractionRing (Polynomial ℂ))).symm.toLinearMap

theorem rationalCoordinateDifferential_X :
    rationalCoordinateDifferential
      (D ℂ (FractionRing (Polynomial ℂ))
        (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)) Polynomial.X)) = 1 := by
  simp [rationalCoordinateDifferential,
    tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap, polynomialEquiv_D]

/-- In a finitely generated characteristic-zero field extension, an element killed by
the universal differential is algebraic over the ground field. The proof tests a purported
transcendental element in its own rational function subfield. -/
theorem differential_zero_isAlgebraic (K : Type*) [Field K] [Algebra ℂ K]
    [Algebra.EssFiniteType ℂ K] (x : K) (hx : D ℂ K x = 0) : IsAlgebraic ℂ x := by
  by_contra hAlg
  let E := FractionRing (Polynomial ℂ)
  have hi : Function.Injective (Polynomial.aeval x : Polynomial ℂ →ₐ[ℂ] K) :=
    transcendental_iff_injective.mp hAlg
  let e : E →ₐ[ℂ] K := IsFractionRing.liftAlgHom hi
  letI : Algebra E K := e.toRingHom.toAlgebra
  letI : IsScalarTower ℂ E K := IsScalarTower.of_algHom e
  letI : Algebra.EssFiniteType E K := Algebra.EssFiniteType.of_comp ℂ E K
  have hz : algebraMap E K (algebraMap (Polynomial ℂ) E Polynomial.X) = x := by
    change e (algebraMap (Polynomial ℂ) E Polynomial.X) = x
    simp [e, IsFractionRing.lift_algebraMap]
  have ht : (1 : K) ⊗ₜ[E] D ℂ E (algebraMap (Polynomial ℂ) E Polynomial.X) = 0 := by
    apply (mapBaseChange_injective_of_smooth ℂ E K).eq_iff.mp
    simp only [mapBaseChange_tmul, map_D, one_smul, hz, hx, map_zero]
  let detector : K ⊗[E] KaehlerDifferential ℂ E →ₗ[K] K :=
    ((Algebra.linearMap E K).comp rationalCoordinateDifferential).liftBaseChange K
  have h01 : (1 : K) = 0 := by
    have := congrArg detector ht
    dsimp only [detector, E] at this
    erw [LinearMap.liftBaseChange_tmul] at this
    simpa only [LinearMap.comp_apply, rationalCoordinateDifferential_X,
      Algebra.linearMap_apply, map_one, one_smul, map_zero] using this
  exact one_ne_zero h01

/-- Over `ℂ`, the algebraic constants in a function field are scalars. -/
theorem differential_zero_is_constant (K : Type*) [Field K] [Algebra ℂ K]
    [Algebra.EssFiniteType ℂ K] (x : K) (hx : D ℂ K x = 0) :
    ∃ c : ℂ, x = algebraMap ℂ K c := by
  have hAlg := differential_zero_isAlgebraic K x hx
  have hm := minpoly.monic hAlg.isIntegral
  have hd := IsAlgClosed.degree_eq_one_of_irreducible ℂ (minpoly.irreducible hAlg.isIntegral)
  have hroot := minpoly.aeval ℂ x
  rw [Polynomial.eq_X_add_C_of_degree_eq_one hd, hm,
    Polynomial.C_1, one_mul, map_add, Polynomial.aeval_X, Polynomial.aeval_C,
    add_eq_zero_iff_eq_neg] at hroot
  exact ⟨-(minpoly ℂ x).coeff 0, by simpa only [map_neg] using hroot⟩

end
end DistinctDistances.TrackD
