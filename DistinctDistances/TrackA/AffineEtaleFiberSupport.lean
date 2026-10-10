import DistinctDistances.TrackA.AffineEtaleOpenSupport
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.TensorProduct.Maps

set_option backward.isDefEq.respectTransparency false

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical TensorProduct

/-- A field specialization of a finite flat module over a domain has the
original module rank. This is the library's finite-flat fiber formula. -/
theorem finite_flat_domain_field_finrank (R M K : Type*) [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Flat R M]
    [Field K] [Algebra R K] :
    Module.finrank K (K ⊗[R] M) = Module.finrank R M := by
  let p : PrimeSpectrum K := ⟨⊥, inferInstance⟩
  calc
    Module.finrank K (K ⊗[R] M) = Module.rankAtStalk (K ⊗[R] M) p := by
      rw [Module.rankAtStalk_eq_finrank_of_free]
      rfl
    _ = Module.rankAtStalk M (p.comap (algebraMap R K)) :=
      Module.rankAtStalk_baseChange p
    _ = Module.finrank R M := by
      rw [Module.rankAtStalk_eq, Ideal.finrank_fiber_eq_finrank]

/-- An etale base principal open of a finite algebra supplies etale field
fibers and their exact original rank wherever its denominator is nonzero. -/
theorem etale_base_open_field_fiber (R B K : Type*) [CommRing R] [IsDomain R]
    [CommRing B] [Algebra R B] [Module.Finite R B] [Field K] [Algebra R K]
    (g : R) (hg : g ≠ 0)
    (he : Algebra.Etale R (Localization.Away (algebraMap R B g)))
    (hgK : algebraMap R K g ≠ 0) :
    Algebra.Etale K (K ⊗[R] B) ∧
      Module.finrank K (K ⊗[R] B) = Module.finrank R B := by
  let S := Submonoid.powers g
  let Rg := Localization S
  let Bg := Localization (Algebra.algebraMapSubmonoid B S)
  haveI : IsLocalization.Away (algebraMap R B g) Bg := by
    change IsLocalization (Submonoid.powers (algebraMap R B g)) Bg
    rw [show Submonoid.powers (algebraMap R B g) = Algebra.algebraMapSubmonoid B S by
      simp [S, Algebra.algebraMapSubmonoid, Submonoid.map_powers]]
    infer_instance
  haveI : Algebra.Etale R (Localization.Away (algebraMap R B g)) := he
  haveI : Algebra.Etale R Bg := Algebra.Etale.of_equiv
    ((IsLocalization.algEquiv (Submonoid.powers (algebraMap R B g))
      (Localization.Away (algebraMap R B g)) Bg).restrictScalars R)
  haveI : Algebra.Etale R Rg := Algebra.Etale.of_isLocalizationAway g
  haveI : Algebra.Etale Rg Bg := Algebra.Etale.of_restrictScalars R Rg Bg
  haveI : Module.Finite Rg Bg := Module.Finite.of_isLocalization R B S
  have hS : S ≤ nonZeroDivisors R := Submonoid.powers_le.mpr
    (mem_nonZeroDivisors_of_ne_zero hg)
  haveI : IsDomain Rg := IsLocalization.isDomain_of_le_nonZeroDivisors Rg hS
  haveI : FaithfulSMul R Rg := (faithfulSMul_iff_algebraMap_injective R Rg).mpr
    (IsLocalization.injective Rg hS)
  let hunit : IsUnit (algebraMap R K g) := isUnit_iff_ne_zero.mpr hgK
  letI : Algebra Rg K := (IsLocalization.Away.lift (S := Rg) g hunit).toAlgebra
  haveI : IsScalarTower R Rg K := IsScalarTower.of_algebraMap_eq fun r =>
    (IsLocalization.Away.lift_eq g hunit r).symm
  haveI : Algebra.IsPushout R Rg B Bg :=
    (Algebra.isPushout_of_isLocalization S Rg B Bg).symm
  let e : (K ⊗[Rg] Bg) ≃ₐ[K] (K ⊗[R] B) :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K)
      (Algebra.IsPushout.equiv R Rg B Bg).symm).trans
        (Algebra.TensorProduct.cancelBaseChange R Rg K K B)
  have hbc : IsBaseChange Rg (IsScalarTower.toAlgHom R B Bg).toLinearMap :=
    (inferInstance : Algebra.IsPushout R Rg B Bg).out
  refine ⟨Algebra.Etale.of_equiv e, ?_⟩
  exact e.toLinearEquiv.finrank_eq.symm.trans
    ((finite_flat_domain_field_finrank Rg Bg K).trans hbc.finrank_eq)

end
end DistinctDistances.TrackA
