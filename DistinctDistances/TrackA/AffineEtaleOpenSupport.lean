import DistinctDistances.TrackA.NormalizationAffineRankSupport
import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Localization.Integral

set_option backward.isDefEq.respectTransparency false

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical

/-- The algebraic generic point of a finite characteristic-zero domain
extension is formally etale over the original base. This helper isolates
the field/localization instances from the concrete coordinate quotient. -/
theorem finite_domain_generic_etale (R B : Type*) [CommRing R] [IsDomain R]
    [CharZero R] [CommRing B] [IsDomain B] [Algebra R B]
    [Module.Finite R B] [Module.IsTorsionFree R B] : Algebra.IsEtaleAt R (⊥ : Ideal B) := by
  haveI : IsFractionRing B (Localization.AtPrime (⊥ : Ideal B)) := by
    simpa [Ideal.primeCompl_bot] using
      Localization.isLocalization (M := (⊥ : Ideal B).primeCompl)
  letI : Field (Localization.AtPrime (⊥ : Ideal B)) := IsFractionRing.toField B
  haveI : FaithfulSMul R (Localization.AtPrime (⊥ : Ideal B)) := by
    rw [faithfulSMul_iff_algebraMap_injective,
      IsScalarTower.algebraMap_eq R B (Localization.AtPrime ⊥)]
    exact (IsFractionRing.injective B _).comp (FaithfulSMul.algebraMap_injective R B)
  letI := FractionRing.liftAlgebra R (Localization.AtPrime (⊥ : Ideal B))
  haveI : Algebra.IsAlgebraic (FractionRing R) (Localization.AtPrime (⊥ : Ideal B)) :=
    isAlgebraic_of_isFractionRing R B (FractionRing R) (Localization.AtPrime (⊥ : Ideal B))
  haveI : Algebra.FormallyEtale (FractionRing R) (Localization.AtPrime (⊥ : Ideal B)) :=
    Algebra.FormallyEtale.of_isSeparable _ _
  haveI : Algebra.FormallyEtale R (FractionRing R) :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors R)
  exact Algebra.FormallyEtale.comp R (FractionRing R) (Localization.AtPrime (⊥ : Ideal B))

/-- Algebraicity shrinks a source principal etale open to a nonzero
principal BASE open. The map and its coordinate algebra are unchanged. -/
theorem finite_domain_etale_base_open (R B : Type*) [CommRing R] [IsDomain R]
    [CharZero R] [IsNoetherianRing R] [CommRing B] [IsDomain B] [Algebra R B]
    [Module.Finite R B] [Module.IsTorsionFree R B] :
      ∃ g : R, g ≠ 0 ∧ Algebra.Etale R (Localization.Away (algebraMap R B g)) := by
  haveI : Algebra.FinitePresentation R B := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  haveI : Algebra.IsEtaleAt R (⊥ : Ideal B) := finite_domain_generic_etale R B
  obtain ⟨b, hb, he⟩ := Algebra.exists_etale_of_isEtaleAt (R := R) (⊥ : Ideal B)
  have hb0 : b ≠ 0 := by simpa only [Ideal.mem_bot] using hb
  obtain ⟨g, hg, c, hgc⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := R) b).exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero hb0)
  refine ⟨g, hg, ?_⟩
  apply Algebra.basicOpen_subset_etaleLocus_iff_etale.mp
  have hbe : (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum B)) ⊆ Algebra.etaleLocus R B :=
    Algebra.basicOpen_subset_etaleLocus_iff_etale.mpr he
  rw [hgc]
  intro p hp
  exact hbe ((PrimeSpectrum.basicOpen_mul_le_left b c) hp)

/-- The actual original affine parameter map has an etale open given by
a nonzero polynomial on its original base. -/
theorem affineNormalization_etale_base_open {n k : ℕ} (V : AffineVariety n)
    (hV : V.IsIrreducible) (hd : V.dimension = k) (ψ : LinearProjection n k)
    (hf : (affineNormalizationMap V ψ).Finite) :
    letI := (affineNormalizationMap V ψ).toRingHom.toAlgebra
    ∃ g : Poly k, g ≠ 0 ∧ Algebra.Etale (Poly k)
      (Localization.Away (affineNormalizationMap V ψ g)) := by
  letI : V.ideal.IsPrime := hV
  letI := (affineNormalizationMap V ψ).toRingHom.toAlgebra
  letI : Module (Poly k) (Poly n ⧸ V.ideal) :=
    (affineNormalizationMap V ψ).toRingHom.toAlgebra.toModule
  haveI : Module.Finite (Poly k) (Poly n ⧸ V.ideal) := hf
  haveI : Module.IsTorsionFree (Poly k) (Poly n ⧸ V.ideal) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (affineNormalizationMap_injective V hV hd ψ hf)
  exact finite_domain_etale_base_open (Poly k) (Poly n ⧸ V.ideal)

end
end DistinctDistances.TrackA
