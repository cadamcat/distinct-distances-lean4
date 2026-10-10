import DistinctDistances.TrackA.AlgebraicEtaleOpenSupport
import DistinctDistances.TrackA.GenericFiberFieldSupport

set_option backward.isDefEq.respectTransparency false

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical TensorProduct

/-- A closed field fiber of a finite etale domain map has the original
positive module rank, expressed as literal base algebra homomorphisms. -/
theorem finite_etale_domain_field_hom_count (R B K : Type*)
    [CommRing R] [IsDomain R] [CommRing B] [IsDomain B] [Algebra R B]
    [Module.Finite R B] [Module.IsTorsionFree R B] [Algebra.Etale R B]
    [Field K] [Algebra R K] [IsAlgClosed K] :
    0 < Module.finrank R B ∧ Finite (B →ₐ[R] K) ∧
      Nat.card (B →ₐ[R] K) = Module.finrank R B := by
  obtain ⟨hf, hc⟩ := finite_etale_closed_algHom_count K (K ⊗[R] B)
  let e := (AlgHom.liftEquiv R K B K).symm
  letI := hf
  haveI : Finite (B →ₐ[R] K) := Finite.of_equiv _ e
  exact ⟨Module.finrank_pos, inferInstance,
    (Nat.card_congr e.symm).trans (hc.trans (finite_flat_domain_field_finrank R B K))⟩

/-- Extending a field point across the same principal base localization
preserves the original algebra homomorphisms and their actual source. -/
def localized_base_field_hom_equiv (R B Rg Bg K : Type*)
    [CommRing R] [CommRing B] [CommRing Rg] [CommRing Bg] [Field K]
    [Algebra R B] [Algebra R Rg] [Algebra R Bg] [Algebra B Bg] [Algebra Rg Bg]
    [Algebra R K] [Algebra Rg K]
    [IsScalarTower R B Bg] [IsScalarTower R Rg Bg] [IsScalarTower R Rg K]
    (g : R) [IsLocalization.Away g Rg] [IsLocalization.Away (algebraMap R B g) Bg]
    (hgK : algebraMap R K g ≠ 0) :
    (Bg →ₐ[Rg] K) ≃ (B →ₐ[R] K) := by
  let embed : B →ₐ[R] Bg := IsScalarTower.toAlgHom R B Bg
  let lift (f : B →ₐ[R] K) : Bg →ₐ[R] K := by
    letI := f.toRingHom.toAlgebra
    haveI : IsScalarTower R B K := IsScalarTower.of_algHom f
    exact IsLocalization.Away.liftAlgHom (A := R) (algebraMap R B g)
      (by change IsUnit (f (algebraMap R B g)); rw [f.commutes]; exact isUnit_iff_ne_zero.mpr hgK)
  have hlift (f : B →ₐ[R] K) (b : B) : lift f (algebraMap B Bg b) = f b := by
    dsimp only [lift]
    exact IsLocalization.Away.lift_eq (g := f.toRingHom) (algebraMap R B g)
      (by change IsUnit (f (algebraMap R B g)); rw [f.commutes]; exact isUnit_iff_ne_zero.mpr hgK) b
  let fromPoint (f : B →ₐ[R] K) : Bg →ₐ[Rg] K :=
    { __ := (lift f).toRingHom
      commutes' r := by
        have heq : (lift f).toRingHom.comp (algebraMap Rg Bg) = algebraMap Rg K := by
          apply IsLocalization.ringHom_ext (Submonoid.powers g)
          ext a
          simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply R Rg Bg,
            ← IsScalarTower.algebraMap_apply R Rg K]
          exact (lift f).commutes a
        exact RingHom.congr_fun heq r }
  refine
    { toFun := fun h => (h.restrictScalars R).comp embed
      invFun := fromPoint
      left_inv := ?_
      right_inv := ?_ }
  · intro h
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext (Submonoid.powers (algebraMap R B g))
    ext b
    exact hlift _ b
  · intro f
    apply AlgHom.ext
    intro b
    exact hlift f b

/-- One nonzero base denominator gives every algebraically closed field
point the same positive number of original source algebra homomorphisms.
No finiteness of the unshrunk source map is assumed. -/
theorem algebraic_finiteType_field_hom_fibers (R B : Type*)
    [CommRing R] [IsDomain R] [CharZero R] [IsNoetherianRing R]
    [CommRing B] [IsDomain B] [Algebra R B] [Algebra.FiniteType R B]
    [Algebra.IsAlgebraic R B] [Module.IsTorsionFree R B] :
    ∃ g : R, g ≠ 0 ∧ ∃ r : ℕ, 0 < r ∧
      ∀ (K : Type*) [Field K] [Algebra R K] [IsAlgClosed K],
        algebraMap R K g ≠ 0 → Finite (B →ₐ[R] K) ∧ Nat.card (B →ₐ[R] K) = r := by
  obtain ⟨g, hg, hf, he⟩ := algebraic_finiteType_finite_etale_base_open R B
  let Rg := Localization (Submonoid.powers g)
  let Bg := Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers g))
  have hM : Submonoid.powers g ≤ nonZeroDivisors R := Submonoid.powers_le.mpr
    (mem_nonZeroDivisors_of_ne_zero hg)
  have hMB : Algebra.algebraMapSubmonoid B (Submonoid.powers g) ≤ nonZeroDivisors B :=
    Submonoid.map_le_of_le_comap _ (hM.trans
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (FaithfulSMul.algebraMap_injective R B)))
  haveI : IsDomain Rg := IsLocalization.isDomain_of_le_nonZeroDivisors Rg hM
  haveI : IsDomain Bg := IsLocalization.isDomain_of_le_nonZeroDivisors Bg hMB
  haveI : Module.IsTorsionFree Rg Bg := Module.IsTorsionFree.of_isLocalization R B hM
  haveI : IsLocalization.Away (algebraMap R B g) Bg := by
    change IsLocalization (Submonoid.powers (algebraMap R B g)) Bg
    rw [show Submonoid.powers (algebraMap R B g) =
      Algebra.algebraMapSubmonoid B (Submonoid.powers g) by
      simp [Algebra.algebraMapSubmonoid, Submonoid.map_powers]]
    infer_instance
  haveI : Module.Finite Rg Bg := hf
  haveI : Algebra.Etale Rg Bg := he
  refine ⟨g, hg, Module.finrank Rg Bg, Module.finrank_pos, ?_⟩
  intro K _ _ _ hgK
  let hunit : IsUnit (algebraMap R K g) := isUnit_iff_ne_zero.mpr hgK
  letI : Algebra Rg K := (IsLocalization.Away.lift (S := Rg) g hunit).toAlgebra
  haveI : IsScalarTower R Rg K := IsScalarTower.of_algebraMap_eq fun a =>
    (IsLocalization.Away.lift_eq g hunit a).symm
  obtain ⟨_, hfinite, hcard⟩ := finite_etale_domain_field_hom_count Rg Bg K
  let e := localized_base_field_hom_equiv R B Rg Bg K g hgK
  letI := hfinite
  exact ⟨Finite.of_equiv _ e, (Nat.card_congr e.symm).trans hcard⟩

end
end DistinctDistances.TrackA
