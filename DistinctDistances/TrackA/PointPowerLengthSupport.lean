import DistinctDistances.TrackA.PointJetSupport
import DistinctDistances.TrackA.SeparatorTranslationSupport

namespace DistinctDistances.TrackA
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped Classical
open MvPolynomial IsLocalRing

theorem pointIdeal_origin_eq_vars (n : ℕ) :
    pointIdeal (0 : Point n) = MvPolynomial.idealOfVars (Fin n) ℂ := by
  ext p
  rw [pointIdeal, mem_vanishingIdeal_singleton_iff, aeval_eq_eval,
    eval_zero, ← pow_one (MvPolynomial.idealOfVars (Fin n) ℂ), mem_pow_idealOfVars_iff']
  constructor
  · intro hp d hd
    have he : d = 0 := (Finsupp.degree_eq_zero_iff d).mp (by omega)
    subst d
    exact hp
  · intro hp
    exact hp 0 (by simp)

def pointQuotientEquiv {n : ℕ} (p : Point n) : (Poly n ⧸ pointIdeal p) ≃ₐ[ℂ] ℂ := by
  have hker : pointIdeal p = RingHom.ker (MvPolynomial.aeval p : Poly n →ₐ[ℂ] ℂ) := by
    ext f
    rw [pointIdeal, mem_vanishingIdeal_singleton_iff, RingHom.mem_ker]
  have hsurj : Function.Surjective (MvPolynomial.aeval p : Poly n →ₐ[ℂ] ℂ) := by
    intro a
    exact ⟨C a, by simp⟩
  exact (Ideal.quotientEquivAlgOfEq ℂ hker).trans
    (Ideal.quotientKerAlgEquivOfSurjective hsurj)

def pointResidueEquiv {n : ℕ} (p : Point n) :
    IsLocalRing.ResidueField (PointLocalRing p) ≃ₐ[ℂ] ℂ := by
  let e := (IsLocalization.AtPrime.equivQuotMaximalIdealPow (pointIdeal p) (PointLocalRing p) 1).restrictScalars ℂ
  let e₁ : (Poly n ⧸ pointIdeal p) ≃ₐ[ℂ] IsLocalRing.ResidueField (PointLocalRing p) := by
    exact ((Ideal.quotientEquivAlgOfEq ℂ (pow_one (pointIdeal p)).symm).trans e).trans
      (Ideal.quotientEquivAlgOfEq ℂ (pow_one (maximalIdeal (PointLocalRing p))))
  exact e₁.symm.trans (pointQuotientEquiv p)

theorem point_local_length_eq_complex_length {n : ℕ} (p : Point n)
    (M : Type*) [AddCommGroup M] [Module ℂ M] [Module (PointLocalRing p) M]
    [IsScalarTower ℂ (PointLocalRing p) M] :
    Module.length (PointLocalRing p) M = Module.length ℂ M := by
  let R := PointLocalRing p
  letI : IsLocalHom (algebraMap ℂ R) := ⟨fun a ha =>
    isUnit_iff_ne_zero.mpr (fun hz => ha.ne_zero (by rw [hz, map_zero]))⟩
  have hres : Function.Surjective (algebraMap ℂ (ResidueField R)) := by
    intro a
    refine ⟨pointResidueEquiv p a, ?_⟩
    apply (pointResidueEquiv p).injective
    simpa only [Algebra.algebraMap_self, RingHom.id_apply] using
      (pointResidueEquiv p).commutes (pointResidueEquiv p a)
  have hres' : Function.Surjective (algebraMap (ResidueField ℂ) (ResidueField R)) := by
    intro a
    obtain ⟨c, hc⟩ := hres a
    refine ⟨IsLocalRing.residue ℂ c, ?_⟩
    change algebraMap (ResidueField ℂ) (ResidueField R) (algebraMap ℂ (ResidueField ℂ) c) = a
    rw [← IsScalarTower.algebraMap_apply, hc]
  have hfactor : Module.length (ResidueField ℂ) (ResidueField R) = 1 := by
    rw [Module.length_eq_of_surjective hres', Module.length_eq_one]
  have hh := IsLocalRing.length_restrictScalars ℂ R M
  rw [hfactor, mul_one] at hh
  exact hh.symm

def planePointPowerQuotientEquiv (p : Point 2) (t : ℕ) :
    (Poly 2 ⧸ pointIdeal p ^ t) ≃ₐ[ℂ]
      (Poly 2 ⧸ MvPolynomial.idealOfVars (Fin 2) ℂ ^ t) := by
  let e := OAI.PiExponent.WeightedBezout.translationEquiv p
  have hp : (pointIdeal p).map e.toRingHom = MvPolynomial.idealOfVars (Fin 2) ℂ := by
    have hh := separator_translation_pointIdeal p
    change (pointIdeal p).map e.toRingHom = pointIdeal (0 : Point 2) at hh
    exact hh.trans (pointIdeal_origin_eq_vars 2)
  have hpow : (pointIdeal p^t).map e.toRingHom = MvPolynomial.idealOfVars (Fin 2) ℂ ^t := by
    rw [Ideal.map_pow e.toRingHom (pointIdeal p) t, hp]
  exact Ideal.quotientEquivAlg (pointIdeal p^t) _ e hpow.symm

theorem plane_point_power_length (p : Point 2) (t : ℕ) :
    Module.length (PointLocalRing p)
      (PointLocalRing p ⧸ IsLocalRing.maximalIdeal (PointLocalRing p)^t) =
        ((t+1).choose 2 : ℕ∞) := by
  let e := (IsLocalization.AtPrime.equivQuotMaximalIdealPow (pointIdeal p) (PointLocalRing p) t).restrictScalars ℂ
  let e₀ := planePointPowerQuotientEquiv p t
  letI : Module.Finite ℂ (Poly 2 ⧸ pointIdeal p^t) := e₀.toLinearEquiv.symm.finiteDimensional
  letI : Module.Finite ℂ (PointLocalRing p ⧸ maximalIdeal (PointLocalRing p)^t) :=
    e.toLinearEquiv.finiteDimensional
  rw [point_local_length_eq_complex_length p, Module.length_eq_finrank,
    ← e.toLinearEquiv.finrank_eq, e₀.toLinearEquiv.finrank_eq, plane_jet_quotient_finrank]

end
end DistinctDistances.TrackA
