import DistinctDistances.TrackA.PointPowerLengthSupport
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import OAI.NumberTheory.PiExponent.Polynomials.PolynomialGrowthRanks

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical
open MvPolynomial

abbrev PointJetIndex (n t : ℕ) := {d : Fin n →₀ ℕ // d.degree < t}

instance pointJetIndex_fintype (n t : ℕ) : Fintype (PointJetIndex n t) := by
  have hh : {d : Fin n →₀ ℕ | d.degree < t}.Finite :=
    (OAI.QuarticPowerFree.simplexExponents n t).finite_toSet.subset (by
      intro d hd
      exact (OAI.QuarticPowerFree.mem_simplexExponents d).mpr hd.le)
  exact hh.fintype

theorem pointJetIndex_card (n t : ℕ) :
    Fintype.card (PointJetIndex n (t+1)) = (t+n).choose n := by
  let e : PointJetIndex n (t+1) ≃ (OAI.QuarticPowerFree.simplexExponents n t) :=
    Equiv.subtypeEquivRight (fun d => by
      rw [OAI.QuarticPowerFree.mem_simplexExponents]
      omega)
  rw [Fintype.card_congr e, Fintype.card_coe, OAI.QuarticPowerFree.card_simplexExponents]

def pointJetProjection (n t : ℕ) : Poly n →ₗ[ℂ] (PointJetIndex n t →₀ ℂ) :=
  (Finsupp.lcomapDomain Subtype.val Subtype.val_injective).comp
    (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

@[simp] theorem pointJetProjection_apply (n t : ℕ) (p : Poly n) (d : PointJetIndex n t) :
    pointJetProjection n t p d = p.coeff d.val := rfl

theorem pointJetProjection_kernel (n t : ℕ) :
    LinearMap.ker (pointJetProjection n t) =
      ((MvPolynomial.idealOfVars (Fin n) ℂ)^t).restrictScalars ℂ := by
  ext p
  rw [LinearMap.mem_ker]
  change pointJetProjection n t p = 0 ↔ p ∈ MvPolynomial.idealOfVars (Fin n) ℂ ^ t
  rw [MvPolynomial.mem_pow_idealOfVars_iff']
  constructor
  · intro h d hd
    exact congrArg (fun q : PointJetIndex n t →₀ ℂ => q ⟨d,hd⟩) h
  · intro h
    ext d
    exact h d.val d.property

theorem pointJetProjection_surjective (n t : ℕ) : Function.Surjective (pointJetProjection n t) := by
  intro q
  let p : Poly n := (AddMonoidAlgebra.coeffLinearEquiv ℂ).symm
    ((Finsupp.lmapDomain ℂ ℂ Subtype.val) q)
  refine ⟨p, ?_⟩
  ext d
  simp [p, pointJetProjection, Finsupp.lcomapDomain, Finsupp.lmapDomain,
    Finsupp.comapDomain_apply, Finsupp.mapDomain_injective Subtype.val_injective]

def pointJetQuotientEquiv (n t : ℕ) :
    (Poly n ⧸ MvPolynomial.idealOfVars (Fin n) ℂ ^ t) ≃ₗ[ℂ] (PointJetIndex n t →₀ ℂ) := by
  let I := MvPolynomial.idealOfVars (Fin n) ℂ ^ t
  exact (Submodule.Quotient.restrictScalarsEquiv ℂ I).symm.trans
    ((Submodule.quotEquivOfEq (I.restrictScalars ℂ) (LinearMap.ker (pointJetProjection n t))
      (pointJetProjection_kernel n t).symm).trans
        (LinearMap.quotKerEquivOfSurjective (pointJetProjection n t) (pointJetProjection_surjective n t)))

instance point_jet_quotient_finite (n t : ℕ) :
    Module.Finite ℂ (Poly n ⧸ MvPolynomial.idealOfVars (Fin n) ℂ ^ t) :=
  (pointJetQuotientEquiv n t).symm.finiteDimensional

theorem point_jet_quotient_finrank (n t : ℕ) :
    Module.finrank ℂ (Poly n ⧸ MvPolynomial.idealOfVars (Fin n) ℂ ^ (t+1)) = (t+n).choose n := by
  rw [(pointJetQuotientEquiv n (t+1)).finrank_eq, Module.finrank_finsupp,
    Module.finrank_self, mul_one, pointJetIndex_card]

theorem mem_vars_power_iff_series_order {n : ℕ} (f : Poly n) (t : ℕ) :
    f ∈ MvPolynomial.idealOfVars (Fin n) ℂ ^ t ↔
      (t : ℕ∞) ≤ (f : MvPowerSeries (Fin n) ℂ).order := by
  rw [MvPolynomial.mem_pow_idealOfVars_iff']
  constructor
  · intro h
    exact MvPowerSeries.nat_le_order (by simpa only [MvPolynomial.coeff_coe] using h)
  · intro h d hd
    exact MvPowerSeries.coeff_of_lt_order ((WithTop.coe_lt_coe.mpr hd).trans_le h)

theorem vars_power_mul_detect {n : ℕ} (f : Poly n) (s : ℕ)
    (hs : (f : MvPowerSeries (Fin n) ℂ).order = (s : ℕ∞)) (t : ℕ) (hst : s ≤ t)
    (a : Poly n) :
    f*a ∈ MvPolynomial.idealOfVars (Fin n) ℂ ^ t ↔
      a ∈ MvPolynomial.idealOfVars (Fin n) ℂ ^ (t-s) := by
  rw [mem_vars_power_iff_series_order, MvPolynomial.coe_mul, MvPowerSeries.order_mul, hs,
    mem_vars_power_iff_series_order]
  by_cases ha : a = 0
  · subst a
    simp
  · have ha' : (a : MvPowerSeries (Fin n) ℂ) ≠ 0 := by
      intro h
      apply ha
      apply MvPolynomial.coe_injective (Fin n) ℂ
      simpa only [MvPolynomial.coe_zero] using h
    have hf := MvPowerSeries.ne_zero_iff_order_finite.mp ha'
    rw [← hf]
    norm_cast
    omega

end
end DistinctDistances.TrackA
