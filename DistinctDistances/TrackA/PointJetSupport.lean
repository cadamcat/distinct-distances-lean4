import DistinctDistances.Foundations.PointLocal

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical
open MvPolynomial

abbrev PlaneJetIndex (t : ℕ) := {d : Fin 2 →₀ ℕ // d.degree < t}

instance planeJetIndex_fintype (t : ℕ) : Fintype (PlaneJetIndex t) := by
  have hh : {d : Fin 2 →₀ ℕ | d.degree < t}.Finite :=
    (OAI.QuarticPowerFree.simplexExponents 2 t).finite_toSet.subset (by
      intro d hd
      exact (OAI.QuarticPowerFree.mem_simplexExponents d).mpr hd.le)
  exact hh.fintype

theorem planeJetIndex_card (t : ℕ) : Fintype.card (PlaneJetIndex t) = (t+1).choose 2 := by
  by_cases ht : t = 0
  · subst t
    haveI : IsEmpty (PlaneJetIndex 0) := ⟨fun d => by have := d.property; omega⟩
    simp
  let e : PlaneJetIndex t ≃ (OAI.QuarticPowerFree.simplexExponents 2 (t-1)) :=
    Equiv.subtypeEquivRight (fun d => by
      rw [OAI.QuarticPowerFree.mem_simplexExponents]
      omega)
  rw [Fintype.card_congr e, Fintype.card_coe, OAI.QuarticPowerFree.card_simplexExponents]
  congr 1
  omega

def planeJetProjection (t : ℕ) : Poly 2 →ₗ[ℂ] (PlaneJetIndex t →₀ ℂ) :=
  (Finsupp.lcomapDomain Subtype.val Subtype.val_injective).comp
    (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

@[simp] theorem planeJetProjection_apply (t : ℕ) (p : Poly 2) (d : PlaneJetIndex t) :
    planeJetProjection t p d = p.coeff d.val := rfl

theorem planeJetProjection_kernel (t : ℕ) :
    LinearMap.ker (planeJetProjection t) =
      ((MvPolynomial.idealOfVars (Fin 2) ℂ)^t).restrictScalars ℂ := by
  ext p
  rw [LinearMap.mem_ker]
  change planeJetProjection t p = 0 ↔ p ∈ MvPolynomial.idealOfVars (Fin 2) ℂ ^ t
  rw [MvPolynomial.mem_pow_idealOfVars_iff']
  constructor
  · intro h d hd
    have hh := congrArg (fun q : PlaneJetIndex t →₀ ℂ => q ⟨d,hd⟩) h
    exact hh
  · intro h
    ext d
    exact h d.val d.property

theorem planeJetProjection_surjective (t : ℕ) : Function.Surjective (planeJetProjection t) := by
  intro q
  let p : Poly 2 := (AddMonoidAlgebra.coeffLinearEquiv ℂ).symm
    ((Finsupp.lmapDomain ℂ ℂ Subtype.val) q)
  refine ⟨p, ?_⟩
  ext d
  simp [p, planeJetProjection, Finsupp.lcomapDomain, Finsupp.lmapDomain,
    Finsupp.comapDomain_apply, Finsupp.mapDomain_injective Subtype.val_injective]

def planeJetQuotientEquiv (t : ℕ) :
    (Poly 2 ⧸ MvPolynomial.idealOfVars (Fin 2) ℂ ^ t) ≃ₗ[ℂ] (PlaneJetIndex t →₀ ℂ) := by
  let I := MvPolynomial.idealOfVars (Fin 2) ℂ ^ t
  exact (Submodule.Quotient.restrictScalarsEquiv ℂ I).symm.trans
    ((Submodule.quotEquivOfEq (I.restrictScalars ℂ) (LinearMap.ker (planeJetProjection t))
      (planeJetProjection_kernel t).symm).trans
        (LinearMap.quotKerEquivOfSurjective (planeJetProjection t) (planeJetProjection_surjective t)))

instance plane_jet_quotient_finite (t : ℕ) :
    Module.Finite ℂ (Poly 2 ⧸ MvPolynomial.idealOfVars (Fin 2) ℂ ^ t) :=
  (planeJetQuotientEquiv t).symm.finiteDimensional

theorem plane_jet_quotient_finrank (t : ℕ) :
    Module.finrank ℂ (Poly 2 ⧸ MvPolynomial.idealOfVars (Fin 2) ℂ ^ t) = (t+1).choose 2 := by
  rw [(planeJetQuotientEquiv t).finrank_eq, Module.finrank_finsupp,
    Module.finrank_self, mul_one, planeJetIndex_card]

end
end DistinctDistances.TrackA
