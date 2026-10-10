import DistinctDistances.TrackA.FormalOriginLengthSupport

namespace DistinctDistances.TrackA
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped Classical
open IsLocalRing
open OAI.BoundaryOnly.FormalObstruction.FormalCorrection

/-- Transport quotient lengths without unfolding the implementation of
the ambient equivalence. -/
theorem algEquiv_quotient_field_length {K R S : Type*} [Field K]
    [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    (e : R ≃ₐ[K] S) (I : Ideal R) (J : Ideal S) (h : I.map e.toRingHom = J) :
    Module.length K (R ⧸ I) = Module.length K (S ⧸ J) :=
  (Ideal.quotientEquivAlg I J e h.symm).toLinearEquiv.length_eq

/-- An actual formal quotient equivalence transports all maximal-ideal
power quotients, with their exact coefficient-field lengths. -/
theorem formalQuotient_power_field_length {K β α : Type}
    [Field K] [Fintype β] [Fintype α]
    (I : Ideal (MvPowerSeries β K)) [I.IsPrime]
    (e : (MvPowerSeries β K ⧸ I) ≃ₐ[K] MvPowerSeries α K) (r : ℕ) :
    Module.length K (MvPowerSeries β K ⧸ I ⊔ maximalIdeal (MvPowerSeries β K)^r) =
      Module.length K (MvPowerSeries α K ⧸ maximalIdeal (MvPowerSeries α K)^r) := by
  let S := MvPowerSeries β K
  let Q := S ⧸ I
  letI : IsLocalRing Q := IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective
  have hm : (maximalIdeal S ^ r).map (Ideal.Quotient.mk I) = maximalIdeal Q ^ r := by
    rw [Ideal.map_pow, map_maximalIdeal_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective]
  have he : (maximalIdeal Q ^ r).map e.toRingHom =
      maximalIdeal (MvPowerSeries α K)^r := by
    rw [Ideal.map_pow]
    exact congrArg (fun J => J^r)
      (map_maximalIdeal_of_surjective (R := Q) e.toRingHom e.surjective)
  let e₀ := DoubleQuot.quotQuotEquivQuotSupₐ K I (maximalIdeal S^r)
  have h₀ := e₀.toLinearEquiv.length_eq
  change Module.length K (Q ⧸ (maximalIdeal S^r).map (Ideal.Quotient.mk I)) = _ at h₀
  rw [hm] at h₀
  let e₁ := Ideal.quotientEquivAlg (maximalIdeal Q^r)
    (maximalIdeal (MvPowerSeries α K)^r) e he.symm
  exact h₀.symm.trans e₁.toLinearEquiv.length_eq

/-- The original base-chart local residue is the original coefficient field. -/
def formalOriginResidueEquiv (β : Type) [Fintype β] :
    ResidueField (AffineEtaleChart.base (K := ℂ) (α := β)).LocalRing ≃ₐ[ℂ] ℂ := by
  let E : AffineEtaleChart ℂ β := .base
  let f : MvPolynomial β ℂ →ₐ[ℂ] ℂ :=
    ⟨MvPolynomial.constantCoeff, fun c => MvPolynomial.constantCoeff_C β c⟩
  have hp : E.point = RingHom.ker f.toRingHom := rfl
  have hsurj : Function.Surjective f :=
    fun c => ⟨MvPolynomial.C c, MvPolynomial.constantCoeff_C β c⟩
  letI : E.point.IsMaximal := by
    rw [hp]
    exact RingHom.ker_isMaximal_of_surjective f.toRingHom hsurj
  let e₀ : (E.S ⧸ E.point) ≃ₐ[ℂ] ℂ :=
    (Ideal.quotientEquivAlgOfEq ℂ hp).trans
      (Ideal.quotientKerAlgEquivOfSurjective (f := f) hsurj)
  let e := (IsLocalization.AtPrime.equivQuotMaximalIdealPow E.point E.LocalRing 1).restrictScalars ℂ
  let e₁ : (E.S ⧸ E.point) ≃ₐ[ℂ] ResidueField E.LocalRing :=
    ((Ideal.quotientEquivAlgOfEq ℂ (pow_one E.point).symm).trans e).trans
      (Ideal.quotientEquivAlgOfEq ℂ (pow_one (maximalIdeal E.LocalRing)))
  exact e₁.symm.trans e₀

theorem formalOrigin_length_eq_complex_length (β : Type) [Fintype β]
    (M : Type*) [AddCommGroup M] [Module ℂ M]
    [Module (AffineEtaleChart.base (K := ℂ) (α := β)).LocalRing M]
    [IsScalarTower ℂ (AffineEtaleChart.base (K := ℂ) (α := β)).LocalRing M] :
    Module.length (AffineEtaleChart.base (K := ℂ) (α := β)).LocalRing M =
      Module.length ℂ M :=
  length_eq_field_of_residue_equiv _ (formalOriginResidueEquiv β) M

/-- The actual centered polynomial system has exactly the local power
quotient lengths of its free formal coordinates. -/
theorem formalOrigin_system_power_length {α ι : Type} [Fintype α] [Fintype ι]
    (F : ι → MvPolynomial (α ⊕ ι) ℂ) (hF : ∀ i, (F i).coeff 0 = 0)
    (hdet : IsUnit (internalJacobian F).det) (r : ℕ) :
    Module.length ℂ ((AffineEtaleChart.base (K := ℂ) (α := α ⊕ ι)).LocalRing ⧸
      (Ideal.span (Set.range F)).map (algebraMap (MvPolynomial (α ⊕ ι) ℂ)
        (AffineEtaleChart.base (K := ℂ) (α := α ⊕ ι)).LocalRing) ⊔
      maximalIdeal (AffineEtaleChart.base (K := ℂ) (α := α ⊕ ι)).LocalRing^r) =
    Module.length ℂ (MvPowerSeries α ℂ ⧸ maximalIdeal (MvPowerSeries α ℂ)^r) := by
  let E : AffineEtaleChart ℂ (α ⊕ ι) := .base
  let I := (Ideal.span (Set.range F)).map (algebraMap (MvPolynomial (α ⊕ ι) ℂ) E.LocalRing)
  let J : Ideal (MvPowerSeries (α ⊕ ι) ℂ) :=
    Ideal.span (Set.range (fun i => (F i).toMvPowerSeries))
  letI : J.IsPrime := formalPolynomial_ideal_isPrime F hF hdet
  obtain ⟨e⟩ := formalPolynomial_quotient_exists F hF hdet
  rw [← formalOrigin_length_eq_complex_length (α ⊕ ι), formalOrigin_quotient_length,
    Ideal.map_sup, Ideal.map_pow, formalOrigin_localExpansion_maximalIdeal,
    formalOrigin_localized_span_map F]
  exact formalQuotient_power_field_length J e r

end
end DistinctDistances.TrackA
