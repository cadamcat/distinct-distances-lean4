import Mathlib

/-! Real polynomial coprimality is preserved by complex scalar extension. -/

namespace DistinctDistances.Bridges

open scoped TensorProduct
attribute [local instance] MvPolynomial.algebraMvPolynomial
noncomputable section

private abbrev RealPoly := MvPolynomial (Fin 3) ℝ
private abbrev ComplexPoly := MvPolynomial (Fin 3) ℂ

private def realPolynomialBaseChange :
    (RealPoly ⊗[ℝ] ℂ) ≃ₐ[RealPoly] ComplexPoly where
  toRingEquiv := ((Algebra.TensorProduct.comm ℝ RealPoly ℂ).trans
    ((MvPolynomial.algebraTensorAlgEquiv ℝ ℂ).restrictScalars ℝ)).toRingEquiv
  commutes' := by
    intro p
    change (MvPolynomial.algebraTensorAlgEquiv ℝ ℂ)
      ((Algebra.TensorProduct.comm ℝ RealPoly ℂ) (p ⊗ₜ[ℝ] 1)) =
      MvPolynomial.map (algebraMap ℝ ℂ) p
    simp only [Algebra.TensorProduct.comm_tmul, MvPolynomial.algebraTensorAlgEquiv_tmul,
      one_smul]

private theorem realPolynomial_flat : Module.Flat RealPoly ComplexPoly :=
  Module.Flat.of_linearEquiv realPolynomialBaseChange.symm.toLinearEquiv

/-- In Noetherian UFDs, a flat faithful scalar extension preserves relative primality. -/
theorem relPrime_algebraMap_of_flat {R S : Type*} [CommRing R] [CommRing S]
    [IsDomain R] [IsDomain S] [UniqueFactorizationMonoid R] [UniqueFactorizationMonoid S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Algebra R S]
    [Module.Flat R S] [FaithfulSMul R S]
    (f g : R) (hf : f ≠ 0) (hcop : IsRelPrime f g) :
    IsRelPrime (algebraMap R S f) (algebraMap R S g) := by
  classical
  have hfmap : algebraMap R S f ≠ 0 := by
    exact fun h => hf ((FaithfulSMul.algebraMap_injective R S)
      (h.trans (map_zero _).symm))
  apply (UniqueFactorizationMonoid.isRelPrime_iff_no_prime_factors hfmap).mpr
  intro a haf hag ha
  let Q : Ideal S := Ideal.span {a}
  let : Q.IsPrime := Ideal.isPrime_span_singleton_of_prime ha
  let P : Ideal R := Q.comap (algebraMap R S)
  let : P.IsPrime := inferInstance
  let : Q.LiesOver P := ⟨rfl⟩
  have hfP : f ∈ P := Ideal.mem_span_singleton.mpr haf
  have hgP : g ∈ P := Ideal.mem_span_singleton.mpr hag
  have hPbot : P ≠ ⊥ := by
    intro h
    exact hf (Ideal.mem_bot.mp (h ▸ hfP))
  have hheight : P.height ≤ Q.height := by
    rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown P Q]
    exact le_add_of_nonneg_right zero_le
  have hPle : P.height ≤ 1 :=
    hheight.trans (Ideal.height_span_singleton_le_one ha.not_isUnit)
  have hPheight : P.height = 1 := by
    apply le_antisymm hPle
    apply Order.one_le_iff_ne_zero.mpr
    simpa only [ne_eq, Ideal.height_eq_zero_iff_eq_bot] using hPbot
  let : P.IsPrincipal := UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hPheight
  have hu : IsUnit (Submodule.IsPrincipal.generator P) := hcop
    ((Submodule.IsPrincipal.mem_iff_generator_dvd P).mp hfP)
    ((Submodule.IsPrincipal.mem_iff_generator_dvd P).mp hgP)
  exact (show P.IsPrime from inferInstance).ne_top
    (P.eq_top_of_isUnit_mem (Submodule.IsPrincipal.generator_mem P) hu)

theorem real_coprimality (f g : RealPoly) (hcop : IsRelPrime f g) :
    IsRelPrime (MvPolynomial.map (algebraMap ℝ ℂ) f)
      (MvPolynomial.map (algebraMap ℝ ℂ) g) := by
  by_cases hf : f = 0
  · subst f
    have hu : IsUnit g := hcop (dvd_zero g) (dvd_refl g)
    intro a _ hag
    exact isUnit_of_dvd_unit hag (hu.map (MvPolynomial.map (algebraMap ℝ ℂ)))
  · let : Module.Flat RealPoly ComplexPoly := realPolynomial_flat
    exact relPrime_algebraMap_of_flat f g hf hcop

end
end DistinctDistances.Bridges
