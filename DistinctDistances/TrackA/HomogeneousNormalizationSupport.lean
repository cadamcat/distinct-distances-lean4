import DistinctDistances.TrackA.Definitions
import DistinctDistances.OAIInterface.LinearNormalization
import OAI.NumberTheory.PiExponent.Polynomials.HomogeneousQuotientDimension

set_option backward.isDefEq.respectTransparency.types false

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical
attribute [local instance] MvPolynomial.gradedAlgebra
open OAI.PiExponentJets.W64

/-- The original internal-direct-sum theorem equips the actual
homogeneous polynomial quotient with its quotient-section grading. -/
def homogeneousQuotientGrading {n : ℕ} (I : Ideal (Poly n))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) ℂ)) :
    GradedAlgebra (quotientSection I) where
  toDecomposition :=
    (OAI.PiExponentJets.W25.quotientSection_isInternal I hI).chooseDecomposition
  one_mem := by
    refine ⟨1, MvPolynomial.isHomogeneous_one _ _, ?_⟩
    exact map_one (Ideal.Quotient.mk I)
  mul_mem := by
    intro a b p q hp hq
    obtain ⟨f, hf, rfl⟩ := hp
    obtain ⟨g, hg, rfl⟩ := hq
    exact ⟨f * g, hf.mul hg, map_mul (Ideal.Quotient.mk I) f g⟩

/-- The coordinate classes generate the actual quotient algebra. -/
theorem quotient_coordinate_adjoin {n : ℕ} (I : Ideal (Poly n)) :
    Algebra.adjoin ℂ (Set.range (fun i : Fin n => Ideal.Quotient.mk I (MvPolynomial.X i))) = ⊤ := by
  let q := Ideal.Quotient.mkₐ ℂ I
  have h := congrArg (Subalgebra.map q) (MvPolynomial.adjoin_range_X (R := ℂ) (σ := Fin n))
  simpa only [q, Ideal.Quotient.mkₐ_eq_mk, AlgHom.map_adjoin, ← Set.range_comp, Function.comp_def, Algebra.map_top,
    (AlgHom.range_eq_top q).mpr Ideal.Quotient.mk_surjective] using h

/-- Coordinate integrality makes the actual quotient finite over the
polynomial algebra on the selected parameters. -/
theorem normalization_finite_of_integral_coordinates {n s : ℕ}
    (I : Ideal (Poly n)) (z : Fin s → Poly n ⧸ I)
    (hi : ∀ i : Fin n, IsIntegral (Algebra.adjoin ℂ (Set.range z))
      (Ideal.Quotient.mk I (MvPolynomial.X i))) :
    (MvPolynomial.aeval (R := ℂ) z).Finite := by
  let Q := Poly n ⧸ I
  let x : Fin n → Q := fun i => Ideal.Quotient.mk I (MvPolynomial.X i)
  let g : Poly s →ₐ[ℂ] Q := MvPolynomial.aeval (R := ℂ) z
  let B := g.range
  have hx : Algebra.adjoin ℂ (Set.range x) = ⊤ := quotient_coordinate_adjoin I
  have hxi (i : Fin n) : IsIntegral B (x i) := by
    change IsIntegral (MvPolynomial.aeval (R := ℂ) z).range (x i)
    rw [← Algebra.adjoin_range_eq_range_aeval]
    exact hi i
  have hXB : Algebra.adjoin B (Set.range x) = ⊤ := by
    have hle : Algebra.adjoin ℂ (Set.range x) ≤
        (Algebra.adjoin B (Set.range x)).restrictScalars ℂ :=
      Algebra.adjoin_le_iff.mpr Algebra.subset_adjoin
    apply eq_top_iff.mpr
    intro a _
    exact hle (by rw [hx]; trivial)
  let : Module.Finite B (Algebra.adjoin B (Set.range x)) :=
    Algebra.finite_adjoin_of_finite_of_isIntegral (Set.finite_range x)
      (by rintro a ⟨i, rfl⟩; exact hxi i)
  let : Module.Finite B Q := Module.Finite.of_surjective
    (Algebra.adjoin B (Set.range x)).val.toLinearMap
    (fun a => ⟨⟨a, by rw [hXB]; trivial⟩, rfl⟩)
  have hv : B.val.Finite := by
    change (algebraMap B Q).Finite
    exact RingHom.finite_algebraMap.mpr inferInstance
  have hr : g.rangeRestrict.Finite :=
    AlgHom.Finite.of_surjective _ g.rangeRestrict_surjective
  exact hv.comp hr

/-- The original graded normalization gives actual independent linear
parameters and a finite polynomial map on this homogeneous quotient. -/
theorem homogeneous_quotient_linear_normalization {n : ℕ} (I : Ideal (Poly n))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) ℂ)) (hne : I ≠ ⊤) :
    ∃ s : ℕ, s ≤ n ∧ ∃ z : Fin s → Poly n ⧸ I,
      (∀ j, z j ∈ quotientSection I 1) ∧
      (∀ j, z j ∈ Submodule.span ℂ
        (Set.range (fun i : Fin n => Ideal.Quotient.mk I (MvPolynomial.X i)))) ∧
      Function.Injective (MvPolynomial.aeval (R := ℂ) z) ∧ (MvPolynomial.aeval (R := ℂ) z).Finite := by
  let Q := Poly n ⧸ I
  let : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr hne
  let : GradedAlgebra (quotientSection I) := homogeneousQuotientGrading I hI
  let x : Fin n → Q := fun i => Ideal.Quotient.mk I (MvPolynomial.X i)
  have hx (i : Fin n) : x i ∈ quotientSection I 1 :=
    ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X _ _, rfl⟩
  obtain ⟨s, hs, z, hz, hzi, hxi⟩ :=
    OAI.Lech.LinearNormalization.exists_linear_normalization (quotientSection I) x hx
  have hspan : Submodule.span ℂ (Set.range x) ≤ quotientSection I 1 :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hx i)
  exact ⟨s, hs, z, (fun j => hspan (hz j)), hz, hzi,
    normalization_finite_of_integral_coordinates I z hxi⟩

/-- The number of independent integral parameters is the actual
quotient's Krull dimension. -/
theorem homogeneous_normalization_dimension {n s : ℕ} (I : Ideal (Poly n))
    (z : Fin s → Poly n ⧸ I) (hi : Function.Injective (MvPolynomial.aeval (R := ℂ) z))
    (hf : (MvPolynomial.aeval (R := ℂ) z).Finite) :
    ringKrullDim (Poly n ⧸ I) = (s : WithBot ℕ∞) := by
  have h := OAI.PiExponentJets.W24.ringKrullDim_eq_of_integral_injective
    (MvPolynomial.aeval (R := ℂ) z).toRingHom hi hf.to_isIntegral
  simpa only [MvPolynomial.ringKrullDim_of_isNoetherianRing,
    ringKrullDim_eq_zero_of_field, ENat.card_eq_coe_natCard, Nat.card_fin, zero_add,
    WithBot.coe_natCast] using h

end
end DistinctDistances.TrackA
