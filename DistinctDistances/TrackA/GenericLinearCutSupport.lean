import DistinctDistances.TrackA.CutSaturationSupport
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Localization.BaseChange

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical
open scoped TensorProduct
attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- The universal linear equation, with its coefficients as independent
polynomial parameters. The coefficient ring may be a singular reduced chart. -/
def universalLinearEquation {R σ : Type*} [CommRing R] [Fintype σ]
    (v : σ → R) : MvPolynomial σ R :=
  ∑ j, MvPolynomial.X j * MvPolynomial.C (v j)

/-- A linear polynomial with an invertible leading coefficient has a
reduced quotient whenever its coefficient ring is reduced. -/
theorem unit_linear_polynomial_radical {R : Type*} [CommRing R] [IsReduced R]
    (u : Rˣ) (b : R) :
    (Ideal.span {Polynomial.C (u : R) * Polynomial.X + Polynomial.C b}).IsRadical := by
  let a : R := -(↑u⁻¹ * b)
  have hua : (u : R) * a = -b := by
    dsimp only [a]
    rw [mul_neg, ← mul_assoc, Units.mul_inv, one_mul]
  have heq : Polynomial.C (u : R) * Polynomial.X + Polynomial.C b =
      Polynomial.C (u : R) * (Polynomial.X - Polynomial.C a) := by
    rw [mul_sub, ← Polynomial.C_mul, hua, Polynomial.C_neg, sub_neg_eq_add]
  rw [heq, Ideal.span_singleton_mul_left_unit (u.isUnit.map Polynomial.C)]
  rw [Ideal.isRadical_iff_quotient_reduced]
  exact isReduced_of_injective (Polynomial.quotientSpanXSubCAlgEquiv a).toRingHom
    (Polynomial.quotientSpanXSubCAlgEquiv a).injective

/-- Eliminate the parameter indexed by `none` from the universal equation.
Only the corresponding chart coordinate has to be invertible. -/
theorem universalLinearEquation_option_radical {R τ : Type*}
    [CommRing R] [IsReduced R] [Fintype τ] (v : Option τ → R)
    (hv : IsUnit (v none)) :
    (Ideal.span {universalLinearEquation v}).IsRadical := by
  obtain ⟨u, hu⟩ := hv
  let B := MvPolynomial τ R
  let e := MvPolynomial.optionEquivLeft R τ
  let b : B := ∑ j, MvPolynomial.X j * MvPolynomial.C (v (some j))
  have he : e (universalLinearEquation v) =
      Polynomial.C (MvPolynomial.C (u : R)) * Polynomial.X + Polynomial.C b := by
    simp only [e, universalLinearEquation, map_sum, Fintype.sum_option, map_add, map_mul,
      MvPolynomial.optionEquivLeft_X_none, MvPolynomial.optionEquivLeft_X_some,
      MvPolynomial.optionEquivLeft_C, b, hu]
    rw [mul_comm Polynomial.X]
  have hmap : (Ideal.span {universalLinearEquation v}).map e.toRingHom =
      Ideal.span {Polynomial.C (MvPolynomial.C (u : R)) * Polynomial.X + Polynomial.C b} := by
    rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {e (universalLinearEquation v)} = _
    rw [he]
  have hred := unit_linear_polynomial_radical (u.map MvPolynomial.C.toMonoidHom) b
  change (Ideal.span {Polynomial.C (MvPolynomial.C (u : R)) *
    Polynomial.X + Polynomial.C b}).IsRadical at hred
  have hc := hred.comap e.toRingHom
  rw [← hmap, Ideal.comap_map_of_bijective e.toRingHom e.bijective] at hc
  exact hc

/-- The universal incidence equation cuts a reduced scheme on any chart
where one of its coordinate coefficients is a unit. -/
theorem universalLinearEquation_radical {R σ : Type*}
    [CommRing R] [IsReduced R] [Fintype σ] (v : σ → R)
    (i : σ) (hv : IsUnit (v i)) :
    (Ideal.span {universalLinearEquation v}).IsRadical := by
  let τ := {j : σ // j ≠ i}
  let f : Option τ ≃ σ := Equiv.optionSubtypeNe i
  let e := MvPolynomial.renameEquiv R f.symm
  have he : e (universalLinearEquation v) = universalLinearEquation (v ∘ f) := by
    simp only [e, universalLinearEquation, map_sum, map_mul,
      MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X, MvPolynomial.rename_C]
    exact Fintype.sum_equiv f.symm _ _ (fun j => by simp)
  have hmap : (Ideal.span {universalLinearEquation v}).map e.toRingHom =
      Ideal.span {universalLinearEquation (v ∘ f)} := by
    rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {e (universalLinearEquation v)} = _
    rw [he]
  have hred := universalLinearEquation_option_radical (v ∘ f) hv
  have hc := hred.comap e.toRingHom
  rw [← hmap, Ideal.comap_map_of_bijective e.toRingHom e.bijective] at hc
  exact hc

/-- The actual generic coefficient fiber is a localization of the reduced
universal incidence ring. This proves reducedness before scalar extension;
it does not assert geometric reducedness in positive characteristic. -/
abbrev universalLinearGenericRing {K R σ : Type}
    [Field K] [CommRing R] [Algebra K R] [Fintype σ] (v : σ → R) :=
  FractionRing (MvPolynomial σ K) ⊗[MvPolynomial σ K]
    (MvPolynomial σ R ⧸ Ideal.span {universalLinearEquation v})

/-- Localizing the reduced universal incidence at the nonzero coefficient
polynomials gives a reduced generic coefficient fiber. -/
theorem universalLinearEquation_generic_reduced {K R σ : Type}
    [Field K] [CommRing R] [Algebra K R] [IsReduced R] [Fintype σ]
    (v : σ → R) (i : σ) (hv : IsUnit (v i)) :
    IsReduced (universalLinearGenericRing (K := K) v) := by
  let P := MvPolynomial σ K
  let Q := MvPolynomial σ R ⧸ Ideal.span {universalLinearEquation v}
  let : IsReduced Q := (Ideal.isRadical_iff_quotient_reduced _).mp
    (universalLinearEquation_radical v i hv)
  let : Algebra Q (FractionRing P ⊗[P] Q) := Algebra.TensorProduct.rightAlgebra
  exact isReduced_localizationPreserves (Algebra.algebraMapSubmonoid Q (nonZeroDivisors P))
    (FractionRing P ⊗[P] Q) inferInstance

/-- Coordinates of the actual cone on its standard open chart. -/
def linearCutChartCoordinates {n : ℕ} (V : ProjectiveVariety n) (i : Fin n)
    (j : Fin n) : Localization.Away (Ideal.Quotient.mk V.ideal (MvPolynomial.X i)) :=
  algebraMap (Poly n ⧸ V.ideal) _ (Ideal.Quotient.mk V.ideal (MvPolynomial.X j))

/-- The coefficient-field action on the localized coordinate quotient. -/
@[instance_reducible] def linearCutChartAlgebra {n : ℕ} (V : ProjectiveVariety n) (i : Fin n) :
    Algebra ℂ (Localization.Away (Ideal.Quotient.mk V.ideal (MvPolynomial.X i))) :=
  Algebra.compHom _ (algebraMap ℂ (Poly n ⧸ V.ideal))

attribute [local instance] linearCutChartAlgebra

/-- Every standard chart of the universal hyperplane incidence is reduced,
including for reducible or singular projective varieties. -/
theorem projective_universal_linear_cut_chart_radical {n : ℕ}
    (V : ProjectiveVariety n) (i : Fin n) :
    (Ideal.span {universalLinearEquation (linearCutChartCoordinates V i)}).IsRadical := by
  let : IsReduced (Poly n ⧸ V.ideal) :=
    (Ideal.isRadical_iff_quotient_reduced V.ideal).mp V.isRadical
  exact universalLinearEquation_radical (linearCutChartCoordinates V i) i
    (IsLocalization.Away.algebraMap_isUnit _)

/-- Reducedness of the generic coefficient fiber on every actual standard
chart, with the same coefficient field and parameter index for all charts. -/
theorem projective_generic_linear_cut_chart_reduced {n : ℕ}
    (V : ProjectiveVariety n) (i : Fin n) :
    IsReduced (universalLinearGenericRing (K := ℂ) (linearCutChartCoordinates V i)) := by
  let : IsReduced (Poly n ⧸ V.ideal) :=
    (Ideal.isRadical_iff_quotient_reduced V.ideal).mp V.isRadical
  exact universalLinearEquation_generic_reduced (linearCutChartCoordinates V i) i
    (IsLocalization.Away.algebraMap_isUnit _)

end
end DistinctDistances.TrackA
