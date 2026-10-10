import DistinctDistances.TrackA.LocalizedLinearCutSupport
import DistinctDistances.TrackA.LinearParameterAvoidanceSupport

set_option backward.isDefEq.respectTransparency.types false

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical
attribute [local instance] MvPolynomial.algebraMvPolynomial linearCutChartAlgebra

/-- The homogeneous equation with the selected common coefficients. -/
def coefficientLinearForm {n : ℕ} (α : Fin n → ℂ) : Poly n :=
  ∑ j, MvPolynomial.C (α j) * MvPolynomial.X j

theorem coefficientLinearForm_homogeneous {n : ℕ} (α : Fin n → ℂ) :
    (coefficientLinearForm α).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro j _
  simpa only [zero_add] using
    (MvPolynomial.isHomogeneous_C _ (α j)).mul (MvPolynomial.isHomogeneous_X _ j)

theorem coefficientLinearForm_eval {n : ℕ} (α : Fin n → ℂ) (x : Point n) :
    MvPolynomial.eval x (coefficientLinearForm α) = ∑ j, α j * x j := by
  simp [coefficientLinearForm]

/-- The standard quotient charts have finite type for their actual
canonical complex scalar action. -/
theorem linearCutChart_finiteType {n : ℕ} (V : ProjectiveVariety n) (i : Fin n) :
    Algebra.FiniteType ℂ
      (Localization.Away (Ideal.Quotient.mk V.ideal (MvPolynomial.X i))) := by
  let Q := Poly n ⧸ V.ideal
  let B := Localization.Away (Ideal.Quotient.mk V.ideal (MvPolynomial.X i))
  let : Algebra.FiniteType ℂ Q := inferInstance
  apply RingHom.finiteType_algebraMap.mp
  change ((algebraMap Q B).comp (algebraMap ℂ Q)).FiniteType
  exact RingHom.FiniteType.comp
    (RingHom.finiteType_algebraMap.mpr (inferInstance : Algebra.FiniteType Q B))
    (RingHom.finiteType_algebraMap.mpr (inferInstance : Algebra.FiniteType ℂ Q))

/-- The localized homogeneous equation is the same literal sum of chart
coordinates used by simultaneous reduced specialization. -/
theorem coefficientLinearForm_chart {n : ℕ} (V : ProjectiveVariety n)
    (i : Fin n) (α : Fin n → ℂ) :
    algebraMap (Poly n ⧸ V.ideal)
      (Localization.Away (Ideal.Quotient.mk V.ideal (MvPolynomial.X i)))
      (Ideal.Quotient.mk V.ideal (coefficientLinearForm α)) =
      ∑ j, algebraMap ℂ
        (Localization.Away (Ideal.Quotient.mk V.ideal (MvPolynomial.X i))) (α j) *
        linearCutChartCoordinates V i j := by
  simp only [coefficientLinearForm, map_sum, map_mul, linearCutChartCoordinates]
  rfl

/-- Choose one actual degree-one equation whose chart sum ideals are
radical and whose evaluation at one point on each component is nonzero. -/
theorem projective_family_reduced_linear_form {n : ℕ} (F : ProjectiveFamily.Family n)
    (hF : ∀ V ∈ F, V.IsIrreducible) :
    ∃ ℓ : Poly n, ℓ.IsHomogeneous 1 ∧
      (∀ V ∈ F, ℓ ∉ V.ideal) ∧ ReducedLinearCutCharts (ProjectiveFamily.locus F) ℓ := by
  let V := ProjectiveFamily.locus F
  let A : Fin n → Type := fun i =>
    Localization.Away (Ideal.Quotient.mk V.ideal (MvPolynomial.X i))
  let : ∀ i, CommRing (A i) := fun i => inferInstance
  let : ∀ i, Algebra ℂ (A i) := fun i => linearCutChartAlgebra V i
  let : ∀ i, Algebra.FiniteType ℂ (A i) := fun i => linearCutChart_finiteType V i
  let : IsReduced (Poly n ⧸ V.ideal) :=
    (Ideal.isRadical_iff_quotient_reduced V.ideal).mp V.isRadical
  let : ∀ i, IsReduced (A i) := fun i => inferInstance
  let : Uncountable ℂ := Cardinal.aleph0_lt_mk_iff.mp (by
    rw [Cardinal.mk_complex]
    exact Cardinal.aleph0_lt_continuum)
  have hunit (i : Fin n) : IsUnit (linearCutChartCoordinates V i i) := by
    change IsUnit (algebraMap (Poly n ⧸ V.ideal)
      (Localization.Away (Ideal.Quotient.mk V.ideal (MvPolynomial.X i)))
      (Ideal.Quotient.mk V.ideal (MvPolynomial.X i)))
    exact IsLocalization.Away.algebraMap_isUnit _
  have hpoints (W : F) : ∃ p : ProjectivePoint n, p ∈ W.val.points :=
    ProjectiveFamily.irreducible_points_nonempty W.val (hF W.val W.property)
  choose p hp using hpoints
  let x : F → Fin n → ℂ := fun W => (p W).rep
  have hx (W : F) : ∃ j, x W j ≠ 0 := by
    by_contra h
    push Not at h
    apply (p W).rep_nonzero
    funext j
    exact h j
  obtain ⟨α, hcut, havoid⟩ := simultaneous_reduced_linear_equations_avoiding
    A (linearCutChartCoordinates V) id hunit x hx
  refine ⟨coefficientLinearForm α, coefficientLinearForm_homogeneous α, ?_, ?_⟩
  · intro W hW hmem
    let w : F := ⟨W, hW⟩
    have hz := hp w (p w).rep (p w).rep_nonzero (Projectivization.mk_rep (p w))
      (coefficientLinearForm α) hmem
    apply havoid w
    simpa only [MvPolynomial.aeval_eq_eval, coefficientLinearForm_eval] using hz
  · intro i
    apply localized_sum_ideal_radical_of_quotient_cut V.ideal (MvPolynomial.X i)
    rw [coefficientLinearForm_chart]
    exact hcut i

end
end DistinctDistances.TrackA
