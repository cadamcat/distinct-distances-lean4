import DistinctDistances.TrackA.FormalJacobianIdealSupport

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical
open MvPowerSeries Matrix
open OAI.BoundaryOnly.FormalObstruction.FormalCorrection

variable {K α ι : Type*} [Field K] [Fintype α] [Fintype ι]

/-- The OAI polynomial normalization is multiplication by the actual inverse Jacobian. -/
theorem formalPolynomial_normalization
    (F : ι → MvPolynomial (α ⊕ ι) K) (A : Matrix ι ι K) (i : ι) :
    X (Sum.inr i) - formalFreeInclusion (implicitL (implicitG F A) i).toMvPowerSeries -
      (implicitH (implicitG F A) i).toMvPowerSeries =
        ((A.map (MvPowerSeries.C : K →+* MvPowerSeries (α ⊕ ι) K)) *ᵥ
          (fun j => (F j).toMvPowerSeries)) i := by
  have hlinear : formalFreeInclusion (ι := ι)
      (implicitL (implicitG F A) i).toMvPowerSeries =
      (∑ a, MvPolynomial.C ((implicitG F A i).coeff (Finsupp.single (Sum.inl a) 1)) *
        MvPolynomial.X (Sum.inl a)).toMvPowerSeries := by
    simp only [formalFreeInclusion, implicitL, polynomial_series_sum,
      MvPolynomial.coe_mul, MvPolynomial.coe_C, MvPolynomial.coe_X,
      map_sum, map_mul, rename_C, rename_X]
    rfl
  rw [hlinear, implicitH, polynomial_series_sub]
  have hG : (implicitG F A i).toMvPowerSeries =
      X (Sum.inr i) - ((A.map (MvPowerSeries.C : K →+* MvPowerSeries (α ⊕ ι) K)) *ᵥ
        (fun j => (F j).toMvPowerSeries)) i := by
    simp only [implicitG, polynomial_series_sub, polynomial_series_sum,
      MvPolynomial.coe_X, MvPolynomial.coe_mul, MvPolynomial.coe_C,
      Matrix.mulVec, dotProduct, Matrix.map_apply]
  rw [hG]
  abel

/-- Every nonsingular centered polynomial system generates a literal formal graph ideal. -/
theorem formalPolynomial_ideal_eq_graph
    (F : ι → MvPolynomial (α ⊕ ι) K) (hF : ∀ i, (F i).coeff 0 = 0)
    (hdet : IsUnit (internalJacobian F).det) :
    ∃ (w : ι → MvPowerSeries α K) (hw : ∀ i, constantCoeff (w i) = 0),
      Ideal.span (Set.range (fun i => (F i).toMvPowerSeries)) = formalGraphIdeal w := by
  let A : Matrix ι ι K := (internalJacobian F)⁻¹
  let G := implicitG F A
  let L := fun i => (implicitL G i).toMvPowerSeries
  let H := fun i => (implicitH G i).toMvPowerSeries
  have hA : A * internalJacobian F = 1 := Matrix.nonsing_inv_mul _ hdet
  have hL : ∀ i, constantCoeff (L i) = 0 := implicitL_centered G
  have hH : ∀ i, Vanishes 2 (H i) := implicitH_quadratic G
    (implicitG_constant F A hF) (implicitG_internal_linear F A hA)
  obtain ⟨w, ⟨hw, hfixed⟩, _⟩ := centered_implicit_solution L H hL hH
  refine ⟨w, hw, ?_⟩
  have hu : IsUnit (A.map (MvPowerSeries.C : K →+* MvPowerSeries (α ⊕ ι) K)) := by
    apply ((A.map (MvPowerSeries.C : K →+* MvPowerSeries (α ⊕ ι) K)).isUnit_iff_isUnit_det).mpr
    have hmap := (MvPowerSeries.C : K →+* MvPowerSeries (α ⊕ ι) K).map_det A
    change MvPowerSeries.C A.det = (A.map (MvPowerSeries.C : K →+* MvPowerSeries (α ⊕ ι) K)).det at hmap
    rw [← hmap]
    exact (Matrix.isUnit_nonsing_inv_det _ hdet).map MvPowerSeries.C
  have hnorm : (fun i => X (Sum.inr i) - formalFreeInclusion (L i) - H i) =
      (A.map (MvPowerSeries.C : K →+* MvPowerSeries (α ⊕ ι) K)) *ᵥ
        (fun i => (F i).toMvPowerSeries) := by
    funext i
    exact formalPolynomial_normalization F A i
  calc
    Ideal.span (Set.range (fun i => (F i).toMvPowerSeries)) =
        Ideal.span (Set.range (fun i => X (Sum.inr i) - formalFreeInclusion (L i) - H i)) := by
      rw [hnorm]
      exact (vectorIdeal_unit_mulVec _ hu _).symm
    _ = formalGraphIdeal w := formalNormalized_ideal_eq_graph L H hH w hw hfixed

/-- The nonsingular formal polynomial quotient has exactly the free formal coordinates. -/
theorem formalPolynomial_quotient_exists
    (F : ι → MvPolynomial (α ⊕ ι) K) (hF : ∀ i, (F i).coeff 0 = 0)
    (hdet : IsUnit (internalJacobian F).det) :
    Nonempty ((MvPowerSeries (α ⊕ ι) K ⧸ Ideal.span
      (Set.range (fun i => (F i).toMvPowerSeries))) ≃ₐ[K] MvPowerSeries α K) := by
  obtain ⟨w, hw, heq⟩ := formalPolynomial_ideal_eq_graph F hF hdet
  exact ⟨(Ideal.quotientEquivAlgOfEq K heq).trans (formalGraphQuotientEquiv w hw)⟩

/-- Nonsingular centered polynomial equations generate a prime formal ideal. -/
theorem formalPolynomial_ideal_isPrime
    (F : ι → MvPolynomial (α ⊕ ι) K) (hF : ∀ i, (F i).coeff 0 = 0)
    (hdet : IsUnit (internalJacobian F).det) :
    (Ideal.span (Set.range (fun i => (F i).toMvPowerSeries))).IsPrime := by
  obtain ⟨w, hw, heq⟩ := formalPolynomial_ideal_eq_graph F hF hdet
  rw [heq]
  exact formalGraphIdeal_isPrime w hw

end
end DistinctDistances.TrackA
