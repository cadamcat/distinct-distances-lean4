import DistinctDistances.TrackA.FormalJacobianGraphSupport

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical
open MvPowerSeries Matrix
open OAI.BoundaryOnly.FormalObstruction.FormalCorrection

variable {K α ι : Type*} [Field K] [Fintype α] [Fintype ι]

/-- A normalized implicit system has the literal graph as its full formal ideal. -/
theorem formalNormalized_ideal_eq_graph
    (L : ι → MvPowerSeries α K) (H : ι → MvPowerSeries (α ⊕ ι) K)
    (hH : ∀ i, Vanishes 2 (H i)) (w : ι → MvPowerSeries α K)
    (hw : ∀ i, constantCoeff (w i) = 0)
    (hfixed : ∀ i, w i = L i + subst (Sum.elim X w) (H i)) :
    Ideal.span (Set.range (fun i => X (Sum.inr i) - formalFreeInclusion (L i) - H i)) =
      formalGraphIdeal w := by
  let v : (α ⊕ ι) → MvPowerSeries (α ⊕ ι) K :=
    Sum.elim (fun a => X (Sum.inl a)) (fun i => formalFreeInclusion (w i))
  let δ : ι → MvPowerSeries (α ⊕ ι) K :=
    fun i => X (Sum.inr i) - formalFreeInclusion (w i)
  have hv : ∀ j, constantCoeff (v j) = 0 := by
    intro j
    cases j <;> simp [v, formalFreeInclusion, hw]
  have hδ : ∀ i, constantCoeff (δ i) = 0 := by
    intro i
    simp [δ, formalFreeInclusion, hw]
  have hshift : shiftedGraph v δ = X := by
    funext j
    cases j <;> simp [shiftedGraph, v, δ]
  choose q hq hfact using (fun i => exists_first_remainder (H i))
  let B : Matrix ι ι (MvPowerSeries (α ⊕ ι) K) :=
    fun i j => subst (Sum.elim v δ) (q i j)
  have hB : ∀ i j, Vanishes 1 (B i j) := by
    intro i j
    exact (hq i 1 (hH i) j).subst _ (extended_centered v δ hv hδ)
  have hunit : IsUnit (1-B) := by
    simpa only [sub_eq_add_neg] using matrix_one_add_isUnit (-B)
      (fun i j => (hB i j).neg)
  have hdiff (i : ι) : H i - subst v (H i) = (B *ᵥ δ) i := by
    have hs := hasSubst_of_constantCoeff_zero (extended_centered v δ hv hδ)
    have he := congrArg (substAlgHom hs) (hfact i)
    simp only [map_sub, map_sum, map_mul, substAlgHom_apply, subst_X hs,
      Sum.elim_inr, subst_extended_shifted v δ hv hδ,
      subst_extended_base v δ hv hδ, hshift, subst_self, id_eq] at he
    exact he
  have hfixed' (i : ι) : formalFreeInclusion (ι := ι) (w i) =
      formalFreeInclusion (L i) + subst v (H i) := by
    rw [hfixed i, map_add]
    congr 1
    simpa only [formalGraphEvaluation_apply] using
      (formalGraph_full_substitution w hw (H i)).symm
  have heq : (fun i => X (Sum.inr i) - formalFreeInclusion (L i) - H i) =
      (1-B) *ᵥ δ := by
    funext i
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    change _ = δ i - (B *ᵥ δ) i
    rw [← hdiff]
    dsimp only [δ]
    rw [hfixed']
    abel
  rw [heq]
  exact vectorIdeal_unit_mulVec (1-B) hunit δ

/-- The normalized implicit quotient is a power series ring in the free coordinates. -/
theorem formalNormalized_quotient_exists
    (L : ι → MvPowerSeries α K) (H : ι → MvPowerSeries (α ⊕ ι) K)
    (hL : ∀ i, constantCoeff (L i) = 0) (hH : ∀ i, Vanishes 2 (H i)) :
    Nonempty ((MvPowerSeries (α ⊕ ι) K ⧸
      Ideal.span (Set.range (fun i => X (Sum.inr i) - formalFreeInclusion (L i) - H i)))
        ≃ₐ[K] MvPowerSeries α K) := by
  obtain ⟨w, ⟨hw, hfixed⟩, _⟩ := centered_implicit_solution L H hL hH
  exact ⟨(Ideal.quotientEquivAlgOfEq K
    (formalNormalized_ideal_eq_graph L H hH w hw hfixed)).trans
      (formalGraphQuotientEquiv w hw)⟩

/-- Normalized implicit equations generate a prime ideal in the full formal ring. -/
theorem formalNormalized_ideal_isPrime
    (L : ι → MvPowerSeries α K) (H : ι → MvPowerSeries (α ⊕ ι) K)
    (hL : ∀ i, constantCoeff (L i) = 0) (hH : ∀ i, Vanishes 2 (H i)) :
    (Ideal.span (Set.range (fun i => X (Sum.inr i) - formalFreeInclusion (L i) - H i))).IsPrime := by
  obtain ⟨w, ⟨hw, hfixed⟩, _⟩ := centered_implicit_solution L H hL hH
  rw [formalNormalized_ideal_eq_graph L H hH w hw hfixed]
  exact formalGraphIdeal_isPrime w hw

end
end DistinctDistances.TrackA
