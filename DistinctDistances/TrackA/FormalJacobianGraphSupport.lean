import OAI.Algebra.AlgebraicObstruction.ImplicitFunction
import OAI.Algebra.AlgebraicObstruction.FiniteCoefficients
import OAI.Algebra.AlgebraicObstruction.GraphCorrection

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical
open MvPowerSeries
open OAI.BoundaryOnly.FormalObstruction.FormalCorrection

variable {K α ι : Type*} [Field K] [Fintype α] [Fintype ι]

/-- The inclusion of the free formal coordinates in the full coordinate ring. -/
def formalFreeInclusion : MvPowerSeries α K →ₐ[K] MvPowerSeries (α ⊕ ι) K :=
  rename (Function.Embedding.inl : α ↪ α ⊕ ι)

theorem formalGraph_hasSubst (w : ι → MvPowerSeries α K)
    (hw : ∀ i, constantCoeff (w i) = 0) : HasSubst (Sum.elim X w) :=
  hasSubst_of_constantCoeff_zero (fun j => by cases j <;> simp [hw])

/-- Evaluate the dependent coordinates on the specified centered graph. -/
def formalGraphEvaluation (w : ι → MvPowerSeries α K)
    (hw : ∀ i, constantCoeff (w i) = 0) :
    MvPowerSeries (α ⊕ ι) K →ₐ[K] MvPowerSeries α K :=
  substAlgHom (formalGraph_hasSubst w hw)

@[simp] theorem formalGraphEvaluation_apply (w : ι → MvPowerSeries α K)
    (hw : ∀ i, constantCoeff (w i) = 0) (p : MvPowerSeries (α ⊕ ι) K) :
    formalGraphEvaluation w hw p = subst (Sum.elim X w) p :=
  substAlgHom_apply (formalGraph_hasSubst w hw) p

/-- The ideal of the literal differences between dependent coordinates and graph values. -/
def formalGraphIdeal (w : ι → MvPowerSeries α K) : Ideal (MvPowerSeries (α ⊕ ι) K) :=
  Ideal.span (Set.range (fun i => X (Sum.inr i) - formalFreeInclusion (w i)))

@[simp] theorem formalGraphEvaluation_free (w : ι → MvPowerSeries α K)
    (hw : ∀ i, constantCoeff (w i) = 0) (p : MvPowerSeries α K) :
    formalGraphEvaluation w hw (formalFreeInclusion (ι := ι) p) = p := by
  rw [formalGraphEvaluation_apply]
  change subst (Sum.elim X w) (rename Function.Embedding.inl p) = p
  rw [rename_eq_subst, subst_comp_subst_apply
    (HasSubst.X_comp _) (formalGraph_hasSubst w hw)]
  simp only [Function.comp_apply, subst_X (formalGraph_hasSubst w hw),
    Function.Embedding.inl_apply, Sum.elim_inl, subst_self, id_eq]

/-- Substitution in the full ring factors through evaluation on the free graph. -/
theorem formalGraph_full_substitution (w : ι → MvPowerSeries α K)
    (hw : ∀ i, constantCoeff (w i) = 0) (p : MvPowerSeries (α ⊕ ι) K) :
    subst (Sum.elim (fun a => X (Sum.inl a)) (fun i => formalFreeInclusion (ι := ι) (w i))) p =
      formalFreeInclusion (formalGraphEvaluation w hw p) := by
  rw [formalGraphEvaluation_apply]
  change _ = rename Function.Embedding.inl (subst (Sum.elim X w) p)
  rw [rename_eq_subst, subst_comp_subst_apply
    (formalGraph_hasSubst w hw) (HasSubst.X_comp _)]
  congr 1
  funext j
  cases j with
  | inl a =>
      simp only [Sum.elim_inl, subst_X (HasSubst.X_comp _), Function.comp_apply]
      rfl
  | inr i =>
      simp only [Sum.elim_inr, formalFreeInclusion]
      exact rename_eq_subst Function.Embedding.inl (w i)

/-- Formal first remainders identify the graph ideal with the evaluation kernel. -/
theorem formalGraphIdeal_eq_kernel (w : ι → MvPowerSeries α K)
    (hw : ∀ i, constantCoeff (w i) = 0) :
    formalGraphIdeal w = RingHom.ker (formalGraphEvaluation w hw).toRingHom := by
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
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change formalGraphEvaluation w hw (X (Sum.inr i) - formalFreeInclusion (w i)) = 0
    rw [map_sub, formalGraphEvaluation_free]
    rw [formalGraphEvaluation_apply, subst_X (formalGraph_hasSubst w hw)]
    exact sub_self _
  · intro p hp
    have hpzero : formalGraphEvaluation w hw p = 0 := hp
    obtain ⟨q, hq⟩ := evaluated_first_remainder p v δ hv hδ
    have hsub : subst v p = 0 := by
      change subst (Sum.elim (fun a => X (Sum.inl a))
        (fun i => formalFreeInclusion (w i))) p = 0
      rw [formalGraph_full_substitution w hw p, hpzero, map_zero]
    rw [hshift, subst_self, hsub, sub_zero, id_eq] at hq
    rw [hq]
    apply Ideal.sum_mem
    intro i _
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

/-- The formal graph quotient is the power series ring on the free coordinates. -/
def formalGraphQuotientEquiv (w : ι → MvPowerSeries α K)
    (hw : ∀ i, constantCoeff (w i) = 0) :
    (MvPowerSeries (α ⊕ ι) K ⧸ formalGraphIdeal w) ≃ₐ[K] MvPowerSeries α K := by
  let e := Ideal.quotientKerAlgEquivOfSurjective (f := formalGraphEvaluation w hw)
    (fun p => ⟨formalFreeInclusion p, formalGraphEvaluation_free w hw p⟩)
  exact (Ideal.quotientEquivAlgOfEq K (formalGraphIdeal_eq_kernel w hw)).trans e

/-- A centered formal graph has a prime defining ideal over a field. -/
theorem formalGraphIdeal_isPrime (w : ι → MvPowerSeries α K)
    (hw : ∀ i, constantCoeff (w i) = 0) : (formalGraphIdeal w).IsPrime := by
  rw [formalGraphIdeal_eq_kernel w hw]
  let : IsDomain (MvPowerSeries α K) := NoZeroDivisors.to_isDomain _
  exact RingHom.ker_isPrime _

end
end DistinctDistances.TrackA
