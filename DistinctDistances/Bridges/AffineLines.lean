import DistinctDistances.Foundations.Affine

/-! Polynomial coordinates and filtered Hilbert spaces of complex affine lines. -/

namespace DistinctDistances.Bridges

open scoped BigOperators
noncomputable section

theorem totalDegree_aeval_le_of_linear {n m : ℕ} (gs : Fin n → Poly m)
    (hgs : ∀ i, (gs i).totalDegree ≤ 1) (f : Poly n) :
    (MvPolynomial.aeval gs f).totalDegree ≤ f.totalDegree := by
  classical
  conv_lhs => rw [f.as_sum, map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro s hs
  rw [MvPolynomial.aeval_monomial]
  change (MvPolynomial.C (f.coeff s) * ∏ i ∈ s.support, gs i ^ s i).totalDegree ≤ _
  apply (MvPolynomial.totalDegree_mul _ _).trans
  rw [MvPolynomial.totalDegree_C, zero_add]
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc
    (∑ i ∈ s.support, (gs i ^ s i).totalDegree) ≤ ∑ i ∈ s.support, s i := by
      apply Finset.sum_le_sum
      intro i hi
      exact (MvPolynomial.totalDegree_pow _ _).trans
        ((Nat.mul_le_mul_left (s i) (hgs i)).trans_eq (Nat.mul_one _))
    _ ≤ f.totalDegree := MvPolynomial.le_totalDegree hs

def linePullback {n : ℕ} (a v : Point n) : Poly n →ₐ[ℂ] Poly 1 :=
  MvPolynomial.aeval (fun i => MvPolynomial.C (a i) +
    MvPolynomial.C (v i) * MvPolynomial.X 0)

def lineSection {n : ℕ} (a v : Point n) (j : Fin n) : Poly 1 →ₐ[ℂ] Poly n :=
  MvPolynomial.aeval (fun _ => MvPolynomial.C ((v j)⁻¹) *
    (MvPolynomial.X j - MvPolynomial.C (a j)))

theorem linePullback_degree_le {n : ℕ} (a v : Point n) (f : Poly n) :
    (linePullback a v f).totalDegree ≤ f.totalDegree := by
  apply totalDegree_aeval_le_of_linear
  intro i
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · simp only [MvPolynomial.totalDegree_C, Nat.zero_le]
  · apply (MvPolynomial.totalDegree_mul _ _).trans
    simp only [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X, zero_add, le_refl]

theorem lineSection_degree_le {n : ℕ} (a v : Point n) (j : Fin n) (f : Poly 1) :
    (lineSection a v j f).totalDegree ≤ f.totalDegree := by
  apply totalDegree_aeval_le_of_linear
  intro i
  apply (MvPolynomial.totalDegree_mul _ _).trans
  rw [MvPolynomial.totalDegree_C, zero_add]
  apply (MvPolynomial.totalDegree_sub _ _).trans
  simp only [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C,
    max_eq_left (Nat.zero_le 1), le_refl]

theorem linePullback_comp_section {n : ℕ} (a v : Point n) (j : Fin n) (hj : v j ≠ 0) :
    (linePullback a v).comp (lineSection a v j) = AlgHom.id ℂ (Poly 1) := by
  ext i : 1
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  change linePullback a v (lineSection a v j (MvPolynomial.X 0)) = MvPolynomial.X 0
  simp only [lineSection, MvPolynomial.aeval_X, linePullback, map_mul, map_sub,
    MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
  rw [add_sub_cancel_left, ← mul_assoc, ← MvPolynomial.C_mul, inv_mul_cancel₀ hj]
  simp only [map_one, one_mul]

end
end DistinctDistances.Bridges
