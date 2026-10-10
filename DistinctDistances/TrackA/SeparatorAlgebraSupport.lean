import DistinctDistances.TrackA.DividedDifferenceSupport

namespace DistinctDistances.TrackA
noncomputable section
open scoped BigOperators Classical
open MvPolynomial

/-- Extract one normalized scalar separator from a polynomial over a
possibly nonreduced algebra, without increasing its degree. -/
theorem scalar_separator_from_algebra {F A : Type*} [Field F] [CommRing A] [Algebra F A]
    {c : ℕ} (p : MvPolynomial (Fin c) A) (D : ℕ) (hp : p.totalDegree ≤ D)
    (z : FieldPoint c F) (hz : eval (fun i => algebraMap F A (z i)) p ≠ 0)
    (T : Set (FieldPoint c F))
    (hT : ∀ y ∈ T, y ≠ z → eval (fun i => algebraMap F A (y i)) p = 0) :
    ∃ s : FieldPoly c F, s.totalDegree ≤ D ∧ eval z s = 1 ∧
      ∀ y ∈ T, y ≠ z → eval y s = 0 := by
  obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_eq_one F hz
  let s : FieldPoly c F := ∑ m ∈ p.support, monomial m (ℓ (p.coeff m))
  have hdegree : s.totalDegree ≤ D := by
    apply totalDegree_finsetSum_le
    intro m hm
    exact (totalDegree_monomial_le m _).trans ((le_totalDegree hm).trans hp)
  have heval (y : FieldPoint c F) : eval y s = ℓ (eval (fun i => algebraMap F A (y i)) p) := by
    conv_rhs => rw [p.as_sum]
    simp only [s, map_sum, eval_monomial]
    apply Finset.sum_congr rfl
    intro m _
    have hprod : m.prod (fun i e => algebraMap F A (y i)^e) =
        algebraMap F A (m.prod (fun i e => y i^e)) := by
      simp only [map_finsuppProd, map_pow]
    rw [hprod, mul_comm (p.coeff m)]
    rw [← Algebra.smul_def, ℓ.map_smul]
    simp only [smul_eq_mul, mul_comm]
  refine ⟨s, hdegree, ?_, ?_⟩
  · rw [heval, hℓ]
  · intro y hy hne
    rw [heval, hT y hy hne, map_zero]

theorem polynomial_matrix_det_degree_le {R : Type*} [CommRing R] {c a : ℕ}
    (Q : Matrix (Fin a) (Fin a) (MvPolynomial (Fin c) R)) (L : ℕ)
    (hQ : ∀ i j, (Q i j).totalDegree ≤ L) :
    Q.det.totalDegree ≤ a*L := by
  rw [Matrix.det_apply]
  apply (totalDegree_finsetSum _ _).trans
  apply Finset.sup_le
  intro e _
  apply (totalDegree_smul_le _ _).trans
  apply (totalDegree_finsetProd _ _).trans
  exact (Finset.sum_le_sum (fun i _ => hQ (e i) i)).trans_eq (by simp)

end
end DistinctDistances.TrackA
