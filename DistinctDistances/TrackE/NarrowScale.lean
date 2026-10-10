import DistinctDistances.TrackA.DepthDefinitions

/-! The common `N/A` scale on the last target plateau (`sparse-cones.tex:880–895`). -/

namespace DistinctDistances.SparseCones

open scoped BigOperators

noncomputable section

/-- The framework's real power convention gives `B^d = N`. -/
theorem regime_B_pow_dimension {d : ℕ} (r : Regime d) (i : ℕ) : r.B i ^ d = r.N i := by
  have hd : (d : ℝ) ≠ 0 := by
    exact_mod_cast (show d ≠ 0 by have := r.dimension_ge_three; omega)
  rw [Regime.B, ← Real.rpow_natCast, ← Real.rpow_mul (r.N_pos i).le,
    one_div_mul_cancel hd, Real.rpow_one]

/-- A balanced profile's complete degree product is exactly `N`. -/
theorem balanced_cut_product {d j : ℕ} {regime : Regime d}
    (D : TrackA.SeparatedDepthData regime j) (i : ℕ) :
    (∏ t : Fin d, D.cutDegree i t) = regime.N i := by
  simp only [TrackA.SeparatedDepthData.cutDegree]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← Real.exp_sum, ← Finset.sum_mul, D.b_sum, zero_mul, Real.exp_zero, mul_one]
  exact regime_B_pow_dimension regime i

/-- Before and after-cut products partition the complete degree product. -/
theorem degreeBudget_mul_tailBudget {d j : ℕ} {regime : Regime d}
    (D : TrackA.SeparatedDepthData regime j) (i : ℕ) :
    D.degreeBudget i * D.tailBudget i = regime.N i := by
  have h := Finset.prod_filter_mul_prod_filter_not Finset.univ
    (fun t : Fin d => t.val < j) (D.cutDegree i)
  have heq : D.degreeBudget i * D.tailBudget i = ∏ t : Fin d, D.cutDegree i t := by
    simpa only [TrackA.SeparatedDepthData.degreeBudget,
      TrackA.SeparatedDepthData.tailBudget, not_lt] using h
  exact heq.trans (balanced_cut_product D i)

/-- On the final one-dimensional target plateau, the narrow depth rate times the
remaining cut scale is exactly `A = B²`. -/
theorem narrowRate_mul_final_tail {d j : ℕ} {regime : Regime d}
    (D : TrackA.SeparatedDepthData regime j) (hlast : j + 1 = d) (i : ℕ) :
    D.narrowRate i * D.tailBudget i = regime.A i := by
  classical
  have htail : Finset.univ.filter (fun t : Fin d => j ≤ t.val) = {⟨j, D.j_lt⟩} := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro ht
      apply Fin.ext
      change t.val = j
      have := t.isLt
      omega
    · intro h
      rw [h]
  have ht : D.tailBudget i = regime.B i * Real.exp (D.b ⟨j, D.j_lt⟩ * D.s i) := by
    rw [TrackA.SeparatedDepthData.tailBudget, htail, Finset.prod_singleton]
    rfl
  have hn : D.narrowRate i = regime.B i * Real.exp (-D.s i * D.b ⟨j, D.j_lt⟩) := by
    rw [TrackA.SeparatedDepthData.narrowRate, htail, Finset.sum_singleton]
  have he : Real.exp (-D.s i * D.b ⟨j, D.j_lt⟩) *
      Real.exp (D.b ⟨j, D.j_lt⟩ * D.s i) = 1 := by
    rw [← Real.exp_add]
    have hz : -D.s i * D.b ⟨j, D.j_lt⟩ + D.b ⟨j, D.j_lt⟩ * D.s i = 0 := by ring
    rw [hz, Real.exp_zero]
  rw [ht, hn, regime.A_eq_B_sq]
  calc
    _ = regime.B i ^ 2 * (Real.exp (-D.s i * D.b ⟨j, D.j_lt⟩) *
        Real.exp (D.b ⟨j, D.j_lt⟩ * D.s i)) := by ring
    _ = _ := by rw [he, mul_one]

/-- `sc:u-final-curve.regularity.scale`: the projected-degree lower bound and the
exceptional-degree upper bound have the identical `N/A` prefactor. -/
theorem final_narrow_scale {d j : ℕ} {regime : Regime d}
    (D : TrackA.SeparatedDepthData regime j) (hlast : j + 1 = d) (i : ℕ) :
    D.degreeBudget i / D.narrowRate i = regime.N i / regime.A i := by
  have hn : 0 < D.narrowRate i := by
    unfold TrackA.SeparatedDepthData.narrowRate
    exact mul_pos (regime.B_pos i) (Real.exp_pos _)
  have ht : 0 < D.tailBudget i := by
    unfold TrackA.SeparatedDepthData.tailBudget
    apply Finset.prod_pos
    intro t _
    exact mul_pos (regime.B_pos i) (Real.exp_pos _)
  calc
    _ = (D.degreeBudget i * D.tailBudget i) / (D.narrowRate i * D.tailBudget i) := by
      field_simp [ne_of_gt hn, ne_of_gt ht]
    _ = _ := by rw [degreeBudget_mul_tailBudget D i, narrowRate_mul_final_tail D hlast i]

end

end DistinctDistances.SparseCones
