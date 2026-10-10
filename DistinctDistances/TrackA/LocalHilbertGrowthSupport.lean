import DistinctDistances.TrackA.LocalHilbertFiniteSupport

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical

/-- Any polynomial representing the actual original local Hilbert values
eventually has degree at most the original ambient dimension. -/
theorem localHilbert_polynomial_degree_le {n : ℕ} (V : AffineVariety n)
    (p : Point n) (P : Polynomial ℚ)
    (hP : ∀ᶠ t : ℕ in Filter.atTop,
      P.eval (t : ℚ) = ((V.localHilbert p t).toNat : ℚ)) :
    P.natDegree ≤ n := by
  let Q : Polynomial ℚ := (Polynomial.X + Polynomial.C (n : ℚ))^n
  have hbounds : ∀ᶠ t : ℕ in Filter.atTop,
      0 ≤ P.eval (t : ℚ) ∧ P.eval (t : ℚ) ≤ Q.eval (t : ℚ) := by
    filter_upwards [hP] with t ht
    obtain ⟨a, ha, hbound⟩ := localHilbert_finite_value V p t
    rw [ha, ENat.toNat_natCast] at ht
    rw [ht]
    refine ⟨Nat.cast_nonneg a, ?_⟩
    simp only [Q, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C]
    exact_mod_cast hbound.trans (Nat.choose_le_pow (t+n) n)
  have hdegree : Q.natDegree ≤ n := by
    exact Polynomial.natDegree_pow_le.trans
      (by rw [Polynomial.natDegree_X_add_C]; simp)
  exact (OAI.QuarticPowerFree.natDegree_le_of_eventually_nat_eval_bounds P Q
    (hbounds.mono (fun _ h => h.1)) (hbounds.mono (fun _ h => h.2))).trans hdegree

end
end DistinctDistances.TrackA
