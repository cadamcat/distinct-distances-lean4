import DistinctDistances.TrackA.CylinderHilbertSupport

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical

/-- A dimensional cylinder degree bound sufficient for the original narrow
root count. No exact cumulative Hilbert formula is needed. -/
theorem lineCylinder_degree_le {n : ℕ} (V : AffineVariety n)
    (hV : V.IsIrreducible) :
    (lineCylinder V).degree ≤ (V.dimension+1 : ℕ) * V.degree := by
  let P := (lineCylinder V).hilbertPolynomial
  let Q : Polynomial ℚ := (Polynomial.X + 1) * V.hilbertPolynomial
  have hdim := lineCylinder_dimension V hV
  have hP : P.natDegree ≤ V.dimension+1 := by
    change (lineCylinder V).dimension ≤ V.dimension+1
    exact hdim.le
  have hQ : Q.natDegree ≤ V.dimension+1 := by
    have hx : (Polynomial.X + 1 : Polynomial ℚ).natDegree ≤ 1 := by
      simpa using (Polynomial.natDegree_add_le (Polynomial.X : Polynomial ℚ) 1)
    exact Polynomial.natDegree_mul_le.trans
      (by change _ ≤ V.hilbertPolynomial.natDegree + 1; omega)
  have hle : ∀ᶠ D : ℕ in Filter.atTop, P.eval (D : ℚ) ≤ Q.eval (D : ℚ) := by
    filter_upwards [(lineCylinder V).hilbert_eventually, V.hilbert_eventually] with D hD hVd
    change (lineCylinder V).hilbertPolynomial.eval (D : ℚ) ≤
      ((Polynomial.X + 1) * V.hilbertPolynomial).eval (D : ℚ)
    rw [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_one, ← hD, ← hVd]
    exact_mod_cast lineCylinder_hilbert_le V D
  have hc := OAI.QuarticPowerFree.coeff_le_of_eventually_nat_eval_le
    P Q (V.dimension+1) hP hQ hle
  have hcoeff : Q.coeff (V.dimension+1) = V.hilbertPolynomial.coeff V.dimension := by
    have hz : V.hilbertPolynomial.coeff (V.dimension+1) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (by change V.dimension < V.dimension+1; omega)
    change ((Polynomial.X + 1) * V.hilbertPolynomial).coeff (V.dimension+1) = _
    rw [add_mul, Polynomial.coeff_add, Polynomial.coeff_X_mul, one_mul,
      hz, add_zero]
  rw [hcoeff] at hc
  have h := mul_le_mul_of_nonneg_left hc
    (show (0 : ℚ) ≤ ((V.dimension+1).factorial : ℚ) from Nat.cast_nonneg _)
  simpa [AffineVariety.degree, OAI.QuarticPowerFree.affineDegree, hdim, P,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_assoc] using h

end
end DistinctDistances.TrackA
