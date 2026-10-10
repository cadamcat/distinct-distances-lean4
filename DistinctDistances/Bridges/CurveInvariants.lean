import DistinctDistances.Bridges.CurveSamples
import DistinctDistances.TrackA.Hilbert

/-! Natural-valued degree and local multiplicity for irreducible affine curves. -/

namespace DistinctDistances.Bridges

noncomputable section

/-- The slope of a linear polynomial with eventual natural values is natural. -/
theorem linearPolynomial_slope_nat (P : Polynomial ℚ) (hdeg : P.natDegree ≤ 1)
    (hpos : 0 ≤ P.coeff 1) (N : ℕ)
    (hN : ∀ t ≥ N, ∃ a : ℕ, P.eval (t : ℚ) = (a : ℚ)) :
    ∃ a : ℕ, P.coeff 1 = (a : ℚ) := by
  obtain ⟨a, ha⟩ := hN N le_rfl
  obtain ⟨b, hb⟩ := hN (N+1) (Nat.le_succ N)
  have he : P = Polynomial.C (P.coeff 1) * Polynomial.X + Polynomial.C (P.coeff 0) :=
    Polynomial.eq_X_add_C_of_natDegree_le_one hdeg
  have hs : P.coeff 1 = (b : ℚ) - (a : ℚ) := by
    rw [he] at ha hb
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Nat.cast_add, Nat.cast_one] at ha hb
    linarith
  have hab : a ≤ b := by exact_mod_cast (by linarith [hpos] : (a : ℚ) ≤ (b : ℚ))
  exact ⟨b-a, by rw [Nat.cast_sub hab]; exact hs⟩

theorem curve_degree_nat {n : ℕ} (Y : AffineVariety n)
    (hY : Y.IsIrreducible) (hdim : Y.dimension = 1) :
    ∃ a : ℕ, Y.degree = (a : ℚ) := by
  have hdegree : Y.degree = Y.hilbertPolynomial.coeff 1 := by
    change ((Y.dimension).factorial : ℚ) * Y.hilbertPolynomial.coeff Y.dimension = _
    simp [hdim]
  rw [hdegree]
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp Y.hilbert_eventually
  apply linearPolynomial_slope_nat Y.hilbertPolynomial hdim.le
    (by rw [← hdegree]; exact (Y.one_le_degree hY.ne_top).trans' (by norm_num)) N
  intro t ht
  exact ⟨Y.hilbert t, (hN t ht).symm⟩

theorem curve_multiplicity_nat {n : ℕ} (Y : AffineVariety n)
    (hY : Y.IsIrreducible) (hdim : Y.dimension = 1) (p : Point n) :
    ∃ m : ℕ, Y.multiplicity p = (m : ℚ) := by
  by_cases hp : p ∈ Y
  · have hlocal : Y.localDimension p = 1 :=
      (Y.localDimension_eq_dimension p hY hp).trans hdim
    have hm : Y.multiplicity p = (Y.localHilbertPolynomial p).coeff 1 := by
      simp [AffineVariety.multiplicity, hlocal]
    rw [hm]
    obtain ⟨N, hN⟩ := (Y.localHilbert_eventually_polynomial p).choose_spec.2
    apply linearPolynomial_slope_nat (Y.localHilbertPolynomial p) hlocal.le
      (by rw [← hm]; exact (Y.multiplicity_pos p hp).le) N
    intro t ht
    obtain ⟨a, _, ha⟩ := hN t ht
    exact ⟨a, ha⟩
  · exact ⟨0, by simpa using Y.multiplicity_eq_zero_off p hp⟩

theorem curve_natural_invariants {n : ℕ} (Y : AffineVariety n)
    (hY : Y.IsIrreducible) (hdim : Y.dimension = 1) :
    (∃ degree : ℕ, Y.degree = (degree : ℚ)) ∧
      ∀ p : Point n, ∃ m : ℕ, Y.multiplicity p = (m : ℚ) :=
  ⟨curve_degree_nat Y hY hdim, curve_multiplicity_nat Y hY hdim⟩

end
end DistinctDistances.Bridges
