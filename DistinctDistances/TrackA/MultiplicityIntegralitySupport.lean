import DistinctDistances.Foundations.Local
import OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertDifferenceDegree

namespace DistinctDistances.TrackA
noncomputable section

/-- Eventual integer values force the factorial-normalized leading coefficient
to be integral. Backward differences reduce the degree without changing it. -/
theorem factorial_leadingCoeff_integral (P : Polynomial ℚ) (N : ℕ)
    (hP : ∀ t ≥ N, ∃ a : ℤ, P.eval (t : ℚ) = (a : ℚ)) :
    ∃ a : ℤ, P.leadingCoeff * (P.natDegree.factorial : ℚ) = (a : ℚ) := by
  suffices hall : ∀ d : ℕ, ∀ (Q : Polynomial ℚ) (M : ℕ), Q.natDegree = d →
      (∀ t ≥ M, ∃ a : ℤ, Q.eval (t : ℚ) = (a : ℚ)) →
      ∃ a : ℤ, Q.leadingCoeff * (Q.natDegree.factorial : ℚ) = (a : ℚ) by
    exact hall P.natDegree P N rfl hP
  intro d
  induction d with
  | zero =>
    intro Q M hdegree hvalues
    obtain ⟨a, ha⟩ := hvalues M le_rfl
    refine ⟨a, ?_⟩
    have hconstant := Polynomial.eq_C_of_natDegree_eq_zero hdegree
    rw [hconstant, Polynomial.eval_C] at ha
    simpa only [Polynomial.leadingCoeff, hdegree, Nat.factorial_zero,
      Nat.cast_one, mul_one] using ha
  | succ d ih =>
    intro Q M hdegree hvalues
    let D := Q - Polynomial.taylor (-1) Q
    have hDdegree : D.natDegree = d :=
      (OAI.PiExponentJets.W27.backward_difference_degree_and_leading
        Q d hdegree 1 one_ne_zero).1
    have hDvalues : ∀ t ≥ M+1, ∃ a : ℤ, D.eval (t : ℚ) = (a : ℚ) := by
      intro t ht
      obtain ⟨a, ha⟩ := hvalues t (by omega)
      obtain ⟨b, hb⟩ := hvalues (t-1) (by omega)
      refine ⟨a-b, ?_⟩
      have hcast : ((t-1 : ℕ) : ℚ) = (t : ℚ)-1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ t)]
        simp
      simp only [D, Polynomial.eval_sub, Polynomial.taylor_eval]
      rw [show (t : ℚ) + (-1) = ((t-1 : ℕ) : ℚ) by rw [hcast]; ring, ha, hb]
      simp
    obtain ⟨a, ha⟩ := ih D (M+1) hDdegree hDvalues
    refine ⟨a, ?_⟩
    have hmult := OAI.PiExponentJets.W27.backward_difference_multiplicity
      Q d hdegree 1 one_ne_zero
    have hmult' : D.leadingCoeff * (D.natDegree.factorial : ℚ) =
        Q.leadingCoeff * (Q.natDegree.factorial : ℚ) := by
      simpa only [D, one_mul] using hmult
    exact hmult'.symm.trans ha

/-- The local Hilbert polynomial gives a natural multiplicity at a point
of the variety. Its existence remains the frozen shared-model input. -/
theorem multiplicity_eq_nat {n : ℕ} (V : AffineVariety n) (p : Point n)
    (hp : p ∈ V.points) : ∃ a : ℕ, V.multiplicity p = (a : ℚ) := by
  obtain ⟨N, hN⟩ := (V.localHilbert_eventually_polynomial p).choose_spec.2
  have hvalues : ∀ t ≥ N, ∃ a : ℤ,
      (V.localHilbertPolynomial p).eval (t : ℚ) = (a : ℚ) := by
    intro t ht
    obtain ⟨a, _, ha⟩ := hN t ht
    refine ⟨(a : ℤ), ?_⟩
    simpa only [AffineVariety.localHilbertPolynomial, Int.cast_natCast] using ha
  obtain ⟨a, ha⟩ := factorial_leadingCoeff_integral (V.localHilbertPolynomial p) N hvalues
  have hmult : V.multiplicity p = (a : ℚ) := by
    simpa only [AffineVariety.multiplicity, AffineVariety.localDimension,
      Polynomial.leadingCoeff, mul_comm] using ha
  have ha_nonneg : 0 ≤ a := by
    have hpos := (V.multiplicity_pos p hp).le
    rw [hmult] at hpos
    exact_mod_cast hpos
  refine ⟨a.toNat, ?_⟩
  rw [hmult, ← Int.cast_natCast, Int.toNat_of_nonneg ha_nonneg]

end
end DistinctDistances.TrackA
