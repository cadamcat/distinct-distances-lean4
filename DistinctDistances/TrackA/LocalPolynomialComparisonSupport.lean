import DistinctDistances.Foundations.LocalHilbert

namespace DistinctDistances.TrackA
noncomputable section

/-- The chosen original polynomial represents the exact finite lengths. -/
theorem localHilbertPolynomial_eventually {n : ℕ} (V : AffineVariety n) (p : Point n) :
    ∀ᶠ t : ℕ in Filter.atTop,
      (V.localHilbertPolynomial p).eval (t : ℚ) = ((V.localHilbert p t).toNat : ℚ) := by
  obtain ⟨N, hN⟩ := (V.localHilbert_eventually_polynomial p).choose_spec.2
  filter_upwards [Filter.eventually_atTop.2 ⟨N, hN⟩] with t ht
  obtain ⟨a, ha, he⟩ := ht
  simpa only [AffineVariety.localHilbertPolynomial, ha, ENat.toNat_natCast] using he

/-- Eventual equality of the actual local lengths identifies the original
chosen rational polynomials, including the zero polynomial off a carrier. -/
theorem localHilbertPolynomial_eq_of_eventually {n m : ℕ}
    (V : AffineVariety n) (p : Point n) (W : AffineVariety m) (q : Point m)
    (h : ∀ᶠ t : ℕ in Filter.atTop, V.localHilbert p t = W.localHilbert q t) :
    V.localHilbertPolynomial p = W.localHilbertPolynomial q := by
  apply OAI.QuarticPowerFree.polynomial_eq_of_eventually_nat_eval_eq
  filter_upwards [localHilbertPolynomial_eventually V p,
    localHilbertPolynomial_eventually W q, h] with t hV hW ht
  rw [hV, hW, ht]

/-- Actual local-length equality preserves the multiplicity computed in
the original model. No dimension comparison is needed. -/
theorem multiplicity_eq_of_localHilbert_eq {n m : ℕ}
    (V : AffineVariety n) (p : Point n) (W : AffineVariety m) (q : Point m)
    (h : ∀ t, V.localHilbert p t = W.localHilbert q t) :
    V.multiplicity p = W.multiplicity q := by
  have hP := localHilbertPolynomial_eq_of_eventually V p W q (Filter.Eventually.of_forall h)
  simp only [AffineVariety.multiplicity, AffineVariety.localDimension, hP]

end
end DistinctDistances.TrackA
