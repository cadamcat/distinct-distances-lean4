import DistinctDistances.TrackC.PartitionSigns
import DistinctDistances.TrackC.LinePolynomial

namespace DistinctDistances.TrackC

/-- Different strict factor-sign vectors force a product zero between ordered line parameters. -/
theorem factor_sign_interval_root (d : ℕ) (fs : List (Poly d)) (x v : E d)
    (a b : ℝ) (hab : a < b) (σ τ : Fin fs.length → Bool) (hστ : σ ≠ τ)
    (ha : x+a • v ∈ factorSignCell fs σ) (hb : x+b • v ∈ factorSignCell fs τ) :
    ∃ u : ℝ, a < u ∧ u < b ∧ (linePolynomial d fs.prod x v).IsRoot u := by
  classical
  obtain ⟨i, hi⟩ : ∃ i : Fin fs.length, σ i ≠ τ i := by
    by_contra! h
    exact hστ (funext h)
  let q := linePolynomial d (fs.get i) x v
  have hqa := ha i
  have hqb := hb i
  have hz (u : ℝ) (hu : q.eval u = 0) : (linePolynomial d fs.prod x v).IsRoot u := by
    have hfactor : evalR (fs.get i) (x+u • v) = 0 := by
      rw [← linePolynomial_eval]
      exact hu
    change (linePolynomial d fs.prod x v).eval u = 0
    rw [linePolynomial_eval]
    by_contra hprod
    exact ((eval_product_ne_zero_iff fs (x+u • v)).mp hprod i) hfactor
  cases hσ : σ i <;> cases hτ : τ i
  · simp [hσ, hτ] at hi
  · have hneg : q.eval a < 0 := by simpa [hσ, q, linePolynomial_eval] using hqa
    have hpos : 0 < q.eval b := by simpa [hτ, q, linePolynomial_eval] using hqb
    obtain ⟨u, hu, heval⟩ := intermediate_value_Ioo hab.le q.continuous.continuousOn ⟨hneg, hpos⟩
    exact ⟨u, hu.1, hu.2, hz u heval⟩
  · have hpos : 0 < q.eval a := by simpa [hσ, q, linePolynomial_eval] using hqa
    have hneg : q.eval b < 0 := by simpa [hτ, q, linePolynomial_eval] using hqb
    obtain ⟨u, hu, heval⟩ := intermediate_value_Ioo' hab.le q.continuous.continuousOn ⟨hneg, hpos⟩
    exact ⟨u, hu.1, hu.2, hz u heval⟩
  · simp [hσ, hτ] at hi

end DistinctDistances.TrackC
