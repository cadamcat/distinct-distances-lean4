import DistinctDistances.TrackB.MixedHilbert
import DistinctDistances.TrackB.BridgesBMixedHilbert
import DistinctDistances.TrackB.BridgesBAuxBirational

namespace DistinctDistances.TrackB.Request
noncomputable section

/-- Request to track A: nonnegative top mixed coefficients of the actual
bigraded restriction-rank polynomial, supplying conc:deg-mixed-positivity
(concentration.tex:768–774). This is a numerical Hilbert statement, with no
smoothness, Chow ring, or replacement degree definition. -/
theorem pairHilbert_mixed_top_nonnegative {n m d : ℕ}
    (T : Set (ProjectivePoint n × ProjectivePoint m)) (P : BaseHilbertPolynomial)
    (hdeg : P.totalDegree ≤ d)
    (hevent : ∃ N : ℕ, ∀ s t : ℕ, N ≤ s → N ≤ t →
      MvPolynomial.eval (Fin.cons (s : ℚ) (fun _ : Fin 1 => (t : ℚ))) P =
        (pairHilbert T s t : ℚ)) :
    ∀ p q : ℕ, p + q = d → 0 ≤ mixedHilbertCoefficient P p q := by
  exact BridgesBMixed.mixed_nonneg_pair T P hdeg hevent

/-- Request to track A: the top second-factor coefficient under a birational
proper projection from an actual closed pair variety. This supplies the final
term of conc:deg-mixed-positivity (concentration.tex:772–774) on a singular base.
Degree and dimension are the existing single-graded Hilbert invariants. -/
theorem pairHilbert_birational_top_coefficient {n m d : ℕ}
    (T : Set (ProjectivePoint n × ProjectivePoint m)) (hclosed : closedPairs T = T)
    (hT : (pairClosure T).IsIrreducible)
    (Y : ProjectiveVariety m) (hY : Y.IsIrreducible) (hdim : Y.dimension = d)
    (hproj : ∀ p q, (p, q) ∈ T → q ∈ Y.points)
    (P : BaseHilbertPolynomial) (hdeg : P.totalDegree ≤ d)
    (hevent : ∃ N : ℕ, ∀ s t : ℕ, N ≤ s → N ≤ t →
      MvPolynomial.eval (Fin.cons (s : ℚ) (fun _ : Fin 1 => (t : ℚ))) P =
        (pairHilbert T s t : ℚ))
    (g : Poly m) (D : ℕ) (hhom : g.IsHomogeneous D) (hg : g ∉ Y.ideal)
    (hgen : ∀ q ∈ Y.points, MvPolynomial.aeval q.rep g ≠ 0 →
      ∃! p : ProjectivePoint n, (p, q) ∈ T) :
    mixedHilbertCoefficient P 0 d = Y.degree := by
  exact BridgesBBir.birational_top_coefficient T hclosed hT Y hY hdim hproj P hdeg hevent
    g D hhom hg hgen

end
end DistinctDistances.TrackB.Request
