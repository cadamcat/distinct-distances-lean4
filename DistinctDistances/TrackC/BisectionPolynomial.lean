import DistinctDistances.TrackC.BisectionLimit
import DistinctDistances.TrackC.BisectionSpace

open scoped BigOperators

namespace DistinctDistances.TrackC

/-- The finite polynomial-bisection construction in the exact frozen form. -/
theorem polynomial_bisection_construct (d : ℕ) (S : Finset (Finset (E d))) (D : ℕ)
    (hD : S.card < Nat.choose (D+d) d) :
    ∃ f : Poly d, f ≠ 0 ∧ f.totalDegree ≤ D ∧ ∀ X ∈ S,
      ((X.filter (fun x => 0 < evalR f x)).card : ℝ) ≤ (X.card : ℝ) / 2 ∧
      ((X.filter (fun x => evalR f x < 0)).card : ℝ) ≤ (X.card : ℝ) / 2 := by
  classical
  obtain ⟨F, hF, hdegree⟩ := bisection_polynomial_embedding d S.card D hD
  let L := fun x : E d =>
    ((MvPolynomial.aeval x).toLinearMap.comp F).toContinuousLinearMap
  let family : Fin S.card → Finset (E d) := fun j => (S.equivFin.symm j).val
  obtain ⟨c, hc, hsign⟩ := bisection_linear_family d S.card family L
  have hc0 : c ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hc
    norm_num at hc
  have hf0 : F c ≠ 0 := by
    intro hz
    apply hc0
    exact hF (by simpa using hz)
  have heval (x : E d) : L x c = evalR (F c) x := by
    change MvPolynomial.aeval x (F c) = MvPolynomial.eval x (F c)
    simp [MvPolynomial.aeval_def]
  refine ⟨F c, hf0, hdegree c, ?_⟩
  intro X hX
  let j := S.equivFin ⟨X, hX⟩
  have hj : family j = X := by simp [family, j]
  have h := hsign j
  rw [hj] at h
  simpa only [heval] using h

end DistinctDistances.TrackC
