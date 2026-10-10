import DistinctDistances.Upper
import DistinctDistances.TrackE.Top

/-!
# The target (TOP.main)

The statement of `jsp_000900` in `Challenge.lean`, from the lower clause `lower_bound`
(track E) and the upper clause `upper_bound` (`Upper.lean`).
-/

namespace DistinctDistances

/-- TOP.main: the target `jsp_000900` of `Challenge.lean`, with the same statement. -/
theorem jsp_000900 :
    ∀ d : ℕ, 3 ≤ d →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
        (∀ P : Finset (EuclideanSpace ℝ (Fin d)), 2 ≤ P.card →
          c * (P.card : ℝ) ^ ((2 : ℝ) / (d : ℝ)) ≤ (distinctDistances P : ℝ)) ∧
        (∀ n : ℕ, 2 ≤ n → ∃ P : Finset (EuclideanSpace ℝ (Fin d)), P.card = n ∧
          (distinctDistances P : ℝ) ≤ C * (n : ℝ) ^ ((2 : ℝ) / (d : ℝ))) := by
  intro d hd
  obtain ⟨c, hc, hlow⟩ := lower_bound d hd
  obtain ⟨C, hC, hup⟩ := upper_bound d (by omega)
  exact ⟨c, C, hc, hC, hlow, hup⟩

end DistinctDistances
