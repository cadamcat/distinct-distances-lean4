import DistinctDistances.Bridges.CIncidence
import DistinctDistances.TrackC.WeakPlanar
import DistinctDistances.TrackE.Basic

/-! Track C's planar occupancy estimate at the reduction's distance scale. -/

namespace DistinctDistances.Bridges

open scoped Classical
noncomputable section

theorem planar_occupancy_mcount : ∃ C : ℝ, 0 < C ∧
    ∀ (m : ℕ) (Q : Finset (RPoint m)) (H : AffineSubspace ℝ (RPoint m)),
      Module.finrank ℝ H.direction = 2 →
      ((Q.filter (· ∈ H)).card : ℝ) ≤ C * Mcount Q ^ ((4 : ℝ) / 3) := by
  obtain ⟨C, hC, h⟩ := TrackC.ci_planar_occupancy
  refine ⟨C, hC, ?_⟩
  intro d Q H hH
  have hM : 1 ≤ Mcount Q := by
    dsimp [Mcount]
    exact le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hΔ : ((TrackC.positiveDistances Q).card : ℝ) ≤ Mcount Q := by
    change (distinctDistances Q : ℝ) ≤ (distinctDistances Q : ℝ) + 1
    linarith
  exact h d Q (Mcount Q) hM hΔ
    ⟨H, flat_nonempty_of_positive_rank H (by norm_num) hH, hH⟩

end
end DistinctDistances.Bridges
