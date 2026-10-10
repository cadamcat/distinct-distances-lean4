import DistinctDistances.TrackD.DProfilesAux
import DistinctDistances.TrackD.Profiles.PartitionDyadic

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section

/-- The fixed-grid regularization losses and small-remainder losses are
summable over the actual finite halving chain, uniformly in its length. -/
theorem partition_fixed_grid_loss (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ u₀ : ℝ, 1 ≤ u₀ ∧ ∀ (b : ℝ) (n : ℕ), u₀ ≤ b / 2 ^ n →
      (∑ i ∈ Finset.range n,
        (C * Real.exp (-(b / 2 ^ i) ^ ((1 : ℝ) / 10) / 2) +
          Real.exp (-(b / 2 ^ i) ^ ((1 : ℝ) / 3)))) ≤ ε := by
  obtain ⟨U, hU⟩ := prof_partition_discard_aux C hC (ε / 2) (by positivity)
  refine ⟨max 1 U, le_max_left _ _, ?_⟩
  intro b n hu
  let u : ℝ := b / 2 ^ n
  have huU : U ≤ u := (le_max_right _ _).trans hu
  obtain ⟨hsum1, hbound1, hsum2, hbound2⟩ := hU u huU
  let f : ℝ → ℝ := fun x => C * (1 + Real.sqrt (Real.log x)) *
    Real.exp (-x ^ ((1 : ℝ) / 10) / 2)
  let g : ℝ → ℝ := fun x => Real.exp (-x ^ ((1 : ℝ) / 3))
  have h1 : (∑ i ∈ Finset.range n,
      C * Real.exp (-(b / 2 ^ i) ^ ((1 : ℝ) / 10) / 2)) ≤ ε / 2 := by
    apply le_trans _ ((partition_dyadic_sum_le f b u n rfl
      (fun m => by dsimp [f]; positivity) hsum1).trans hbound1)
    apply Finset.sum_le_sum
    intro i hi
    dsimp [f]
    calc
      _ = C * 1 * Real.exp (-(b / 2 ^ i) ^ ((1 : ℝ) / 10) / 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith [Real.sqrt_nonneg (Real.log (b / 2 ^ i))]) hC)
        (Real.exp_nonneg _)
  have h2 : (∑ i ∈ Finset.range n,
      Real.exp (-(b / 2 ^ i) ^ ((1 : ℝ) / 3))) ≤ ε / 2 :=
    (partition_dyadic_sum_le g b u n rfl (fun m => Real.exp_nonneg _) hsum2).trans hbound2
  rw [Finset.sum_add_distrib]
  linarith

end
end DistinctDistances.TrackD
