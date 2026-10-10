import DistinctDistances.TrackD.Profiles.PartitionGrid

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section

/-- The finitary time grid is chosen before the sample. It begins at -1,
ends beyond the isolation entry scale, and has mesh smaller than both the
profile tolerance and the interior testing margin. -/
theorem partition_fixed_grid (θ ξ : ℝ) (hθ : 0 < θ) (hξ : 0 < ξ) :
    ∃ G : ℕ, ∃ hG : 0 < G, ∃ grid : Fin G → ℝ,
      StrictMono grid ∧ grid ⟨0, hG⟩ = -1 ∧
      1 + θ / 2 ≤ grid ⟨G - 1, by omega⟩ ∧
      grid ⟨G - 1, by omega⟩ ≤ 1 + θ ∧
      ∀ k : Fin G, ∀ hk : k.val + 1 < G,
        grid ⟨k.val + 1, hk⟩ - grid k ≤ min (θ / 8) (ξ / 4) := by
  let h : ℝ := min (θ / 8) (ξ / 4)
  have hh : 0 < h := by dsimp [h]; positivity
  let q : ℝ := (2 + θ / 2) / h
  have hq : 0 < q := by dsimp [q]; positivity
  let n : ℕ := ⌈q⌉₊
  let grid : Fin (n + 1) → ℝ := fun k => -1 + (k.val : ℝ) * h
  have hlower : 2 + θ / 2 ≤ (n : ℝ) * h := by
    have hc : q ≤ (n : ℝ) := Nat.le_ceil q
    exact (div_le_iff₀ hh).mp hc
  have hupper : (n : ℝ) * h < 2 + θ / 2 + h := by
    have hc : (n : ℝ) < q + 1 := Nat.ceil_lt_add_one hq.le
    have hc' := mul_lt_mul_of_pos_right hc hh
    have heq : (q + 1) * h = 2 + θ / 2 + h := by
      dsimp [q]
      field_simp
    rwa [heq] at hc'
  refine ⟨n + 1, by omega, grid, ?_, ?_, ?_, ?_, ?_⟩
  · intro i k hik
    have hikR : (i.val : ℝ) < (k.val : ℝ) := by exact_mod_cast hik
    dsimp [grid]
    have hmul := mul_lt_mul_of_pos_right hikR hh
    linarith
  · simp [grid]
  · change 1 + θ / 2 ≤ -1 + ((n + 1 - 1 : ℕ) : ℝ) * h
    simp only [Nat.add_sub_cancel] at *
    linarith
  · change -1 + ((n + 1 - 1 : ℕ) : ℝ) * h ≤ 1 + θ
    simp only [Nat.add_sub_cancel] at *
    have hhθ : h ≤ θ / 8 := min_le_left _ _
    linarith
  · intro k hk
    change (-1 + ((k.val + 1 : ℕ) : ℝ) * h) - (-1 + (k.val : ℝ) * h) ≤ h
    push_cast
    linarith

end
end DistinctDistances.TrackD
