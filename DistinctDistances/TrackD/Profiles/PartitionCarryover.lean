import DistinctDistances.TrackD.Profiles.PartitionBoundary

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section
variable {d : ℕ}

theorem partition_interpolation_degree_le (d L : ℕ) (hL : 1 ≤ L) :
    d * (L - 1) + 1 ≤ (d + 1) * L := by
  have hsub : L - 1 + 1 = L := Nat.sub_add_cancel hL
  have hprod : d * (L - 1) + d = d * L := by
    simpa only [Nat.mul_add, mul_one] using congrArg (fun n => d * n) hsub
  simp only [Nat.add_mul, one_mul]
  omega

/-- The number of second batches and interpolation loss are absorbed by the
strict entry-degree gap at the next halved window. -/
theorem partition_degree_carryover (B s θ C batches L D : ℝ)
    (hB : 0 ≤ B) (hC : 0 < C) (hL : 0 ≤ L)
    (hbatch : batches ≤ Real.exp (Real.sqrt s))
    (hdegree : L ≤ testDeg B s (1 / 2)) (hD : D ≤ batches * C * L)
    (hgap : Real.sqrt s + Real.log C ≤ θ * s / 2) :
    D ≤ testDeg B (s / 2) (1 + θ) := by
  calc
    D ≤ batches * C * L := hD
    _ ≤ Real.exp (Real.sqrt s) * C * L :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hbatch hC.le) hL
    _ ≤ Real.exp (Real.sqrt s) * C * testDeg B s (1 / 2) :=
      mul_le_mul_of_nonneg_left hdegree (mul_nonneg (Real.exp_nonneg _) hC.le)
    _ = B * Real.exp (s / 2 + Real.sqrt s + Real.log C) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log hC]
      unfold testDeg
      rw [show (1 / 2 : ℝ) * s = s / 2 by ring]
      ring
    _ ≤ testDeg B (s / 2) (1 + θ) := by
      unfold testDeg
      apply mul_le_mul_of_nonneg_left _ hB
      apply Real.exp_le_exp.mpr
      nlinarith

/-- The final core degree is tested against the same fixed delta bound
chosen before the sample. -/
theorem partition_core_energy (N B δ L t θ : ℝ)
    (hN : 0 ≤ N) (hB : 0 < B) (hδ : 0 ≤ δ) (hL : 0 ≤ L)
    (hdegree : L ≤ B * Real.exp (3 * t)) (hsmall : δ * Real.exp (6 * t) ≤ θ) :
    δ * N / B ^ 2 * L ^ 2 ≤ θ * N := by
  have hden : 0 ≤ δ * N / B ^ 2 := by positivity
  calc
    _ ≤ δ * N / B ^ 2 * (B * Real.exp (3 * t)) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hden
      exact pow_le_pow_left₀ hL hdegree 2
    _ = δ * N * Real.exp (6 * t) := by
      have hpow : Real.exp (3 * t) ^ 2 = Real.exp (6 * t) := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      rw [mul_pow, hpow]
      field_simp
    _ ≤ θ * N := by nlinarith

/-- A disjoint family of batches, each of the extraction threshold size,
has at most exp(sqrt(s)) members. -/
theorem partition_window_batch_count (N n s : ℝ) (b : ℕ) (hN : 0 < N)
    (hmass : N * Real.exp (-Real.sqrt s) * b ≤ n) (hn : n ≤ N) :
    (b : ℝ) ≤ Real.exp (Real.sqrt s) := by
  have h := mul_le_mul_of_nonneg_right (hmass.trans hn) (Real.exp_nonneg (Real.sqrt s))
  have hcancel : N * Real.exp (-Real.sqrt s) * b * Real.exp (Real.sqrt s) = N * b := by
    rw [Real.exp_neg]
    field_simp
  rw [hcancel] at h
  exact (mul_le_mul_iff_right₀ hN).mp (by simpa only [mul_comm N] using h)

/-- The second-batch union meets the entry degree at the halved width;
the only dimension-dependent interpolation factor is d+1. -/
theorem partition_next_entry_degree (P U : Finset (Pt d)) (b L : ℕ) (s θ : ℝ)
    (hUP : U ⊆ P) (hN : 0 < cfgN P) (hL : 1 ≤ L)
    (hmass : cfgN P * Real.exp (-Real.sqrt s) * b ≤ U.card)
    (hdegree : (L : ℝ) ≤ testDeg (cfgB P) s (1 / 2))
    (hgap : Real.sqrt s + Real.log (d + 1 : ℝ) ≤ θ * s / 2) :
    (b * (d * (L - 1) + 1) : ℕ) ≤ testDeg (cfgB P) (s / 2) (1 + θ) := by
  have hn : (U.card : ℝ) ≤ cfgN P := by
    unfold cfgN
    exact_mod_cast Finset.card_le_card hUP
  have hcount := partition_window_batch_count (cfgN P) (U.card : ℝ) s b hN hmass hn
  have hinterp : ((d * (L - 1) + 1 : ℕ) : ℝ) ≤ (d + 1 : ℝ) * L := by
    exact_mod_cast partition_interpolation_degree_le d L hL
  apply partition_degree_carryover (cfgB P) s θ (d + 1) b L
    ((b * (d * (L - 1) + 1) : ℕ) : ℝ)
    (by unfold cfgB; positivity) (by positivity) (Nat.cast_nonneg L) hcount hdegree
    (by
      push_cast
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, mul_assoc] using
        mul_le_mul_of_nonneg_left hinterp (Nat.cast_nonneg b)) hgap

end
end DistinctDistances.TrackD
