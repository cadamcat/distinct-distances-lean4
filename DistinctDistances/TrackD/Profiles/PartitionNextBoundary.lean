import DistinctDistances.TrackD.Profiles.PartitionImbalance

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section
variable {d : ℕ}

/-- The first greedy operation supplies every low polynomial test in the
next window. The initial cut path is fixed before those tests. -/
theorem partition_next_low_boundary (P V : Finset (Pt d)) (π : CutPath d)
    (ξ K s : ℝ) (hK : 1 ≤ K) (hs : 0 ≤ s)
    (hlarge : Real.log K ≤ ξ / 4 * (s / 2))
    (hlow : ∀ g : Poly d, g ≠ 0 → g.totalDegree ≤ ⌊testDeg (cfgB P) s (-1 / 2)⌋₊ →
      ((V.filter (fun x => MvPolynomial.eval (toC x) g = 0)).card : ℝ) <
        cfgN P * Real.exp (-Real.sqrt s)) :
    ∀ b : ℝ, b + ξ / 4 ≤ -1 → ∀ g : Poly d,
      (g.totalDegree : ℝ) ≤ K * testDeg (cfgB P) (s / 2) b →
        ((π.captured 0 V g).card : ℝ) ≤ cfgN P * Real.exp (-Real.sqrt s) := by
  intro b hb g hg
  by_cases hzero : g = 0
  · subst g
    rw [partition_constant_capture_empty π V 0 (by simp)]
    simp only [Finset.card_empty, Nat.cast_zero]
    unfold cfgN
    positivity
  · rw [partition_initial_capture_eq π V g hzero]
    apply (hlow g hzero _).le
    have hB : 0 ≤ cfgB P := by unfold cfgB; positivity
    have hdegree : (g.totalDegree : ℝ) ≤ testDeg (cfgB P) (s / 2) (-1) :=
      hg.trans (partition_degree_absorption (cfgB P) (s / 2) b (-1) ξ K
        hB (by positivity) hK hb hlarge)
    have heq : testDeg (cfgB P) (s / 2) (-1) = testDeg (cfgB P) s (-1 / 2) := by
      unfold testDeg
      congr 2
      ring
    rw [heq] at hdegree
    exact (Nat.le_floor_iff (mul_nonneg hB (Real.exp_nonneg _))).mpr hdegree

end
end DistinctDistances.TrackD
