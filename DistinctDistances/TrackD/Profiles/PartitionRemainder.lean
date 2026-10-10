import DistinctDistances.TrackD.Profiles.PartitionImbalance
import DistinctDistances.TrackD.Profiles.PartitionWindowPackages

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section
variable {d : ℕ}

/-- The small-remainder threshold is still above the greedy threshold after
every terminal fragmentation loss, at sufficiently large widths. -/
theorem partition_remainder_leaf_mass (N m n s loss : ℝ) (hN : 0 < N)
    (hbatch : N * Real.exp (-s ^ ((1 : ℝ) / 3)) ≤ m)
    (hleaf : m * Real.exp (-loss) ≤ n)
    (hbudget : s ^ ((1 : ℝ) / 3) + loss < Real.sqrt s) :
    N * Real.exp (-Real.sqrt s) < n := by
  calc
    _ < N * Real.exp (-s ^ ((1 : ℝ) / 3) - loss) := by
      apply mul_lt_mul_of_pos_left _ hN
      exact Real.exp_lt_exp.mpr (by linarith)
    _ = (N * Real.exp (-s ^ ((1 : ℝ) / 3))) * Real.exp (-loss) := by
      rw [sub_eq_add_neg, Real.exp_add]
      ring
    _ ≤ m * Real.exp (-loss) := mul_le_mul_of_nonneg_right hbatch (Real.exp_nonneg _)
    _ ≤ n := hleaf

/-- A large terminal leaf of the second-operation remainder cannot be
isolated below time 1/2: that would be another admissible extracted batch. -/
theorem partition_remainder_imbalance (R : Finset (Pt d)) (X : Piece d)
    (B θ threshold : ℝ) (hB : 0 ≤ B) (hs : 0 ≤ X.width) (hXR : X.pts ⊆ R)
    (hvan : ∀ x ∈ X.pts, ∀ i, MvPolynomial.eval (toC x) (X.path.cut i) = 0)
    (hproper : ∀ x ∈ X.pts, X.path.ProperAt (toC x))
    (hdegree : ∀ i, ((X.path.cut i).totalDegree : ℝ) ≤
      testDeg B X.width (X.path.time i + θ))
    (hmass : threshold ≤ (X.pts.card : ℝ))
    (hsaturated : ∀ T : Finset (Pt d), T ⊆ R →
      CoreIsolated T ⌊testDeg B X.width (1 / 2)⌋₊ → (T.card : ℝ) < threshold) :
    ∃ i : Fin d, 1 / 2 - θ ≤ |X.path.time i| := by
  classical
  by_contra hn
  have hsmall : ∀ i : Fin d, |X.path.time i| < 1 / 2 - θ := by
    intro i
    exact lt_of_not_ge (fun hi => hn ⟨i, hi⟩)
  have hdeg : ∀ i, (X.path.cut i).totalDegree ≤ ⌊testDeg B X.width (1 / 2)⌋₊ := by
    intro i
    apply (Nat.le_floor_iff (mul_nonneg hB (Real.exp_nonneg _))).mpr
    have htime : X.path.time i + θ ≤ 1 / 2 := by
      have ha := le_abs_self (X.path.time i)
      have hi := hsmall i
      linarith
    exact (hdegree i).trans (RankCore.testDeg_mono hB hs htime)
  have hcore := partition_completed_path_core X.pts X.path
    ⌊testDeg B X.width (1 / 2)⌋₊ hvan hproper hdeg
  have hbad := hsaturated X.pts hXR hcore
  linarith

end
end DistinctDistances.TrackD
