import DistinctDistances.TrackD.Profiles.PartitionTreeConstruction
import DistinctDistances.TrackD.Profiles.PartitionInitialBoundary

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section
variable {d G : ℕ}

/-- Convert the stronger internal grid certificates into the external piece
properties after size, imbalance and the low boundary have been established. -/
theorem partition_piece_good_of_grid (P S : Finset (Pt d)) (hSP : S ⊆ P)
    (θ ξ K s u : ℝ) (hθ : 0 < θ) (hξ : 0 < ξ) (hK : 1 ≤ K) (hs : 0 ≤ s)
    (hdyadic : ∃ a : ℕ, s = Real.log (cfgB P) / 2 ^ a)
    (hG : 0 < G) (grid : Fin G → ℝ) (hgrid : StrictMono grid)
    (hfirst : grid ⟨0, hG⟩ = -1)
    (hlast : grid ⟨G - 1, by omega⟩ ≤ 1 + θ)
    (hmesh : ∀ k : Fin G, ∀ hk : k.val + 1 < G,
      grid ⟨k.val + 1, hk⟩ - grid k ≤ ξ / 4)
    (hlarge : Real.log K ≤ ξ / 4 * s)
    (L : Fin G → ℕ) (hL : ∀ k, L k = ⌊testDeg (cfgB P) s (grid k)⌋₊)
    (π : CutPath d) (X : Piece d)
    (hX : PartitionGridLeaf grid L ⟨0, hG⟩ π 0 S s X)
    (hsize : cfgN P * Real.exp (-θ * s) ≤ X.pts.card)
    (himbalance : ∃ i, 1 / 2 - θ ≤ |X.path.time i|)
    (htests : PartitionGridTests grid L ⟨0, hG⟩ u X)
    (hsmall : Real.exp (-7 * u / 18) ≤ θ)
    (hboundary : ∀ b : ℝ, b + ξ / 4 ≤ grid ⟨0, hG⟩ →
      ∀ g : Poly d, (g.totalDegree : ℝ) ≤ K * testDeg (cfgB P) s b →
        ((X.path.captured 0 X.pts g).card : ℝ) ≤ θ * X.pts.card) :
    PieceGood P θ ξ K X := by
  classical
  have hB : 0 ≤ cfgB P := by unfold cfgB; positivity
  have htime : ∀ i, ∃ k : Fin G, X.path.time i = grid k := by
    intro i
    obtain ⟨k, hk, hdeg, ht⟩ := hX.newcuts i (Nat.zero_le _)
    exact ⟨k, ht⟩
  have hzero (k : Fin G) : (⟨0, hG⟩ : Fin G) ≤ k := by change 0 ≤ k.val; omega
  refine ⟨hX.subset.trans hSP, ?_, ?_, hX.mono, ?_, himbalance,
    hX.vanish, hX.proper, ?_, ?_⟩
  · rw [hX.width]
    exact hdyadic
  · rw [hX.width]
    exact hsize
  · intro i
    obtain ⟨k, ht⟩ := htime i
    rw [ht]
    constructor
    · rw [← hfirst]
      exact hgrid.monotone (hzero k)
    · apply le_trans _ hlast
      apply hgrid.monotone
      change k.val ≤ G - 1
      have := k.isLt
      omega
  · intro i
    obtain ⟨k, hk, hdeg, ht⟩ := hX.newcuts i (Nat.zero_le _)
    rw [hX.width, ht]
    have hdegR : ((X.path.cut i).totalDegree : ℝ) ≤ L k := by exact_mod_cast hdeg
    have hfloor : (L k : ℝ) ≤ testDeg (cfgB P) s (grid k) := by
      rw [hL k]
      exact Nat.floor_le (mul_nonneg hB (Real.exp_nonneg _))
    exact hdegR.trans (hfloor.trans (RankCore.testDeg_mono hB hs (by linarith)))
  · intro j hj b hb hT g hg
    rw [hX.width] at hT hg
    apply partition_no_capture_of_grid X.path X.pts hG grid hgrid.monotone ξ K (cfgB P) s θ
      hξ hK hB hs hlarge hmesh htime hboundary ?_ j hj b hb g hg
    intro k ℓ hℓ hp f hf
    have hfNat : f.totalDegree ≤ L k := by
      rw [hL k]
      exact (Nat.le_floor_iff (mul_nonneg hB (Real.exp_nonneg _))).mpr hf
    exact (htests k (hzero k) ℓ hℓ hp f hfNat).trans
      (mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg X.pts.card))

/-- The branch-size loss is charged to the original batch, and is absorbed
by the fixed output tolerance once the window is sufficiently wide. -/
theorem partition_leaf_size_of_losses (N m n s loss θ : ℝ) (hN : 0 ≤ N)
    (hbatch : N * Real.exp (-Real.sqrt s) ≤ m)
    (hleaf : m * Real.exp (-loss) ≤ n)
    (hbudget : Real.sqrt s + loss ≤ θ * s) :
    N * Real.exp (-θ * s) ≤ n := by
  calc
    N * Real.exp (-θ * s) ≤ N * Real.exp (-Real.sqrt s - loss) := by
      apply mul_le_mul_of_nonneg_left _ hN
      exact Real.exp_le_exp.mpr (by linarith)
    _ = (N * Real.exp (-Real.sqrt s)) * Real.exp (-loss) := by
      rw [sub_eq_add_neg, Real.exp_add]
      ring
    _ ≤ m * Real.exp (-loss) := mul_le_mul_of_nonneg_right hbatch (Real.exp_nonneg _)
    _ ≤ n := hleaf

end
end DistinctDistances.TrackD
