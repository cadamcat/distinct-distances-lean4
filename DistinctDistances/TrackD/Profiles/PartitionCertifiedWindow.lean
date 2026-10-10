import DistinctDistances.TrackD.Profiles.PartitionSingleWindow
import DistinctDistances.TrackD.Profiles.PartitionBatchFromTree
import DistinctDistances.TrackD.Profiles.PartitionWidthControls

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section
variable {d : ℕ}

/-- The grid, isolation equations, hierarchy and boundary certificate of one
window are chosen before either greedy operation and before any batch. -/
structure PartitionWindowSetup (P U : Finset (Pt d)) (θ ξ K s ε : ℝ) where
  subset : U ⊆ P
  theta_pos : 0 < θ
  theta_small : θ ≤ 1 / 2
  xi_pos : 0 < ξ
  multiplier : 1 ≤ K
  mass_pos : 0 < cfgN P
  dyadic : ∃ a : ℕ, s = Real.log (cfgB P) / 2 ^ a
  gridSize : ℕ
  gridSize_pos : 0 < gridSize
  grid : Fin gridSize → ℝ
  grid_mono : StrictMono grid
  grid_first : grid ⟨0, gridSize_pos⟩ = -1
  grid_last_lower : 1 ≤ grid ⟨gridSize - 1, by omega⟩
  grid_last_upper : grid ⟨gridSize - 1, by omega⟩ ≤ 1 + θ
  grid_mesh : ∀ k : Fin gridSize, ∀ hk : k.val + 1 < gridSize,
    grid ⟨k.val + 1, hk⟩ - grid k ≤ min (θ / 8) (ξ / 4)
  weights : Fin (gridSize * d) → ℝ
  controls : PartitionWidthControls d gridSize θ ξ K s weights
  error : partitionEventTail (fun i => Real.exp (-weights i / 2)) 0 ≤ ε
  equations : Set (Poly d)
  degree : ∀ f ∈ equations,
    f.totalDegree ≤ ⌊testDeg (cfgB P) s (grid ⟨gridSize - 1, by omega⟩)⌋₊
  isolate : MvPolynomial.zeroLocus ℂ (Ideal.span equations) = toC '' (U : Set (Pt d))
  initial : CutPath d
  boundaryExponent : ℝ
  boundary_ratio : Real.exp (Real.sqrt s + partitionEventTail weights 0 - boundaryExponent) ≤ θ
  boundary : ∀ b : ℝ, b + ξ / 4 ≤ grid ⟨0, gridSize_pos⟩ → ∀ g : Poly d,
    (g.totalDegree : ℝ) ≤ K * testDeg (cfgB P) s b →
      ((initial.captured 0 U g).card : ℝ) ≤ cfgN P * Real.exp (-boundaryExponent)

/-- Both regularization callbacks in the greedy window follow from one
uniform tree setup. The first batch forces an early cut; saturation of the
remainder forces a late cut. -/
theorem partition_window_callbacks (P U : Finset (Pt d)) (θ ξ K s ε : ℝ)
    (hd : 0 < d) (W : PartitionWindowSetup P U θ ξ K s ε) :
    (∀ T : Finset (Pt d), T ⊆ U → cfgN P * Real.exp (-Real.sqrt s) ≤ (T.card : ℝ) →
      ∀ g : Poly d, g ≠ 0 → g.totalDegree ≤ ⌊testDeg (cfgB P) s (-1 / 2)⌋₊ →
      (∀ x ∈ T, MvPolynomial.eval (toC x) g = 0) →
      Nonempty (PartitionBatchPieces P θ ξ K s ε T)) ∧
    (∀ R : Finset (Pt d), R ⊆ U → cfgN P * Real.exp (-s ^ ((1 : ℝ) / 3)) ≤ (R.card : ℝ) →
      (∀ T : Finset (Pt d), T ⊆ R → CoreIsolated T ⌊testDeg (cfgB P) s (1 / 2)⌋₊ →
        (T.card : ℝ) < cfgN P * Real.exp (-Real.sqrt s)) →
      Nonempty (PartitionBatchPieces P θ ξ K s ε R)) := by
  classical
  let L : Fin W.gridSize → ℕ := fun k => ⌊testDeg (cfgB P) s (W.grid k)⌋₊
  let u : ℝ := s ^ ((1 : ℝ) / 10)
  have hs : 0 ≤ s := (show (0 : ℝ) ≤ 1 by norm_num).trans W.controls.width
  have hB : 0 ≤ cfgB P := by unfold cfgB; positivity
  have hmesh : ∀ k : Fin W.gridSize, ∀ hk : k.val + 1 < W.gridSize,
      W.grid ⟨k.val + 1, hk⟩ - W.grid k ≤ ξ / 4 := by
    intro k hk
    exact (W.grid_mesh k hk).trans (min_le_right _ _)
  have hmeshTheta : ∀ k : Fin W.gridSize, ∀ hk : k.val + 1 < W.gridSize,
      W.grid ⟨k.val + 1, hk⟩ - W.grid k ≤ θ := by
    intro k hk
    have h := (W.grid_mesh k hk).trans (min_le_left _ _)
    linarith [W.theta_pos]
  have hbuild : ∀ T : Finset (Pt d), T ⊆ U →
      cfgN P * Real.exp (-Real.sqrt s) ≤ (T.card : ℝ) →
      (∀ X : Piece d,
        PartitionGridLeaf W.grid L ⟨0, W.gridSize_pos⟩ W.initial 0 T s X →
        (T.card : ℝ) * Real.exp (-partitionEventTail W.weights 0) ≤ X.pts.card →
        PartitionGridTests W.grid L ⟨0, W.gridSize_pos⟩ u X →
        ∃ i, 1 / 2 - θ ≤ |X.path.time i|) →
      Nonempty (PartitionBatchPieces P θ ξ K s ε T) := by
    intro T hTU hmass himbalance
    exact partition_batch_from_tree P U T W.subset hTU θ ξ K s u ε W.boundaryExponent
      W.theta_pos W.xi_pos W.multiplier hs W.controls.positive W.dyadic
      W.gridSize_pos W.grid W.grid_mono W.grid_first W.grid_last_upper hmesh
      W.controls.multiplier.le L (fun k => rfl) W.weights W.controls.weights W.controls.tail
      W.equations W.degree W.isolate hmass W.controls.size W.controls.capture
      W.error W.boundary_ratio W.initial W.boundary himbalance
  constructor
  · intro T hTU hmass g hg hdegree hvan
    apply hbuild T hTU hmass
    intro X hX hleaf htests
    obtain ⟨k, hk, hktime⟩ := partition_grid_after_half W.gridSize_pos W.grid θ W.theta_pos
      W.theta_small W.grid_first W.grid_last_lower hmeshTheta
    have hdeg : g.totalDegree ≤ L k := hdegree.trans
      (Nat.floor_le_floor (RankCore.testDeg_mono hB hs hk))
    exact partition_first_type_imbalance hd W.grid L ⟨0, W.gridSize_pos⟩ k
      (show (⟨0, W.gridSize_pos⟩ : Fin W.gridSize) ≤ k by change 0 ≤ k.val; omega)
      s u θ W.controls.positive W.initial T X hX htests g hg hdeg hvan hktime.le
  · intro R hRU hmass hsaturated
    have hloss : 0 ≤ partitionEventTail W.weights 0 :=
      partition_event_tail_nonneg W.weights
        (fun i => W.controls.positive.le.trans (W.controls.weights i)) 0
    have hbatch : cfgN P * Real.exp (-Real.sqrt s) ≤ (R.card : ℝ) := by
      apply le_trans _ hmass
      apply mul_le_mul_of_nonneg_left _ W.mass_pos.le
      apply Real.exp_le_exp.mpr
      linarith [W.controls.remainder]
    apply hbuild R hRU hbatch
    intro X hX hleaf htests
    have hlarge : cfgN P * Real.exp (-Real.sqrt s) ≤ (X.pts.card : ℝ) :=
      (partition_remainder_leaf_mass (cfgN P) (R.card : ℝ) (X.pts.card : ℝ) s
        (partitionEventTail W.weights 0) W.mass_pos hmass hleaf W.controls.remainder).le
    have hdegree : ∀ i, ((X.path.cut i).totalDegree : ℝ) ≤
        testDeg (cfgB P) X.width (X.path.time i + θ) := by
      intro i
      obtain ⟨k, hk, hdeg, ht⟩ := hX.newcuts i (Nat.zero_le _)
      have hdegR : ((X.path.cut i).totalDegree : ℝ) ≤ L k := by exact_mod_cast hdeg
      have hfloor : (L k : ℝ) ≤ testDeg (cfgB P) s (W.grid k) :=
        Nat.floor_le (mul_nonneg hB (Real.exp_nonneg _))
      rw [hX.width, ht]
      exact hdegR.trans (hfloor.trans (RankCore.testDeg_mono hB hs (by linarith [W.theta_pos])))
    apply partition_remainder_imbalance R X (cfgB P) θ
      (cfgN P * Real.exp (-Real.sqrt s)) hB (by rwa [hX.width]) hX.subset
      hX.vanish hX.proper hdegree hlarge
    simpa only [hX.width] using hsaturated

/-- `profiles.tex:92–116, 196–218`: one nonfinal window produces good
disjoint pieces and an exactly isolated next set with its lower boundary. -/
theorem partition_certified_window (P U : Finset (Pt d)) (θ ξ K s ε : ℝ)
    (hd : 0 < d) (W : PartitionWindowSetup P U θ ξ K s ε)
    (hdegree : 1 ≤ ⌊testDeg (cfgB P) s (1 / 2)⌋₊) :
    ∃ (V : Finset (Pt d)) (E : Set (Poly d)) (b : ℕ) (pl : Finset (Piece d)),
      V ⊆ U ∧ cfgN P * Real.exp (-Real.sqrt s) * b ≤ U.card ∧
      (∀ f ∈ E, f.totalDegree ≤ b * (d * (⌊testDeg (cfgB P) s (1 / 2)⌋₊ - 1) + 1)) ∧
      MvPolynomial.zeroLocus ℂ (Ideal.span E) = toC '' (V : Set (Pt d)) ∧
      (∀ g : Poly d, g ≠ 0 → g.totalDegree ≤ ⌊testDeg (cfgB P) s (-1 / 2)⌋₊ →
        ((V.filter (fun x => MvPolynomial.eval (toC x) g = 0)).card : ℝ) <
          cfgN P * Real.exp (-Real.sqrt s)) ∧
      (∀ X ∈ pl, PieceGood P θ ξ K X ∧ X.width = s ∧ X.pts ⊆ U) ∧
      (pl : Set (Piece d)).PairwiseDisjoint Piece.pts ∧
      (∀ X ∈ pl, Disjoint X.pts V) ∧
      (U.card : ℝ) - V.card - (∑ X ∈ pl, (X.pts.card : ℝ)) ≤
        ε * U.card + cfgN P * Real.exp (-s ^ ((1 : ℝ) / 3)) := by
  obtain ⟨hfirst, hrem⟩ := partition_window_callbacks P U θ ξ K s ε hd W
  have hε : 0 ≤ ε := (partition_event_tail_nonneg
    (fun i => Real.exp (-W.weights i / 2)) (fun i => Real.exp_nonneg _) 0).trans W.error
  exact partition_single_window P U ⌊testDeg (cfgB P) s (-1 / 2)⌋₊
    ⌊testDeg (cfgB P) s (1 / 2)⌋₊ hdegree (cfgN P * Real.exp (-Real.sqrt s)) θ ξ K s ε
    (cfgN P * Real.exp (-s ^ ((1 : ℝ) / 3))) (mul_pos W.mass_pos (Real.exp_pos _))
    hε (mul_pos W.mass_pos (Real.exp_pos _)) hfirst hrem

end
end DistinctDistances.TrackD
