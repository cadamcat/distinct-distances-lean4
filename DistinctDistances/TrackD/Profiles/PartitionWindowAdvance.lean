import DistinctDistances.TrackD.Profiles.PartitionCertifiedWindow
import DistinctDistances.TrackD.Profiles.PartitionCarryover
import DistinctDistances.TrackD.Profiles.PartitionNextBoundary

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section
variable {d G : ℕ}

/-- Entry isolation and the inherited boundary at one dyadic width. The
path is fixed before all tests; no completed cut is needed at index zero. -/
structure PartitionWindowEntry (P U : Finset (Pt d)) (θ ξ K s : ℝ) (π : CutPath d) where
  subset : U ⊆ P
  equations : Set (Poly d)
  degree : ∀ f ∈ equations, (f.totalDegree : ℝ) ≤ testDeg (cfgB P) s (1 + θ / 2)
  isolate : MvPolynomial.zeroLocus ℂ (Ideal.span equations) = toC '' (U : Set (Pt d))
  boundary : ∀ b : ℝ, b + ξ / 4 ≤ -1 → ∀ g : Poly d,
    (g.totalDegree : ℝ) ≤ K * testDeg (cfgB P) s b →
      ((π.captured 0 U g).card : ℝ) ≤ cfgN P * Real.exp (-Real.sqrt (2 * s))

/-- `profiles.tex:85–116`: the full window step preserves the entry
invariants at half the width and emits disjoint good pieces. -/
theorem partition_window_advance (P U : Finset (Pt d)) (θ ξ K s ε : ℝ)
    (π : CutPath d) (entry : PartitionWindowEntry P U θ ξ K s π)
    (hd : 0 < d) (hθ : 0 < θ) (hθsmall : θ ≤ 1 / 2) (hξ : 0 < ξ) (hK : 1 ≤ K)
    (hN : 0 < cfgN P) (hdyadic : ∃ a : ℕ, s = Real.log (cfgB P) / 2 ^ a)
    (hG : 0 < G) (grid : Fin G → ℝ) (hgrid : StrictMono grid)
    (hfirst : grid ⟨0, hG⟩ = -1)
    (hlast : 1 + θ / 2 ≤ grid ⟨G - 1, by omega⟩)
    (hupper : grid ⟨G - 1, by omega⟩ ≤ 1 + θ)
    (hmesh : ∀ k : Fin G, ∀ hk : k.val + 1 < G,
      grid ⟨k.val + 1, hk⟩ - grid k ≤ min (θ / 8) (ξ / 4))
    (a : Fin (G * d) → ℝ) (controls : PartitionWidthControls d G θ ξ K s a)
    (herror : partitionEventTail (fun i => Real.exp (-a i / 2)) 0 ≤ ε)
    (hL : 1 ≤ ⌊testDeg (cfgB P) s (1 / 2)⌋₊)
    (hgap : Real.sqrt s + Real.log (d + 1 : ℝ) ≤ θ * s / 4)
    (hmult : Real.log K ≤ ξ / 4 * (s / 2)) :
    ∃ (V : Finset (Pt d)) (pl : Finset (Piece d)),
      Nonempty (PartitionWindowEntry P V θ ξ K (s / 2) π) ∧ V ⊆ U ∧
      (∀ X ∈ pl, PieceGood P θ ξ K X ∧ X.width = s ∧ X.pts ⊆ U) ∧
      (pl : Set (Piece d)).PairwiseDisjoint Piece.pts ∧
      (∀ X ∈ pl, Disjoint X.pts V) ∧
      (U.card : ℝ) - V.card - (∑ X ∈ pl, (X.pts.card : ℝ)) ≤
        ε * U.card + cfgN P * Real.exp (-s ^ ((1 : ℝ) / 3)) := by
  classical
  have hs : 0 ≤ s := (show (0 : ℝ) ≤ 1 by norm_num).trans controls.width
  have hB : 0 ≤ cfgB P := by unfold cfgB; positivity
  let setup : PartitionWindowSetup P U θ ξ K s ε := {
    subset := entry.subset
    theta_pos := hθ
    theta_small := hθsmall
    xi_pos := hξ
    multiplier := hK
    mass_pos := hN
    dyadic := hdyadic
    gridSize := G
    gridSize_pos := hG
    grid := grid
    grid_mono := hgrid
    grid_first := hfirst
    grid_last_lower := by linarith
    grid_last_upper := hupper
    grid_mesh := hmesh
    weights := a
    controls := controls
    error := herror
    equations := entry.equations
    degree := by
      intro f hf
      exact (Nat.le_floor_iff (mul_nonneg hB (Real.exp_nonneg _))).mpr
        ((entry.degree f hf).trans (RankCore.testDeg_mono hB hs hlast))
    isolate := entry.isolate
    initial := π
    boundaryExponent := Real.sqrt (2 * s)
    boundary_ratio := by
      convert controls.boundary using 1
      congr 1
      ring
    boundary := by
      intro b hb g hg
      rw [hfirst] at hb
      exact entry.boundary b hb g hg }
  obtain ⟨V, E, b, pl, hVU, hmass, hdegree, hisolate, hlow, hgood, hdisj, hnext, hdiscard⟩ :=
    partition_certified_window P U θ ξ K s ε hd setup hL
  refine ⟨V, pl, ⟨⟨hVU.trans entry.subset, E, ?_, hisolate, ?_⟩⟩,
    hVU, hgood, hdisj, hnext, hdiscard⟩
  · intro f hf
    have hdeg : (f.totalDegree : ℝ) ≤ ((b *
        (d * (⌊testDeg (cfgB P) s (1 / 2)⌋₊ - 1) + 1) : ℕ) : ℝ) := by
      exact_mod_cast hdegree f hf
    apply hdeg.trans
    exact partition_next_entry_degree P U b ⌊testDeg (cfgB P) s (1 / 2)⌋₊ s (θ / 2)
      entry.subset hN hL hmass (Nat.floor_le (mul_nonneg hB (Real.exp_nonneg _)))
      (by nlinarith)
  · have hboundary := partition_next_low_boundary P V π ξ K s hK hs hmult hlow
    have heq : (2 : ℝ) * (s / 2) = s := by ring
    simpa only [heq] using hboundary

end
end DistinctDistances.TrackD
