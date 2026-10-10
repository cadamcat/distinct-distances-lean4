import DistinctDistances.TrackD.Profiles.PartitionBatchJoin
import DistinctDistances.TrackD.Profiles.PartitionBoundary

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section
variable {d G : ℕ}

/-- The same tree serves every first batch and every large remainder. All
analytic tolerances are fixed before choosing a batch and its later tests. -/
theorem partition_batch_from_tree (P U T : Finset (Pt d)) (hUP : U ⊆ P) (hTU : T ⊆ U)
    (θ ξ K s u ε v : ℝ) (hθ : 0 < θ) (hξ : 0 < ξ) (hK : 1 ≤ K) (hs : 0 ≤ s)
    (hu : 0 < u) (hdyadic : ∃ a : ℕ, s = Real.log (cfgB P) / 2 ^ a)
    (hG : 0 < G) (grid : Fin G → ℝ) (hgrid : StrictMono grid)
    (hfirst : grid ⟨0, hG⟩ = -1) (hlast : grid ⟨G - 1, by omega⟩ ≤ 1 + θ)
    (hmesh : ∀ k : Fin G, ∀ hk : k.val + 1 < G,
      grid ⟨k.val + 1, hk⟩ - grid k ≤ ξ / 4)
    (hlarge : Real.log K ≤ ξ / 4 * s)
    (L : Fin G → ℕ) (hL : ∀ k, L k = ⌊testDeg (cfgB P) s (grid k)⌋₊)
    (a : Fin (G * d) → ℝ) (ha : ∀ i, u ≤ a i)
    (htail : ∀ i, (∑ k ∈ Finset.univ.filter (fun k : Fin (G * d) => i < k), a k) ≤ a i / 9)
    (E : Set (Poly d)) (hdegree : ∀ f ∈ E, f.totalDegree ≤ L ⟨G - 1, by omega⟩)
    (hisolate : MvPolynomial.zeroLocus ℂ (Ideal.span E) = toC '' (U : Set (Pt d)))
    (hbatch : cfgN P * Real.exp (-Real.sqrt s) ≤ T.card)
    (hsizeBudget : Real.sqrt s + partitionEventTail a 0 ≤ θ * s)
    (hsmall : Real.exp (-7 * u / 18) ≤ θ)
    (herror : partitionEventTail (fun i => Real.exp (-a i / 2)) 0 ≤ ε)
    (hratio : Real.exp (Real.sqrt s + partitionEventTail a 0 - v) ≤ θ)
    (π : CutPath d)
    (hboundary : ∀ b : ℝ, b + ξ / 4 ≤ grid ⟨0, hG⟩ → ∀ g : Poly d,
      (g.totalDegree : ℝ) ≤ K * testDeg (cfgB P) s b →
        ((π.captured 0 U g).card : ℝ) ≤ cfgN P * Real.exp (-v))
    (himbalance : ∀ X : Piece d,
      PartitionGridLeaf grid L ⟨0, hG⟩ π 0 T s X →
      (T.card : ℝ) * Real.exp (-partitionEventTail a 0) ≤ X.pts.card →
      PartitionGridTests grid L ⟨0, hG⟩ u X →
      ∃ i, 1 / 2 - θ ≤ |X.path.time i|) :
    Nonempty (PartitionBatchPieces P θ ξ K s ε T) := by
  classical
  obtain ⟨f⟩ := partition_grid_forest_exists grid hgrid L s u hu a ha htail ⟨0, hG⟩ T U hTU
    E hdegree hisolate π 0 (Nat.zero_le _)
    (fun x hx i hi => by omega)
    (fun x hx i hi => by omega)
    (fun i k hi => by omega)
    (fun i hi => by omega)
  refine ⟨⟨f.pieces, ?_, ?_, f.disjoint, ?_⟩⟩
  · intro X hX
    obtain ⟨hgeo, hmass, htests⟩ := f.leaf X hX
    have hmass' : (T.card : ℝ) * Real.exp (-partitionEventTail a 0) ≤ X.pts.card := by
      simpa using hmass
    have hN : 0 ≤ cfgN P := by unfold cfgN; positivity
    have hsize : cfgN P * Real.exp (-θ * s) ≤ X.pts.card :=
      partition_leaf_size_of_losses (cfgN P) (T.card : ℝ) (X.pts.card : ℝ)
        s (partitionEventTail a 0) θ hN hbatch hmass' hsizeBudget
    have hminimum : cfgN P * Real.exp (-(Real.sqrt s + partitionEventTail a 0)) ≤ X.pts.card := by
      have h := mul_le_mul_of_nonneg_right hbatch (Real.exp_nonneg (-partitionEventTail a 0))
      have heq : cfgN P * Real.exp (-Real.sqrt s) * Real.exp (-partitionEventTail a 0) =
          cfgN P * Real.exp (-(Real.sqrt s + partitionEventTail a 0)) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
      rw [heq] at h
      exact h.trans hmass'
    have hlow : ∀ b : ℝ, b + ξ / 4 ≤ grid ⟨0, hG⟩ → ∀ g : Poly d,
        (g.totalDegree : ℝ) ≤ K * testDeg (cfgB P) s b →
          ((X.path.captured 0 X.pts g).card : ℝ) ≤ θ * X.pts.card := by
      intro b hb g hg
      have hcap : ((X.path.captured 0 X.pts g).card : ℝ) ≤ cfgN P * Real.exp (-v) := by
        rw [partition_prefix_captured_eq X.path π 0 (fun i hi => by omega)]
        have hsub := partition_capture_subset π 0 U X.pts (hgeo.subset.trans hTU) g
        exact (show ((π.captured 0 X.pts g).card : ℝ) ≤ (π.captured 0 U g).card by
          exact_mod_cast Finset.card_le_card hsub).trans (hboundary b hb g hg)
      simpa only [mul_comm θ] using partition_boundary_mass_ratio (cfgN P) (X.pts.card : ℝ)
        ((X.path.captured 0 X.pts g).card : ℝ) v (Real.sqrt s + partitionEventTail a 0) θ
        (by positivity) hminimum hcap hratio
    have hgood := partition_piece_good_of_grid P T (hTU.trans hUP) θ ξ K s u hθ hξ hK hs
      hdyadic hG grid hgrid hfirst hlast hmesh hlarge L hL π X hgeo hsize
      (himbalance X hgeo hmass' htests) htests hsmall hlow
    exact ⟨hgood, hgeo.width, hgeo.subset⟩
  · intro X hX
    exact (f.leaf X hX).1.nonempty
  · have hdiscard : (T.card : ℝ) - ∑ X ∈ f.pieces, (X.pts.card : ℝ) ≤
        T.card * partitionEventTail (fun i => Real.exp (-a i / 2)) 0 := by
      simpa using f.discard
    apply hdiscard.trans
    calc
      _ ≤ (T.card : ℝ) * ε := mul_le_mul_of_nonneg_left herror (Nat.cast_nonneg T.card)
      _ = ε * T.card := mul_comm _ _

end
end DistinctDistances.TrackD
