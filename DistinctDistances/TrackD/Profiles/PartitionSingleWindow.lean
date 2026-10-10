import DistinctDistances.TrackD.Profiles.PartitionWindowEmit

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section
variable {d : ℕ}

/-- One complete nonfinal window: the first batches and final remainder
become regular pieces; the exactly isolated second union advances in width. -/
theorem partition_single_window (P U : Finset (Pt d)) (Dlow Dhigh : ℕ)
    (hDhigh : 1 ≤ Dhigh) (m θ ξ K s ε small : ℝ) (hm : 0 < m)
    (hε : 0 ≤ ε) (hsmall : 0 < small)
    (hfirst : ∀ T : Finset (Pt d), T ⊆ U → m ≤ (T.card : ℝ) →
      ∀ g : Poly d, g ≠ 0 → g.totalDegree ≤ Dlow →
      (∀ x ∈ T, MvPolynomial.eval (toC x) g = 0) →
      Nonempty (PartitionBatchPieces P θ ξ K s ε T))
    (hrem : ∀ R : Finset (Pt d), R ⊆ U → small ≤ (R.card : ℝ) →
      (∀ T : Finset (Pt d), T ⊆ R → CoreIsolated T Dhigh → (T.card : ℝ) < m) →
      Nonempty (PartitionBatchPieces P θ ξ K s ε R)) :
    ∃ (V : Finset (Pt d)) (E : Set (Poly d)) (b : ℕ) (pl : Finset (Piece d)),
      V ⊆ U ∧ m * b ≤ U.card ∧
      (∀ f ∈ E, f.totalDegree ≤ b * (d * (Dhigh - 1) + 1)) ∧
      MvPolynomial.zeroLocus ℂ (Ideal.span E) = toC '' (V : Set (Pt d)) ∧
      (∀ g : Poly d, g ≠ 0 → g.totalDegree ≤ Dlow →
        ((V.filter (fun x => MvPolynomial.eval (toC x) g = 0)).card : ℝ) < m) ∧
      (∀ X ∈ pl, PieceGood P θ ξ K X ∧ X.width = s ∧ X.pts ⊆ U) ∧
      (pl : Set (Piece d)).PairwiseDisjoint Piece.pts ∧
      (∀ X ∈ pl, Disjoint X.pts V) ∧
      (U.card : ℝ) - V.card - (∑ X ∈ pl, (X.pts.card : ℝ)) ≤ ε * U.card + small := by
  classical
  obtain ⟨W⟩ := partition_two_greedy_operations U Dlow Dhigh m hm
  have hfirstW : ∀ T ∈ W.first, Nonempty (PartitionBatchPieces P θ ξ K s ε T) := by
    intro T hT
    obtain ⟨hTU, hmass, g, hg, hdegree, hzero⟩ := W.first_good T hT
    exact hfirst T hTU hmass g hg hdegree hzero
  have hremW : small ≤ (W.remainder.card : ℝ) →
      Nonempty (PartitionBatchPieces P θ ξ K s ε W.remainder) := by
    intro hsize
    exact hrem W.remainder (W.remainder_subset.trans W.middle_subset) hsize W.high_saturated
  obtain ⟨pl, hgood, hdisj, hnextDisj, hmass⟩ :=
    partition_emit_window P U Dlow Dhigh m θ ξ K s ε small hε hsmall W hfirstW hremW
  obtain ⟨E, hE, hzero⟩ := partition_interpolated_batch_union W.second Dhigh hDhigh
    (fun T hT => (W.second_good T hT).2.2)
  have hzeroNext : MvPolynomial.zeroLocus ℂ (Ideal.span E) = toC '' (W.next : Set (Pt d)) := by
    rw [W.next_eq]
    exact hzero
  exact ⟨W.next, E, W.second.card, pl, W.next_subset.trans W.middle_subset, W.second_count,
    hE, hzeroNext, W.low_saturated, hgood, hdisj, hnextDisj, hmass⟩

end
end DistinctDistances.TrackD
