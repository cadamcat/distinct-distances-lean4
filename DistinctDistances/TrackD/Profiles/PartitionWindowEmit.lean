import DistinctDistances.TrackD.Profiles.PartitionWindowSplit
import DistinctDistances.TrackD.Profiles.PartitionBatchJoin

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section
variable {d : ℕ}

/-- Join first-type regularized batches and a large final remainder; a small
remainder is charged once. Second-type batches remain for the next window. -/
theorem partition_emit_window (P U : Finset (Pt d)) (Dlow Dhigh : ℕ)
    (m θ ξ K s ε small : ℝ) (hε : 0 ≤ ε) (hsmall : 0 < small)
    (W : PartitionGreedyWindow U Dlow Dhigh m)
    (hfirst : ∀ T ∈ W.first, Nonempty (PartitionBatchPieces P θ ξ K s ε T))
    (hrem : small ≤ (W.remainder.card : ℝ) →
      Nonempty (PartitionBatchPieces P θ ξ K s ε W.remainder)) :
    ∃ pl : Finset (Piece d),
      (∀ X ∈ pl, PieceGood P θ ξ K X ∧ X.width = s ∧ X.pts ⊆ U) ∧
      (pl : Set (Piece d)).PairwiseDisjoint Piece.pts ∧
      (∀ X ∈ pl, Disjoint X.pts W.next) ∧
      (U.card : ℝ) - W.next.card - (∑ X ∈ pl, (X.pts.card : ℝ)) ≤ ε * U.card + small := by
  classical
  have hfirstNext : ∀ T ∈ W.first, Disjoint T W.next := by
    intro T hT
    apply Finset.disjoint_left.mpr
    intro x hxT hxN
    exact Finset.disjoint_left.mp (W.first_middle_disjoint T hT) hxT (W.next_subset hxN)
  by_cases hlarge : small ≤ (W.remainder.card : ℝ)
  · have hRne : W.remainder.Nonempty := by
      apply Finset.card_pos.mp
      exact_mod_cast lt_of_lt_of_le hsmall hlarge
    have hRnot : W.remainder ∉ W.first := by
      intro hR
      obtain ⟨x, hx⟩ := hRne
      exact Finset.disjoint_left.mp (W.first_middle_disjoint _ hR) hx (W.remainder_subset hx)
    have hfirstR : ∀ T ∈ W.first, Disjoint T W.remainder := by
      intro T hT
      apply Finset.disjoint_left.mpr
      intro x hxT hxR
      exact Finset.disjoint_left.mp (W.first_middle_disjoint T hT) hxT (W.remainder_subset hxR)
    let parents := insert W.remainder W.first
    have hpdisj : (parents : Set (Finset (Pt d))).PairwiseDisjoint id := by
      dsimp [parents]
      rw [Finset.coe_insert, Set.pairwiseDisjoint_insert]
      exact ⟨W.first_disjoint, fun T hT hne => (hfirstR T hT).symm⟩
    have hpsub : ∀ T ∈ parents, T ⊆ U := by
      intro T hT
      rcases Finset.mem_insert.mp hT with rfl | hT
      · exact W.remainder_subset.trans W.middle_subset
      · exact (W.first_good T hT).1
    have hpnext : ∀ T ∈ parents, Disjoint T W.next := by
      intro T hT
      rcases Finset.mem_insert.mp hT with rfl | hT
      · exact W.next_remainder_disjoint.symm
      · exact hfirstNext T hT
    have hmissing : (U.card : ℝ) - W.next.card - (∑ T ∈ parents, (T.card : ℝ)) ≤ small := by
      dsimp [parents]
      rw [Finset.sum_insert hRnot]
      have hmass := W.mass
      linarith
    apply partition_join_piece_batches P U W.next θ ξ K s ε small hε parents
      hpsub hpdisj hpnext hmissing
    intro T hT
    rcases Finset.mem_insert.mp hT with rfl | hT
    · exact hrem hlarge
    · exact hfirst T hT
  · have hmissing : (U.card : ℝ) - W.next.card - (∑ T ∈ W.first, (T.card : ℝ)) ≤ small := by
      have hRsmall := (lt_of_not_ge hlarge).le
      have hmass := W.mass
      linarith
    exact partition_join_piece_batches P U W.next θ ξ K s ε small hε W.first
      (fun T hT => (W.first_good T hT).1) W.first_disjoint hfirstNext hmissing hfirst

end
end DistinctDistances.TrackD
