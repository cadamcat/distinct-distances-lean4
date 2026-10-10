import DistinctDistances.TrackD.Profiles.PartitionPieceGood
import DistinctDistances.TrackD.Profiles.PartitionForest

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section
variable {d : ℕ}

structure PartitionBatchPieces (P : Finset (Pt d)) (θ ξ K s ε : ℝ) (T : Finset (Pt d)) where
  pieces : Finset (Piece d)
  good : ∀ X ∈ pieces, PieceGood P θ ξ K X ∧ X.width = s ∧ X.pts ⊆ T
  nonempty : ∀ X ∈ pieces, X.pts.Nonempty
  disjoint : (pieces : Set (Piece d)).PairwiseDisjoint Piece.pts
  discard : (T.card : ℝ) - ∑ X ∈ pieces, (X.pts.card : ℝ) ≤ ε * T.card

/-- Regularize disjoint parent batches and add their original mass losses.
The remaining unresolved set is disjoint from every emitted piece. -/
theorem partition_join_piece_batches (P U V : Finset (Pt d)) (θ ξ K s ε small : ℝ)
    (hε : 0 ≤ ε) (parents : Finset (Finset (Pt d)))
    (hparentSubset : ∀ T ∈ parents, T ⊆ U)
    (hparents : (parents : Set (Finset (Pt d))).PairwiseDisjoint id)
    (hVdisj : ∀ T ∈ parents, Disjoint T V)
    (hmissing : (U.card : ℝ) - V.card - (∑ T ∈ parents, (T.card : ℝ)) ≤ small)
    (hregularize : ∀ T ∈ parents, Nonempty (PartitionBatchPieces P θ ξ K s ε T)) :
    ∃ pl : Finset (Piece d),
      (∀ X ∈ pl, PieceGood P θ ξ K X ∧ X.width = s ∧ X.pts ⊆ U) ∧
      (pl : Set (Piece d)).PairwiseDisjoint Piece.pts ∧
      (∀ X ∈ pl, Disjoint X.pts V) ∧
      (U.card : ℝ) - V.card - (∑ X ∈ pl, (X.pts.card : ℝ)) ≤ ε * U.card + small := by
  classical
  let batches : ∀ T : parents, PartitionBatchPieces P θ ξ K s ε T.val :=
    fun T => Classical.choice (hregularize T.val T.property)
  let children : Finset (Pt d) → Finset (Piece d) := fun T =>
    if hT : T ∈ parents then (batches ⟨T, hT⟩).pieces else ∅
  have hc (T : Finset (Pt d)) (hT : T ∈ parents) :
      children T = (batches ⟨T, hT⟩).pieces := by simp [children, hT]
  have hsub : ∀ T ∈ parents, ∀ X ∈ children T, X.pts ⊆ T := by
    intro T hT X hX
    rw [hc T hT] at hX
    exact ((batches ⟨T, hT⟩).good X hX).2.2
  have hne : ∀ T ∈ parents, ∀ X ∈ children T, X.pts.Nonempty := by
    intro T hT X hX
    rw [hc T hT] at hX
    exact (batches ⟨T, hT⟩).nonempty X hX
  have hdisj : ∀ T ∈ parents, (children T : Set (Piece d)).PairwiseDisjoint Piece.pts := by
    intro T hT
    rw [hc T hT]
    exact (batches ⟨T, hT⟩).disjoint
  have hj := partition_forest_join parents id children Piece.pts hparents hsub hne hdisj
  refine ⟨parents.biUnion children, ?_, hj.1, ?_, ?_⟩
  · intro X hX
    obtain ⟨T, hT, hXT⟩ := Finset.mem_biUnion.mp hX
    have hgood := (batches ⟨T, hT⟩).good X (by rwa [← hc T hT])
    exact ⟨hgood.1, hgood.2.1, hgood.2.2.trans (hparentSubset T hT)⟩
  · intro X hX
    obtain ⟨T, hT, hXT⟩ := Finset.mem_biUnion.mp hX
    apply Finset.disjoint_left.mpr
    intro x hxX hxV
    exact Finset.disjoint_left.mp (hVdisj T hT) (hsub T hT X hXT hxX) hxV
  · rw [hj.2]
    have htotal : (∑ T ∈ parents, (T.card : ℝ)) ≤ U.card := by
      have heq : (∑ T ∈ parents, (T.card : ℝ)) = ((parents.biUnion id).card : ℝ) := by
        norm_cast
        exact (Finset.card_biUnion hparents).symm
      rw [heq]
      exact_mod_cast Finset.card_le_card (Finset.biUnion_subset.mpr hparentSubset)
    have hcost : ∀ T ∈ parents,
        (T.card : ℝ) - ∑ X ∈ children T, (X.pts.card : ℝ) ≤ ε * T.card := by
      intro T hT
      rw [hc T hT]
      exact (batches ⟨T, hT⟩).discard
    have hsum := Finset.sum_le_sum hcost
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
    have htotalCost := mul_le_mul_of_nonneg_left htotal hε
    linarith

end
end DistinctDistances.TrackD
