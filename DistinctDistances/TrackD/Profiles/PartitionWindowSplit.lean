import DistinctDistances.TrackD.Profiles.PartitionTreeBase
import DistinctDistances.TrackD.Profiles.PartitionWindowPackages

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section
variable {d : ℕ}

/-- The two saturated greedy operations of one window, with their original
global extraction threshold. -/
structure PartitionGreedyWindow (U : Finset (Pt d)) (Dlow Dhigh : ℕ) (m : ℝ) where
  first : Finset (Finset (Pt d))
  second : Finset (Finset (Pt d))
  middle : Finset (Pt d)
  next : Finset (Pt d)
  remainder : Finset (Pt d)
  middle_eq : middle = U \ first.biUnion id
  next_eq : next = second.biUnion id
  remainder_eq : remainder = middle \ second.biUnion id
  first_good : ∀ T ∈ first, T ⊆ U ∧ m ≤ (T.card : ℝ) ∧
    ∃ g : Poly d, g ≠ 0 ∧ g.totalDegree ≤ Dlow ∧
      ∀ x ∈ T, MvPolynomial.eval (toC x) g = 0
  second_good : ∀ T ∈ second, T ⊆ middle ∧ m ≤ (T.card : ℝ) ∧ CoreIsolated T Dhigh
  first_disjoint : (first : Set (Finset (Pt d))).PairwiseDisjoint id
  second_disjoint : (second : Set (Finset (Pt d))).PairwiseDisjoint id
  next_subset : next ⊆ middle
  remainder_subset : remainder ⊆ middle
  middle_subset : middle ⊆ U
  first_middle_disjoint : ∀ T ∈ first, Disjoint T middle
  next_remainder_disjoint : Disjoint next remainder
  first_count : m * first.card ≤ U.card
  second_count : m * second.card ≤ U.card
  low_saturated : ∀ g : Poly d, g ≠ 0 → g.totalDegree ≤ Dlow →
    ((next.filter (fun x => MvPolynomial.eval (toC x) g = 0)).card : ℝ) < m
  high_saturated : ∀ T : Finset (Pt d), T ⊆ remainder → CoreIsolated T Dhigh → (T.card : ℝ) < m
  mass : (∑ T ∈ first, (T.card : ℝ)) + next.card + remainder.card = U.card

theorem partition_two_greedy_operations (U : Finset (Pt d)) (Dlow Dhigh : ℕ)
    (m : ℝ) (hm : 0 < m) : Nonempty (PartitionGreedyWindow U Dlow Dhigh m) := by
  classical
  letI : DecidableEq (Pt d) := fun x y => Classical.propDecidable (x = y)
  let firstOK : Finset (Pt d) → Prop := fun T =>
    m ≤ (T.card : ℝ) ∧ ∃ g : Poly d, g ≠ 0 ∧ g.totalDegree ≤ Dlow ∧
      ∀ x ∈ T, MvPolynomial.eval (toC x) g = 0
  obtain ⟨first, hfirst, hfirstDisj, hfirstSat, hfirstCount⟩ :=
    partition_greedy_batches U firstOK m hm (fun T hT => hT.1)
  let middle := U \ first.biUnion id
  let secondOK : Finset (Pt d) → Prop := fun T => m ≤ (T.card : ℝ) ∧ CoreIsolated T Dhigh
  obtain ⟨second, hsecond, hsecondDisj, hsecondSat, hsecondCount⟩ :=
    partition_greedy_batches middle secondOK m hm (fun T hT => hT.1)
  let next := second.biUnion id
  let remainder := middle \ second.biUnion id
  have hmiddleSub : middle ⊆ U := Finset.sdiff_subset
  have hnextSub : next ⊆ middle := Finset.biUnion_subset.mpr (fun T hT => (hsecond T hT).1)
  have hremSub : remainder ⊆ middle := Finset.sdiff_subset
  have hcover1 := partition_greedy_residual U first (fun T hT => (hfirst T hT).1) hfirstDisj
  have hcover2 := partition_greedy_residual middle second (fun T hT => (hsecond T hT).1) hsecondDisj
  refine ⟨⟨first, second, middle, next, remainder, ?_, ?_, ?_,
    (fun T hT => ⟨(hfirst T hT).1, (hfirst T hT).2⟩),
    (fun T hT => ⟨(hsecond T hT).1, (hsecond T hT).2⟩), hfirstDisj, hsecondDisj,
    hnextSub, hremSub, hmiddleSub, ?_, ?_, hfirstCount, ?_, ?_, ?_, ?_⟩⟩
  · ext x; simp [middle]
  · ext x; simp [next]
  · ext x; simp [remainder]
  · intro T hT
    exact hcover1.2.1 T hT
  · apply Finset.disjoint_left.mpr
    intro x hxN hxR
    exact (Finset.mem_sdiff.mp hxR).2 hxN
  · exact hsecondCount.trans (by exact_mod_cast Finset.card_le_card hmiddleSub)
  · intro g hg hdegree
    have hmidSat : ((middle.filter (fun x => MvPolynomial.eval (toC x) g = 0)).card : ℝ) < m := by
      by_contra hn
      let T := middle.filter (fun x => MvPolynomial.eval (toC x) g = 0)
      apply hfirstSat T
      · intro x hx
        exact (Finset.mem_filter.mp hx).1
      · refine ⟨le_of_not_gt hn, g, hg, hdegree, ?_⟩
        intro x hx
        exact (Finset.mem_filter.mp hx).2
    have hzeros : next.filter (fun x => MvPolynomial.eval (toC x) g = 0) ⊆
        middle.filter (fun x => MvPolynomial.eval (toC x) g = 0) := by
      intro x hx
      obtain ⟨hxN, hxg⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨hnextSub hxN, hxg⟩
    exact (show ((next.filter (fun x => MvPolynomial.eval (toC x) g = 0)).card : ℝ) ≤
      (middle.filter (fun x => MvPolynomial.eval (toC x) g = 0)).card by
        exact_mod_cast Finset.card_le_card hzeros).trans_lt hmidSat
  · intro T hT hcore
    by_contra hn
    exact hsecondSat T hT ⟨le_of_not_gt hn, hcore⟩
  · have hsum1 : (∑ T ∈ first, (T.card : ℝ)) + (middle.card : ℝ) = U.card := hcover1.2.2.1
    have hsum2 : (∑ T ∈ second, (T.card : ℝ)) + (remainder.card : ℝ) = middle.card := hcover2.2.2.1
    have hnextCard : (next.card : ℝ) = ∑ T ∈ second, (T.card : ℝ) := by
      norm_cast
      exact Finset.card_biUnion hsecondDisj
    rw [hnextCard]
    linarith

end
end DistinctDistances.TrackD
