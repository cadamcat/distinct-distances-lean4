import DistinctDistances.TrackD.Profiles.PartitionForest

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section

/-- Emitted pieces in different halving windows stay disjoint: every later
window lies in the unresolved set from which earlier pieces were removed. -/
theorem partition_chain_join {α β : Type*} (n : ℕ) (remaining : ℕ → Finset α)
    (pieces : ℕ → Finset β) (pts : β → Finset α)
    (hnested : ∀ i < n, remaining (i + 1) ⊆ remaining i)
    (hsubset : ∀ i < n, ∀ X ∈ pieces i, pts X ⊆ remaining i)
    (hdisjoint : ∀ i < n, (pieces i : Set β).PairwiseDisjoint pts)
    (hnext : ∀ i < n, ∀ X ∈ pieces i, Disjoint (pts X) (remaining (i + 1)))
    (hne : ∀ i < n, ∀ X ∈ pieces i, (pts X).Nonempty) :
    (Finset.range n |>.biUnion pieces : Set β).PairwiseDisjoint pts ∧
      (∑ X ∈ (Finset.range n).biUnion pieces, ((pts X).card : ℝ)) =
        ∑ i ∈ Finset.range n, ∑ X ∈ pieces i, ((pts X).card : ℝ) ∧
      ∀ X ∈ (Finset.range n).biUnion pieces, Disjoint (pts X) (remaining n) := by
  classical
  have hchain : ∀ k ≤ n, ∀ i ≤ k, remaining k ⊆ remaining i := by
    intro k
    induction k with
    | zero =>
        intro hk i hi
        have : i = 0 := by omega
        subst i
        exact Finset.Subset.refl _
    | succ k ih =>
        intro hk i hi
        by_cases hieq : i = k + 1
        · subst i; exact Finset.Subset.refl _
        · exact (hnested k (by omega)).trans (ih (by omega) i (by omega))
  let emitted : ℕ → Finset α := fun i => (pieces i).biUnion pts
  have hbefore : ∀ i < n, ∀ j < n, i < j → Disjoint (emitted i) (emitted j) := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    obtain ⟨X, hX, hxX⟩ := Finset.mem_biUnion.mp hxi
    obtain ⟨Y, hY, hxY⟩ := Finset.mem_biUnion.mp hxj
    have hxLater := hchain j (by omega) (i + 1) (by omega) (hsubset j hj Y hY hxY)
    exact Finset.disjoint_left.mp (hnext i hi X hX) hxX hxLater
  have hparents : (Finset.range n : Set ℕ).PairwiseDisjoint emitted := by
    intro i hi j hj hneij
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    rcases lt_or_gt_of_ne hneij with hij | hji
    · exact hbefore i hi' j hj' hij
    · exact (hbefore j hj' i hi' hji).symm
  have hjoin := partition_forest_join (Finset.range n) emitted pieces pts hparents
    (fun i hi X hX x hx => Finset.mem_biUnion.mpr ⟨X, hX, hx⟩)
    (fun i hi => hne i (Finset.mem_range.mp hi))
    (fun i hi => hdisjoint i (Finset.mem_range.mp hi))
  refine ⟨hjoin.1, hjoin.2, ?_⟩
  intro X hX
  obtain ⟨i, hi, hXi⟩ := Finset.mem_biUnion.mp hX
  have hi' := Finset.mem_range.mp hi
  apply Finset.disjoint_left.mpr
  intro x hxX hxFinal
  have hxNext := hchain n le_rfl (i + 1) (by omega) hxFinal
  exact Finset.disjoint_left.mp (hnext i hi' X hXi) hxX hxNext

end
end DistinctDistances.TrackD
