import DistinctDistances.TrackD.Profiles.PartitionGreedy

/-! Joining finite regularization subtrees without counting a leaf twice or
introducing a loss for the number of branches, `profiles.tex:157–176`. -/

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section

/-- Nonempty descendants of disjoint parents remain disjoint. Their retained
mass is exactly the sum of the retained masses of the subtrees. -/
theorem partition_forest_join {α β γ : Type*} (parents : Finset γ)
    (parentPts : γ → Finset α) (children : γ → Finset β) (pts : β → Finset α)
    (hparents : (parents : Set γ).PairwiseDisjoint parentPts)
    (hsubset : ∀ i ∈ parents, ∀ X ∈ children i, pts X ⊆ parentPts i)
    (hne : ∀ i ∈ parents, ∀ X ∈ children i, (pts X).Nonempty)
    (hchildren : ∀ i ∈ parents, (children i : Set β).PairwiseDisjoint pts) :
    (parents.biUnion children : Set β).PairwiseDisjoint pts ∧
      (∑ X ∈ parents.biUnion children, ((pts X).card : ℝ)) =
        ∑ i ∈ parents, ∑ X ∈ children i, ((pts X).card : ℝ) := by
  classical
  have hsets : (parents : Set γ).PairwiseDisjoint children := by
    intro i hi k hk hik
    apply Finset.disjoint_left.mpr
    intro X hXi hXk
    obtain ⟨x, hx⟩ := hne i hi X hXi
    exact Finset.disjoint_left.mp (hparents hi hk hik)
      (hsubset i hi X hXi hx) (hsubset k hk X hXk hx)
  refine ⟨?_, Finset.sum_biUnion hsets⟩
  intro X hX Y hY hXY
  obtain ⟨i, hi, hXi⟩ := Finset.mem_biUnion.mp hX
  obtain ⟨k, hk, hYk⟩ := Finset.mem_biUnion.mp hY
  by_cases hik : i = k
  · subst k
    exact hchildren i hi hXi hYk hXY
  · apply Finset.disjoint_left.mpr
    intro x hxX hxY
    exact Finset.disjoint_left.mp (hparents hi hk hik)
      (hsubset i hi X hXi hxX) (hsubset k hk Y hYk hxY)

/-- A common fractional mass bound for the subtrees remains the same after
joining them; it is measured on each subtree's original parent. -/
theorem partition_forest_retained_mass {α β γ : Type*} (parents : Finset γ)
    (parentPts : γ → Finset α) (children : γ → Finset β) (pts : β → Finset α)
    (hparents : (parents : Set γ).PairwiseDisjoint parentPts)
    (hsubset : ∀ i ∈ parents, ∀ X ∈ children i, pts X ⊆ parentPts i)
    (hne : ∀ i ∈ parents, ∀ X ∈ children i, (pts X).Nonempty)
    (hchildren : ∀ i ∈ parents, (children i : Set β).PairwiseDisjoint pts)
    (ε : ℝ) (hmass : ∀ i ∈ parents,
      (1 - ε) * (parentPts i).card ≤ ∑ X ∈ children i, ((pts X).card : ℝ)) :
    (1 - ε) * (∑ i ∈ parents, ((parentPts i).card : ℝ)) ≤
      ∑ X ∈ parents.biUnion children, ((pts X).card : ℝ) := by
  classical
  rw [(partition_forest_join parents parentPts children pts
    hparents hsubset hne hchildren).2, Finset.mul_sum]
  exact Finset.sum_le_sum (fun i hi => hmass i hi)

end
end DistinctDistances.TrackD
