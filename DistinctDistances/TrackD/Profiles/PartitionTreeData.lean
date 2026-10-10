import DistinctDistances.TrackD.Profiles.PartitionTreeGeometry
import DistinctDistances.TrackD.Profiles.PartitionEventBudgets
import DistinctDistances.TrackD.Profiles.PartitionForest

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section
variable {d G : ℕ}

def PartitionGridTests (grid : Fin G → ℝ) (L : Fin G → ℕ) (r : Fin G)
    (u : ℝ) (X : Piece d) : Prop :=
  ∀ k : Fin G, r ≤ k → ∀ ℓ < d,
    (∀ i : Fin d, (i.val < ℓ → X.path.time i ≤ grid k) ∧
      (ℓ ≤ i.val → grid k < X.path.time i)) →
    ∀ g : Poly d, g.totalDegree ≤ L k →
      ((X.path.captured ℓ X.pts g).card : ℝ) ≤ Real.exp (-7 * u / 18) * X.pts.card

/-- The retained forest at one original regularization node. -/
structure PartitionGridForest (grid : Fin G → ℝ) (L : Fin G → ℕ)
    (s u : ℝ) (a : Fin (G * d) → ℝ) (r : Fin G)
    (π : CutPath d) (j : ℕ) (S : Finset (Pt d)) where
  pieces : Finset (Piece d)
  leaf : ∀ X ∈ pieces, PartitionGridLeaf grid L r π j S s X ∧
    (S.card : ℝ) * Real.exp (-partitionEventTail a (r.val * d + j)) ≤ X.pts.card ∧
    PartitionGridTests grid L r u X
  disjoint : (pieces : Set (Piece d)).PairwiseDisjoint Piece.pts
  discard : (S.card : ℝ) - ∑ X ∈ pieces, (X.pts.card : ℝ) ≤
    S.card * partitionEventTail (fun i => Real.exp (-a i / 2)) (r.val * d + j)

theorem partition_empty_forest (grid : Fin G → ℝ) (L : Fin G → ℕ)
    (s u : ℝ) (a : Fin (G * d) → ℝ) (r : Fin G) (π : CutPath d) (j : ℕ) :
    Nonempty (PartitionGridForest grid L s u a r π j ∅) := by
  classical
  exact ⟨⟨∅, by simp, by simp, by simp⟩⟩

/-- A completed path with no later cut gives the terminal singleton forest. -/
theorem partition_terminal_forest (grid : Fin G → ℝ) (hgrid : Monotone grid)
    (L : Fin G → ℕ) (s u : ℝ) (a : Fin (G * d) → ℝ) (ha : ∀ i, 0 ≤ a i)
    (r : Fin G) (π : CutPath d) (j : ℕ) (S : Finset (Pt d))
    (X : Piece d) (hX : PartitionGridLeaf grid L r π j S s X)
    (hpts : X.pts = S) (htimes : ∀ i, X.path.time i ≤ grid r) :
    Nonempty (PartitionGridForest grid L s u a r π j S) := by
  classical
  refine ⟨⟨{X}, ?_, by simp, ?_⟩⟩
  · intro Y hY
    have hYX : Y = X := Finset.mem_singleton.mp hY
    subst Y
    refine ⟨hX, ?_, ?_⟩
    · rw [hpts]
      have hexp : Real.exp (-partitionEventTail a (r.val * d + j)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr (partition_event_tail_nonneg a ha _))
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp (Nat.cast_nonneg S.card)
    · intro k hrk ℓ hℓ hp g hg
      have hnext := (hp ⟨ℓ, hℓ⟩).2 le_rfl
      have hupper := (htimes ⟨ℓ, hℓ⟩).trans (hgrid hrk)
      linarith
  · simp only [Finset.sum_singleton, hpts, sub_self]
    exact mul_nonneg (Nat.cast_nonneg S.card)
      (partition_event_tail_nonneg _ (fun i => Real.exp_nonneg _) _)

/-- Join subforests using their own original parent masses. The sum of their
loss fractions and the omitted-parent fraction is the node's tail budget. -/
theorem partition_join_grid_forests (grid : Fin G → ℝ) (L : Fin G → ℕ)
    (s u : ℝ) (a : Fin (G * d) → ℝ) (r : Fin G)
    (π : CutPath d) (j : ℕ) (S : Finset (Pt d))
    (parents : Finset (Finset (Pt d))) (children : Finset (Pt d) → Finset (Piece d))
    (hparents : (parents : Set (Finset (Pt d))).PairwiseDisjoint id)
    (hparentSubset : ∀ T ∈ parents, T ⊆ S)
    (hchildSubset : ∀ T ∈ parents, ∀ X ∈ children T, X.pts ⊆ T)
    (hchildDisjoint : ∀ T ∈ parents, (children T : Set (Piece d)).PairwiseDisjoint Piece.pts)
    (hgood : ∀ T ∈ parents, ∀ X ∈ children T,
      PartitionGridLeaf grid L r π j S s X ∧
        (S.card : ℝ) * Real.exp (-partitionEventTail a (r.val * d + j)) ≤ X.pts.card ∧
        PartitionGridTests grid L r u X)
    (loss drop : ℝ) (hloss : 0 ≤ loss)
    (hchildren : ∀ T ∈ parents,
      (T.card : ℝ) - ∑ X ∈ children T, (X.pts.card : ℝ) ≤ T.card * loss)
    (hmissing : (S.card : ℝ) - (∑ T ∈ parents, (T.card : ℝ)) ≤ S.card * drop)
    (hbudget : loss + drop ≤ partitionEventTail (fun i => Real.exp (-a i / 2)) (r.val * d + j)) :
    Nonempty (PartitionGridForest grid L s u a r π j S) := by
  classical
  have hjoin := partition_forest_join parents id children Piece.pts hparents hchildSubset
    (fun T hT X hX => (hgood T hT X hX).1.nonempty) hchildDisjoint
  refine ⟨⟨parents.biUnion children, ?_, hjoin.1, ?_⟩⟩
  · intro X hX
    obtain ⟨T, hT, hXT⟩ := Finset.mem_biUnion.mp hX
    exact hgood T hT X hXT
  · rw [hjoin.2]
    have htotal : (∑ T ∈ parents, (T.card : ℝ)) ≤ S.card := by
      have hcards : (∑ T ∈ parents, (T.card : ℝ)) = ((parents.biUnion id).card : ℝ) := by
        norm_cast
        exact (Finset.card_biUnion hparents).symm
      rw [hcards]
      exact_mod_cast Finset.card_le_card (Finset.biUnion_subset.mpr hparentSubset)
    have hsum := Finset.sum_le_sum (fun T hT => hchildren T hT)
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul] at hsum
    have hcost := mul_le_mul_of_nonneg_right htotal hloss
    have hbudget' := mul_le_mul_of_nonneg_left hbudget (Nat.cast_nonneg S.card)
    nlinarith

end
end DistinctDistances.TrackD
