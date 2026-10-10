import DistinctDistances.TrackC.PartitionMatches
import DistinctDistances.TrackC.AmbientRichLines
import DistinctDistances.TrackC.LineImages

open scoped BigOperators
open Classical

noncomputable section

namespace DistinctDistances.TrackC

def pooledAssignedWeight (I : Finset (Region × Region))
    (a : Motion 3 → Region × Region → Finset (E 3))
    (pick : Motion 3 → Region × Region → Option (Line 3)) (g : Motion 3) (l : Line 3) : ℝ :=
  ∑ RR ∈ I,if pick g RR = some l then ((a g RR).card:ℝ) else 0

/-- Pooling assignments to full lines preserves mass and bounds each weight by actual full-cloud matches. -/
theorem pooled_assignment_weights (P Q : CubePartition) (X Y : Finset (E 3))
    (G : Finset (Motion 3)) (LX LY : Finset (Line 3))
    (a : Motion 3 → Region × Region → Finset (E 3))
    (pick : Motion 3 → Region × Region → Option (Line 3))
    (hsub : ∀ g ∈ G,∀ RR ∈ P.regions ×ˢ Q.regions,a g RR ⊆ regionPairMatches X Y RR g)
    (hon : ∀ g ∈ G,∀ RR ∈ P.regions ×ˢ Q.regions,∀ l : Line 3,
      pick g RR = some l → ∀ x ∈ a g RR,x ∈ l.1)
    (hchoice : ∀ g ∈ G,∀ RR ∈ P.regions ×ˢ Q.regions,(a g RR).Nonempty →
      ∃ l ∈ LX,pick g RR = some l ∧ ∃ l' ∈ LY,mapsLine g l l') :
    ∀ g ∈ G,
      (∀ l ∈ LX,0 ≤ pooledAssignedWeight (P.regions ×ˢ Q.regions) a pick g l ∧
        pooledAssignedWeight (P.regions ×ˢ Q.regions) a pick g l ≤ (matchCount (pointsOn X l) Y g:ℝ) ∧
        (0 < pooledAssignedWeight (P.regions ×ˢ Q.regions) a pick g l → ∃ l' ∈ LY,mapsLine g l l')) ∧
      (∑ l ∈ LX,pooledAssignedWeight (P.regions ×ˢ Q.regions) a pick g l) =
        ∑ RR ∈ P.regions ×ˢ Q.regions,((a g RR).card:ℝ) := by
  intro g hg
  let I := P.regions ×ˢ Q.regions
  have hpos : ∀ l,0 ≤ pooledAssignedWeight I a pick g l := by
    intro l
    unfold pooledAssignedWeight
    apply Finset.sum_nonneg
    intro RR hRR
    split <;> positivity
  have hupper : ∀ l,pooledAssignedWeight I a pick g l ≤ (matchCount (pointsOn X l) Y g:ℝ) := by
    intro l
    let B : Region × Region → Finset (E 3) := fun RR => if pick g RR = some l then a g RR else ∅
    have hd : (I:Set (Region × Region)).PairwiseDisjoint B := by
      intro RR hRR SS hSS hne
      change Disjoint (B RR) (B SS)
      by_cases hr : pick g RR = some l <;> by_cases hs : pick g SS = some l
      · simp only [B,if_pos hr,if_pos hs]
        exact (regionPairMatches_disjoint P Q X Y g RR SS hRR hSS hne).mono (hsub g hg RR hRR) (hsub g hg SS hSS)
      all_goals simp [B,hr,hs]
    have hs : I.biUnion B ⊆ matchPoints (pointsOn X l) Y g := by
      intro x hx
      obtain ⟨RR,hRR,hxB⟩ := Finset.mem_biUnion.mp hx
      by_cases hp : pick g RR = some l
      · simp only [B,if_pos hp] at hxB
        obtain ⟨hxX,hxR,hgy,hgR⟩ := (mem_regionPairMatches X Y RR g x).mp (hsub g hg RR hRR hxB)
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hxX,hon g hg RR hRR l hp x hxB⟩,hgy⟩
      · simp [B,hp] at hxB
    have heq : pooledAssignedWeight I a pick g l = ((I.biUnion B).card:ℝ) := by
      rw [Finset.card_biUnion hd,Nat.cast_sum]
      unfold pooledAssignedWeight
      apply Finset.sum_congr rfl
      intro RR hRR
      by_cases hp : pick g RR = some l <;> simp [B,hp]
    rw [heq]
    exact Nat.cast_le.mpr (Finset.card_le_card hs)
  have hmap : ∀ l,0 < pooledAssignedWeight I a pick g l → ∃ l' ∈ LY,mapsLine g l l' := by
    intro l hl
    by_contra hnot
    have hz : pooledAssignedWeight I a pick g l = 0 := by
      apply Finset.sum_eq_zero
      intro RR hRR
      by_cases hp : pick g RR = some l
      · by_cases ha : a g RR = ∅
        · simp [ha]
        · obtain ⟨l₀,hl₀,hpick,l',hl',hmap⟩ := hchoice g hg RR hRR (Finset.nonempty_iff_ne_empty.mpr ha)
          have heq : l₀ = l := Option.some.inj (hpick.symm.trans hp)
          subst l₀
          exact (hnot ⟨l',hl',hmap⟩).elim
      · simp [hp]
    linarith
  refine ⟨fun l hl => ⟨hpos l,hupper l,hmap l⟩,?_⟩
  unfold pooledAssignedWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro RR hRR
  by_cases ha : a g RR = ∅
  · simp [ha]
  · obtain ⟨l,hl,hpick,l',hl',hmap⟩ := hchoice g hg RR hRR (Finset.nonempty_iff_ne_empty.mpr ha)
    simp [hpick,hl,eq_comm]

end DistinctDistances.TrackC
