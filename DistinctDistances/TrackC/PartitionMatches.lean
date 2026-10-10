import DistinctDistances.TrackC.Subdivision
import DistinctDistances.TrackC.FiniteIncidence

open scoped BigOperators
open Classical

noncomputable section

namespace DistinctDistances.TrackC

def regionPairMatches (X Y : Finset (E 3)) (RR : Region × Region) (g : Motion 3) : Finset (E 3) :=
  matchPoints (pointsIn X (regionSet RR.1)) (pointsIn Y (regionSet RR.2)) g

@[simp] theorem mem_regionPairMatches (X Y : Finset (E 3)) (RR : Region × Region) (g : Motion 3) (x : E 3) :
    x ∈ regionPairMatches X Y RR g ↔ x ∈ X ∧ x ∈ regionSet RR.1 ∧ g x ∈ Y ∧ g x ∈ regionSet RR.2 := by
  simp [regionPairMatches,matchPoints]
  tauto

theorem regionPairMatches_subset (X Y : Finset (E 3)) (RR : Region × Region) (g : Motion 3) :
    regionPairMatches X Y RR g ⊆ matchPoints X Y g := by
  intro x hx
  obtain ⟨hxX,hxR,hgy,hgR⟩ := (mem_regionPairMatches X Y RR g x).mp hx
  exact Finset.mem_filter.mpr ⟨hxX,hgy⟩

theorem regionPairMatches_disjoint (P Q : CubePartition) (X Y : Finset (E 3)) (g : Motion 3)
    (RR SS : Region × Region) (hRR : RR ∈ P.regions ×ˢ Q.regions) (hSS : SS ∈ P.regions ×ˢ Q.regions)
    (hne : RR ≠ SS) : Disjoint (regionPairMatches X Y RR g) (regionPairMatches X Y SS g) := by
  apply Finset.disjoint_left.mpr
  intro x hxR hxS
  obtain ⟨hxX,hxR,hgy,hgxR⟩ := (mem_regionPairMatches X Y RR g x).mp hxR
  obtain ⟨hxX',hxS,hgy',hgxS⟩ := (mem_regionPairMatches X Y SS g x).mp hxS
  obtain ⟨hR₁,hR₂⟩ := Finset.mem_product.mp hRR
  obtain ⟨hS₁,hS₂⟩ := Finset.mem_product.mp hSS
  by_cases hfirst : RR.1 = SS.1
  · have hsecond : RR.2 ≠ SS.2 := by intro h;exact hne (Prod.ext hfirst h)
    exact Set.disjoint_left.mp (Q.disjoint RR.2 hR₂ SS.2 hS₂ hsecond) hgxR hgxS
  · exact Set.disjoint_left.mp (P.disjoint RR.1 hR₁ SS.1 hS₁ hfirst) hxR hxS

/-- Each physical match belongs to exactly one source-target region pair. -/
theorem regionPairMatches_cover (P Q : CubePartition) (X Y : Finset (E 3)) (g : Motion 3)
    (hX : (X:Set (E 3)) ⊆ cubeSet P.root) (hY : (Y:Set (E 3)) ⊆ cubeSet Q.root) :
    (P.regions ×ˢ Q.regions).biUnion (fun RR => regionPairMatches X Y RR g) = matchPoints X Y g := by
  ext x
  constructor
  · intro hx
    obtain ⟨RR,hRR,hxR⟩ := Finset.mem_biUnion.mp hx
    exact regionPairMatches_subset X Y RR g hxR
  · intro hx
    obtain ⟨hxX,hgy⟩ := Finset.mem_filter.mp hx
    have hxRoot := hX hxX
    have hgRoot := hY hgy
    rw [← P.covers] at hxRoot
    rw [← Q.covers] at hgRoot
    obtain ⟨R,hR,hxR⟩ := (by simpa using hxRoot : ∃ R ∈ P.regions,x ∈ regionSet R)
    obtain ⟨R',hR',hgR'⟩ := (by simpa using hgRoot : ∃ R' ∈ Q.regions,g x ∈ regionSet R')
    exact Finset.mem_biUnion.mpr ⟨(R,R'),Finset.mem_product.mpr ⟨hR,hR'⟩,
      (mem_regionPairMatches X Y (R,R') g x).mpr ⟨hxX,hxR,hgy,hgR'⟩⟩

/-- Count decomposition used for both non-line mass and pooled line assignments. -/
theorem sum_regionPairMatches (P Q : CubePartition) (X Y : Finset (E 3)) (g : Motion 3)
    (hX : (X:Set (E 3)) ⊆ cubeSet P.root) (hY : (Y:Set (E 3)) ⊆ cubeSet Q.root) :
    (∑ RR ∈ P.regions ×ˢ Q.regions,((regionPairMatches X Y RR g).card:ℝ)) = matchCount X Y g := by
  have hd : (↑(P.regions ×ˢ Q.regions):Set (Region × Region)).PairwiseDisjoint
      (fun RR => regionPairMatches X Y RR g) := fun RR hRR SS hSS hne =>
    regionPairMatches_disjoint P Q X Y g RR SS hRR hSS hne
  have hc := congrArg Finset.card (regionPairMatches_cover P Q X Y g hX hY)
  rw [Finset.card_biUnion hd] at hc
  exact_mod_cast hc

/-- A positive local match count forces a geometric overlap of the corresponding regions. -/
theorem regionPairMatches_support (P Q : CubePartition) (X Y : Finset (E 3)) (g : Motion 3) :
    (((P.regions ×ˢ Q.regions).filter (fun RR => (regionPairMatches X Y RR g).card ≠ 0)).card:ℝ) ≤
      regionOverlap P Q g := by
  have hs : (P.regions ×ˢ Q.regions).filter (fun RR => (regionPairMatches X Y RR g).card ≠ 0) ⊆
      (P.regions ×ˢ Q.regions).filter (fun RR => (g '' regionSet RR.1 ∩ regionSet RR.2).Nonempty) := by
    intro RR hRR
    obtain ⟨hR,hcount⟩ := Finset.mem_filter.mp hRR
    obtain ⟨x,hx⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hcount)
    obtain ⟨hxX,hxR,hgy,hgR⟩ := (mem_regionPairMatches X Y RR g x).mp hx
    exact Finset.mem_filter.mpr ⟨hR,g x,⟨x,hxR,rfl⟩,hgR⟩
  exact_mod_cast Finset.card_le_card hs

end DistinctDistances.TrackC
