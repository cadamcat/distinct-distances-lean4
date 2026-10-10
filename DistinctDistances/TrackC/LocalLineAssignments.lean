import DistinctDistances.TrackC.PartitionMatches
import DistinctDistances.TrackC.AmbientRichLines
import DistinctDistances.TrackC.DyadicLocalMass

open scoped BigOperators
open Classical

noncomputable section

namespace DistinctDistances.TrackC

def localRegionRichness (X Y : Finset (E 3)) (RR : Region × Region) (g : Motion 3) : ℝ :=
  (regionPairMatches X Y RR g).card

def localRegionScale (X Y : Finset (E 3)) (b : ℝ) (hb : 0 < b) (RR : Region × Region) (g : Motion 3) : ℝ :=
  b*(2:ℝ)^(dyadicLocalLevel b (localRegionRichness X Y RR g) hb)

def localLineRetained (X Y : Finset (E 3)) (η b : ℝ) (hb : 0 < b) (RR : Region × Region) (g : Motion 3) : Prop :=
  b ≤ localRegionRichness X Y RR g ∧
    ¬nonLineType η (localRegionScale X Y b hb RR g) (pointsIn X (regionSet RR.1)) (pointsIn Y (regionSet RR.2)) g

theorem exists_local_assigned_line (X Y : Finset (E 3)) (η b : ℝ) (hb : 0 < b) (RR : Region × Region)
    (g : Motion 3) (h : localLineRetained X Y η b hb RR g) :
    ∃ l : Line 3,η*localRegionScale X Y b hb RR g ≤ ((pointsOn (regionPairMatches X Y RR g) l).card:ℝ) := by
  have hn := h.2
  change ¬∀ l : Line 3,((pointsOn (regionPairMatches X Y RR g) l).card:ℝ) < η*localRegionScale X Y b hb RR g at hn
  push_neg at hn
  exact hn

def localAssignedLine (X Y : Finset (E 3)) (η b : ℝ) (hb : 0 < b) (g : Motion 3) (RR : Region × Region) : Option (Line 3) :=
  if h : localLineRetained X Y η b hb RR g then some (exists_local_assigned_line X Y η b hb RR g h).choose else none

def localAssignedPoints (X Y : Finset (E 3)) (η b : ℝ) (hb : 0 < b) (g : Motion 3) (RR : Region × Region) : Finset (E 3) :=
  match localAssignedLine X Y η b hb g RR with
  | none => ∅
  | some l => pointsOn (regionPairMatches X Y RR g) l

theorem localAssignedPoints_subset (X Y : Finset (E 3)) (η b : ℝ) (hb : 0 < b) (g : Motion 3) (RR : Region × Region) :
    localAssignedPoints X Y η b hb g RR ⊆ regionPairMatches X Y RR g := by
  unfold localAssignedPoints
  split
  · exact Finset.empty_subset _
  · exact Finset.filter_subset _ _

theorem localAssignedPoints_on_line (X Y : Finset (E 3)) (η b : ℝ) (hb : 0 < b) (g : Motion 3) (RR : Region × Region)
    (l : Line 3) (hl : localAssignedLine X Y η b hb g RR = some l) :
    ∀ x ∈ localAssignedPoints X Y η b hb g RR,x ∈ l.1 := by
  unfold localAssignedPoints
  rw [hl]
  exact fun x hx => (Finset.mem_filter.mp hx).2

theorem localAssignedPoints_mass (X Y : Finset (E 3)) (η b : ℝ) (hb : 0 < b) (hη : 0 < η)
    (g : Motion 3) (RR : Region × Region) :
    (η/2)*(if localLineRetained X Y η b hb RR g then localRegionRichness X Y RR g else 0) ≤
      ((localAssignedPoints X Y η b hb g RR).card:ℝ) := by
  by_cases h : localLineRetained X Y η b hb RR g
  · let l := (exists_local_assigned_line X Y η b hb RR g h).choose
    have hcount := (exists_local_assigned_line X Y η b hb RR g h).choose_spec
    have hbnds := dyadicLocalLevel_bounds b (localRegionRichness X Y RR g) hb h.1
    change b*(2:ℝ)^(dyadicLocalLevel b (localRegionRichness X Y RR g) hb) ≤ _ ∧
      localRegionRichness X Y RR g < 2*localRegionScale X Y b hb RR g at hbnds
    simp only [localAssignedPoints,localAssignedLine,dif_pos h,if_pos h]
    nlinarith
  · simp [localAssignedPoints,localAssignedLine,h]

/-- Assigned source and target lines belong to the ambient rich-line lists. -/
theorem localAssignedPoints_rich_lines (X Y : Finset (E 3)) (η b : ℝ) (hb : 0 < b) (hη : 0 < η)
    (LX LY : Finset (Line 3))
    (hLX : ∀ l : Line 3,l ∈ LX ↔ η*b ≤ ((pointsOn X l).card:ℝ))
    (hLY : ∀ l : Line 3,l ∈ LY ↔ η*b ≤ ((pointsOn Y l).card:ℝ))
    (g : Motion 3) (RR : Region × Region) (hne : (localAssignedPoints X Y η b hb g RR).Nonempty) :
    ∃ l ∈ LX,localAssignedLine X Y η b hb g RR = some l ∧ ∃ l' ∈ LY,mapsLine g l l' := by
  have h : localLineRetained X Y η b hb RR g := by
    by_contra hnot
    simp [localAssignedPoints,localAssignedLine,hnot] at hne
  let l := (exists_local_assigned_line X Y η b hb RR g h).choose
  have hpick : localAssignedLine X Y η b hb g RR = some l := by simp [localAssignedLine,h,l]
  have hAeq : localAssignedPoints X Y η b hb g RR = pointsOn (regionPairMatches X Y RR g) l := by
    simp [localAssignedPoints,hpick]
  have hcount : η*b ≤ ((localAssignedPoints X Y η b hb g RR).card:ℝ) := by
    have hscale : b ≤ localRegionScale X Y b hb RR g := le_mul_of_one_le_right hb.le (one_le_pow₀ (by norm_num))
    have hc := (exists_local_assigned_line X Y η b hb RR g h).choose_spec
    rw [hAeq]
    exact (mul_le_mul_of_nonneg_left hscale hη.le).trans hc
  have hsource : localAssignedPoints X Y η b hb g RR ⊆ pointsOn X l := by
    intro x hx
    obtain ⟨hxX,hxR,hgY,hgR⟩ := (mem_regionPairMatches X Y RR g x).mp (localAssignedPoints_subset X Y η b hb g RR hx)
    exact Finset.mem_filter.mpr ⟨hxX,localAssignedPoints_on_line X Y η b hb g RR l hpick x hx⟩
  have htarget : (localAssignedPoints X Y η b hb g RR).image g ⊆ pointsOn Y (motionImageLine g l) := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hxX,hxR,hgY,hgR⟩ := (mem_regionPairMatches X Y RR g x).mp (localAssignedPoints_subset X Y η b hb g RR hx)
    have hline : g x ∈ (motionImageLine g l).1 := by
      change g x ∈ g '' (l.1:Set (E 3))
      exact Set.mem_image_of_mem g (localAssignedPoints_on_line X Y η b hb g RR l hpick x hx)
    exact Finset.mem_filter.mpr ⟨hgY,hline⟩
  have hlX : l ∈ LX := (hLX l).mpr (hcount.trans (Nat.cast_le.mpr (Finset.card_le_card hsource)))
  have hlY : motionImageLine g l ∈ LY := by
    apply (hLY _).mpr
    have hc : (((localAssignedPoints X Y η b hb g RR).image g).card:ℝ) ≤
        ((pointsOn Y (motionImageLine g l)).card:ℝ) := Nat.cast_le.mpr (Finset.card_le_card htarget)
    rw [Finset.card_image_of_injective _ g.injective] at hc
    exact hcount.trans hc
  exact ⟨l,hlX,hpick,motionImageLine g l,hlY,motionImageLine_maps g l⟩

end DistinctDistances.TrackC
