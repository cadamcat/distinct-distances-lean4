import DistinctDistances.TrackC.MotionLocal

open Classical

noncomputable section

namespace DistinctDistances.TrackC

/-- A collinear finite cloud with two points lies in an actual affine line. -/
theorem collinear_cloud_line (S : Finset (E 3)) (hcard : 2 ≤ S.card)
    (hS : Collinear ℝ (S:Set (E 3))) : ∃ l : Line 3,(S:Set (E 3)) ⊆ l.1 := by
  obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
  let H := affineSpan ℝ (S:Set (E 3))
  have hxH : x ∈ H := mem_affineSpan ℝ hx
  have hyH : y ∈ H := mem_affineSpan ℝ hy
  have hv : y-x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  have hspan : ℝ ∙ (y-x) ≤ H.direction := (Submodule.span_singleton_le_iff_mem (y-x) H.direction).mpr (H.vsub_mem_direction hyH hxH)
  have hdimlow : 1 ≤ Module.finrank ℝ H.direction := by
    have hd := Submodule.finrank_mono hspan
    rwa [finrank_span_singleton hv] at hd
  have hdimhigh : Module.finrank ℝ H.direction ≤ 1 := by
    rw [direction_affineSpan]
    exact hS.finrank_le_one
  refine ⟨⟨H,⟨⟨x,hxH⟩,by omega⟩⟩,?_⟩
  exact subset_affineSpan ℝ _

/-- A match set larger than the ambient line cap cannot be collinear. -/
theorem large_match_not_collinear (X Y : Finset (E 3)) (g : Motion 3) (H k : ℝ)
    (hH : 1 ≤ H) (hcap : cloudLineCap X H) (hk : H < k) (hmatch : k ≤ (matchCount X Y g:ℝ)) :
    ¬Collinear ℝ (matchPoints X Y g:Set (E 3)) := by
  intro hcol
  have hcard : 2 ≤ (matchPoints X Y g).card := by
    have hm : (1:ℝ) < (matchPoints X Y g).card := lt_of_le_of_lt hH (hk.trans_le hmatch)
    have hn : 1 < (matchPoints X Y g).card := by exact_mod_cast hm
    omega
  obtain ⟨l,hl⟩ := collinear_cloud_line _ hcard hcol
  have hsub : matchPoints X Y g ⊆ pointsOn X l := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,hl hx⟩
  have hc : (matchCount X Y g:ℝ) ≤ H := (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hcap l)
  linarith

/-- The global bucket is finite once its richness exceeds the line cap. -/
theorem motion_bucket_finite_of_line_cap (X Y : Finset (E 3)) (H k : ℝ)
    (hH : 1 ≤ H) (hcap : cloudLineCap X H) (hk : H < k) : (motionBucket X Y k).Finite := by
  apply (spatial_motions_finite X Y).subset
  intro g hg
  exact large_match_not_collinear X Y g H k hH hcap hk hg.1

end DistinctDistances.TrackC
