import DistinctDistances.TrackC.RichMotions
import DistinctDistances.TrackE.Basic

/-! A finite witness for rich motions of a rotated copy, including both orientations. -/

namespace DistinctDistances.Bridges

open scoped BigOperators Classical
noncomputable section

theorem rich_motions_rotated : ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
    ∀ (P : Finset (RPoint 3)) (R : RPoint 3 ≃ₗᵢ[ℝ] RPoint 3), 2 ≤ P.card →
      Mcount P ≤ Ascale 3 P.card →
      ∃ G : Finset (RPoint 3 ≃ᵃⁱ[ℝ] RPoint 3),
        (∀ g : RPoint 3 ≃ᵃⁱ[ℝ] RPoint 3,
          C * Ascale 3 P.card ≤ ((P.filter fun p => g p ∈ P.image R).card : ℝ) → g ∈ G) ∧
        ∑ g ∈ G, (((P.filter fun p => g p ∈ P.image R).card : ℝ)) ^ 2 ≤
          K * (P.card : ℝ) ^ 4 / Ascale 3 P.card := by
  obtain ⟨C, K, hC, hK, h⟩ := TrackC.mot_rich
  refine ⟨C, K, hC, hK, ?_⟩
  intro P R hP hsmall
  have hsmall' : 1 + ((TrackC.positiveDistances P).card : ℝ) ≤
      (P.card : ℝ) ^ ((2 : ℝ) / 3) := by
    simpa [Mcount, Ascale, distinctDistances, distanceSet, TrackC.positiveDistances, add_comm]
      using hsmall
  obtain ⟨hfinite, hbound⟩ := h P hP hsmall' (P.image R)
    ⟨R.toAffineIsometryEquiv, rfl⟩
  refine ⟨hfinite.toFinset, ?_, ?_⟩
  · intro g hg
    exact hfinite.mem_toFinset.mpr hg
  · exact hbound hfinite.toFinset (fun g hg => hfinite.mem_toFinset.mp hg)

end
end DistinctDistances.Bridges
