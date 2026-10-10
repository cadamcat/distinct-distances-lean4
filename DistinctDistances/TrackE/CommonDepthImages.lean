import DistinctDistances.TrackE.CommonDepthSums

/-! Original chart-eligible target lists keep all depth and image tests
before later subfamilies, sparse-cones.tex:139–150,172–188. -/
namespace DistinctDistances.SparseCones
open scoped BigOperators Classical
noncomputable section

theorem common_original_list_radial_depth {d k : ℕ} (i₀ : Fin d)
    (X : AffineVariety d) (hX : X.IsIrreducible)
    (F L : AffineFamily.Family d) (hFL : F ⊆ L)
    (hk : 1 ≤ k) (hF : AffineFamily.IsPure F k) (R : ℝ)
    (hchart : ∀ Y ∈ F, ∃ x ∈ X, ∃ y ∈ Y, (y - x) i₀ ≠ 0)
    (hdepth : ∀ Y ∈ F, TrackD.ForGeneralPair X Y (fun x y =>
      y - x ∉ X.tangentSpace x ∧ y - x ∉ Y.tangentSpace y ∧
      (TrackD.movingRoots L x y).Finite ∧
        ((TrackD.movingRoots L x y).ncard : ℝ) ≤ R)) :
    TrackD.ForGeneralPoint X (fun x =>
      (∀ Y ∈ F, (radialImage x Y).dimension = k) ∧
      (∀ Y ∈ F, (TrackA.groupDepth x F Y : ℝ) ≤ R) ∧
      (∀ Y ∈ F, ∀ Y' ∈ F,
        commonProductImage i₀ X Y = commonProductImage i₀ X Y' →
          radialImage x Y = radialImage x Y') ∧
      (∀ Y ∈ F,
        ((∑ V ∈ F.filter (fun V =>
          commonProductImage i₀ X V = commonProductImage i₀ X Y),
            TrackA.radialMapDegree x V) : ℝ) ≤ R)) := by
  have hFirr (Y : AffineVariety d) (hY : Y ∈ F) : Y.IsIrreducible := (hF Y hY).1
  have htrans (Y : AffineVariety d) (hY : Y ∈ F) : TrackD.ForGeneralPair X Y
      (fun x y => y - x ∉ Y.tangentSpace y) := by
    exact (hdepth Y hY).mono (fun x hx y hy hh => hh.2.1)
  have hdim0 := common_product_family_radial_dimension i₀ X hX F hFirr hchart htrans
  have himages : TrackD.ForGeneralPoint X (fun x =>
      ∀ V ∈ F, (radialImage x V).dimension = k) := by
    apply hdim0.mono
    intro x hx hh V hV
    exact (hh V hV).trans (hF V hV).2
  have hroots (Y : AffineVariety d) (hY : Y ∈ F) : TrackD.ForGeneralPair X Y
      (fun x y => (TrackD.movingRoots F x y).Finite ∧
        ((TrackD.movingRoots F x y).ncard : ℝ) ≤ R) := by
    apply (hdepth Y hY).mono
    intro x hx y hy hh
    rcases hh with ⟨_, _, hfinite, hbound⟩
    have hsub := common_moving_roots_mono F L hFL x y
    have hn := Set.ncard_le_ncard hsub hfinite
    have hnR : ((TrackD.movingRoots F x y).ncard : ℝ) ≤
        ((TrackD.movingRoots L x y).ncard : ℝ) := by
      exact_mod_cast hn
    exact ⟨hfinite.subset hsub, hnR.trans hbound⟩
  have hgroups := common_general_radial_group_depth X hX F hk hF R himages hroots
  have hequal := common_product_family_radial_eq i₀ X hX F hFirr hchart
  apply ((himages.and hX hgroups).and hX hequal).mono
  intro x hx hh
  refine ⟨hh.1.1, hh.1.2, hh.2, ?_⟩
  intro Y hY
  have hn := common_complete_image_degree_sum_le_depth i₀ X F x Y
    (fun V hV heq => hh.2 V hV Y hY heq)
  have hnR : ((∑ V ∈ F.filter (fun V =>
      commonProductImage i₀ X V = commonProductImage i₀ X Y),
        TrackA.radialMapDegree x V) : ℝ) ≤ (TrackA.groupDepth x F Y : ℝ) := by
    exact_mod_cast hn
  exact hnR.trans (hh.1.2 Y hY)

end
end DistinctDistances.SparseCones
