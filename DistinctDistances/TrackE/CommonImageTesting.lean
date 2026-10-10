import DistinctDistances.TrackE.CommonImageGeometry
import DistinctDistances.TrackD.Profiles.RegularityChosenProduct

/-! Complete images forced into every later label equation system,
`sc:common-rank.complete-images`, sparse-cones.tex:239–261. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- Uniform product testing on the original pools retains their original
owners and forces complete images into any later equation system. Neither
coverage nor density nor image-degree/rank conclusions are premises. -/
theorem common_graph_complete_images {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (M : CommonPoolProfile T)
    (j : ℕ) (hj : j < d) (τph : ℝ) (W : CommonPhysicalSequence T M j τph)
    (τ ξ : ℝ) (hτ : -1 < τ) (hξ : 0 < ξ)
    (hplateau : TrackD.OnPlateau M.b j ξ τ) :
    ∀ θ : ℝ, 0 < θ → ∀ K : ℝ, 1 ≤ K → ∀ᶠ i in atTop,
      ∀ (i₀ : Fin d) (𝒢 : Set (TrackD.PairPoly d)),
        (∀ G ∈ 𝒢, (G.totalDegree : ℝ) ≤
          K * TrackD.testDeg (TrackD.cfgB (regime.P i)) (M.s i) τ) →
        ∀ (Γ : Finset (RPoint d × RPoint d)),
          Γ ⊆ TrackD.poolPts (T.sources i) ×ˢ TrackD.poolPts (T.targets i) →
          (∀ pq ∈ Γ, (TrackD.toC pq.2 - TrackD.toC pq.1) i₀ ≠ 0 ∧
            ∀ G ∈ 𝒢, MvPolynomial.eval
              (TrackD.labelPt i₀ (TrackD.toC pq.1) (TrackD.toC pq.2)) G = 0) →
          commonImageGoodGraph i₀ Γ 𝒢 (W.owner i) ⊆ Γ ∧
          ((Γ \ commonImageGoodGraph i₀ Γ 𝒢 (W.owner i)).card : ℝ) ≤
            θ * (TrackD.poolPts (T.sources i)).card * (TrackD.poolPts (T.targets i)).card ∧
          ∀ pq ∈ commonImageGoodGraph i₀ Γ 𝒢 (W.owner i), ∀ G ∈ 𝒢,
            commonPairEquation G ∈
              (commonProductImage i₀ (W.owner i pq.1) (W.owner i pq.2)).ideal := by
  intro θ hθ K hK
  obtain ⟨θ₁, hθ₁, η, hη, hηξ, ρ₀, hρ₀, s₁, hproduct⟩ :=
    TrackD.prof_product_testing_labels_with_margin d
      regime.dimension_ge_three θ hθ ξ hξ K hK
  filter_upwards [M.good θ₁ hθ₁ η hη 1 le_rfl
      (ρ₀ / 2) (by positivity), M.width_grows.eventually_ge_atTop s₁,
    common_physical_test_degree_one M τ hτ] with i hpool hs hT
  intro i₀ 𝒢 hdegree Γ hsub hgraph
  have hsource : TrackD.CarrierAssignment (T.sources i) j (W.owner i) := by
    intro X hX q hq
    exact W.supported i X (Finset.mem_union_left _ hX) q hq
  have htarget : TrackD.CarrierAssignment (T.targets i) j (W.owner i) := by
    intro Y hY q hq
    exact W.supported i Y (Finset.mem_union_right _ hY) q hq
  let bad : Finset (RPoint d × RPoint d) := Γ.filter (fun pq =>
    ∃ G ∈ 𝒢, ∃ x ∈ W.owner i pq.1, ∃ y ∈ W.owner i pq.2,
      (y - x) i₀ ≠ 0 ∧ MvPolynomial.eval (TrackD.labelPt i₀ x y) G ≠ 0)
  have hbad : (bad.card : ℝ) ≤
      θ * (TrackD.poolPts (T.sources i)).card * (TrackD.poolPts (T.targets i)).card :=
    hproduct (regime.P i) (T.sources i) (T.targets i) (M.s i) (ρ₀ / 2) M.b
      (by linarith) hpool.1 hpool.2 hs j hj τ hplateau hT
      (W.owner i) (W.owner i) hsource htarget i₀ 𝒢 hdegree Γ hsub hgraph
  have hmissing : Γ \ commonImageGoodGraph i₀ Γ 𝒢 (W.owner i) ⊆ bad := by
    intro pq hpq
    obtain ⟨hpq, hnot⟩ := Finset.mem_sdiff.mp hpq
    have hn : ¬ ∀ G ∈ 𝒢, commonPairEquation G ∈
        (commonProductImage i₀ (W.owner i pq.1) (W.owner i pq.2)).ideal := by
      intro hh
      exact hnot (Finset.mem_filter.mpr ⟨hpq, hh⟩)
    push_neg at hn
    obtain ⟨G, hG, hnG⟩ := hn
    have hnPair : ¬ ∀ x ∈ W.owner i pq.1, ∀ y ∈ W.owner i pq.2,
        (y - x) i₀ ≠ 0 → MvPolynomial.eval (TrackD.labelPt i₀ x y) G = 0 := by
      intro hh
      exact hnG ((common_product_image_equation_iff i₀
        (W.owner i pq.1) (W.owner i pq.2) G).mpr hh)
    push_neg at hnPair
    obtain ⟨x, hx, y, hy, hi, hzero⟩ := hnPair
    exact Finset.mem_filter.mpr ⟨hpq, G, hG, x, hx, y, hy, hi, hzero⟩
  refine ⟨Finset.filter_subset _ _, ?_, ?_⟩
  · have hcard : ((Γ \ commonImageGoodGraph i₀ Γ 𝒢 (W.owner i)).card : ℝ) ≤
        (bad.card : ℝ) := by exact_mod_cast Finset.card_le_card hmissing
    exact hcard.trans hbad
  · intro pq hpq G hG
    exact (Finset.mem_filter.mp hpq).2 G hG

end
end DistinctDistances.SparseCones
