import DistinctDistances.TrackE.CommonImageMass

/-! Actual graph-card transport on the original fixed depth lists,
`sc:retained-products.mass`, sparse-cones.tex:146–148, 239–261. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}
variable {F : ConeCoverageSequence regime} {T : SelectedProfileSequence F}
    {M : CommonPoolProfile T} {j : ℕ} {τ : ℝ}

theorem selected_common_chart_graph_mass (W : CommonPhysicalSequence T M j τ)
    (hj : j < d) (hk : d - j + 1 < d) (ε₀ : ℝ) (hε₀ : 0 < ε₀) :
    ∃ L : CommonProductLists W (ε₀ / 2), ∀ᶠ i in atTop, ∀ i₀ : Fin d,
      AffineFamily.IsPure (commonChartImages W L i i₀) (2 * (d - j)) ∧
      ∀ Γ : Finset (RPoint d × RPoint d), Γ ⊆ W.sources i ×ˢ W.targets i →
        (∀ pq ∈ Γ, W.owner i pq.2 ∈ L.lists i (W.owner i pq.1)) →
        (∀ pq ∈ Γ, (TrackD.toC pq.2 - TrackD.toC pq.1) i₀ ≠ 0) →
        ∀ J : AffineFamily.Family (d + d),
          ((Γ.filter (fun pq =>
            commonProductImage i₀ (W.owner i pq.1) (W.owner i pq.2) ∈ J)).card : ℝ) ≤
            Real.exp (ε₀ * M.s i) *
              (((W.sources i).card : ℝ) * (W.targets i).card /
                (commonCarrierScale M j i) ^ 2) *
              (∑ Z ∈ (commonChartImages W L i i₀).filter (fun Z => Z ∈ J),
                (Z.degree : ℝ)) := by
  obtain ⟨L, hL⟩ := selected_common_chart_image_mass W hj hk ε₀ hε₀
  refine ⟨L, hL.mono ?_⟩
  intro i hi i₀
  refine ⟨(hi i₀).1, ?_⟩
  intro Γ hΓ hlist hchart J
  exact (common_chart_graph_card_le_image_mass W hj.le L i i₀ Γ hΓ hlist hchart J).trans
    ((hi i₀).2 J)

end
end DistinctDistances.SparseCones
