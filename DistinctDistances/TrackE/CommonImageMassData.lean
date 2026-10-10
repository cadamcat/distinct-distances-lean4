import DistinctDistances.TrackE.CommonProductLists
import DistinctDistances.TrackE.CommonImagePooling

/-! Original chart-eligible lists and literal owner-fiber product masses,
`sc:retained-products.mass`, sparse-cones.tex:143–148, 201–213. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}
variable {F : ConeCoverageSequence regime} {T : SelectedProfileSequence F}
    {M : CommonPoolProfile T} {j : ℕ} {τ ε : ℝ}

/-- A chart filter leaves the larger original list in every depth certificate. -/
def commonChartTargets (W : CommonPhysicalSequence T M j τ)
    (L : CommonProductLists W ε) (i : ℕ) (i₀ : Fin d)
    (X : AffineVariety d) : AffineFamily.Family d :=
  (L.lists i X).filter (fun Y => ∃ x ∈ X, ∃ y ∈ Y, (y - x) i₀ ≠ 0)

/-- Every distinct complete original image appears once, including unused images. -/
def commonChartImages (W : CommonPhysicalSequence T M j τ)
    (L : CommonProductLists W ε) (i : ℕ) (i₀ : Fin d) :
    AffineFamily.Family (d + d) :=
  (W.sourceCarriers i).biUnion (fun X =>
    (commonChartTargets W L i i₀ X).image (commonProductImage i₀ X))

/-- All original owner-fiber products whose complete image lies in the later J. -/
def commonChartImageMass (W : CommonPhysicalSequence T M j τ)
    (L : CommonProductLists W ε) (i : ℕ) (i₀ : Fin d)
    (J : AffineFamily.Family (d + d)) : ℝ :=
  ∑ X ∈ W.sourceCarriers i,
    ∑ Y ∈ (commonChartTargets W L i i₀ X).filter
      (fun Y => commonProductImage i₀ X Y ∈ J),
      ((W.sourceAssigned i X).card : ℝ) * (W.targetAssigned i Y).card

end
end DistinctDistances.SparseCones
