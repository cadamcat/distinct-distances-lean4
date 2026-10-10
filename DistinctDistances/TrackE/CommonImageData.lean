import DistinctDistances.TrackE.CommonPhysical
import DistinctDistances.TrackD.SecantsLabelAlgebra

/-! Complete rational product images in the shared affine coordinates,
`sc:retained-products.depth/family`, sparse-cones.tex:143–188. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ}

/-- Closure of the entire product's actual secant label map on its chart.
No finite graph or observed-label envelope is used in this definition. -/
def commonProductImage (i₀ : Fin d) (X Y : AffineVariety d) : AffineVariety (d + d) :=
  TrackD.rationalImage (TrackD.productVariety X Y)
    (TrackD.secantChartNumerator i₀) (TrackD.secantChartDenominator i₀)

/-- Pull back a source polynomial through the first label coordinate. -/
def commonSourcePolynomial (f : Poly d) : Poly (d + d) :=
  MvPolynomial.rename (fun k => finSumFinEquiv (Sum.inl k)) f

/-- Transport the literal label equations to the shared affine coordinates. -/
def commonPairEquation (G : TrackD.PairPoly d) : Poly (d + d) :=
  MvPolynomial.rename finSumFinEquiv G

/-- Physical graph edges whose unchanged complete owner image satisfies
every later label equation. The original physical pairs are retained. -/
def commonImageGoodGraph (i₀ : Fin d) (Γ : Finset (RPoint d × RPoint d))
    (𝒢 : Set (TrackD.PairPoly d)) (α : RPoint d → AffineVariety d) :
    Finset (RPoint d × RPoint d) :=
  Γ.filter (fun pq => ∀ G ∈ 𝒢,
    commonPairEquation G ∈ (commonProductImage i₀ (α pq.1) (α pq.2)).ideal)

end
end DistinctDistances.SparseCones
