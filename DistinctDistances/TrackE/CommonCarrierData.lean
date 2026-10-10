import DistinctDistances.TrackE.CommonImageTesting
import DistinctDistances.TrackE.CommonEndpointInputs
import DistinctDistances.TrackE.RequestsWideFlat

/-! Literal pooled retained carriers, `sc:retained-carrier-weights`,
sparse-cones.tex:122–145. All fibers use the original supported owner. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

def commonOwnerFamily (S : Finset (RPoint d)) (α : RPoint d → AffineVariety d) :
    AffineFamily.Family d := S.image α

def commonOwnerFiber (S : Finset (RPoint d)) (α : RPoint d → AffineVariety d)
    (Z : AffineVariety d) : Finset (RPoint d) := S.filter (fun q => α q = Z)

namespace CommonPhysicalSequence
variable {F : ConeCoverageSequence regime} {T : SelectedProfileSequence F}
    {M : CommonPoolProfile T} {j : ℕ} {τ : ℝ}

def sourceCarriers (W : CommonPhysicalSequence T M j τ) (i : ℕ) : AffineFamily.Family d :=
  commonOwnerFamily (W.sources i) (W.owner i)

def targetCarriers (W : CommonPhysicalSequence T M j τ) (i : ℕ) : AffineFamily.Family d :=
  commonOwnerFamily (W.targets i) (W.owner i)

def sourceAssigned (W : CommonPhysicalSequence T M j τ) (i : ℕ) :
    AffineVariety d → Finset (RPoint d) := commonOwnerFiber (W.sources i) (W.owner i)

def targetAssigned (W : CommonPhysicalSequence T M j τ) (i : ℕ) :
    AffineVariety d → Finset (RPoint d) := commonOwnerFiber (W.targets i) (W.owner i)

end CommonPhysicalSequence

def commonCarrierScale {F : ConeCoverageSequence regime} {T : SelectedProfileSequence F}
    (M : CommonPoolProfile T) (j i : ℕ) : ℝ :=
  TrackD.eScale (regime.B i) (M.s i) M.b j

/-- The two actual pooled degree and individual mass budgets. -/
def CommonCarrierBudgets {F : ConeCoverageSequence regime} {T : SelectedProfileSequence F}
    {M : CommonPoolProfile T} {j : ℕ} {τ : ℝ}
    (W : CommonPhysicalSequence T M j τ) (i : ℕ) (η : ℝ) : Prop :=
  (∑ X ∈ W.sourceCarriers i, (X.degree : ℝ)) ≤
      commonCarrierScale M j i * Real.exp (η * M.s i) ∧
  (∑ Y ∈ W.targetCarriers i, (Y.degree : ℝ)) ≤
      commonCarrierScale M j i * Real.exp (η * M.s i) ∧
  (∀ X ∈ W.sourceCarriers i, ((W.sourceAssigned i X).card : ℝ) ≤
    ((W.sources i).card : ℝ) * (X.degree : ℝ) / commonCarrierScale M j i *
      Real.exp (η * M.s i)) ∧
  (∀ Y ∈ W.targetCarriers i, ((W.targetAssigned i Y).card : ℝ) ≤
    ((W.targets i).card : ℝ) * (Y.degree : ℝ) / commonCarrierScale M j i *
      Real.exp (η * M.s i))

end
end DistinctDistances.SparseCones
