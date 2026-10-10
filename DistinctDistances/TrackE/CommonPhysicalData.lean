import DistinctDistances.TrackE.CommonProfiles
import DistinctDistances.TrackE.TerminalInputs
import DistinctDistances.TrackD.Profiles.RegularitySequenceAdapters

/-! Literal physical retention in `sc:retained-products.points`,
sparse-cones.tex:99–141. The same owner and predicate serve both pool roles. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- The surviving physical points of one role, tested against the whole
original union and the fixed supported owner. -/
def retainedCommonPool (pl allpl : Finset (TrackD.Piece d)) (j : ℕ)
    (E : Finset (Poly d)) (g : Poly d) (α : RPoint d → AffineVariety d) :
    Finset (RPoint d) :=
  (TrackD.poolPts pl).filter (fun q =>
    TrackD.JacRegularAt allpl j E g (TrackD.toC q) ∧ keepRealCarrier (α q))

/-- One finite common physical test system, with loss on every original
piece. There is no graph, projected image or rank hypothesis. -/
structure CommonPhysicalTests {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (M : CommonPoolProfile T)
    (j : ℕ) (τ : ℝ) (i : ℕ) (θ : ℝ) where
  equations : Finset (Poly d)
  minor : Poly d
  equations_degree : ∀ f ∈ equations,
    (f.totalDegree : ℝ) ≤ TrackD.testDeg (TrackD.cfgB (regime.P i)) (M.s i) τ
  minor_degree : (minor.totalDegree : ℝ) ≤
    TrackD.testDeg (TrackD.cfgB (regime.P i)) (M.s i) τ
  carrier_equations : ∀ Z, TrackD.PoolCarrier (T.sources i ∪ T.targets i) j Z →
    ∀ f ∈ equations, f ∈ Z.ideal
  minor_rank : ∀ y : Point d, MvPolynomial.eval y minor ≠ 0 →
    Module.finrank ℂ (TrackD.jacKer equations y) + j ≤ d
  regularity_loss : ∀ X ∈ T.sources i ∪ T.targets i,
    ((X.pts.filter (fun q => ¬ TrackD.JacRegularAt (T.sources i ∪ T.targets i)
      j equations minor (TrackD.toC q))).card : ℝ) ≤ (θ / 2) * X.pts.card
  nonreal_loss : ∀ X ∈ T.sources i ∪ T.targets i,
    ((X.pts.filter (fun q => ∃ Z ∈ X.path.localCarriers j (TrackD.toC q),
      TrackD.IsFlat Z ∧ ¬ TrackD.IsRealFlat Z)).card : ℝ) ≤ (θ / 2) * X.pts.card

/-- Choices fixed before every later graph and image family. The supported
map is defined on the original points, including those subsequently deleted. -/
structure CommonPhysicalSequence {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (M : CommonPoolProfile T) (j : ℕ) (τ : ℝ) where
  equations : ℕ → Finset (Poly d)
  minor : ℕ → Poly d
  owner : ℕ → RPoint d → AffineVariety d
  supported : ∀ i, TrackD.CarrierAssignment (T.sources i ∪ T.targets i) j (owner i)
  terminal : j = d - 1 → ∀ i q, q ∈ TrackD.poolPts (T.sources i ∪ T.targets i) →
    ∀ Y, T.terminal i q = some Y → owner i q = Y
  tests : ∀ᶠ i in atTop,
    (∀ f ∈ equations i, (f.totalDegree : ℝ) ≤
      TrackD.testDeg (TrackD.cfgB (regime.P i)) (M.s i) τ) ∧
    (minor i).totalDegree ≤ ⌊TrackD.testDeg (TrackD.cfgB (regime.P i)) (M.s i) τ⌋₊ ∧
    (∀ Z, TrackD.PoolCarrier (T.sources i ∪ T.targets i) j Z →
      ∀ f ∈ equations i, f ∈ Z.ideal) ∧
    (∀ y : Point d, MvPolynomial.eval y (minor i) ≠ 0 →
      Module.finrank ℂ (TrackD.jacKer (equations i) y) + j ≤ d)
  source_omissions : Framework.LittleO
    (fun i => (((TrackD.poolPts (T.sources i)) \ retainedCommonPool (T.sources i)
      (T.sources i ∪ T.targets i) j (equations i) (minor i) (owner i)).card : ℝ))
    (fun i => ((TrackD.poolPts (T.sources i)).card : ℝ))
  target_omissions : Framework.LittleO
    (fun i => (((TrackD.poolPts (T.targets i)) \ retainedCommonPool (T.targets i)
      (T.sources i ∪ T.targets i) j (equations i) (minor i) (owner i)).card : ℝ))
    (fun i => ((TrackD.poolPts (T.targets i)).card : ℝ))

namespace CommonPhysicalSequence
variable {F : ConeCoverageSequence regime} {T : SelectedProfileSequence F}
    {M : CommonPoolProfile T} {j : ℕ} {τ : ℝ}

def sources (W : CommonPhysicalSequence T M j τ) (i : ℕ) : Finset (RPoint d) :=
  retainedCommonPool (T.sources i) (T.sources i ∪ T.targets i) j
    (W.equations i) (W.minor i) (W.owner i)

def targets (W : CommonPhysicalSequence T M j τ) (i : ℕ) : Finset (RPoint d) :=
  retainedCommonPool (T.targets i) (T.sources i ∪ T.targets i) j
    (W.equations i) (W.minor i) (W.owner i)

end CommonPhysicalSequence
end
end DistinctDistances.SparseCones
