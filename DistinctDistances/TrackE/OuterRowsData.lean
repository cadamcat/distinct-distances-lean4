import DistinctDistances.TrackE.WindowBranches

/-! The covered graph of the outermost pool, sparse-cones.tex:342–348. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- The selected covered incidences `Γ_0` on the selected source and target
pools: the cone covering, the global terminal deletion and the light-line
restriction of `prof:pair-selection`, at the selection precision. -/
def outerSelectedGraph {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (i : ℕ) : Finset (RPoint d × RPoint d) :=
  (TrackD.poolPts (T.sources i) ×ˢ TrackD.poolPts (T.targets i)).filter (fun pq =>
    TrackD.SelectedIncidence (regime.P i) (F.family i) (T.terminal i)
      (selectionTolerance (T.precision i)) pq.1 pq.2)

end
end DistinctDistances.SparseCones
