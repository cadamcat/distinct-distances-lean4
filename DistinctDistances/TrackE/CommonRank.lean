import DistinctDistances.TrackE.CommonProfiles
import DistinctDistances.TrackE.TerminalInputs

/-! The literal common-window label rank, sparse-cones.tex:216–316.
The chart and graph are quantified after the original physical pools. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- Rank of the actual affine chart labels, including the source coordinate. -/
def commonLabelRank (i₀ : Fin d) (Γ : Finset (RPoint d × RPoint d)) (L : ℕ) : ℕ :=
  restrictionRank ((fun pq : RPoint d × RPoint d =>
    TrackD.labelPt i₀ (TrackD.toC pq.1) (TrackD.toC pq.2)) ''
      (Γ : Set (RPoint d × RPoint d))) L

/-- Last limiting cut time, with zero-based paper indices. -/
def commonLastTime {F : ConeCoverageSequence regime} {T : SelectedProfileSequence F}
    (M : CommonPoolProfile T) : ℝ :=
  M.b ⟨d - 1, by have := regime.dimension_ge_three; omega⟩

/-- The exact right side of sc:label-rank, before its logarithmic tolerance. -/
def commonRankTarget {F : ConeCoverageSequence regime} {T : SelectedProfileSequence F}
    (M : CommonPoolProfile T) (i : ℕ) (τ : ℝ) : ℝ :=
  (TrackD.sigma (regime.B i) (M.s i) M.b τ)^2 *
    min 1 (TrackD.testDeg (regime.B i) (M.s i) τ /
      (TrackD.cutScale (regime.B i) (M.s i) M.b
        ⟨0, by have := regime.dimension_ge_three; omega⟩ *
       TrackD.cutScale (regime.B i) (M.s i) M.b
        ⟨1, by have := regime.dimension_ge_three; omega⟩))

end
end DistinctDistances.SparseCones
