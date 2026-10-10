import DistinctDistances.TrackA.DepthDefinitions

/-! Counting the fixed target assignment used by actual-center depth.
`sparse-cones.tex:889–905`: the exceptional physical carriers are chosen using
their complete projected images, while their mass uses the earlier assignment. -/

namespace DistinctDistances.SparseCones

open scoped BigOperators

noncomputable section

open Classical in
/-- Sum the disjoint fibers of the persistent owner map. Carrier membership
may be selected after the center and after the envelope; the assignment is fixed. -/
theorem submass_eq_assigned_card {d j : ℕ} {regime : Regime d}
    (D : TrackA.SeparatedDepthData regime j) (i : ℕ) (J : AffineFamily.Family d) :
    D.submass i J = (((D.targets i).filter (fun q => D.owner i q ∈ J)).card : ℝ) := by
  classical
  unfold TrackA.SeparatedDepthData.submass TrackA.SeparatedDepthData.mass
  calc
    _ = ∑ Y ∈ J, ∑ q ∈ (D.targets i).filter (fun q => D.owner i q = Y), (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro Y hY
      simp
    _ = ∑ q ∈ (D.targets i).filter (fun q => D.owner i q ∈ J), (1 : ℝ) :=
      Finset.sum_fiberwise_eq_sum_filter (D.targets i) J (D.owner i) (fun _ => (1 : ℝ))
    _ = _ := by simp

end

end DistinctDistances.SparseCones
