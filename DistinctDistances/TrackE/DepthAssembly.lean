import DistinctDistances.TrackE.DepthProfile
import DistinctDistances.TrackE.DepthDataCore
import DistinctDistances.TrackE.InitialNoCapture
import DistinctDistances.TrackE.ProfileBudgets
import DistinctDistances.TrackE.NarrowInputs
import DistinctDistances.TrackE.FirstCutInputs
import DistinctDistances.TrackE.FirstCutProfile
import DistinctDistances.TrackE.WideSource
import DistinctDistances.TrackE.WideAssignments

/-!
`G5`: the bridge from the recorded profile pieces to the actual-center
depth interface (`depth.tex:4–16, 93–150, 152–262`; sparse-cones.tex:654–688).
-/

namespace DistinctDistances.SparseCones

open Filter
open scoped Topology BigOperators Classical

noncomputable section

/-- Identity of the actual samples, limiting profile, persistent assignments
and path equations. No degree, depth, or no-capture conclusion is a field. -/
def DepthFromProfile {d j : ℕ} {regime : Regime d}
    (S : LimitingSeparatedProfile regime) (D : TrackA.SeparatedDepthData regime j) : Prop :=
  D.s = (fun i => (S.sequence.target i).width) ∧
  D.v = (fun i => (S.sequence.source i).width) ∧ D.b = S.b ∧
  ∀ i,
    D.centers i = (S.sequence.source i).pts.image TrackD.toC ∧
    D.targets i = (S.sequence.target i).pts.image TrackD.toC ∧
    D.carriers i = (D.targets i).image (D.owner i) ∧
    (∀ q ∈ (S.sequence.target i).pts,
      (S.sequence.target i).path.IsCarrier j (D.owner i (TrackD.toC q))) ∧
    D.pathEquations i =
      (Finset.univ.filter (fun t : Fin d => t.val < j)).image (S.sequence.target i).path.cut

/-- Choose carriers once from the recorded path, before any center, envelope,
or later incidence deletion. A prescribed terminal assignment can be substituted
whenever it supplies the same carrier membership. -/
theorem separated_profile_owners {d : ℕ} {regime : Regime d}
    (S : LimitingSeparatedProfile regime) (j : ℕ) (hj : j ≤ d) :
    ∃ owner : ℕ → RPoint d → AffineVariety d,
      ∀ i, TrackD.CarrierAssignment {S.sequence.target i} j (owner i) := by
  obtain ⟨owner, howner⟩ := source_carrier_owners S.swap j hj
  refine ⟨owner, fun i => ?_⟩
  simpa [LimitingSeparatedProfile.swap, SeparatedProfileSequence.swap] using howner i

/-- `G5.data`: construct A's coherent sequence object from the actual pieces
and a fixed physical assignment. Centers and targets are unchanged; the owner
map agrees with that assignment at every target point. -/
theorem separated_depth_data {d : ℕ} {regime : Regime d}
    (S : LimitingSeparatedProfile regime) (j : ℕ) (hj₀ : 1 ≤ j) (hjd : j < d)
    (owner : ℕ → RPoint d → AffineVariety d)
    (howner : ∀ i, TrackD.CarrierAssignment {S.sequence.target i} j (owner i)) :
    ∃ D : TrackA.SeparatedDepthData regime j,
      DepthFromProfile S D ∧
      ∀ i q, q ∈ (S.sequence.target i).pts → D.owner i (TrackD.toC q) = owner i q := by
  simpa only [DepthFromProfile] using separated_depth_data_core S j hj₀ hjd owner howner

/-- Degree and mass budgets use the limiting cut times of this same profile,
and every later subfamily of the fixed target carriers. -/
theorem profile_depth_budgets {d j : ℕ} {regime : Regime d}
    (S : LimitingSeparatedProfile regime) (D : TrackA.SeparatedDepthData regime j)
    (hD : DepthFromProfile S D) : D.DegreeBudgets := by
  exact profile_depth_budgets_core S D hD.1 hD.2.2.1
    (fun i => (hD.2.2.2 i).2.1)
    (fun i => (hD.2.2.2 i).2.2.1)
    (fun i => (hD.2.2.2 i).2.2.2.1)

/-- Uniform bounded-degree no-capture on the source's initial plateau also
controls all proper complex affine flats. -/
theorem profile_depth_initial {d j : ℕ} {regime : Regime d}
    (S : LimitingSeparatedProfile regime) (D : TrackA.SeparatedDepthData regime j)
    (hD : DepthFromProfile S D) : D.InitialNoCapture ∧ D.UniformFlatCap := by
  have hcenters : ∀ i, D.centers i = (S.sequence.source i).pts.image TrackD.toC :=
    fun i => (hD.2.2.2 i).1
  have hinitial : D.InitialNoCapture := by
    intro q
    simpa only [hcenters] using source_initial_no_capture S q
  exact ⟨hinitial, uniform_flat_cap_of_initial D hinitial⟩

/-- First-cluster common regularity gives A's first-cut input, including when
several limiting cut times coincide. The target is on an open plateau. -/
theorem profile_depth_first_cut {d j : ℕ} {regime : Regime d}
    (S : LimitingSeparatedProfile regime) (D : TrackA.SeparatedDepthData regime j)
    (hD : DepthFromProfile S D) (hplateau : S.b ⟨j - 1, by have := D.j_lt; omega⟩ <
      S.b ⟨j, D.j_lt⟩) : D.FirstCutInput := by
  apply first_cut_of_fixed_precision D
  apply profile_first_cut_certificates S D hD.1 hD.2.2.1
    (fun i => (hD.2.2.2 i).2.1) _ hplateau
  intro i Y hY
  rw [(hD.2.2.2 i).2.2.1] at hY
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hY
  rw [(hD.2.2.2 i).2.1] at hq
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
  refine ⟨(hD.2.2.2 i).2.2.2.1 x hx, x, hx, ?_⟩
  apply D.owner_contains
  rw [(hD.2.2.2 i).2.1]
  exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

/-- All last-cut source equations isolate the narrower center piece, at
degree `B exp(o(s))`; this does not require the source equations to be globally pure. -/
theorem profile_depth_narrow {d j : ℕ} {regime : Regime d}
    (S : LimitingSeparatedProfile regime) (D : TrackA.SeparatedDepthData regime j)
    (hD : DepthFromProfile S D)
    (hnarrow : Tendsto (fun i => D.v i / D.s i) atTop (𝓝 0)) : D.NarrowInput := by
  have hcenters : ∀ i, D.centers i = (S.sequence.source i).pts.image TrackD.toC :=
    fun i => (hD.2.2.2 i).1
  have hratio : Tendsto
      (fun i => (S.sequence.source i).width / (S.sequence.target i).width) atTop (𝓝 0) := by
    simpa only [hD.1, hD.2.1] using hnarrow
  refine ⟨sourceIsolationDegree S, sourceEquations S, ?_, ?_⟩
  · intro i
    simpa only [hcenters] using source_path_isolation S i
  · simpa only [hD.1] using source_isolation_expUpper S hratio

/-- Fix generic lists on the source carriers before choosing actual centers.
The component tests and ignored centers use the same source assignment. -/
theorem profile_depth_wide {d j : ℕ} {regime : Regime d}
    (S : LimitingSeparatedProfile regime) (D : TrackA.SeparatedDepthData regime j)
    (hD : DepthFromProfile S D)
    (hwide : Tendsto (fun i => D.s i / D.v i) atTop (𝓝 0))
    (hb : 0 < D.b ⟨j, D.j_lt⟩) (hk : d - j < d - 1) : D.WideInput := by
  have hbS : 0 < S.b ⟨j, D.j_lt⟩ := by
    simpa only [hD.2.2.1] using hb
  obtain ⟨A⟩ := positive_source_plateau S D.j_lt hbS
  obtain ⟨W⟩ := profile_wide_source_carriers S A
  let T : WideTargetProfile S D := {
    s_eq := hD.1
    v_eq := hD.2.1
    b_eq := hD.2.2.1
    centers_eq := fun i => (hD.2.2.2 i).1
    targets_eq := fun i => (hD.2.2.2 i).2.1
    carriers_eq := fun i => (hD.2.2.2 i).2.2.1
    carrier_path := fun i => (hD.2.2.2 i).2.2.2.1
    budgets := profile_depth_budgets S D hD }
  exact profile_wide_core S D T A W hwide hk

/-- `G5.hypotheses`: assemble the actual profile inputs. There is no adaptive
family or positive density in these inputs; A chooses its deletions afterwards. -/
theorem profile_depth_hypotheses {d j : ℕ} {regime : Regime d}
    (S : LimitingSeparatedProfile regime) (D : TrackA.SeparatedDepthData regime j)
    (hD : DepthFromProfile S D) (hplateau : S.b ⟨j - 1, by have := D.j_lt; omega⟩ <
      S.b ⟨j, D.j_lt⟩) : D.Hypotheses := by
  refine ⟨profile_depth_budgets S D hD, (profile_depth_initial S D hD).2,
    (profile_depth_initial S D hD).1, profile_depth_first_cut S D hD hplateau,
    ?_, ?_⟩
  · intro hratio
    exact profile_depth_narrow S D hD hratio
  · intro hratio hb hk
    exact profile_depth_wide S D hD hratio hb hk

end

end DistinctDistances.SparseCones
