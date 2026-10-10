import DistinctDistances.TrackE.DepthBatch
import DistinctDistances.TrackE.TerminalDepth

/-! Instantiate `sc:u-typical` from the literal separated profile and its
persistent terminal assignment (sparse-cones.tex:668–691, 795–928).
Data are chosen once per open plateau, before rates, tolerances and deletions. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d} {α : Type*} [Fintype α]

/-- The three depth denominators in sc:R-first, sc:R-narrow and sc:R-wide. -/
inductive DepthRateKind where
  | first
  | narrow
  | wide
  deriving DecidableEq

/-- A positive-dimensional open plateau in the fixed limiting profile. -/
def ProfilePlateau (S : LimitingSeparatedProfile regime) : Type :=
  {j : Fin d // 1 ≤ j.val ∧
    S.b ⟨j.val - 1, by have := j.isLt; omega⟩ < S.b j}

/-- Literal target-window rates, independent of the later density parameter. -/
def profileDepthRate (S : LimitingSeparatedProfile regime) (j : ℕ)
    (kind : DepthRateKind) (i : ℕ) : ℝ :=
  match kind with
  | .first => regime.B i * Real.exp
      (S.b ⟨0, by have := regime.dimension_ge_three; omega⟩ * (S.sequence.target i).width)
  | .narrow => regime.B i * Real.exp (-(S.sequence.target i).width *
      ∑ t ∈ (Finset.univ : Finset (Fin d)).filter (fun t => j ≤ t.val), S.b t)
  | .wide => regime.B i * Real.exp (-2 * (S.sequence.target i).width)

/-- Only the paper's permitted orientation/dimension branches may use a rate. -/
def profileDepthRateAllowed (S : LimitingSeparatedProfile regime) (j : ℕ)
    (hj : j < d) (kind : DepthRateKind) : Prop :=
  match kind with
  | .first => True
  | .narrow => Tendsto (fun i => (S.sequence.source i).width /
      (S.sequence.target i).width) atTop (𝓝 0)
  | .wide => Tendsto (fun i => (S.sequence.target i).width /
      (S.sequence.source i).width) atTop (𝓝 0) ∧
      0 < S.b ⟨j, hj⟩ ∧ d - j < d - 1

/-- Match the chosen literal rate to A's exact conclusion using the G5
hypotheses for the same assignment and the same open plateau. -/
theorem profile_depth_rate_conclusion {j : ℕ}
    (S : LimitingSeparatedProfile regime) (D : TrackA.SeparatedDepthData regime j)
    (hD : DepthFromProfile S D)
    (hplateau : S.b ⟨j - 1, by have := D.j_lt; omega⟩ < S.b ⟨j, D.j_lt⟩)
    (kind : DepthRateKind) (hkind : profileDepthRateAllowed S j D.j_lt kind)
    (ε : ℝ) (hε : 0 < ε) :
    D.ProjectedDegreeConclusion (profileDepthRate S j kind) ε := by
  have hhyp : D.Hypotheses := profile_depth_hypotheses S D hD hplateau
  have hconc := TrackA.dep_projected_degree D hhyp ε hε
  cases kind with
  | first =>
    have heq : D.firstRate = profileDepthRate S j .first := by
      ext i
      unfold TrackA.SeparatedDepthData.firstRate TrackA.SeparatedDepthData.cutDegree profileDepthRate
      rw [hD.2.2.1, hD.1]
    rw [← heq]
    exact hconc.1
  | narrow =>
    have heq : D.narrowRate = profileDepthRate S j .narrow := by
      ext i
      unfold TrackA.SeparatedDepthData.narrowRate profileDepthRate
      rw [hD.2.2.1, hD.1]
    rw [← heq]
    apply hconc.2.1
    dsimp [profileDepthRateAllowed] at hkind
    simpa only [hD.2.1, hD.1] using hkind
  | wide =>
    have heq : D.wideRate = profileDepthRate S j .wide := by
      ext i
      unfold TrackA.SeparatedDepthData.wideRate profileDepthRate
      rw [hD.1]
    rw [← heq]
    dsimp [profileDepthRateAllowed] at hkind
    obtain ⟨hratio, hb, hk⟩ := hkind
    apply hconc.2.2
    · simpa only [hD.1, hD.2.1] using hratio
    · simpa only [hD.2.2.1] using hb
    · exact hk

/-- All applications at a given plateau use one fixed depth datum. In the
final curve plateau its owner agrees with the globally recorded terminal map. -/
structure ProfileDepthBatchData {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (S : LimitingSeparatedProfile regime)
    (plateau : α → ProfilePlateau S) (kind : α → DepthRateKind) (ε : α → ℝ) where
  data : (u : ProfilePlateau S) → TrackA.SeparatedDepthData regime u.val.val
  from_profile : ∀ u, DepthFromProfile S (data u)
  hypotheses : ∀ u, (data u).Hypotheses
  terminal_owner : ∀ u, u.val.val = d - 1 →
    ∀ i q, q ∈ (S.sequence.target i).pts → ∀ Y,
      T.terminal i q = some Y → (data u).owner i (TrackD.toC q) = Y
  terminal_excluded : ∀ u, u.val.val = d - 1 →
    ∀ i p q, (p, q) ∈ terminalSelectedGraph T i →
      ¬ TrackD.ProjectsInto (F.family i p) p ((data u).owner i (TrackD.toC q))
  real_terminal_lines : ∀ u, u.val.val = d - 1 →
    ∀ i q, q ∈ (S.sequence.target i).pts → T.terminal i q ≠ none →
      TrackD.IsLine ((data u).owner i (TrackD.toC q)) →
        TrackD.IsRealFlat ((data u).owner i (TrackD.toC q))
  batch : DepthBatchData (fun a => (plateau a).val.val) (fun a => data (plateau a))
    (fun i => (S.sequence.source i).pts.image TrackD.toC)
    (fun i => (S.sequence.target i).pts.image TrackD.toC)
    (fun a => profileDepthRate S (plateau a).val.val (kind a)) ε

/-- `sc:u-typical.profile-batch`: construct all coherent plateau data once,
preserve the terminal owner on the final curve, apply A at each permitted rate
and tolerance, and assemble one batch chosen before every later density. -/
theorem selected_profile_depth_batch {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (S : LimitingSeparatedProfile regime)
    (hsource : ∀ i, T.sources i = {S.sequence.source i})
    (htarget : ∀ i, T.targets i = {S.sequence.target i})
    (plateau : α → ProfilePlateau S) (kind : α → DepthRateKind) (ε : α → ℝ)
    (hε : ∀ a, 0 < ε a)
    (hkind : ∀ a, profileDepthRateAllowed S (plateau a).val.val
      (plateau a).val.isLt (kind a)) :
    Nonempty (ProfileDepthBatchData T S plateau kind ε) := by
  classical
  have hlocal (u : ProfilePlateau S) :
      ∃ D : TrackA.SeparatedDepthData regime u.val.val,
        DepthFromProfile S D ∧ D.Hypotheses ∧
        (u.val.val = d - 1 → ∀ i q, q ∈ (S.sequence.target i).pts → ∀ Y,
          T.terminal i q = some Y → D.owner i (TrackD.toC q) = Y) ∧
        (u.val.val = d - 1 → ∀ i p q, (p, q) ∈ terminalSelectedGraph T i →
          ¬ TrackD.ProjectsInto (F.family i p) p (D.owner i (TrackD.toC q))) ∧
        (u.val.val = d - 1 → ∀ i q, q ∈ (S.sequence.target i).pts →
          T.terminal i q ≠ none → TrackD.IsLine (D.owner i (TrackD.toC q)) →
            TrackD.IsRealFlat (D.owner i (TrackD.toC q))) := by
    by_cases hlast : u.val.val = d - 1
    · have hgap : S.b ⟨u.val.val - 1, by have := u.val.isLt; omega⟩ <
          S.b ⟨u.val.val, u.val.isLt⟩ := u.property.2
      have hfinalGap : S.b ⟨(d - 1) - 1, by have := regime.dimension_ge_three; omega⟩ <
          S.b ⟨d - 1, by have := regime.dimension_ge_three; omega⟩ := by
        simpa only [hlast] using hgap
      obtain ⟨E⟩ := selected_terminal_depth T S hsource htarget hfinalGap
      rw [hlast]
      exact ⟨E.data, E.from_profile, E.hypotheses, fun _ => E.owner_agrees,
        fun _ => E.terminal_excluded, fun _ => E.real_terminal_lines⟩
    · obtain ⟨owner, howner⟩ := separated_profile_owners S u.val.val u.val.isLt.le
      obtain ⟨D, hD, _⟩ := separated_depth_data S u.val.val u.property.1 u.val.isLt
        owner howner
      exact ⟨D, hD, profile_depth_hypotheses S D hD u.property.2,
        fun h => (hlast h).elim, fun h => (hlast h).elim, fun h => (hlast h).elim⟩
  choose data hfrom hhyp howner hexcluded hreal using hlocal
  have hcenters : ∀ a i, (data (plateau a)).centers i =
      (S.sequence.source i).pts.image TrackD.toC :=
    fun a i => ((hfrom (plateau a)).2.2.2 i).1
  have htargets : ∀ a i, (data (plateau a)).targets i =
      (S.sequence.target i).pts.image TrackD.toC :=
    fun a i => ((hfrom (plateau a)).2.2.2 i).2.1
  have hconclusion : ∀ a, (data (plateau a)).ProjectedDegreeConclusion
      (profileDepthRate S (plateau a).val.val (kind a)) (ε a) := by
    intro a
    exact profile_depth_rate_conclusion S (data (plateau a)) (hfrom (plateau a))
      (plateau a).property.2 (kind a) (hkind a) (ε a) (hε a)
  obtain ⟨batch⟩ := projected_degree_batch (fun a => (plateau a).val.val)
    (fun a => data (plateau a))
    (fun i => (S.sequence.source i).pts.image TrackD.toC)
    (fun i => (S.sequence.target i).pts.image TrackD.toC)
    (fun a => profileDepthRate S (plateau a).val.val (kind a)) ε
    hcenters htargets hconclusion
  exact ⟨{
    data := data
    from_profile := hfrom
    hypotheses := hhyp
    terminal_owner := howner
    terminal_excluded := hexcluded
    real_terminal_lines := hreal
    batch := batch }⟩

end
end DistinctDistances.SparseCones
