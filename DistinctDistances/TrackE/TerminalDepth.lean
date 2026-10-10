import DistinctDistances.TrackE.TerminalInputs
import DistinctDistances.TrackE.DepthAssembly

/-! Route the persistent global terminal assignment into the actual-center
depth data before any later envelope, center or incidence deletion
(`sc:selection.terminal-depth`, sparse-cones.tex:658–688, 795–928). -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- Coherent final-plateau depth data and the original selected graph after
negligible target omission. Unassigned targets have a fallback in the complete
depth data; every target in the graph keeps its global terminal owner. -/
structure TerminalDepthData {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (S : LimitingSeparatedProfile regime) where
  data : TrackA.SeparatedDepthData regime (d - 1)
  from_profile : DepthFromProfile S data
  hypotheses : data.Hypotheses
  owner_agrees : ∀ i q, q ∈ (S.sequence.target i).pts → ∀ Y,
    T.terminal i q = some Y → data.owner i (TrackD.toC q) = Y
  unassigned_small : Framework.LittleO
    (fun i => (((S.sequence.target i).pts.filter
      (fun q => T.terminal i q = none)).card : ℝ))
    (fun i => ((data.targets i).card : ℝ))
  graph_dense : ∀ᶠ i in atTop, (1 / 4 : ℝ) * (data.centers i).card *
    (data.targets i).card ≤ (terminalSelectedGraph T i).card
  terminal_excluded : ∀ i p q, (p, q) ∈ terminalSelectedGraph T i →
    ¬ TrackD.ProjectsInto (F.family i p) p (data.owner i (TrackD.toC q))
  real_terminal_lines : ∀ i q, q ∈ (S.sequence.target i).pts →
    T.terminal i q ≠ none → TrackD.IsLine (data.owner i (TrackD.toC q)) →
      TrackD.IsRealFlat (data.owner i (TrackD.toC q))

/-- `sc:selection.terminal-depth`: use the literal terminal owner on the final
open target plateau, assemble G5 hypotheses for that same assignment and retain
positive selected density after omitting only globally unassigned columns. -/
theorem selected_terminal_depth {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (S : LimitingSeparatedProfile regime)
    (hsource : ∀ i, T.sources i = {S.sequence.source i})
    (htarget : ∀ i, T.targets i = {S.sequence.target i})
    (hplateau : S.b ⟨(d - 1) - 1, by have := regime.dimension_ge_three; omega⟩ <
      S.b ⟨d - 1, by have := regime.dimension_ge_three; omega⟩) :
    Nonempty (TerminalDepthData T S) := by
  have hd := regime.dimension_ge_three
  have hj₀ : 1 ≤ d - 1 := by omega
  have hjd : d - 1 < d := by omega
  obtain ⟨fallback, hfb⟩ := separated_profile_owners S (d - 1) hjd.le
  have hfbPool : ∀ i, TrackD.CarrierAssignment (T.targets i) (d - 1) (fallback i) := by
    intro i
    rw [htarget i]
    exact hfb i
  let own : ℕ → RPoint d → AffineVariety d :=
    fun i => terminalOwner (T.terminal i) (fallback i)
  have hownPool := terminal_owner_assignment T fallback hfbPool
  have hown : ∀ i, TrackD.CarrierAssignment {S.sequence.target i} (d - 1) (own i) := by
    intro i
    rw [← htarget i]
    exact hownPool i
  obtain ⟨D, hD, howner⟩ := separated_depth_data S (d - 1) hj₀ hjd own hown
  have hHyp : D.Hypotheses := profile_depth_hypotheses S D hD hplateau
  have hsourcePts (i : ℕ) : TrackD.poolPts (T.sources i) = (S.sequence.source i).pts := by
    rw [hsource i]
    simp [TrackD.poolPts]
  have htargetPts (i : ℕ) : TrackD.poolPts (T.targets i) = (S.sequence.target i).pts := by
    rw [htarget i]
    simp [TrackD.poolPts]
  have hsourceCard (i : ℕ) : (D.centers i).card = (TrackD.poolPts (T.sources i)).card := by
    rw [(hD.2.2.2 i).1, hsourcePts i]
    exact Finset.card_image_of_injective _ profile_toC_injective
  have htargetCard (i : ℕ) : (D.targets i).card = (TrackD.poolPts (T.targets i)).card := by
    rw [(hD.2.2.2 i).2.1, htargetPts i]
    exact Finset.card_image_of_injective _ profile_toC_injective
  have hOwner : ∀ i q, q ∈ (S.sequence.target i).pts → ∀ Y,
      T.terminal i q = some Y → D.owner i (TrackD.toC q) = Y := by
    intro i q hq Y hτ
    rw [howner i q hq]
    simp [own, terminalOwner, hτ]
  have hsmall : Framework.LittleO
      (fun i => (((S.sequence.target i).pts.filter
        (fun q => T.terminal i q = none)).card : ℝ))
      (fun i => ((D.targets i).card : ℝ)) := by
    simpa only [htargetPts, htargetCard] using (selected_terminal_omissions_small T).2
  have hdense : ∀ᶠ i in atTop, (1 / 4 : ℝ) * (D.centers i).card *
      (D.targets i).card ≤ (terminalSelectedGraph T i).card := by
    simpa only [hsourceCard, htargetCard] using selected_terminal_graph_dense T
  have hexcluded : ∀ i p q, (p, q) ∈ terminalSelectedGraph T i →
      ¬ TrackD.ProjectsInto (F.family i p) p (D.owner i (TrackD.toC q)) := by
    intro i p q hpq
    obtain ⟨_, hq, hselected, Y, hτ⟩ := (mem_terminalSelectedGraph T i p q).mp hpq
    have hq' : q ∈ (S.sequence.target i).pts := by
      simpa only [htargetPts] using hq
    rw [hOwner i q hq' Y hτ]
    exact hselected.2.2.1 Y hτ
  have hreal : ∀ i q, q ∈ (S.sequence.target i).pts →
      T.terminal i q ≠ none → TrackD.IsLine (D.owner i (TrackD.toC q)) →
        TrackD.IsRealFlat (D.owner i (TrackD.toC q)) := by
    intro i q hq hτne hline
    cases hτ : T.terminal i q with
    | none => exact (hτne hτ).elim
    | some Y =>
      rw [hOwner i q hq Y hτ] at hline ⊢
      exact (T.certificate i).terminal.realLines q Y hτ hline
  exact ⟨{
    data := D
    from_profile := hD
    hypotheses := hHyp
    owner_agrees := hOwner
    unassigned_small := hsmall
    graph_dense := hdense
    terminal_excluded := hexcluded
    real_terminal_lines := hreal }⟩

end
end DistinctDistances.SparseCones
