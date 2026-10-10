import DistinctDistances.TrackE.FinalNarrowBatch

/-! Place complete projections of the unchanged terminal carriers in the
full curve component family, sparse-cones.tex:849–870. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- sc:u-final-curve.capture: failure of complete projection containment
in Env(C_p) has negligible physical mass, uniformly over all later covered
rows and whole-family envelopes. No owner is changed. -/
theorem covering_projection_failures_small (S : LimitingSeparatedProfile regime)
    (u : ProfilePlateau S) (D : TrackA.SeparatedDepthData regime u.val.val)
    (hD : DepthFromProfile S D) (τ : ℝ)
    (hτ : profilePlateauLeft S u < τ ∧ τ < S.b u.val) :
    ∀ ρ : ℝ, 0 < ρ → ∀ᶠ i in atTop,
      ∀ p : Point d, ∀ Q : Finset (RPoint d), Q ⊆ (S.sequence.target i).pts →
        (∀ q ∈ Q, TrackD.toC q ≠ p) → ∀ C : ProjectiveFamily.Family d,
        rowDirections p Q ⊆ (ProjectiveFamily.locus C).points →
        ((coveringProjectionFailures D i p Q C
          ⌊TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ⌋₊).card : ℝ)
          ≤ ρ * (S.sequence.target i).pts.card := by
  classical
  intro ρ hρ
  filter_upwards [direction_envelope_failures_small S u D hD τ (by
    simpa only [profilePlateauLeft] using hτ) ρ hρ] with i hi
  intro p Q hQ hneq C hcover
  let L : ℕ := ⌊TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ⌋₊
  have henv := row_envelope_sub_covering p Q C L hcover
  have hsub : coveringProjectionFailures D i p Q C L ⊆ directionEnvelopeFailures D i p Q L := by
    intro q hq
    obtain ⟨hqQ, houtside⟩ := Finset.mem_filter.mp hq
    refine Finset.mem_filter.mpr ⟨hqQ, ?_⟩
    intro hinside
    apply houtside
    exact le_trans henv hinside
  have hcard : ((coveringProjectionFailures D i p Q C L).card : ℝ) ≤
      ((directionEnvelopeFailures D i p Q L).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  exact hcard.trans (hi p Q hQ hneq)

/-- sc:u-final-curve.terminal-members: after the two actual-label removals,
each retained one-dimensional complete projection is a member of the entire
curve component family. Its owner is the one fixed in the original batch. -/
theorem covering_retained_curve_members {α : Type*} [Fintype α]
    {F : ConeCoverageSequence regime} {T : SelectedProfileSequence F}
    (S : LimitingSeparatedProfile regime)
    {plateau : α → ProfilePlateau S} {kind : α → DepthRateKind} {ε : α → ℝ}
    (H : ProfileDepthBatchData T S plateau kind ε) (a : α)
    (hlast : (plateau a).val.val + 1 = d) (τ : ℝ) :
    ∀ᶠ i in atTop, ∀ p : Point d, ∀ Q : Finset (RPoint d),
      DenseSurvivingDirectionRow H i p Q 0 → ∀ C : ProjectiveFamily.Family d,
      ∀ G : CoveringEnvelopeComponents C
        ⌊TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ⌋₊,
      ∀ q ∈ Q,
        q ∉ coveringProjectionFailures (H.data (plateau a)) i p Q C
          ⌊TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ⌋₊ →
        q ∉ coveringEnvelopeLargeLabels G p Q →
        radialImage p ((H.data (plateau a)).owner i (TrackD.toC q)) ∈
          envelopeDimensionPart G.components 1 := by
  classical
  let D := H.data (plateau a)
  have hfrom := H.from_profile (plateau a)
  filter_upwards [H.batch.dimension] with i hdim
  intro p Q hrow C G q hq hcapture hlarge
  obtain ⟨hp, htypical, hQ, hneq, hsurvives, _⟩ := hrow
  have hqTarget : TrackD.toC q ∈ (S.sequence.target i).pts.image TrackD.toC :=
    Finset.mem_image.mpr ⟨q, hQ hq, rfl⟩
  have hqD : TrackD.toC q ∈ D.targets i := by
    rw [(hfrom.2.2.2 i).2.1]
    exact hqTarget
  have hretained : D.owner i (TrackD.toC q) ∈ D.retained i (H.batch.bad a i) p :=
    H.batch.owner_retained i p (TrackD.toC q) hqTarget (hsurvives q hq) a
  let W := radialImage p (D.owner i (TrackD.toC q))
  have hWdim : W.dimension = 1 := by
    have hh := hdim a p hp htypical _ hretained
    have heq : d - (plateau a).val.val = 1 := by omega
    simpa only [heq] using hh
  have hW : W.IsIrreducible := radialImage_irreducible p _
    (D.carrier_pure i _ (D.owner_member i _ hqD)).1
    ⟨TrackD.toC q, D.owner_contains i _ hqD, hneq q hq⟩
  have hWenv : W.Subvariety (coveringDirectionEnvelope C
      ⌊TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ⌋₊) := by
    by_contra houtside
    exact hcapture (Finset.mem_filter.mpr ⟨hq, houtside⟩)
  obtain ⟨V, hVG, hWV, hdimWV, hequal⟩ := Request.projective_irreducible_container
    _ G.components (fun V hV => (G.spec V hV).1) G.locus W hW hWenv
  let z := radialProjection p (TrackD.toC q) (hneq q hq)
  have hzW : z ∈ W.points := ProjectiveVariety.subset_closure _
    ⟨TrackD.toC q, D.owner_contains i _ hqD, hneq q hq, rfl⟩
  have hzV : z ∈ V.points := by
    intro x hx he f hf
    exact hzW x hx he f (hWV hf)
  have hVsmall : ¬ 2 ≤ V.dimension := by
    intro hVlarge
    exact hlarge (Finset.mem_filter.mpr ⟨hq,
      ⟨hneq q hq, V, hVG, hVlarge, hzV⟩⟩)
  have hVdim : V.dimension = 1 := by omega
  have hWVeq : W = V := hequal (hWdim.trans hVdim.symm)
  change W ∈ envelopeDimensionPart G.components 1
  rw [hWVeq]
  exact Finset.mem_filter.mpr ⟨hVG, hVdim⟩

end
end DistinctDistances.SparseCones
