import DistinctDistances.TrackE.DirectionGroupInputs

/-! Dimension grouping of later direction envelopes on genuine physical rows
(`sc:separated-rank`, sparse-cones.tex:721–751). -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- `sc:separated-rank.dimension-group`: every later dense surviving row has
a dense dimension group, with one component choice per projected member and
with the original physical owner and the fixed batch deletions unchanged. -/
theorem dense_direction_envelope_group {α : Type*} [Fintype α]
    {F : ConeCoverageSequence regime} {T : SelectedProfileSequence F}
    (S : LimitingSeparatedProfile regime)
    {plateau : α → ProfilePlateau S} {kind : α → DepthRateKind} {ε : α → ℝ}
    (H : ProfileDepthBatchData T S plateau kind ε) (a : α) (τ : ℝ)
    (hτ : S.b ⟨(plateau a).val.val - 1, by have := (plateau a).val.isLt; omega⟩ < τ ∧
      τ < S.b (plateau a).val) :
    ∀ ρ : ℝ, 0 < ρ → ∀ᶠ i in atTop,
      ∀ p ∈ (S.sequence.source i).pts.image TrackD.toC, p ∉ H.batch.badCenters i →
      ∀ Q : Finset (RPoint d), Q ⊆ (S.sequence.target i).pts →
        (∀ q ∈ Q, TrackD.toC q ≠ p) →
        (∀ q ∈ Q, TrackD.toC q ∉ batchBadTargets (fun a => H.data (plateau a))
          (fun i => (S.sequence.target i).pts.image TrackD.toC) H.batch.bad i p) →
        ρ * (((S.sequence.target i).pts.image TrackD.toC).card : ℝ) ≤ Q.card →
        ∃ G : DirectionEnvelopeGroup (H.data (plateau a)) i p Q
          ⌊TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ⌋₊
          (H.batch.bad a i),
          (ρ / (2 * (d + 1 : ℝ))) *
            (((S.sequence.target i).pts.image TrackD.toC).card : ℝ) ≤ G.row.card := by
  classical
  let D := H.data (plateau a)
  have hfrom : DepthFromProfile S D := H.from_profile (plateau a)
  have htargetCard (i : ℕ) : ((S.sequence.target i).pts.image TrackD.toC).card =
      (S.sequence.target i).pts.card :=
    Finset.card_image_of_injective _ profile_toC_injective
  intro ρ hρ
  have hhalf : 0 < ρ / 2 := by positivity
  filter_upwards [direction_envelope_failures_small S (plateau a) D hfrom τ hτ
      (ρ / 2) hhalf, H.batch.dimension] with i hcapture hdim
  intro p hp htypical Q hQ hneq hsurvives hdense
  let L : ℕ := ⌊TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ⌋₊
  let V := rowDirectionEnvelope p Q L
  let R : Finset (RPoint d) := Q \ directionEnvelopeFailures D i p Q L
  let J : AffineFamily.Family d := R.image (fun q => D.owner i (TrackD.toC q))
  have hRQ : R ⊆ Q := Finset.sdiff_subset
  have hqD (q : RPoint d) (hq : q ∈ Q) : TrackD.toC q ∈ D.targets i := by
    rw [(hfrom.2.2.2 i).2.1]
    exact Finset.mem_image.mpr ⟨q, hQ hq, rfl⟩
  have hbadSub : directionEnvelopeFailures D i p Q L ⊆ Q := Finset.filter_subset _ _
  have hcard : (R.card : ℝ) + (directionEnvelopeFailures D i p Q L).card = Q.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hbadSub
  have hbad := hcapture p Q hQ hneq
  rw [← htargetCard i] at hbad
  have hRmass : (ρ / 2) * (((S.sequence.target i).pts.image TrackD.toC).card : ℝ) ≤
      (R.card : ℝ) := by linarith
  have hJsub : J ⊆ D.retained i (H.batch.bad a i) p := by
    intro Y hY
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hY
    have hqQ := hRQ hq
    have hqTarget : TrackD.toC q ∈ (S.sequence.target i).pts.image TrackD.toC :=
      Finset.mem_image.mpr ⟨q, hQ hqQ, rfl⟩
    exact H.batch.owner_retained i p (TrackD.toC q) hqTarget (hsurvives q hqQ) a
  have hJenv : ∀ Y ∈ J, (radialImage p Y).Subvariety V := by
    intro Y hY
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hY
    by_contra hnot
    exact (Finset.mem_sdiff.mp hq).2 (Finset.mem_filter.mpr ⟨hRQ hq, hnot⟩)
  have houtside : ∀ Y ∈ J, ∃ x ∈ Y.points, x ≠ p := by
    intro Y hY
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hY
    exact ⟨TrackD.toC q, D.owner_contains i _ (hqD q (hRQ hq)), hneq q (hRQ hq)⟩
  have hpure := retained_projected_family_pure D i p (H.batch.bad a i) J hJsub
    (hdim a p hp htypical) houtside
  have henvspec := (Bridges.projective_envelope d (rowDirections p Q) L).choose_spec
  obtain ⟨C, hC, hlocus⟩ := Request.homogeneous_envelope_carriers d
    regime.dimension_ge_three L (Bridges.homogeneousEquations (rowDirections p Q) L)
    (fun f hf => hf.1) V henvspec.1
  have hdefined : ProjectiveFamily.ComponentsDefinedInDegree C L := by
    refine ⟨Bridges.homogeneousEquations (rowDirections p Q) L, ?_, ?_⟩
    · intro f hf
      exact ⟨L, le_rfl, hf.1⟩
    · intro W hW
      exact henvspec.2.2 W (hC W hW).2.1
  have hcontainers : ∀ W ∈ TrackA.projectedFamily p J,
      ∃ U ∈ C, W.Subvariety U ∧ W.dimension ≤ U.dimension ∧
        (W.dimension = U.dimension → W = U) := by
    intro W hW
    have hWV : W.Subvariety V := by
      obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hW
      exact hJenv Y hY
    exact Request.projective_irreducible_container V C
      (fun U hU => (hC U hU).1) hlocus W (hpure W hW).1 hWV
  let choice (W : ProjectiveVariety d) : ProjectiveVariety d :=
    if hW : W ∈ TrackA.projectedFamily p J then (hcontainers W hW).choose else W
  have hchoice (W : ProjectiveVariety d) (hW : W ∈ TrackA.projectedFamily p J) :
      choice W ∈ C ∧ W.Subvariety (choice W) ∧ W.dimension ≤ (choice W).dimension ∧
        (W.dimension = (choice W).dimension → W = choice W) := by
    simpa only [choice, dif_pos hW] using (hcontainers W hW).choose_spec
  have hWmem (q : RPoint d) (hq : q ∈ R) :
      radialImage p (D.owner i (TrackD.toC q)) ∈ TrackA.projectedFamily p J :=
    Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hq)
  let f (q : RPoint d) : ℕ := (choice (radialImage p (D.owner i (TrackD.toC q)))).dimension
  have hf : ∀ q ∈ R, d - (plateau a).val.val ≤ f q ∧ f q ≤ d := by
    intro q hq
    have hch := hchoice _ (hWmem q hq)
    have hdimq := (hpure _ (hWmem q hq)).2
    exact ⟨hdimq.symm.trans_le hch.2.2.1, (hC _ hch.1).2.2⟩
  obtain ⟨h, hlh, hhd, hrow⟩ := finite_dimension_row_pigeonhole R f
    (d - (plateau a).val.val) (Nat.sub_le _ _) hf
  let R' := R.filter (fun q => f q = h)
  have hR'R : R' ⊆ R := Finset.filter_subset _ _
  let G : DirectionEnvelopeGroup D i p Q L (H.batch.bad a i) :=
    { components := C
      components_spec := hC
      components_locus := hlocus
      components_defined := hdefined
      dimension := h
      dimension_ge := hlh
      dimension_le := hhd
      choice := choice
      row := R'
      row_subset := hR'R.trans hRQ
      owner_retained := by
        intro q hq
        exact hJsub (Finset.mem_image_of_mem _ (hR'R hq))
      owner_dimension := by
        intro q hq
        exact (hpure _ (hWmem q (hR'R hq))).2
      chosen_member := by
        intro q hq
        exact Finset.mem_filter.mpr
          ⟨(hchoice _ (hWmem q (hR'R hq))).1, (Finset.mem_filter.mp hq).2⟩
      chosen_contains := by
        intro q hq
        exact (hchoice _ (hWmem q (hR'R hq))).2.1
      chosen_equal := by
        intro q hq heq
        apply (hchoice _ (hWmem q (hR'R hq))).2.2.2
        exact heq.trans (Finset.mem_filter.mp hq).2.symm }
  refine ⟨G, ?_⟩
  have htotal : (ρ / 2) * (((S.sequence.target i).pts.image TrackD.toC).card : ℝ) ≤
      (d + 1 : ℝ) * (R'.card : ℝ) := hRmass.trans hrow
  change (ρ / (2 * (d + 1 : ℝ))) *
    (((S.sequence.target i).pts.image TrackD.toC).card : ℝ) ≤ (R'.card : ℝ)
  calc
    _ = ((ρ / 2) * (((S.sequence.target i).pts.image TrackD.toC).card : ℝ)) /
        (d + 1 : ℝ) := by
      field_simp [show (d + 1 : ℝ) ≠ 0 by positivity] <;> ring
    _ ≤ (R'.card : ℝ) := (div_le_iff₀ (by positivity)).mpr
      (by simpa only [mul_comm] using htotal)

end
end DistinctDistances.SparseCones
