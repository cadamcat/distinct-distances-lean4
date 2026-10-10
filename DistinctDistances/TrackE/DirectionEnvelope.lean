import DistinctDistances.TrackE.DirectionEnvelopeInputs
import DistinctDistances.TrackD.Profiles.RegularityChosenCuts

/-! Force complete projected carriers into the later row envelope, then use
the actual-center batch degree bound (sc:separated-rank, sparse-cones.tex:721–751). -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- `sc:separated-rank.capture`: individual proper cuts capture only negligible
physical target mass, uniformly over every later center and row subset. -/
theorem direction_envelope_failures_small (S : LimitingSeparatedProfile regime)
    (u : ProfilePlateau S) (D : TrackA.SeparatedDepthData regime u.val.val)
    (hD : DepthFromProfile S D) (τ : ℝ)
    (hτ : S.b ⟨u.val.val - 1, by have := u.val.isLt; omega⟩ < τ ∧ τ < S.b u.val) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ i in atTop,
      ∀ p : Point d, ∀ Q : Finset (RPoint d), Q ⊆ (S.sequence.target i).pts →
        (∀ q ∈ Q, TrackD.toC q ≠ p) →
        ((directionEnvelopeFailures D i p Q
          ⌊TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ⌋₊).card : ℝ)
          ≤ δ * (S.sequence.target i).pts.card := by
  classical
  intro δ hδ
  obtain ⟨ξ, hξ, hplateau⟩ := target_plateau_margin S u τ hτ
  obtain ⟨θ₁, hθ₁, η, hη, hηξ, s₁, hcuts⟩ := TrackD.prof_regularity_cuts_with_margin d
    regime.dimension_ge_three δ hδ ξ hξ 1 le_rfl
  filter_upwards [S.sequence.good θ₁ hθ₁ η hη 1 le_rfl,
    hplateau, S.sequence.target_grows.eventually_ge_atTop s₁, target_test_degree S τ]
    with i hgood hplateaui hwidth htest
  intro p Q hQ hneq
  let L : ℕ := ⌊TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ⌋₊
  obtain ⟨g, hgdeg, hgproper, hgzero⟩ := direction_envelope_proper_cuts p Q L
  have hdegree : ∀ Z : AffineVariety d, ((g Z).totalDegree : ℝ) ≤
      1 * TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ := by
    intro Z
    have hnat : ((g Z).totalDegree : ℝ) ≤ (L : ℝ) := by exact_mod_cast hgdeg Z
    have hfloor : (L : ℝ) ≤ TrackD.testDeg (TrackD.cfgB (regime.P i))
        (S.sequence.target i).width τ := Nat.floor_le (by linarith)
    exact hnat.trans (by simpa only [one_mul] using hfloor)
  have hcap := hcuts (regime.P i) (S.sequence.target i) hgood.2 hwidth
    u.val.val u.val.isLt τ hplateaui htest g hdegree
  have hsub : directionEnvelopeFailures D i p Q L ⊆
      (S.sequence.target i).pts.filter (fun q =>
        ∃ Z ∈ (S.sequence.target i).path.localCarriers u.val.val (TrackD.toC q),
          g Z ∉ Z.ideal ∧ MvPolynomial.eval (TrackD.toC q) (g Z) = 0) := by
    intro q hq
    obtain ⟨hqQ, houtside⟩ := Finset.mem_filter.mp hq
    have hqTarget := hQ hqQ
    have hqD : TrackD.toC q ∈ D.targets i := by
      rw [(hD.2.2.2 i).2.1]
      exact Finset.mem_image.mpr ⟨q, hqTarget, rfl⟩
    have hlocal : D.owner i (TrackD.toC q) ∈
        (S.sequence.target i).path.localCarriers u.val.val (TrackD.toC q) :=
      ⟨(hD.2.2.2 i).2.2.2.1 q hqTarget, D.owner_contains i _ hqD⟩
    exact Finset.mem_filter.mpr ⟨hqTarget,
      ⟨D.owner i (TrackD.toC q), hlocal, hgproper _ houtside,
        hgzero _ q hqQ (hneq q hqQ)⟩⟩
  have hcard : ((directionEnvelopeFailures D i p Q L).card : ℝ) ≤
      (((S.sequence.target i).pts.filter (fun q =>
        ∃ Z ∈ (S.sequence.target i).path.localCarriers u.val.val (TrackD.toC q),
          g Z ∉ Z.ideal ∧ MvPolynomial.eval (TrackD.toC q) (g Z) = 0)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  exact hcard.trans hcap

/-- `sc:separated-rank.envelope-degree`: every later dense surviving row
subset supplies a pure family of complete projected carriers inside its
envelope, with positive assigned mass and A's adaptive projected-degree bound. -/
theorem dense_direction_envelope_family {α : Type*} [Fintype α]
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
        ∃ J : AffineFamily.Family d,
          J ⊆ (H.data (plateau a)).retained i (H.batch.bad a i) p ∧
          (∀ Y ∈ J, (radialImage p Y).Subvariety (rowDirectionEnvelope p Q
            ⌊TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ⌋₊)) ∧
          ProjectiveFamily.IsPure (TrackA.projectedFamily p J) (d - (plateau a).val.val) ∧
          (ρ / 2) * (((S.sequence.target i).pts.image TrackD.toC).card : ℝ) ≤
            (H.data (plateau a)).submass i J ∧
          (H.data (plateau a)).degreeBudget i /
              profileDepthRate S (plateau a).val.val (kind a) i *
              Real.exp (-ε a * (H.data (plateau a)).s i) ≤
            (ProjectiveFamily.degree (TrackA.projectedFamily p J) : ℝ) := by
  classical
  let D := H.data (plateau a)
  have hfrom : DepthFromProfile S D := H.from_profile (plateau a)
  have htargetCard (i : ℕ) : ((S.sequence.target i).pts.image TrackD.toC).card =
      (S.sequence.target i).pts.card :=
    Finset.card_image_of_injective _ profile_toC_injective
  intro ρ hρ
  have hhalf : 0 < ρ / 2 := by positivity
  filter_upwards [direction_envelope_failures_small S (plateau a) D hfrom τ hτ
      (ρ / 2) hhalf, H.batch.dimension, H.batch.degree (ρ / 2) hhalf]
    with i hcapture hdim hdegree
  intro p hp htypical Q hQ hneq hsurvives hdense
  let L : ℕ := ⌊TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ⌋₊
  let G : Finset (RPoint d) := Q \ directionEnvelopeFailures D i p Q L
  let J : AffineFamily.Family d := G.image (fun q => D.owner i (TrackD.toC q))
  have hGQ : G ⊆ Q := Finset.sdiff_subset
  have hqD (q : RPoint d) (hq : q ∈ Q) : TrackD.toC q ∈ D.targets i := by
    rw [(hfrom.2.2.2 i).2.1]
    exact Finset.mem_image.mpr ⟨q, hQ hq, rfl⟩
  have hGtarget : G.image TrackD.toC ⊆ D.targets i := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
    exact hqD q (hGQ hq)
  have hbadSub : directionEnvelopeFailures D i p Q L ⊆ Q :=
    Finset.filter_subset _ _
  have hcard : (G.card : ℝ) + (directionEnvelopeFailures D i p Q L).card = Q.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hbadSub
  have hbad := hcapture p Q hQ hneq
  rw [← htargetCard i] at hbad
  have hGmass : (ρ / 2) * (((S.sequence.target i).pts.image TrackD.toC).card : ℝ) ≤
      (G.card : ℝ) := by linarith
  have hJsub : J ⊆ D.retained i (H.batch.bad a i) p := by
    intro Y hY
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hY
    have hqQ := hGQ hq
    have hqTarget : TrackD.toC q ∈ (S.sequence.target i).pts.image TrackD.toC :=
      Finset.mem_image.mpr ⟨q, hQ hqQ, rfl⟩
    exact H.batch.owner_retained i p (TrackD.toC q) hqTarget (hsurvives q hqQ) a
  have hJenv : ∀ Y ∈ J, (radialImage p Y).Subvariety (rowDirectionEnvelope p Q L) := by
    intro Y hY
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hY
    by_contra hnot
    exact (Finset.mem_sdiff.mp hq).2
      (Finset.mem_filter.mpr ⟨hGQ hq, hnot⟩)
  have houtside : ∀ Y ∈ J, ∃ x ∈ Y.points, x ≠ p := by
    intro Y hY
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hY
    exact ⟨TrackD.toC q, D.owner_contains i _ (hqD q (hGQ hq)), hneq q (hGQ hq)⟩
  have hpure := retained_projected_family_pure D i p (H.batch.bad a i) J hJsub
    (hdim a p hp htypical) houtside
  have hmass : (ρ / 2) * (((S.sequence.target i).pts.image TrackD.toC).card : ℝ) ≤
      D.submass i J := hGmass.trans (assigned_submass_of_real_subset D i G hGtarget)
  exact ⟨J, hJsub, hJenv, hpure, hmass, hdegree a p hp htypical J hJsub hmass⟩

end
end DistinctDistances.SparseCones
