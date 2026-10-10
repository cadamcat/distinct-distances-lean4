import DistinctDistances.TrackE.DepthProfile
import DistinctDistances.TrackE.Directional
import DistinctDistances.TrackE.WideAssignments

/-! The slow diagonal in prof:pair-selection (`profiles.tex:570–618`).
The selected pieces, terminal assignment, and directional families retain their
physical labels. No endpoint contradiction or actual-center depth is an input. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section

variable {d : ℕ} {regime : Regime d}

/-- The unchanged finitary sparse-cones conclusion, before its proof. -/
def SparseConeConclusion (d : ℕ) : Prop :=
  ∃ η δ₀ ε₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧ 0 < ε₀ ∧ ∃ N₀ : ℕ,
    ∀ P : Finset (RPoint d), N₀ ≤ P.card → Mcount P ≤ ε₀ * Ascale d P.card →
    ∀ C : RPoint d → ProjectiveFamily.Family d,
      (∀ p ∈ P, IsDirectionalFamily (C p)) →
      (∀ p ∈ P, (ProjectiveFamily.degree (C p) : ℝ) ≤ δ₀ * P.card / Ascale d P.card) →
      η * (P.card : ℝ) ^ 2 ≤ (uncoveredPairs P C).card

/-- Actual cone families on a contradiction regime, before profile selection. -/
structure ConeCoverageSequence (regime : Regime d) where
  family : ℕ → RPoint d → ProjectiveFamily.Family d
  delta : ℕ → ℝ
  delta_pos : ∀ i, 0 < delta i
  delta_tendsto : Tendsto delta atTop (𝓝 0)
  directional : ∀ i p, p ∈ regime.P i → TrackD.IsDirectionalFamily (family i p)
  degree : ∀ i p, p ∈ regime.P i →
    (ProjectiveFamily.degree (family i p) : ℝ) ≤ delta i * regime.N i / regime.A i
  coverage : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop,
    (1 - ε) * regime.N i * (regime.N i - 1) ≤
      ((TrackD.coveredPairs (regime.P i) (family i)).card : ℝ)

namespace ConeCoverageSequence
/-- Reindex the original cone families together with their actual configurations. -/
def comp (F : ConeCoverageSequence regime) (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    ConeCoverageSequence (regime.comp φ hφ) := {
  family := fun i => F.family (φ i)
  delta := fun i => F.delta (φ i)
  delta_pos := fun i => F.delta_pos (φ i)
  delta_tendsto := F.delta_tendsto.comp hφ.tendsto_atTop
  directional := fun i => F.directional (φ i)
  degree := fun i => F.degree (φ i)
  coverage := fun ε hε => hφ.tendsto_atTop.eventually (F.coverage ε hε) }
end ConeCoverageSequence

/-- Covered and uncovered ordered pairs partition the literal off-diagonal. -/
theorem covered_uncovered_card (P : Finset (RPoint d))
    (C : RPoint d → ProjectiveFamily.Family d) :
    (TrackD.coveredPairs P C).card + (uncoveredPairs P C).card = P.card * (P.card - 1) := by
  classical
  have htoC (x : RPoint d) : TrackD.toC x = cplx x := rfl
  have hdir (p q : RPoint d) : TrackD.DirIn (C p) p q ↔ DirCovered C p q := by
    simp only [TrackD.DirIn, TrackD.familyPoints, DirCovered, DirMem, htoC,
      Set.mem_iUnion]
    constructor
    · rintro ⟨h, γ, hγ, hproj⟩
      exact ⟨γ, hγ, h, hproj⟩
    · rintro ⟨γ, hγ, h, hproj⟩
      exact ⟨h, γ, hγ, hproj⟩
  have hcovered : TrackD.coveredPairs P C = P.offDiag.filter (fun e =>
      DirCovered C e.1 e.2 ∨ DirCovered C e.2 e.1) := by
    ext e
    simp [TrackD.coveredPairs, Finset.mem_offDiag, hdir, and_assoc]
  have huncovered : uncoveredPairs P C = P.offDiag.filter (fun e =>
      ¬ (DirCovered C e.1 e.2 ∨ DirCovered C e.2 e.1)) := by
    ext e
    simp [uncoveredPairs, not_or]
  rw [hcovered, huncovered, Finset.card_filter_add_card_filter_not]
  rw [Finset.offDiag_card, Nat.mul_sub_left_distrib]
  simp

/-- `sc:failure-sequence`: extract actual cone families from failure of the
finitary conclusion. This lemma must not use the sparse_cones theorem. -/
theorem cone_sequence_of_failure (hd : 3 ≤ d) (hIH : IH d)
    (hfail : ¬ SparseConeConclusion d) :
    ∃ (regime : Regime d), Nonempty (ConeCoverageSequence regime) := by
  classical
  let δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2)
  have hδpos (n : ℕ) : 0 < δ n := by
    dsimp [δ]
    positivity
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    simpa [δ] using hden.const_div_atTop (1 : ℝ)
  have hbad (n : ℕ) :
      ∃ P : Finset (RPoint d), n + 2 ≤ P.card ∧
        Mcount P ≤ δ n * Ascale d P.card ∧
        ∃ C : RPoint d → ProjectiveFamily.Family d,
          (∀ p ∈ P, IsDirectionalFamily (C p)) ∧
          (∀ p ∈ P, (ProjectiveFamily.degree (C p) : ℝ) ≤ δ n * P.card / Ascale d P.card) ∧
          ¬ δ n * (P.card : ℝ) ^ 2 ≤ ((uncoveredPairs P C).card : ℝ) := by
    have hnot : ¬ ∀ P : Finset (RPoint d), n + 2 ≤ P.card →
        Mcount P ≤ δ n * Ascale d P.card →
        ∀ C : RPoint d → ProjectiveFamily.Family d,
          (∀ p ∈ P, IsDirectionalFamily (C p)) →
          (∀ p ∈ P, (ProjectiveFamily.degree (C p) : ℝ) ≤ δ n * P.card / Ascale d P.card) →
          δ n * (P.card : ℝ) ^ 2 ≤ ((uncoveredPairs P C).card : ℝ) := by
      intro hgood
      exact hfail ⟨δ n, δ n, δ n, hδpos n, hδpos n, hδpos n, n + 2, hgood⟩
    by_contra hnone
    apply hnot
    intro P hcard hmass C hdir hdegree
    by_contra hcoverage
    exact hnone ⟨P, hcard, hmass, C, hdir, hdegree, hcoverage⟩
  choose P hP using hbad
  have hCexists (i : ℕ) : ∃ C : RPoint d → ProjectiveFamily.Family d,
      (∀ p ∈ P i, IsDirectionalFamily (C p)) ∧
      (∀ p ∈ P i, (ProjectiveFamily.degree (C p) : ℝ) ≤
        δ i * (P i).card / Ascale d (P i).card) ∧
      ¬ δ i * ((P i).card : ℝ) ^ 2 ≤ ((uncoveredPairs (P i) C).card : ℝ) := by
    rcases hP i with ⟨_, _, hC⟩
    exact hC
  choose C hC using hCexists
  have hcardTwo (i : ℕ) : 2 ≤ (P i).card := by
    have := (hP i).1
    omega
  have hApos (i : ℕ) : 0 < Ascale d (P i).card := by
    unfold Ascale
    have hpos : 0 < (P i).card := by have hi := hcardTwo i; omega
    exact Real.rpow_pos_of_pos (by exact_mod_cast hpos) _
  have hratioBound (i : ℕ) :
      (1 + (distinctDistances (P i) : ℝ)) /
        ((P i).card : ℝ) ^ ((2 : ℝ) / (d : ℝ)) ≤ δ i := by
    apply (div_le_iff₀ (hApos i)).2
    have hmass := (hP i).2.1
    simpa [Mcount, Ascale, add_comm] using hmass
  have hratioNonneg (i : ℕ) :
      0 ≤ (1 + (distinctDistances (P i) : ℝ)) /
        ((P i).card : ℝ) ^ ((2 : ℝ) / (d : ℝ)) := by
    apply div_nonneg
    · positivity
    · exact (hApos i).le
  have hratio : Tendsto (fun i =>
      (1 + (distinctDistances (P i) : ℝ)) /
        ((P i).card : ℝ) ^ ((2 : ℝ) / (d : ℝ))) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hδlim
    · filter_upwards with i
      exact hratioNonneg i
    · filter_upwards with i
      exact hratioBound i
  have hcoverage (ε : ℝ) (hε : 0 < ε) : ∀ᶠ i in atTop,
      (1 - ε) * (P i).card * ((P i).card - 1 : ℝ) ≤
        ((TrackD.coveredPairs (P i) (C i)).card : ℝ) := by
    have hδsmall : ∀ᶠ i in atTop, δ i < ε / 2 :=
      hδlim.eventually (Iio_mem_nhds (by linarith))
    filter_upwards [hδsmall] with i hδi
    let N : ℝ := (P i).card
    let T : ℝ := N * (N - 1)
    have hcardOne : 1 ≤ (P i).card := by have hi := hcardTwo i; omega
    have hN : 2 ≤ N := by
      dsimp [N]
      exact_mod_cast hcardTwo i
    have hTnonneg : 0 ≤ T := mul_nonneg (by linarith) (by linarith)
    have hNfactor : N ≤ 2 * (N - 1) := by nlinarith
    have hNsquare : N ^ 2 ≤ 2 * T := by
      dsimp [T]
      nlinarith
    have hUstrict : ((uncoveredPairs (P i) (C i)).card : ℝ) < δ i * N ^ 2 := by
      have hnot := hC i |>.2.2
      exact lt_of_not_ge (by simpa [N] using hnot)
    have hδT : δ i * N ^ 2 ≤ ε * T := by
      calc
        δ i * N ^ 2 ≤ (ε / 2) * N ^ 2 :=
          mul_le_mul_of_nonneg_right hδi.le (sq_nonneg N)
        _ ≤ (ε / 2) * (2 * T) := mul_le_mul_of_nonneg_left hNsquare (by positivity)
        _ = ε * T := by ring
    have hpartition :
        ((TrackD.coveredPairs (P i) (C i)).card : ℝ) +
          ((uncoveredPairs (P i) (C i)).card : ℝ) = T := by
      have hnat := covered_uncovered_card (P i) (C i)
      have hcast := congrArg (fun k : ℕ => (k : ℝ)) hnat
      simpa [N, T, Nat.cast_mul, Nat.cast_sub hcardOne] using hcast
    have hcoveredLower :
        (1 - ε) * T ≤ ((TrackD.coveredPairs (P i) (C i)).card : ℝ) := by
      nlinarith [hpartition, hUstrict.le.trans hδT]
    simpa [N, T, mul_assoc] using hcoveredLower
  let regime : Regime d := {
    dimension_ge_three := hd
    P := P
    card_ge_two := hcardTwo
    ratio_tendsto := by simpa [Ascale] using hratio
    inductionHypothesis := hIH }
  let F : ConeCoverageSequence regime := {
    family := C
    delta := δ
    delta_pos := hδpos
    delta_tendsto := hδlim
    directional := by
      intro i p hp
      simpa [TrackD.IsDirectionalFamily, TrackD.SpansAtMostPlane,
        IsDirectionalFamily, SpansAtMostPlane] using (hC i).1 p hp
    degree := by
      intro i p hp
      simpa [regime, Regime.N, Regime.A, Ascale] using (hC i).2.1 p hp
    coverage := by
      intro ε hε
      filter_upwards [hcoverage ε hε] with i hi
      simpa [regime, Regime.N] using hi }
  exact ⟨regime, ⟨F⟩⟩

/-- All scalar precisions use real division after the natural cast. -/
def selectionTolerance (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)

def selectionScale (n : ℕ) : ℝ := (n : ℝ) + 2

/-- Literal finitary selection certificate at one precision and configuration. -/
structure ProfileSelectionCertificate (F : ConeCoverageSequence regime)
    (n i : ℕ) (Q : TrackD.Partition d)
    (τ : RPoint d → Option (AffineVariety d))
    (plx ply : Finset (TrackD.Piece d)) (t : Fin d → ℝ) : Prop where
  good : Q.Good (regime.P i) (F.delta i) (selectionTolerance n)
    (selectionTolerance n) (selectionScale n) (selectionScale n)
  terminal : TrackD.TerminalAssignment Q (selectionTolerance n) τ
  sources_subset : plx ⊆ Q.pieces
  targets_subset : ply ⊆ Q.pieces
  sources_nonempty : plx.Nonempty
  targets_nonempty : ply.Nonempty
  close : ∀ X ∈ plx ∪ ply, ∀ a, |X.path.time a - t a| ≤ selectionTolerance n
  window : TrackD.WindowAlternative (regime.P i) (F.delta i) (selectionTolerance n) plx ply
  selected : (1 / 2 - selectionTolerance n) * (TrackD.poolPts plx).card *
    (TrackD.poolPts ply).card ≤
      (((TrackD.poolPts plx ×ˢ TrackD.poolPts ply).filter (fun pq =>
        TrackD.SelectedIncidence (regime.P i) (F.family i) τ
          (selectionTolerance n) pq.1 pq.2)).card : ℝ)

namespace ProfileSelectionCertificate
/-- Rebuild the proposition record at the new configuration index. -/
def comp {F : ConeCoverageSequence regime} {n : ℕ} (φ : ℕ → ℕ)
    (hφ : StrictMono φ) (i : ℕ) {Q : TrackD.Partition d}
    {τ : RPoint d → Option (AffineVariety d)} {plx ply : Finset (TrackD.Piece d)}
    {t : Fin d → ℝ} (C : ProfileSelectionCertificate F n (φ i) Q τ plx ply t) :
    ProfileSelectionCertificate (F.comp φ hφ) n i Q τ plx ply t := {
  good := C.good
  terminal := C.terminal
  sources_subset := C.sources_subset
  targets_subset := C.targets_subset
  sources_nonempty := C.sources_nonempty
  targets_nonempty := C.targets_nonempty
  close := C.close
  window := C.window
  selected := C.selected }
end ProfileSelectionCertificate

/-- `sc:selection.fixed`: every fixed precision eventually has a literal
certificate from Track D, including the persistent global terminal assignment. -/
theorem profile_selection_fixed (F : ConeCoverageSequence regime) (n : ℕ) :
    ∀ᶠ i in atTop, ∃ (Q : TrackD.Partition d)
      (τ : RPoint d → Option (AffineVariety d)) (plx ply : Finset (TrackD.Piece d))
      (t : Fin d → ℝ), ProfileSelectionCertificate F n i Q τ plx ply t := by
  have hρ : 0 < selectionTolerance n := by
    unfold selectionTolerance
    positivity
  have hK : 1 ≤ selectionScale n := by
    unfold selectionScale
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  obtain ⟨η, hη, N₀, hselect⟩ := TrackD.prof_pair_selection d
    (by exact regime.dimension_ge_three) (1 / 3 : ℝ) (by norm_num)
    (selectionTolerance n) hρ (selectionTolerance n) hρ (selectionTolerance n) hρ
    (selectionScale n) hK (selectionScale n)
  have hcard : ∀ᶠ i in atTop, N₀ ≤ (regime.P i).card :=
    regime.card_tendsto.eventually (eventually_ge_atTop N₀)
  have hmass : ∀ᶠ i in atTop,
      TrackD.cfgM (regime.P i) ≤ η * TrackD.cfgA (regime.P i) := by
    have hsmall := regime.M_div_A_tendsto.eventually (Iio_mem_nhds hη)
    filter_upwards [hsmall] with i hi
    have hmul := (div_lt_iff₀ (regime.A_pos i)).mp hi
    have hMeq : Mcount (regime.P i) = regime.M i := by
      simp [Mcount, Regime.M, add_comm]
    have hAeq : Ascale d (regime.P i).card = regime.A i := rfl
    have hM := hmul
    rw [← hMeq, ← hAeq] at hM
    simpa [TrackD.cfgM, TrackD.cfgA, Mcount, Ascale] using hM.le
  have hflat : ∀ᶠ i in atTop,
      TrackD.RealFlatCap (regime.P i) (1 / 3 : ℝ) := wide_regime_flat_cap regime
  have hδ : ∀ᶠ i in atTop, F.delta i ≤ η :=
    F.delta_tendsto.eventually (Iio_mem_nhds hη) |>.mono fun _ hi => hi.le
  have hcoverage : ∀ᶠ i in atTop,
      (1 - η) * TrackD.cfgN (regime.P i) * (TrackD.cfgN (regime.P i) - 1) ≤
        ((TrackD.coveredPairs (regime.P i) (F.family i)).card : ℝ) := by
    filter_upwards [F.coverage η hη] with i hi
    simpa [TrackD.cfgN, Regime.N] using hi
  filter_upwards [hcard, hmass, hflat, hδ, hcoverage]
    with i hcardi hmass_i hflati hδi hcoverage_i
  have hfamily : ∀ p ∈ regime.P i,
      TrackD.IsDirectionalFamily (F.family i p) ∧
        (ProjectiveFamily.degree (F.family i p) : ℝ) ≤
          F.delta i * TrackD.cfgN (regime.P i) / TrackD.cfgA (regime.P i) := by
    intro p hp
    refine ⟨F.directional i p hp, ?_⟩
    simpa [Regime.N, Regime.A, TrackD.cfgN, TrackD.cfgA] using F.degree i p hp
  obtain ⟨Q, τ, plx, ply, t, hgood, hterminal, hsrcsub, htgtSub, hsrcne, htgtne,
      hclose, hwindow, hselected⟩ :=
    hselect (regime.P i) hcardi hmass_i hflati (F.delta i) (F.delta_pos i) hδi
      (F.family i) hfamily hcoverage_i
  exact ⟨Q, τ, plx, ply, t,
    ⟨hgood, hterminal, hsrcsub, htgtSub, hsrcne, htgtne, hclose, hwindow, hselected⟩⟩

/-- A precision diagonal of literal finitary certificates, with no lost role
information in the source/target pools or terminal assignment. -/
structure SelectedProfileSequence (F : ConeCoverageSequence regime) where
  precision : ℕ → ℕ
  precision_grows : Tendsto precision atTop atTop
  partition : ℕ → TrackD.Partition d
  terminal : ℕ → RPoint d → Option (AffineVariety d)
  sources : ℕ → Finset (TrackD.Piece d)
  targets : ℕ → Finset (TrackD.Piece d)
  reference : ℕ → Fin d → ℝ
  certificate : ∀ i, ProfileSelectionCertificate F (precision i) i
    (partition i) (terminal i) (sources i) (targets i) (reference i)

namespace SelectedProfileSequence
/-- Retain every actual family and assignment on a common subsequence. -/
def comp {F : ConeCoverageSequence regime} (T : SelectedProfileSequence F)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) : SelectedProfileSequence (F.comp φ hφ) := {
  precision := fun i => T.precision (φ i)
  precision_grows := T.precision_grows.comp hφ.tendsto_atTop
  partition := fun i => T.partition (φ i)
  terminal := fun i => T.terminal (φ i)
  sources := fun i => T.sources (φ i)
  targets := fun i => T.targets (φ i)
  reference := fun i => T.reference (φ i)
  certificate := fun i => ProfileSelectionCertificate.comp φ hφ i (T.certificate (φ i)) }

/-- The separated-window branch of the exact window alternative. -/
def IsSeparated {F : ConeCoverageSequence regime} (T : SelectedProfileSequence F)
    (i : ℕ) : Prop :=
  ∃ X Y : TrackD.Piece d, T.sources i = {X} ∧ T.targets i = {Y} ∧
    (X.width ≤ selectionTolerance (T.precision i) * Y.width ∨
      Y.width ≤ selectionTolerance (T.precision i) * X.width) ∧
    X.width ≤ selectionTolerance (T.precision i) * Real.log (regime.B i) ∧
    Y.width ≤ selectionTolerance (T.precision i) * Real.log (regime.B i)
end SelectedProfileSequence

/-- `sc:selection.diagonal`: discard a finite prefix and select precision
slowly, retaining literal certificates at every index of one subsequence. -/
theorem select_profile_sequence (F : ConeCoverageSequence regime) :
    ∃ (φ : ℕ → ℕ) (hφ : StrictMono φ), Nonempty (SelectedProfileSequence (F.comp φ hφ)) := by
  let R : ℕ → ℕ → Prop := fun n i =>
    ∃ (Q : TrackD.Partition d) (τ : RPoint d → Option (AffineVariety d))
      (plx ply : Finset (TrackD.Piece d)) (t : Fin d → ℝ),
      ProfileSelectionCertificate F n i Q τ plx ply t
  have hR (n : ℕ) : ∀ᶠ i in atTop, R n i := profile_selection_fixed F n
  obtain ⟨a, _, hagrows, hdiag⟩ := Framework.exists_slow_diagonal R hR
  obtain ⟨φ, hφ, hgood⟩ := Filter.extraction_of_eventually_atTop hdiag
  choose Q τ plx ply t hcertificate using fun i => hgood i (a (φ i)) le_rfl
  refine ⟨φ, hφ, ⟨{
    precision := fun i => a (φ i)
    precision_grows := hagrows.comp hφ.tendsto_atTop
    partition := Q
    terminal := τ
    sources := plx
    targets := ply
    reference := t
    certificate := fun i => ProfileSelectionCertificate.comp φ hφ i (hcertificate i) }⟩⟩

/-- Larger error/margin and smaller degree constant weaken PieceGood. -/
theorem selection_piece_good_weaken (P : Finset (RPoint d)) (X : TrackD.Piece d)
    {θ₀ θ ξ₀ ξ K₀ K : ℝ} (hwidth : 0 ≤ X.width)
    (hθ : θ₀ ≤ θ) (hξ : ξ₀ ≤ ξ) (hK : K ≤ K₀)
    (hX : TrackD.PieceGood P θ₀ ξ₀ K₀ X) : TrackD.PieceGood P θ ξ K X := by
  have hXθ : TrackD.PieceGood P θ ξ₀ K₀ X :=
    TrackD.dprofiles2_pieceGood_mono P X hθ hwidth hX
  refine ⟨hXθ.subset, hXθ.width_dyadic, hXθ.size, hXθ.mono, hXθ.time_range,
    hXθ.imbalance, hXθ.vanish, hXθ.proper, hXθ.degree, ?_⟩
  intro j hj b hb htest g hg
  have hb₀ : TrackD.OnPlateau X.path.time j ξ₀ b := by
    intro i
    constructor
    · intro hi
      have h := (hb i).1 hi
      linarith
    · intro hi
      have h := (hb i).2 hi
      linarith
  have hdeg : (g.totalDegree : ℝ) ≤ K₀ * TrackD.testDeg (TrackD.cfgB P) X.width b :=
    hg.trans (mul_le_mul_of_nonneg_right hK (by linarith))
  exact hXθ.noCapture j hj b hb₀ htest g hdeg

/-- Uniform eventual good-piece facts for the entire selected physical pools. -/
theorem selected_piece_good_eventually {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) :
    ∀ θ : ℝ, 0 < θ → ∀ ξ : ℝ, 0 < ξ → ∀ K : ℝ, 1 ≤ K →
    ∀ᶠ i in atTop, ∀ X ∈ T.sources i ∪ T.targets i,
      TrackD.PieceGood (regime.P i) θ ξ K X := by
  intro θ hθ ξ hξ K hK
  have hcast : Tendsto (fun i => (T.precision i : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp T.precision_grows
  have hden : Tendsto (fun i => (T.precision i : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 hcast
  have htol : Tendsto (fun i => selectionTolerance (T.precision i)) atTop (𝓝 0) := by
    simpa [selectionTolerance] using hden.const_div_atTop (1 : ℝ)
  have htolθ : ∀ᶠ i in atTop, selectionTolerance (T.precision i) ≤ θ :=
    (htol.eventually (Iio_mem_nhds hθ)).mono fun _ hi => hi.le
  have htolξ : ∀ᶠ i in atTop, selectionTolerance (T.precision i) ≤ ξ :=
    (htol.eventually (Iio_mem_nhds hξ)).mono fun _ hi => hi.le
  have hscale : Tendsto (fun i => selectionScale (T.precision i)) atTop atTop := by
    simpa [selectionScale] using tendsto_atTop_add_const_right atTop 2 hcast
  have hscaleK : ∀ᶠ i in atTop, K ≤ selectionScale (T.precision i) :=
    hscale.eventually (eventually_ge_atTop K)
  filter_upwards [htolθ, htolξ, hscaleK] with i hθi hξi hKi
  intro X hX
  have hmem : X ∈ (T.partition i).pieces := by
    rcases Finset.mem_union.mp hX with hsrc | htgt
    · exact (T.certificate i).sources_subset hsrc
    · exact (T.certificate i).targets_subset htgt
  have hgood := (T.certificate i).good.pieces_good X hmem
  have hwidth : 0 ≤ X.width := by
    have hscale_nonneg : 0 ≤ selectionScale (T.precision i) := by
      unfold selectionScale
      positivity
    exact le_trans hscale_nonneg hgood.2
  exact selection_piece_good_weaken (regime.P i) X hwidth hθi hξi hKi hgood.1

/-- The scalar precision tends to zero on every increasing selected scale. -/
theorem selection_tolerance_tendsto_zero (n : ℕ → ℕ) (hn : Tendsto n atTop atTop) :
    Tendsto (fun i => selectionTolerance (n i)) atTop (𝓝 0) := by
  have hcast : Tendsto (fun i => (n i : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  have hden : Tendsto (fun i => (n i : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 hcast
  simpa [selectionTolerance] using hden.const_div_atTop (1 : ℝ)

/-- Positive widths controlled by a vanishing scalar times the ambient
logarithmic scale are both little-o of that scale. -/
theorem selection_widths_littleO (u v w ρ : ℕ → ℝ)
    (huv : ∀ i, 0 < u i ∧ 0 < v i) (hw : ∀ᶠ i in atTop, 0 ≤ w i)
    (hρ : Tendsto ρ atTop (𝓝 0))
    (hbound : ∀ i, u i ≤ ρ i * w i ∧ v i ≤ ρ i * w i) :
    Framework.LittleO u w ∧ Framework.LittleO v w := by
  have hρ_nonneg : ∀ᶠ i in atTop, 0 ≤ ρ i := by
    filter_upwards [hw] with i hwi
    by_contra hρi
    have hρi' : ρ i ≤ 0 := (lt_of_not_ge hρi).le
    have hprod : ρ i * w i ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hρi' hwi
    linarith [(hbound i).1, (huv i).1]
  have hρε (ε : ℝ) (hε : 0 < ε) : ∀ᶠ i in atTop, ρ i < ε :=
    hρ.eventually (Iio_mem_nhds hε)
  constructor
  · refine Asymptotics.IsLittleO.of_bound ?_
    intro ε hε
    filter_upwards [hw, hρ_nonneg, hρε ε hε] with i hwi hρi hρiε
    have hmul : ρ i * w i ≤ ε * w i :=
      mul_le_mul_of_nonneg_right hρiε.le hwi
    simpa [Real.norm_eq_abs, abs_of_pos (huv i).1, abs_of_nonneg hwi] using
      (hbound i).1.trans hmul
  · refine Asymptotics.IsLittleO.of_bound ?_
    intro ε hε
    filter_upwards [hw, hρ_nonneg, hρε ε hε] with i hwi hρi hρiε
    have hmul : ρ i * w i ≤ ε * w i :=
      mul_le_mul_of_nonneg_right hρiε.le hwi
    simpa [Real.norm_eq_abs, abs_of_pos (huv i).2, abs_of_nonneg hwi] using
      (hbound i).2.trans hmul

/-- Choose the width-ratio orientation on a subsequence before taking its limit. -/
theorem selection_ratio_tendsto_zero (u v ρ : ℕ → ℝ)
    (huv : ∀ i, 0 < u i ∧ 0 < v i) (hρ : Tendsto ρ atTop (𝓝 0))
    (hbound : ∀ i, u i ≤ ρ i * v i) :
    Tendsto (fun i => u i / v i) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hρ
  · filter_upwards with i
    exact le_of_lt (div_pos (huv i).1 (huv i).2)
  · filter_upwards with i
    exact (div_le_iff₀ (huv i).2).2 (hbound i)

/-- Two recorded profiles close to the same reference have vanishing difference. -/
theorem selection_times_close (x y t : ℕ → Fin d → ℝ) (ρ : ℕ → ℝ)
    (hρ : Tendsto ρ atTop (𝓝 0))
    (hclose : ∀ i a, |x i a - t i a| ≤ ρ i ∧ |y i a - t i a| ≤ ρ i) :
    ∀ a, Tendsto (fun i => x i a - y i a) atTop (𝓝 0) := by
  intro a
  rw [tendsto_zero_iff_abs_tendsto_zero]
  have h2ρ : Tendsto (fun i => 2 * ρ i) atTop (𝓝 0) := by
    simpa using hρ.const_mul (2 : ℝ)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds h2ρ
  · filter_upwards with i
    exact abs_nonneg _
  · filter_upwards with i
    calc
      |x i a - y i a| ≤ |x i a - t i a| + |t i a - y i a| := abs_sub_le _ _ _
      _ ≤ ρ i + ρ i := add_le_add (hclose i a).1 (by simpa [abs_sub_comm] using (hclose i a).2)
      _ = 2 * ρ i := by ring

/-- `sc:selection.separated`: choose one width-ratio orientation on a
subsequence and construct the exact SeparatedProfileSequence consumed by G5.
No physical source/target role is swapped. -/
theorem selected_separated_sequence {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (hsep : ∃ᶠ i in atTop, T.IsSeparated i) :
    ∃ (φ : ℕ → ℕ) (hφ : StrictMono φ)
      (S : SeparatedProfileSequence (regime.comp φ hφ)),
      ∀ i, T.sources (φ i) = {S.source i} ∧ T.targets (φ i) = {S.target i} := by
  obtain ⟨φ₀, hφ₀, hseparated⟩ := Filter.extraction_of_frequently_atTop hsep
  unfold SelectedProfileSequence.IsSeparated at hseparated
  choose X Y hXY using hseparated
  have horientation : ∃ᶠ i in atTop,
      (X i).width ≤ selectionTolerance (T.precision (φ₀ i)) * (Y i).width ∨
      (Y i).width ≤ selectionTolerance (T.precision (φ₀ i)) * (X i).width :=
    Filter.Frequently.of_forall fun i => (hXY i).2.2.1
  have hchoose : ∃ (φ₁ : ℕ → ℕ) (hφ₁ : StrictMono φ₁),
      (∀ i, (X (φ₁ i)).width ≤ selectionTolerance (T.precision (φ₀ (φ₁ i))) *
        (Y (φ₁ i)).width) ∨
      (∀ i, (Y (φ₁ i)).width ≤ selectionTolerance (T.precision (φ₀ (φ₁ i))) *
        (X (φ₁ i)).width) := by
    rcases Filter.frequently_or_distrib.mp horientation with hf | hb
    · obtain ⟨φ₁, hφ₁, hforall⟩ := Filter.extraction_of_frequently_atTop hf
      exact ⟨φ₁, hφ₁, Or.inl hforall⟩
    · obtain ⟨φ₁, hφ₁, hforall⟩ := Filter.extraction_of_frequently_atTop hb
      exact ⟨φ₁, hφ₁, Or.inr hforall⟩
  obtain ⟨φ₁, hφ₁, hside⟩ := hchoose
  let φ : ℕ → ℕ := φ₀ ∘ φ₁
  have hφ : StrictMono φ := hφ₀.comp hφ₁
  let source : ℕ → TrackD.Piece d := fun i => X (φ₁ i)
  let target : ℕ → TrackD.Piece d := fun i => Y (φ₁ i)
  have hxmem (i : ℕ) : source i ∈ T.sources (φ i) := by
    change X (φ₁ i) ∈ T.sources (φ₀ (φ₁ i))
    rw [(hXY (φ₁ i)).1]
    exact Finset.mem_singleton_self _
  have hymem (i : ℕ) : target i ∈ T.targets (φ i) := by
    change Y (φ₁ i) ∈ T.targets (φ₀ (φ₁ i))
    rw [(hXY (φ₁ i)).2.1]
    exact Finset.mem_singleton_self _
  have hxdata (i : ℕ) :
      TrackD.PieceGood (regime.P (φ i)) (selectionTolerance (T.precision (φ i)))
        (selectionTolerance (T.precision (φ i))) (selectionScale (T.precision (φ i)))
        (source i) ∧ selectionScale (T.precision (φ i)) ≤ (source i).width :=
    (T.certificate (φ i)).good.pieces_good (source i)
      ((T.certificate (φ i)).sources_subset (hxmem i))
  have hydata (i : ℕ) :
      TrackD.PieceGood (regime.P (φ i)) (selectionTolerance (T.precision (φ i)))
        (selectionTolerance (T.precision (φ i))) (selectionScale (T.precision (φ i)))
        (target i) ∧ selectionScale (T.precision (φ i)) ≤ (target i).width :=
    (T.certificate (φ i)).good.pieces_good (target i)
      ((T.certificate (φ i)).targets_subset (hymem i))
  have hpos (i : ℕ) : 0 < (source i).width ∧ 0 < (target i).width := by
    have hscale : 0 < selectionScale (T.precision (φ i)) := by
      dsimp [selectionScale]
      positivity
    exact ⟨hscale.trans_le (hxdata i).2, hscale.trans_le (hydata i).2⟩
  have hparameters (n : ℕ) : selectionTolerance n ≤ 1 ∧ 1 ≤ selectionScale n := by
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    constructor
    · dsimp [selectionTolerance]
      apply (div_le_one₀ (by positivity)).mpr
      linarith
    · dsimp [selectionScale]
      linarith
  have hbase (i : ℕ) : TrackD.PieceGood (regime.P (φ i)) 1 1 1 (source i) ∧
      TrackD.PieceGood (regime.P (φ i)) 1 1 1 (target i) := by
    have hpar := hparameters (T.precision (φ i))
    exact ⟨selection_piece_good_weaken _ _ (hpos i).1.le hpar.1 hpar.1 hpar.2 (hxdata i).1,
      selection_piece_good_weaken _ _ (hpos i).2.le hpar.1 hpar.1 hpar.2 (hydata i).1⟩
  have hngrows : Tendsto (fun i => T.precision (φ i)) atTop atTop :=
    T.precision_grows.comp hφ.tendsto_atTop
  have hncast : Tendsto (fun i => (T.precision (φ i) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hngrows
  have hxgrows : Tendsto (fun i => (source i).width) atTop atTop := by
    apply Filter.tendsto_atTop_mono _ hncast
    intro i
    have h := (hxdata i).2
    dsimp [selectionScale] at h
    linarith
  have hygrows : Tendsto (fun i => (target i).width) atTop atTop := by
    apply Filter.tendsto_atTop_mono _ hncast
    intro i
    have h := (hydata i).2
    dsimp [selectionScale] at h
    linarith
  let ρ : ℕ → ℝ := fun i => selectionTolerance (T.precision (φ i))
  have hρ : Tendsto ρ atTop (𝓝 0) := selection_tolerance_tendsto_zero _ hngrows
  have hlog : ∀ᶠ i in atTop, 0 ≤ Real.log (regime.B (φ i)) := by
    filter_upwards [hφ.tendsto_atTop.eventually
      (regime.B_tendsto.eventually_ge_atTop 1)] with i hi
    exact Real.log_nonneg hi
  have hbounds (i : ℕ) : (source i).width ≤ ρ i * Real.log (regime.B (φ i)) ∧
      (target i).width ≤ ρ i * Real.log (regime.B (φ i)) :=
    ⟨(hXY (φ₁ i)).2.2.2.1, (hXY (φ₁ i)).2.2.2.2⟩
  obtain ⟨hxsmall, hysmall⟩ := selection_widths_littleO
    (fun i => (source i).width) (fun i => (target i).width)
    (fun i => Real.log (regime.B (φ i))) ρ hpos hlog hρ hbounds
  have hratio : Tendsto (fun i => (source i).width / (target i).width) atTop (𝓝 0) ∨
      Tendsto (fun i => (target i).width / (source i).width) atTop (𝓝 0) := by
    rcases hside with hf | hb
    · exact Or.inl (selection_ratio_tendsto_zero _ _ ρ hpos hρ hf)
    · exact Or.inr (selection_ratio_tendsto_zero _ _ ρ (fun i => (hpos i).symm) hρ hb)
  have hclose (i : ℕ) (a : Fin d) :
      |(source i).path.time a - T.reference (φ i) a| ≤ ρ i ∧
      |(target i).path.time a - T.reference (φ i) a| ≤ ρ i :=
    ⟨(T.certificate (φ i)).close _ (Finset.mem_union_left _ (hxmem i)) a,
      (T.certificate (φ i)).close _ (Finset.mem_union_right _ (hymem i)) a⟩
  have htimes := selection_times_close (fun i => (source i).path.time)
    (fun i => (target i).path.time) (fun i => T.reference (φ i)) ρ hρ hclose
  let S : SeparatedProfileSequence (regime.comp φ hφ) := {
    source := source
    target := target
    base_good := hbase
    good := by
      intro θ hθ ξ hξ K hK
      filter_upwards [hφ.tendsto_atTop.eventually
        (selected_piece_good_eventually T θ hθ ξ hξ K hK)] with i hi
      exact ⟨hi _ (Finset.mem_union_left _ (hxmem i)),
        hi _ (Finset.mem_union_right _ (hymem i))⟩
    width_pos := hpos
    source_grows := hxgrows
    target_grows := hygrows
    source_small := hxsmall
    target_small := hysmall
    separated := hratio
    times_close := htimes }
  exact ⟨φ, hφ, S, fun i => ⟨(hXY (φ₁ i)).1, (hXY (φ₁ i)).2.1⟩⟩

end
end DistinctDistances.SparseCones
