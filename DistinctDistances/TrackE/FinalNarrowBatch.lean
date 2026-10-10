import DistinctDistances.TrackE.FinalNarrowInputs

/-! Fix the final narrow rate and reserved regularity times before adaptive
envelopes, sparse-cones.tex:802–839. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- sc:u-final-curve.batch: select the final narrow rate with tolerance below
the later regularity gap, preserving earlier strict ranks and the global owner. -/
theorem selected_final_narrow_batch {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (S : LimitingSeparatedProfile regime)
    [Fintype (ProfilePlateau S)]
    (hsource : ∀ i, T.sources i = {S.sequence.source i})
    (htarget : ∀ i, T.targets i = {S.sequence.target i}) :
    Nonempty (FinalNarrowBatchData T S) := by
  classical
  obtain ⟨hnarrow, hopen⟩ := separated_profile_forces_narrow_final_curve T S hsource htarget
  let u : ProfilePlateau S :=
    ⟨⟨d - 1, by have := regime.dimension_ge_three; omega⟩,
      ⟨by change 1 ≤ d - 1; have := regime.dimension_ge_three; omega,
        by simpa using hopen⟩⟩
  have hu : u.val.val + 1 = d := by dsimp [u]; have := regime.dimension_ge_three; omega
  have huLast : S.b u.val = profileLastTime S := rfl
  obtain ⟨η, originalKind, hη, hallowed, hlogs⟩ := exists_uniform_plateau_rate_margin S
  obtain ⟨κ₀, hκ₀, hfirst, _, _⟩ := S.balance
  let m₀ : ℝ := min (η / 2) (-S.b ⟨0, by have := regime.dimension_ge_three; omega⟩)
  have hm₀ : 0 < m₀ := lt_min (by positivity) (by linarith)
  have hmη : m₀ ≤ η / 2 := min_le_left _ _
  have hmfirst : m₀ ≤ -S.b ⟨0, by have := regime.dimension_ge_three; omega⟩ :=
    min_le_right _ _
  obtain ⟨hpositive, hfour, _⟩ := plateau_rank_margin_bounds (d := d) m₀ hm₀
  let q : ℝ := plateauRankMargin m₀ d
  have hq : 0 < q := (hpositive d).1
  have hfourq : 4 * q ≤ m₀ := by
    have hh := hfour 0 d (by have := regime.dimension_ge_three; omega)
    simpa only [q, plateauRankMargin, pow_zero, div_one] using hh
  let κ : ℝ := q / (d + 1 : ℝ)
  have hκ : 0 < κ := by dsimp [κ]; positivity
  obtain ⟨a, ha, hcluster, hprevious⟩ := exists_preceding_open_test S u κ hκ
  obtain ⟨b₀, hb₀l, hb₀r, hendpoint⟩ := exists_final_testing_time S u huLast
    (2 * q) (by positivity)
  let b_eq : ℝ := (b₀ + S.b u.val) / 2
  let b_test : ℝ := (b_eq + S.b u.val) / 2
  have htimes : b₀ < b_eq ∧ b_eq < b_test ∧ b_test < S.b u.val := by
    dsimp [b_eq, b_test]
    constructor
    · linarith
    constructor <;> linarith
  have hgap : 0 < b_eq - b₀ := sub_pos.mpr htimes.1
  let ε : ℝ := min (η / 8) ((b_eq - b₀) / 2)
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  have hεsmall : ε ≤ η / 4 := by
    have hle : ε ≤ η / 8 := min_le_left _ _
    linarith
  have hεgap : ε < b_eq - b₀ := by
    have hle : ε ≤ (b_eq - b₀) / 2 := min_le_right _ _
    linarith
  let kind (v : ProfilePlateau S) : DepthRateKind :=
    if StrictPlateauEligible S v then originalKind v else .narrow
  have hkind : ∀ v, profileDepthRateAllowed S v.val.val v.val.isLt (kind v) := by
    intro v
    by_cases hv : StrictPlateauEligible S v
    · simpa only [kind, if_pos hv] using hallowed v
    · simpa only [kind, if_neg hv, profileDepthRateAllowed] using hnarrow
  have hkindfinal : kind u = .narrow := by
    simp only [kind, if_neg (narrow_final_plateau_ineligible S hnarrow u hu)]
  obtain ⟨H⟩ := selected_profile_depth_batch T S hsource htarget
    (id : ProfilePlateau S → ProfilePlateau S) kind (fun _ => ε) (fun _ => hε) hkind
  have hlogs' : ∀ v, StrictPlateauEligible S (id v) →
      profileRateEndpointLog S (id v) (kind v) ≤ -η := by
    intro v hv
    change StrictPlateauEligible S v at hv
    change profileRateEndpointLog S v (kind v) ≤ -η
    simpa only [kind, if_pos hv] using hlogs v hv
  have hind := separated_direction_rank_induction S H (fun v => ⟨v, rfl⟩)
    η m₀ hη hm₀ hmη hmfirst (fun _ => ⟨hε, hεsmall⟩) hlogs'
  have htarget (i : ℕ) (t : ℝ) : 0 ≤ profileDirectionRankTarget S i t := by
    unfold profileDirectionRankTarget
    exact div_nonneg
      (mul_nonneg (TrackD.RankCore.sigma_nonneg (regime.B_pos i).le _ _ _)
        (TrackD.RankCore.testDeg_pos (regime.B_pos i) _ _).le) (regime.A_pos i).le
  have hmono {t x y : ℝ} (hxy : x ≤ y) (h : DirectionRowRankMargin H t y) :
      DirectionRowRankMargin H t x := by
    intro ρ hρ
    filter_upwards [h ρ hρ] with i hi
    intro p Q hrow
    exact (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hxy (S.sequence.width_pos i).2.le))
      (htarget i t)).trans (hi p Q hrow)
  have hprior : DirectionRowRankMargin H a (4 * q) := by
    rcases hprevious with hinitial | ⟨v, hvu, hv, hav, hav'⟩
    · have hfoura : 4 * q ≤ -a := by linarith
      intro ρ hρ
      filter_upwards [initial_direction_rank_full S a hinitial ρ hρ,
        initial_profile_rank_margin S a hinitial] with i hfull hmargin
      intro p Q hrow
      obtain ⟨hp, htypical, hQ, hneq, hsurvives, hdense⟩ := hrow
      have hcard : ρ * ((S.sequence.target i).pts.card : ℝ) ≤ Q.card := by
        simpa only [Finset.card_image_of_injective _ profile_toC_injective] using hdense
      rw [hfull p Q hQ hneq hcard]
      exact (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hfoura
          (S.sequence.width_pos i).2.le)) (htarget i a)).trans hmargin
    · apply hmono (by simpa only [q] using hfour v.val.val d v.val.isLt)
      exact hind v hv a ⟨hav, hav'⟩
  have hclusterLoss : (d : ℝ) * κ ≤ (4 * q) / 4 := by
    have hden : 0 < (d + 1 : ℝ) := by positivity
    have heq : κ * (d + 1 : ℝ) = q := by
      dsimp [κ]
      exact div_mul_cancel₀ _ hden.ne'
    nlinarith
  refine ⟨{
    finalPlateau := u
    final_index := hu
    a := a
    b₀ := b₀
    b_eq := b_eq
    b_test := b_test
    κ := κ
    m := 4 * q
    ε := ε
    margin_pos := by positivity
    epsilon_pos := hε
    epsilon_gap := hεgap
    before := ha.le
    cluster_gap := hcluster
    cluster_loss := hclusterLoss
    plateau_time := ⟨hb₀l, hb₀r⟩
    reserved_times := htimes
    endpoint_gap := by linarith
    kind := kind
    kind_allowed := hkind
    final_rate := hkindfinal
    H := H
    preceding_rank := hprior }⟩

/-- sc:u-final-curve.large-batch: the chosen final narrow batch supplies
every rank and fixed-time input of the whole-envelope larger-label removal. -/
theorem final_narrow_large_labels_small {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} {S : LimitingSeparatedProfile regime}
    [Fintype (ProfilePlateau S)] (K : FinalNarrowBatchData T S) :
    ∀ ρ : ℝ, 0 < ρ → ∀ᶠ i in atTop,
      ∀ p ∈ regime.P i, ∀ Q : Finset (RPoint d),
        DenseSurvivingDirectionRow K.H i (TrackD.toC p) Q 0 →
      ∀ G : CoveringEnvelopeComponents (F.family i p)
        ⌊TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width K.b₀⌋₊,
        ((coveringEnvelopeLargeLabels G (TrackD.toC p) Q).card : ℝ) ≤
          ρ * (((S.sequence.target i).pts.image TrackD.toC).card : ℝ) := by
  exact covering_envelope_large_labels_small S K.H K.finalPlateau K.final_index
    K.a K.b₀ K.κ K.m K.margin_pos K.before K.cluster_gap K.plateau_time
    K.cluster_loss K.endpoint_gap K.preceding_rank

end
end DistinctDistances.SparseCones
