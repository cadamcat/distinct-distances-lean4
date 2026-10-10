import DistinctDistances.TrackE.StrictRankNumerics

/-! Finite strict-rank induction over the actual open limiting plateaux.
The batch and every tolerance precede all later row choices. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- sc:separated-rank.induction: a fixed small tolerance and rate at each
open plateau propagate the initial margin across all eligible cut clusters. -/
theorem separated_direction_rank_induction {α : Type*} [Fintype α]
    {F : ConeCoverageSequence regime} {T : SelectedProfileSequence F}
    (S : LimitingSeparatedProfile regime)
    {plateau : α → ProfilePlateau S} {kind : α → DepthRateKind} {ε : α → ℝ}
    (H : ProfileDepthBatchData T S plateau kind ε) (cover : ∀ u, ∃ a, plateau a = u)
    (η m : ℝ) (hη : 0 < η) (hm : 0 < m) (hmη : m ≤ η / 2)
    (hmfirst : m ≤ -S.b ⟨0, by have := regime.dimension_ge_three; omega⟩)
    (hε : ∀ a, 0 < ε a ∧ ε a ≤ η / 4)
    (hlog : ∀ a, StrictPlateauEligible S (plateau a) →
      profileRateEndpointLog S (plateau a) (kind a) ≤ -η) :
    ∀ u : ProfilePlateau S, StrictPlateauEligible S u → ∀ τ : ℝ,
      profilePlateauLeft S u < τ ∧ τ < S.b u.val →
      DirectionRowRankMargin H τ (plateauRankMargin m u.val.val) := by
  classical
  have htarget (i : ℕ) (τ : ℝ) : 0 ≤ profileDirectionRankTarget S i τ := by
    unfold profileDirectionRankTarget
    exact div_nonneg
      (mul_nonneg (TrackD.RankCore.sigma_nonneg (regime.B_pos i).le _ _ _)
        (TrackD.RankCore.testDeg_pos (regime.B_pos i) _ _).le) (regime.A_pos i).le
  have hmono {τ x y : ℝ} (hxy : x ≤ y) (hy : DirectionRowRankMargin H τ y) :
      DirectionRowRankMargin H τ x := by
    intro ρ hρ
    filter_upwards [hy ρ hρ] with i hi
    intro p Q hrow
    exact (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hxy (S.sequence.width_pos i).2.le))
      (htarget i τ)).trans (hi p Q hrow)
  obtain ⟨hpositive, hfour, hfinal⟩ := plateau_rank_margin_bounds (d := d) m hm
  have hind : ∀ n : ℕ, ∀ u : ProfilePlateau S, u.val.val = n →
      StrictPlateauEligible S u → ∀ τ : ℝ,
      profilePlateauLeft S u < τ ∧ τ < S.b u.val →
      DirectionRowRankMargin H τ (plateauRankMargin m n) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro u hun hu τ hτ
      obtain ⟨a₀, ha₀⟩ := cover u
      have hnpos : 1 ≤ n := by have := u.property.1; omega
      let q : ℝ := plateauRankMargin m n
      have hq : 0 < q := (hpositive n).1
      have hqm : 4 * q ≤ m := by
        have hh := hfour 0 n (by omega)
        simpa only [q, plateauRankMargin, pow_zero, div_one] using hh
      let κ : ℝ := q / (d + 1 : ℝ)
      have hκ : 0 < κ := div_pos hq (by positivity)
      obtain ⟨a, hal, hgap, hprevious⟩ := exists_preceding_open_test S u κ hκ
      have hpreviousRank : DirectionRowRankMargin H a (4 * q) := by
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
        · have hvn : v.val.val < n := by omega
          have hprior := ih v.val.val hvn v rfl hv a ⟨hav, hav'⟩
          exact hmono (by simpa only [q] using hfour v.val.val n hvn) hprior
      have hgaple : (d : ℝ) * κ ≤ q := by
        have hden : 0 < (d + 1 : ℝ) := by positivity
        have heq : κ * (d + 1 : ℝ) = q := by
          dsimp [κ]
          exact div_mul_cancel₀ _ hden.ne'
        nlinarith
      obtain ⟨c, hc, hchoice⟩ := dense_direction_rank_power_alternative S H a₀ τ (by
        simpa only [ha₀, profilePlateauLeft] using hτ)
      have hsame := profile_same_dimension_margin S u (H.data u) (H.from_profile u)
        (kind a₀) η (ε a₀) c τ hη (hε a₀).1 (hε a₀).2 hc
        (by simpa only [ha₀] using hlog a₀ (by simpa only [ha₀] using hu)) hτ
      obtain ⟨hz, hb⟩ := limiting_plateau_boundary S u τ hτ
      intro ρ hρ
      let ρ' : ℝ := ρ / (2 * (d + 1 : ℝ))
      have hρ' : 0 < ρ' := by dsimp [ρ']; positivity
      filter_upwards [hchoice ρ hρ, hpreviousRank ρ' hρ', hsame,
        target_absorb_lower_constant S c q hc hq, target_test_degree S a]
        with i hchoice_i hprior_i hsame_i hc_i htest
      intro p Q hrow
      obtain ⟨hp, htypical, hQ, hneq, hsurvives, hdense⟩ := hrow
      obtain ⟨h, hlh, hhd, Q', hQ'Q, hQ'dense, hcases⟩ :=
        hchoice_i p hp htypical Q hQ hneq hsurvives hdense
      rcases hcases with ⟨heq, hequal⟩ | ⟨hlt, hborrow⟩
      · have hequal' : c * ((H.data u).degreeBudget i /
            profileDepthRate S u.val.val (kind a₀) i *
            Real.exp (-ε a₀ * (H.data u).s i)) *
            (TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ)^
              (d - u.val.val) ≤
            rowDirectionRank p Q
              ⌊TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ⌋₊ := by
          have hbudgetEq := congrArg (fun v : ProfilePlateau S => (H.data v).degreeBudget i) ha₀
          have hwidthEq := congrArg (fun v : ProfilePlateau S => (H.data v).s i) ha₀
          simpa only [heq, ha₀, hbudgetEq, hwidthEq] using hequal
        have hqη : q ≤ η / 2 := (hpositive n).2.trans hmη
        exact (mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hqη
            (S.sequence.width_pos i).2.le)) (htarget i τ)).trans (hsame_i.trans hequal')
      · have hrow' : DenseSurvivingDirectionRow H i p Q' ρ' :=
          ⟨hp, htypical, hQ'Q.trans hQ, fun q hq => hneq q (hQ'Q hq),
            fun q hq => hsurvives q (hQ'Q hq), hQ'dense⟩
        have hstart := hprior_i p Q' hrow'
        have hcompare := hborrow a htest
        have hdim : d - u.val.val + 1 ≤ h := by rw [ha₀] at hlt; omega
        have hstep := direction_target_propagate_step (regime.B_pos i) (regime.A_pos i)
          (S.sequence.width_pos i).2.le hal.le hτ.1.le hgap S.b u.val.val h
          u.val.isLt.le hdim hz hb hc_i hstart (by
            simpa only [TrackD.cfgB, Regime.B, Regime.N] using hcompare)
        have hstep' : profileDirectionRankTarget S i τ *
            Real.exp ((4 * q - q - (d : ℝ) * κ) * (S.sequence.target i).width) ≤
            rowDirectionRank p Q
              ⌊TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ⌋₊ := by
          simpa only [profileDirectionRankTarget, TrackD.cfgB, Regime.B, Regime.N] using hstep
        exact (mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
            (by linarith : q ≤ 4 * q - q - (d : ℝ) * κ)
            (S.sequence.width_pos i).2.le)) (htarget i τ)).trans hstep'
  intro u hu τ hτ
  exact hind u.val.val u rfl hu τ hτ

/-- sc:separated-rank: all permitted rates, one tolerance and one positive
margin are chosen from the fixed profile before the depth batch or any density. -/
theorem separated_direction_rank_margin (S : LimitingSeparatedProfile regime) :
    ∃ (c ε : ℝ) (kind : ProfilePlateau S → DepthRateKind),
      0 < c ∧ 0 < ε ∧
      (∀ u, profileDepthRateAllowed S u.val.val u.val.isLt (kind u)) ∧
      ∀ (α : Type*) [Fintype α] {F : ConeCoverageSequence regime}
        {T : SelectedProfileSequence F} (plateau : α → ProfilePlateau S)
        (hcover : ∀ u, ∃ a, plateau a = u)
        (H : ProfileDepthBatchData T S plateau (fun a => kind (plateau a)) (fun _ => ε)),
        ∀ u : ProfilePlateau S, StrictPlateauEligible S u → ∀ τ : ℝ,
          profilePlateauLeft S u < τ ∧ τ < S.b u.val → DirectionRowRankMargin H τ c := by
  classical
  obtain ⟨η, kind, hη, hallowed, hlog⟩ := exists_uniform_plateau_rate_margin S
  obtain ⟨κ, hκ, hb₀, _, _⟩ := S.balance
  let m : ℝ := min (η / 2) (-S.b ⟨0, by have := regime.dimension_ge_three; omega⟩)
  have hm : 0 < m := lt_min (by positivity) (by linarith)
  have hmη : m ≤ η / 2 := min_le_left _ _
  have hmfirst : m ≤ -S.b ⟨0, by have := regime.dimension_ge_three; omega⟩ :=
    min_le_right _ _
  obtain ⟨hpositive, _, hfinal⟩ := plateau_rank_margin_bounds (d := d) m hm
  refine ⟨plateauRankMargin m d, η / 8, kind, (hpositive d).1,
    by positivity, hallowed, ?_⟩
  intro α _ F T plateau hcover H u hu τ hτ
  have hsmall : ∀ a : α, 0 < η / 8 ∧ η / 8 ≤ η / 4 := fun _ => by constructor <;> linarith
  have hlogs : ∀ a : α, StrictPlateauEligible S (plateau a) →
      profileRateEndpointLog S (plateau a) (kind (plateau a)) ≤ -η :=
    fun a ha => hlog (plateau a) ha
  have hbound := separated_direction_rank_induction S H hcover η m hη hm hmη
    hmfirst hsmall hlogs u hu τ hτ
  intro ρ hρ
  filter_upwards [hbound ρ hρ] with i hi
  intro p Q hrow
  have htarget : 0 ≤ profileDirectionRankTarget S i τ := by
    unfold profileDirectionRankTarget
    exact div_nonneg
      (mul_nonneg (TrackD.RankCore.sigma_nonneg (regime.B_pos i).le _ _ _)
        (TrackD.RankCore.testDeg_pos (regime.B_pos i) _ _).le) (regime.A_pos i).le
  exact (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (hfinal u.val.val u.val.isLt.le)
      (S.sequence.width_pos i).2.le)) htarget).trans (hi p Q hrow)

end
end DistinctDistances.SparseCones
