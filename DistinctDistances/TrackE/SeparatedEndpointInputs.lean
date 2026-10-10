import DistinctDistances.TrackE.StrictRankInduction

/-! Actual-row inputs for the eligible separated endpoint,
sparse-cones.tex:783–793. All batch deletions precede the row choice. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- The last limiting target cut time, retaining the zero-based convention. -/
def profileLastTime (S : LimitingSeparatedProfile regime) : ℝ :=
  S.b ⟨d - 1, by have := regime.dimension_ge_three; omega⟩

/-- A terminal repeated-cut cluster begins at an actual open positive plateau. -/
theorem exists_final_open_plateau (S : LimitingSeparatedProfile regime) :
    ∃ u : ProfilePlateau S, S.b u.val = profileLastTime S := by
  classical
  unfold profileLastTime
  obtain ⟨c, hc, hb0, hblast, _⟩ := S.balance
  have hlt : S.b ⟨0, by have := regime.dimension_ge_three; omega⟩ <
      S.b ⟨d - 1, by have := regime.dimension_ge_three; omega⟩ := by linarith
  let F : Finset (Fin d) :=
    Finset.univ.filter (fun t => S.b t = S.b ⟨d - 1, by have := regime.dimension_ge_three; omega⟩)
  have hmem_last : (⟨d - 1, by have := regime.dimension_ge_three; omega⟩ : Fin d) ∈ F := by
    simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
  have hne : F.Nonempty := ⟨_, hmem_last⟩
  obtain ⟨j0, hj0_mem, hj0_min⟩ : ∃ j0 ∈ F, ∀ t ∈ F, j0 ≤ t :=
    ⟨F.min' hne, Finset.min'_mem F hne, fun t ht => Finset.min'_le F t ht⟩
  rw [Finset.mem_filter] at hj0_mem
  obtain ⟨_, hj0_eq⟩ := hj0_mem
  have hj0_ne0 : j0.val ≠ 0 := by
    intro h0
    have hj0_eq0 : j0 = (⟨0, by have := regime.dimension_ge_three; omega⟩ : Fin d) :=
      Fin.ext (by omega)
    rw [hj0_eq0] at hj0_eq
    linarith
  have hj0_ge1 : 1 ≤ j0.val := by omega
  have hprev_lt : S.b ⟨j0.val - 1, by have := j0.isLt; omega⟩ < S.b j0 := by
    have hle : S.b ⟨j0.val - 1, by have := j0.isLt; omega⟩ ≤ S.b j0 := by
      apply S.sorted
      exact Fin.mk_le_mk.mpr (by omega)
    by_contra hnot
    push Not at hnot
    -- hnot : S.b j0 ≤ S.b ⟨j0-1,...⟩, so equality
    have heq : S.b ⟨j0.val - 1, by have := j0.isLt; omega⟩ = S.b j0 :=
      le_antisymm hle hnot
    have ht0_mem : (⟨j0.val - 1, by have := j0.isLt; omega⟩ : Fin d) ∈ F := by
      simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [heq, hj0_eq]
    have hle_min := hj0_min _ ht0_mem
    have hval : j0.val ≤ j0.val - 1 := Fin.le_def.mp hle_min
    omega
  refine ⟨⟨j0, hj0_ge1, hprev_lt⟩, hj0_eq⟩

/-- Choose a fixed interior test close enough to the last endpoint before
selecting centers, rows or a density. -/
theorem exists_final_testing_time (S : LimitingSeparatedProfile regime)
    (u : ProfilePlateau S) (hu : S.b u.val = profileLastTime S)
    (c : ℝ) (hc : 0 < c) :
    ∃ τ : ℝ, profilePlateauLeft S u < τ ∧ τ < S.b u.val ∧
      (d : ℝ) * (profileLastTime S - τ) < c / 2 := by
  have hd3 := regime.dimension_ge_three
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hd1_pos : (0 : ℝ) < (d : ℝ) + 1 := by linarith
  have hleft_lt : profilePlateauLeft S u < S.b u.val := u.property.2
  have hlast_eq : S.b u.val = profileLastTime S := hu
  have hleft_last : profilePlateauLeft S u < profileLastTime S := hlast_eq ▸ hleft_lt
  have hdiv_pos : (0 : ℝ) < c / (2 * ((d : ℝ) + 1)) := by positivity
  let M : ℝ := max (profilePlateauLeft S u) (profileLastTime S - c / (2 * ((d : ℝ) + 1)))
  have hM_lt : M < profileLastTime S := by
    simp only [M, max_lt_iff]
    constructor
    · exact hleft_last
    · linarith
  let τ : ℝ := (M + profileLastTime S) / 2
  have hMτ : M < τ := by simp only [τ]; linarith
  have hτlast : τ < profileLastTime S := by simp only [τ]; linarith
  have hleftM : profilePlateauLeft S u ≤ M := le_max_left _ _
  have hdivM : profileLastTime S - c / (2 * ((d : ℝ) + 1)) ≤ M := le_max_right _ _
  have hleftτ : profilePlateauLeft S u < τ := lt_of_le_of_lt hleftM hMτ
  have hτb : τ < S.b u.val := hlast_eq ▸ hτlast
  refine ⟨τ, hleftτ, hτb, ?_⟩
  have hlastM_le : profileLastTime S - M ≤ c / (2 * ((d : ℝ) + 1)) := by linarith
  have hlastτ_eq : profileLastTime S - τ = (profileLastTime S - M) / 2 := by
    simp only [τ]; ring
  have hlastτ_le : profileLastTime S - τ ≤ c / (4 * ((d : ℝ) + 1)) := by
    rw [hlastτ_eq]
    have : (profileLastTime S - M) / 2 ≤ (c / (2 * ((d : ℝ) + 1))) / 2 :=
      div_le_div_of_nonneg_right hlastM_le (by norm_num : (0:ℝ) ≤ 2)
    have heq : (c / (2 * ((d : ℝ) + 1))) / 2 = c / (4 * ((d : ℝ) + 1)) := by
      rw [div_div]
      congr 1
      ring
    rwa [heq] at this
  have hd_nonneg : (0 : ℝ) ≤ (d : ℝ) := hd_pos.le
  have hprod_le : (d : ℝ) * (profileLastTime S - τ) ≤
      (d : ℝ) * (c / (4 * ((d : ℝ) + 1))) :=
    mul_le_mul_of_nonneg_left hlastτ_le hd_nonneg
  have hprod_lt : (d : ℝ) * (c / (4 * ((d : ℝ) + 1))) < c / 2 := by
    have hposA : (0 : ℝ) < 4 * ((d : ℝ) + 1) := by positivity
    rw [← mul_div_assoc, div_lt_iff₀ hposA]
    nlinarith [hc, hd_pos, mul_pos hc hd_pos]
  exact lt_of_le_of_lt hprod_le hprod_lt

/-- At the final cut σ is the complete limiting cut product, exactly N. -/
theorem profile_sigma_last (S : LimitingSeparatedProfile regime) (i : ℕ) :
    TrackD.sigma (regime.B i) (S.sequence.target i).width S.b (profileLastTime S) =
      regime.N i := by
  have hd3 := regime.dimension_ge_three
  have hdpos_nat : 0 < d := by omega
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos_nat
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdpos
  have hBpos := regime.B_pos i
  have hNpos := regime.N_pos i
  have hspos := (S.sequence.width_pos i).2
  have hlast : ∀ j : Fin d, S.b j ≤ profileLastTime S := by
    intro j
    unfold profileLastTime
    apply S.sorted
    show j ≤ ⟨d - 1, by omega⟩
    rw [Fin.le_def]
    simp only
    omega
  have hmin : ∀ j : Fin d,
      min (TrackD.testDeg (regime.B i) (S.sequence.target i).width (profileLastTime S))
        (TrackD.cutScale (regime.B i) (S.sequence.target i).width S.b j) =
      TrackD.cutScale (regime.B i) (S.sequence.target i).width S.b j := by
    intro j
    apply min_eq_right
    show TrackD.cutScale (regime.B i) (S.sequence.target i).width S.b j ≤
      TrackD.testDeg (regime.B i) (S.sequence.target i).width (profileLastTime S)
    unfold TrackD.cutScale
    exact TrackD.RankCore.testDeg_mono hBpos.le hspos.le (hlast j)
  have hsig : TrackD.sigma (regime.B i) (S.sequence.target i).width S.b (profileLastTime S) =
      ∏ j : Fin d, TrackD.cutScale (regime.B i) (S.sequence.target i).width S.b j := by
    unfold TrackD.sigma
    apply Finset.prod_congr rfl
    intro j _
    exact hmin j
  rw [hsig]
  have hcut : ∀ j : Fin d, TrackD.cutScale (regime.B i) (S.sequence.target i).width S.b j =
      regime.B i * Real.exp (S.b j * (S.sequence.target i).width) := by
    intro j
    rfl
  simp_rw [hcut]
  rw [Finset.prod_mul_distrib]
  have hprodB : (∏ _ : Fin d, regime.B i) = regime.B i ^ d := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hprodB]
  have hexp : (∏ j : Fin d, Real.exp (S.b j * (S.sequence.target i).width)) =
      Real.exp ((∑ j : Fin d, S.b j) * (S.sequence.target i).width) := by
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.sum_mul]
  rw [hexp, S.sum_zero]
  simp only [zero_mul, Real.exp_zero, mul_one]
  have hBdef : regime.B i = regime.N i ^ ((1 : ℝ) / (d : ℝ)) := rfl
  rw [hBdef]
  have hrpow : (regime.N i ^ ((1 : ℝ) / (d : ℝ))) ^ d =
      regime.N i ^ (((1 : ℝ) / (d : ℝ)) * (d : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
  rw [hrpow]
  have hone : ((1 : ℝ) / (d : ℝ)) * (d : ℝ) = 1 := by
    field_simp
  rw [hone, Real.rpow_one]

/-- Endpoint approximation costs at most half the fixed strict exponent.
The remaining exponent dominates the actual cone degree upper scale. -/
theorem endpoint_rank_target_dominates_cones (F : ConeCoverageSequence regime)
    (S : LimitingSeparatedProfile regime) (C c τ : ℝ) (hC : 0 < C) (hc : 0 < c)
    (hτ : τ < profileLastTime S)
    (hgap : (d : ℝ) * (profileLastTime S - τ) < c / 2) :
    ∀ᶠ i in atTop,
      (C * F.delta i * regime.N i / regime.A i) *
        (TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ + 1) <
      profileDirectionRankTarget S i τ * Real.exp (c * (S.sequence.target i).width) := by
  have hc2 : (0 : ℝ) < c / 2 := by linarith
  have hδ1 : ∀ᶠ i in atTop, F.delta i ≤ 1 := by
    have hlim := F.delta_tendsto.eventually (Iio_mem_nhds (show (1 : ℝ) > 0 by norm_num))
    filter_upwards [hlim] with i hi
    exact hi.le
  have hT1 := target_test_degree S τ
  obtain ⟨s₀, hs₀⟩ := TrackD.RankCore.absorb_constant (show (0 : ℝ) < 2 * C + 1 by positivity) hc2
  have hAbs : ∀ᶠ i in atTop,
      (2 * C + 1 : ℝ) ≤ Real.exp ((c / 2) * (S.sequence.target i).width) := by
    filter_upwards [S.sequence.target_grows.eventually_ge_atTop s₀] with i hi
    exact hs₀ _ hi
  filter_upwards [hδ1, hT1, hAbs] with i hδi hT1i hAbsi
  have hs_pos : (0 : ℝ) < (S.sequence.target i).width := (S.sequence.width_pos i).2
  have hs_nonneg : (0 : ℝ) ≤ (S.sequence.target i).width := hs_pos.le
  have hBpos : (0 : ℝ) < regime.B i := regime.B_pos i
  have hApos : (0 : ℝ) < regime.A i := regime.A_pos i
  have hNpos : (0 : ℝ) < regime.N i := regime.N_pos i
  have hB_nonneg : (0 : ℝ) ≤ regime.B i := hBpos.le
  have hTpos : (0 : ℝ) < TrackD.testDeg (TrackD.cfgB (regime.P i))
      (S.sequence.target i).width τ := by
    have hBcfg : regime.B i = TrackD.cfgB (regime.P i) := rfl
    rw [← hBcfg]
    exact TrackD.RankCore.testDeg_pos hBpos _ _
  have hTge1 : (1 : ℝ) ≤ TrackD.testDeg (TrackD.cfgB (regime.P i))
      (S.sequence.target i).width τ := hT1i
  have hτ_le : τ ≤ profileLastTime S := hτ.le
  have hlip := TrackD.RankCore.sigma_lipschitz hB_nonneg hs_nonneg hτ_le S.b
  have hsig_last := profile_sigma_last S i
  -- Unfold rank target and B/N/A identities.
  have hBcfg : regime.B i = TrackD.cfgB (regime.P i) := rfl
  have hrank_eq : profileDirectionRankTarget S i τ =
      TrackD.sigma (regime.B i) (S.sequence.target i).width S.b τ *
        TrackD.testDeg (regime.B i) (S.sequence.target i).width τ / regime.A i := rfl
  -- Lower bound N*T/A*exp((c/2)s) ≤ rank*exp(c s).
  have hLower : regime.N i *
      TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ /
        regime.A i *
      Real.exp ((c / 2) * (S.sequence.target i).width) ≤
      profileDirectionRankTarget S i τ * Real.exp (c * (S.sequence.target i).width) := by
    rw [hrank_eq, ← hBcfg]
    have hNle : regime.N i ≤
        TrackD.sigma (regime.B i) (S.sequence.target i).width S.b τ *
          Real.exp ((d : ℝ) * (profileLastTime S - τ) *
            (S.sequence.target i).width) := by
      rw [← hsig_last]
      exact hlip
    have hTA_nonneg : (0 : ℝ) ≤ TrackD.testDeg (regime.B i)
        (S.sequence.target i).width τ / regime.A i *
        Real.exp ((c / 2) * (S.sequence.target i).width) :=
      mul_nonneg (div_nonneg (TrackD.RankCore.testDeg_pos hBpos _ _).le hApos.le)
        (Real.exp_nonneg _)
    have hstep1 : regime.N i *
        TrackD.testDeg (regime.B i) (S.sequence.target i).width τ / regime.A i *
        Real.exp ((c / 2) * (S.sequence.target i).width) ≤
        (TrackD.sigma (regime.B i) (S.sequence.target i).width S.b τ *
          Real.exp ((d : ℝ) * (profileLastTime S - τ) *
            (S.sequence.target i).width)) *
          TrackD.testDeg (regime.B i) (S.sequence.target i).width τ / regime.A i *
        Real.exp ((c / 2) * (S.sequence.target i).width) := by
      have hmul := mul_le_mul_of_nonneg_right hNle hTA_nonneg
      -- Rearrange (N ≤ S*E) * (T/A*e) to N*T/A*e ≤ (S*E)*T/A*e
      calc regime.N i * TrackD.testDeg (regime.B i) (S.sequence.target i).width τ /
            regime.A i * Real.exp ((c / 2) * (S.sequence.target i).width)
          = (regime.N i) *
            (TrackD.testDeg (regime.B i) (S.sequence.target i).width τ / regime.A i *
              Real.exp ((c / 2) * (S.sequence.target i).width)) := by ring
        _ ≤ (TrackD.sigma (regime.B i) (S.sequence.target i).width S.b τ *
              Real.exp ((d : ℝ) * (profileLastTime S - τ) *
                (S.sequence.target i).width)) *
            (TrackD.testDeg (regime.B i) (S.sequence.target i).width τ / regime.A i *
              Real.exp ((c / 2) * (S.sequence.target i).width)) :=
          mul_le_mul_of_nonneg_right hNle (mul_nonneg (div_nonneg (TrackD.RankCore.testDeg_pos hBpos _ _).le hApos.le) (Real.exp_nonneg _))
        _ = (TrackD.sigma (regime.B i) (S.sequence.target i).width S.b τ *
              Real.exp ((d : ℝ) * (profileLastTime S - τ) *
                (S.sequence.target i).width)) *
            TrackD.testDeg (regime.B i) (S.sequence.target i).width τ / regime.A i *
            Real.exp ((c / 2) * (S.sequence.target i).width) := by ring
    have hexp_le : Real.exp ((d : ℝ) * (profileLastTime S - τ) *
          (S.sequence.target i).width) *
        Real.exp ((c / 2) * (S.sequence.target i).width) ≤
        Real.exp (c * (S.sequence.target i).width) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hle : (d : ℝ) * (profileLastTime S - τ) + c / 2 ≤ c := by linarith
      have hmul : ((d : ℝ) * (profileLastTime S - τ) + c / 2) *
          (S.sequence.target i).width ≤
          c * (S.sequence.target i).width :=
        mul_le_mul_of_nonneg_right hle hs_nonneg
      have heq : (d : ℝ) * (profileLastTime S - τ) * (S.sequence.target i).width +
          (c / 2) * (S.sequence.target i).width =
          ((d : ℝ) * (profileLastTime S - τ) + c / 2) *
            (S.sequence.target i).width := by ring
      linarith [hmul, heq]
    -- Combine: N*T/A*e_{c/2} ≤ S*T/A*e_c
    have hSTA_nonneg : (0 : ℝ) ≤ TrackD.sigma (regime.B i)
        (S.sequence.target i).width S.b τ *
        TrackD.testDeg (regime.B i) (S.sequence.target i).width τ / regime.A i :=
      div_nonneg (mul_nonneg (TrackD.RankCore.sigma_nonneg hB_nonneg _ _ _)
        (TrackD.RankCore.testDeg_pos hBpos _ _).le) hApos.le
    calc regime.N i * TrackD.testDeg (regime.B i) (S.sequence.target i).width τ /
          regime.A i * Real.exp ((c / 2) * (S.sequence.target i).width)
        ≤ (TrackD.sigma (regime.B i) (S.sequence.target i).width S.b τ *
            Real.exp ((d : ℝ) * (profileLastTime S - τ) *
              (S.sequence.target i).width)) *
          TrackD.testDeg (regime.B i) (S.sequence.target i).width τ / regime.A i *
          Real.exp ((c / 2) * (S.sequence.target i).width) := hstep1
      _ = TrackD.sigma (regime.B i) (S.sequence.target i).width S.b τ *
          TrackD.testDeg (regime.B i) (S.sequence.target i).width τ / regime.A i *
          (Real.exp ((d : ℝ) * (profileLastTime S - τ) *
            (S.sequence.target i).width) *
            Real.exp ((c / 2) * (S.sequence.target i).width)) := by ring
      _ ≤ TrackD.sigma (regime.B i) (S.sequence.target i).width S.b τ *
          TrackD.testDeg (regime.B i) (S.sequence.target i).width τ / regime.A i *
          Real.exp (c * (S.sequence.target i).width) :=
        mul_le_mul_of_nonneg_left hexp_le hSTA_nonneg
  -- Rewrite hLower to use cfgB (definitionally equal) for the final comparison.
  have hLower_cfg : regime.N i *
      TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ /
        regime.A i *
      Real.exp ((c / 2) * (S.sequence.target i).width) ≤
      profileDirectionRankTarget S i τ * Real.exp (c * (S.sequence.target i).width) := by
    simpa only [← hBcfg] using hLower
  -- Upper bound for the cone side: C*δ*(T+1) < T*exp((c/2)s).
  have hConeLt : C * F.delta i *
      (TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ + 1) <
      TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ *
        Real.exp ((c / 2) * (S.sequence.target i).width) := by
    have hT1_le : TrackD.testDeg (TrackD.cfgB (regime.P i))
        (S.sequence.target i).width τ + 1 ≤
        2 * TrackD.testDeg (TrackD.cfgB (regime.P i))
          (S.sequence.target i).width τ := by linarith
    have h2Cδ_lt : 2 * C * F.delta i <
        Real.exp ((c / 2) * (S.sequence.target i).width) := by
      have hδ_le : F.delta i ≤ 1 := hδi
      have hδ_pos : (0 : ℝ) < F.delta i := F.delta_pos i
      have h2Cδ_le : 2 * C * F.delta i ≤ 2 * C := by
        nlinarith [hC, hδ_le, hδ_pos]
      have h2C_lt : 2 * C < 2 * C + 1 := by linarith
      calc 2 * C * F.delta i ≤ 2 * C := h2Cδ_le
        _ < 2 * C + 1 := h2C_lt
        _ ≤ Real.exp ((c / 2) * (S.sequence.target i).width) := hAbsi
    calc C * F.delta i *
          (TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ + 1)
        ≤ C * F.delta i * (2 * TrackD.testDeg (TrackD.cfgB (regime.P i))
            (S.sequence.target i).width τ) :=
          mul_le_mul_of_nonneg_left hT1_le (mul_nonneg hC.le (F.delta_pos i).le)
      _ = (2 * C * F.delta i) *
          TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ := by ring
      _ < Real.exp ((c / 2) * (S.sequence.target i).width) *
          TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ :=
        mul_lt_mul_of_pos_right h2Cδ_lt hTpos
      _ = TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ *
          Real.exp ((c / 2) * (S.sequence.target i).width) := by ring
  -- Cancel N/A > 0 to conclude.
  have hNApos : (0 : ℝ) < regime.N i / regime.A i :=
    div_pos hNpos hApos
  have hFinal : (C * F.delta i * regime.N i / regime.A i) *
      (TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ + 1) <
      regime.N i * TrackD.testDeg (TrackD.cfgB (regime.P i))
        (S.sequence.target i).width τ / regime.A i *
        Real.exp ((c / 2) * (S.sequence.target i).width) := by
    have heq1 : (C * F.delta i * regime.N i / regime.A i) *
        (TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ + 1) =
        (regime.N i / regime.A i) * (C * F.delta i *
          (TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ + 1)) := by ring
    have heq2 : regime.N i * TrackD.testDeg (TrackD.cfgB (regime.P i))
          (S.sequence.target i).width τ / regime.A i *
          Real.exp ((c / 2) * (S.sequence.target i).width) =
        (regime.N i / regime.A i) * (TrackD.testDeg (TrackD.cfgB (regime.P i))
            (S.sequence.target i).width τ *
          Real.exp ((c / 2) * (S.sequence.target i).width)) := by ring
    rw [heq1, heq2]
    exact mul_lt_mul_of_pos_left hConeLt hNApos
  exact hFinal.trans_le hLower_cfg

/-- The literal homogeneous rank of covered radial directions is bounded
by the whole directional curve family's Hilbert function. -/
theorem covered_row_direction_rank_upper (C : ProjectiveFamily.Family d)
    (hC : TrackD.IsDirectionalFamily C) (p : RPoint d) (Q : Finset (RPoint d))
    (hQ : ∀ q ∈ Q, TrackD.DirIn C p q) (L : ℕ) :
    (rowDirectionRank (TrackD.toC p) Q L : ℝ) ≤
      (ProjectiveFamily.degree C : ℝ) * (L + 1 : ℝ) := by
  classical
  have hPure : ProjectiveFamily.IsPure C 1 := by
    intro V hV
    obtain ⟨hirr, hdim, _⟩ := hC V hV
    exact ⟨hirr, hdim⟩
  have hSub : rowDirections (TrackD.toC p) Q ⊆ (ProjectiveFamily.locus C).points := by
    intro z hz
    obtain ⟨q, hq, h, rfl⟩ := hz
    obtain ⟨h', hmem⟩ := hQ q hq
    have heq : radialProjection (TrackD.toC p) (TrackD.toC q) h =
        radialProjection (TrackD.toC p) (TrackD.toC q) h' := rfl
    rw [heq] at *
    have hmem' : radialProjection (TrackD.toC p) (TrackD.toC q) h' ∈
        ⋃ γ ∈ C, γ.points := by
      simpa only [TrackD.familyPoints] using hmem
    have hlocus := ProjectiveFamily.points_locus C
    rw [hlocus]
    exact hmem'
  have hLe : rowDirectionRank (TrackD.toC p) Q L ≤
      (ProjectiveFamily.locus C).hilbert L :=
    row_direction_rank_le _ _ _ hSub L
  have hUpperQ : ((ProjectiveFamily.hilbert C L : ℕ) : ℚ) ≤
      ProjectiveFamily.degree C * (((L + 1).choose 1 : ℕ) : ℚ) := by
    have h := TrackA.poly_hilbert_projective_upper C 1 hPure L
    simpa only [Nat.add_comm L 1] using h
  have hChoose : ((L + 1).choose 1 : ℕ) = L + 1 := Nat.choose_one_right _
  have hRankQ : ((rowDirectionRank (TrackD.toC p) Q L : ℕ) : ℚ) ≤
      ((ProjectiveFamily.hilbert C L : ℕ) : ℚ) := by
    have h' : rowDirectionRank (TrackD.toC p) Q L ≤ ProjectiveFamily.hilbert C L := by
      simpa only [ProjectiveFamily.hilbert] using hLe
    exact_mod_cast h'
  have hChainQ : ((rowDirectionRank (TrackD.toC p) Q L : ℕ) : ℚ) ≤
      ProjectiveFamily.degree C * (((L + 1).choose 1 : ℕ) : ℚ) :=
    hRankQ.trans hUpperQ
  rw [hChoose] at hChainQ
  have hChainR : ((rowDirectionRank (TrackD.toC p) Q L : ℕ) : ℝ) ≤
      (ProjectiveFamily.degree C : ℝ) * ((L + 1 : ℕ) : ℝ) := by
    exact_mod_cast hChainQ
  simpa only [Nat.cast_add, Nat.cast_one] using hChainR

/-- A positive-density finite graph has a row of at least the same density.
This counts physical targets and does not assume direction injectivity. -/
theorem exists_dense_physical_graph_row (X Y : Finset (RPoint d))
    (Γ : Finset (RPoint d × RPoint d)) (hΓ : Γ ⊆ X ×ˢ Y)
    (hX : X.Nonempty) (hY : Y.Nonempty) (ρ : ℝ) (hρ : 0 < ρ)
    (hdense : ρ * (X.card : ℝ) * Y.card ≤ Γ.card) :
    ∃ p ∈ X, ρ * (Y.card : ℝ) ≤ ((Y.filter (fun q => (p, q) ∈ Γ)).card : ℝ) := by
  classical
  by_contra hneg
  push Not at hneg
  have hlt : ∀ p ∈ X,
      ((Y.filter (fun q => (p, q) ∈ Γ)).card : ℝ) < ρ * (Y.card : ℝ) :=
    fun p hp => hneg p hp
  -- Sum of row sizes equals Γ.card.
  have hsum_nat : ∑ p ∈ X, (Y.filter (fun q => (p, q) ∈ Γ)).card = Γ.card := by
    have hdisj : Set.PairwiseDisjoint (↑X : Set (RPoint d))
        (fun p => Γ.filter (fun pq : RPoint d × RPoint d => pq.1 = p)) := by
      intro p _ q _ hne
      apply Finset.disjoint_left.mpr
      intro pq h1 h2
      obtain ⟨_, h1eq⟩ := Finset.mem_filter.mp h1
      obtain ⟨_, h2eq⟩ := Finset.mem_filter.mp h2
      exact hne (h1eq.symm.trans h2eq)
    have hcover : Γ = X.biUnion (fun p => Γ.filter (fun pq : RPoint d × RPoint d => pq.1 = p)) := by
      ext pq
      constructor
      · intro hpq
        have hmem := hΓ hpq
        rw [Finset.mem_product] at hmem
        exact Finset.mem_biUnion.mpr ⟨pq.1, hmem.1, Finset.mem_filter.mpr ⟨hpq, rfl⟩⟩
      · intro hpq
        obtain ⟨p, _, hmem⟩ := Finset.mem_biUnion.mp hpq
        exact (Finset.mem_filter.mp hmem).1
    have hcard_eq : ∀ p ∈ X, (Γ.filter (fun pq : RPoint d × RPoint d => pq.1 = p)).card =
        (Y.filter (fun q => (p, q) ∈ Γ)).card := by
      intro p hp
      have himg : Γ.filter (fun pq : RPoint d × RPoint d => pq.1 = p) =
          (Y.filter (fun q => (p, q) ∈ Γ)).image (fun q => (p, q)) := by
        ext pq
        constructor
        · intro hmem
          obtain ⟨hmemΓ, hfst⟩ := Finset.mem_filter.mp hmem
          have hmemXY := hΓ hmemΓ
          rw [Finset.mem_product] at hmemXY
          have hpq_eq : pq = (p, pq.2) := by
            obtain ⟨a, b⟩ := pq
            simp at hfst ⊢
            rw [hfst]
          rw [hpq_eq]
          apply Finset.mem_image.mpr
          refine ⟨pq.2, ?_, rfl⟩
          rw [Finset.mem_filter]
          constructor
          · exact hmemXY.2
          · have : (p, pq.2) ∈ Γ := hpq_eq ▸ hmemΓ
            exact this
        · intro hmem
          obtain ⟨q, hqmem, rfl⟩ := Finset.mem_image.mp hmem
          rw [Finset.mem_filter] at hqmem
          obtain ⟨_, hqΓ⟩ := hqmem
          exact Finset.mem_filter.mpr ⟨hqΓ, rfl⟩
      rw [himg]
      exact Finset.card_image_of_injective _ (fun a b hab => (Prod.mk.inj hab).2)
    have hbiUnion_card : (X.biUnion (fun p => Γ.filter (fun pq : RPoint d × RPoint d => pq.1 = p))).card =
        ∑ p ∈ X, (Γ.filter (fun pq : RPoint d × RPoint d => pq.1 = p)).card :=
      Finset.card_biUnion hdisj
    rw [← hcover, hbiUnion_card] at *
    have : ∑ p ∈ X, (Y.filter (fun q => (p, q) ∈ Γ)).card =
        ∑ p ∈ X, (Γ.filter (fun pq : RPoint d × RPoint d => pq.1 = p)).card := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [hcard_eq p hp]
    rw [this]
  have hsum_real : (∑ p ∈ X, ((Y.filter (fun q => (p, q) ∈ Γ)).card : ℝ)) =
      (Γ.card : ℝ) := by
    exact_mod_cast hsum_nat
  have hsum_lt : (∑ p ∈ X, ((Y.filter (fun q => (p, q) ∈ Γ)).card : ℝ)) <
      (∑ _p ∈ X, ρ * (Y.card : ℝ)) :=
    Finset.sum_lt_sum_of_nonempty hX hlt
  rw [hsum_real] at hsum_lt
  have hsum_eq : (∑ _p ∈ X, ρ * (Y.card : ℝ)) = ρ * (X.card : ℝ) * Y.card := by
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hsum_eq] at hsum_lt
  linarith

/-- Every later nonempty row of the literal batch graph retains the source
configuration membership, every batch survival condition and the covered direction. -/
theorem profile_batch_row_facts {α : Type*} [Fintype α]
    {F : ConeCoverageSequence regime} (T : SelectedProfileSequence F)
    (S : LimitingSeparatedProfile regime)
    (hsource : ∀ i, T.sources i = {S.sequence.source i})
    (htarget : ∀ i, T.targets i = {S.sequence.target i})
    {plateau : α → ProfilePlateau S} {kind : α → DepthRateKind} {ε : α → ℝ}
    (H : ProfileDepthBatchData T S plateau kind ε)
    (i : ℕ) (p : RPoint d) (Q : Finset (RPoint d)) (hQ : Q.Nonempty)
    (hedges : ∀ q ∈ Q, (p, q) ∈ profileBatchGraph H i) (ρ : ℝ)
    (hdense : ρ * (((S.sequence.target i).pts.image TrackD.toC).card : ℝ) ≤ Q.card) :
    p ∈ regime.P i ∧ DenseSurvivingDirectionRow H i (TrackD.toC p) Q ρ ∧
      (∀ q ∈ Q, TrackD.DirIn (F.family i p) p q) := by
  classical
  obtain ⟨q0, hq0⟩ := hQ
  have hmem0 := hedges q0 hq0
  rw [profileBatchGraph, Finset.mem_filter] at hmem0
  obtain ⟨hterm0, hgood0⟩ := hmem0
  have hterm_mem := (mem_terminalSelectedGraph T i p q0).mp hterm0
  obtain ⟨hp_pool, _, hinc0, _⟩ := hterm_mem
  have hsource_pool : TrackD.poolPts (T.sources i) = (S.sequence.source i).pts := by
    rw [hsource i]
    simp [TrackD.poolPts]
  have htarget_pool : TrackD.poolPts (T.targets i) = (S.sequence.target i).pts := by
    rw [htarget i]
    simp [TrackD.poolPts]
  have hp_src : p ∈ (S.sequence.source i).pts := by
    rwa [hsource_pool] at hp_pool
  have hp_P : p ∈ regime.P i := (S.sequence.base_good i).1.subset hp_src
  have hQ_sub : Q ⊆ (S.sequence.target i).pts := by
    intro q hq
    have hmem := hedges q hq
    rw [profileBatchGraph, Finset.mem_filter] at hmem
    obtain ⟨hterm, _⟩ := hmem
    have hmemT := (mem_terminalSelectedGraph T i p q).mp hterm
    obtain ⟨_, hq_pool, _, _⟩ := hmemT
    rwa [htarget_pool] at hq_pool
  have hp_image : TrackD.toC p ∈ (S.sequence.source i).pts.image TrackD.toC :=
    Finset.mem_image.mpr ⟨p, hp_src, rfl⟩
  have hcenters_eq : (fun i => (S.sequence.source i).pts.image TrackD.toC) i =
      (S.sequence.source i).pts.image TrackD.toC := rfl
  -- badCenters avoidance from the witness row edge
  have hp_notbad : TrackD.toC p ∉ H.batch.badCenters i := hgood0.1
  -- physical distinctness via SelectedIncidence
  have hneq : ∀ q ∈ Q, TrackD.toC q ≠ TrackD.toC p := by
    intro q hq
    have hmem := hedges q hq
    rw [profileBatchGraph, Finset.mem_filter] at hmem
    obtain ⟨hterm, _⟩ := hmem
    have hmemT := (mem_terminalSelectedGraph T i p q).mp hterm
    obtain ⟨_, _, hinc, _⟩ := hmemT
    obtain ⟨hne, _, _, _⟩ := hinc
    exact fun heq => hne ((profile_toC_injective heq).symm)
  have hsurvives : ∀ q ∈ Q, TrackD.toC q ∉ batchBadTargets
      (fun a => H.data (plateau a))
      (fun i => (S.sequence.target i).pts.image TrackD.toC) H.batch.bad i (TrackD.toC p) := by
    intro q hq hbad
    have hmem := hedges q hq
    rw [profileBatchGraph, Finset.mem_filter] at hmem
    obtain ⟨_, hgood⟩ := hmem
    apply hgood.2
    -- (toC p, toC q) ∈ batchBadPairs
    have hq_image : TrackD.toC q ∈ (S.sequence.target i).pts.image TrackD.toC := by
      have hq_src : q ∈ (S.sequence.target i).pts := hQ_sub hq
      exact Finset.mem_image.mpr ⟨q, hq_src, rfl⟩
    have hp_c : TrackD.toC p ∈ (S.sequence.source i).pts.image TrackD.toC := hp_image
    rw [batchBadPairs, Finset.mem_filter]
    refine ⟨Finset.mem_product.mpr ⟨hp_c, hq_image⟩, ?_⟩
    rw [batchBadTargets, Finset.mem_filter] at hbad
    obtain ⟨_, a, ha⟩ := hbad
    exact ⟨a, ha⟩
  have hDir : ∀ q ∈ Q, TrackD.DirIn (F.family i p) p q := by
    intro q hq
    have hmem := hedges q hq
    rw [profileBatchGraph, Finset.mem_filter] at hmem
    obtain ⟨hterm, _⟩ := hmem
    have hmemT := (mem_terminalSelectedGraph T i p q).mp hterm
    obtain ⟨_, _, hinc, _⟩ := hmemT
    obtain ⟨_, hdir, _, _⟩ := hinc
    exact hdir
  refine ⟨hp_P, ⟨hp_image, hp_notbad, hQ_sub, hneq, hsurvives, hdense⟩, hDir⟩

end
end DistinctDistances.SparseCones
