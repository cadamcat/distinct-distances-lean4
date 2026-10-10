import DistinctDistances.TrackE.CommonRankInduction
import DistinctDistances.TrackE.CommonImageTesting
import DistinctDistances.TrackD.Profiles.RegularityChosenProduct
import DistinctDistances.TrackE.MERankAux

/-! The common label rank before the first cut, sparse-cones.tex:232–237. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

private lemma finite_exponents_initial_aux (σ : Type*) [Fintype σ] (D : ℕ) :
    Finite {m : σ →₀ ℕ // m.sum (fun _ e => e) ≤ D} := by
  classical
  have hbounded : Finite {m : σ →₀ ℕ // ∀ a, m a ≤ D} :=
    ((Set.Finite.pi' fun _ => Set.finite_le_nat D).preimage
      DFunLike.coe_injective.injOn).to_subtype
  letI : Finite {m : σ →₀ ℕ // ∀ a, m a ≤ D} := hbounded
  refine Finite.of_injective (fun m : {m : σ →₀ ℕ // m.sum (fun _ e => e) ≤ D} =>
    (⟨m.1, fun a => ?_⟩ : {m : σ →₀ ℕ // ∀ a, m a ≤ D})) ?_
  · by_cases ha : m.1 a = 0
    · exact ha ▸ Nat.zero_le _
    · exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finsupp.mem_support_iff.mpr ha)).trans m.2
  · intro a b h
    apply Subtype.ext
    exact congrArg (fun x : {m : σ →₀ ℕ // ∀ a, m a ≤ D} => x.1) h

/-- sc:common-rank.initial (sparse-cones.tex:232–237): before the first cut,
two successive full-dimensional no-capture steps force the degree-`⌊T⌋`
envelope of every dense label graph to be the whole `(2d-1)`-dimensional
label chart, of rank `≍ T^{2d-1} ≥ σ² min(1, T/(D_1D_2))`. When `T < 1`
the rank at degree zero is one and the target is below one (the paper's
rank-one convention). -/
theorem common_rank_initial {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (M : CommonPoolProfile T) (τ : ℝ)
    (hτ : τ < M.b ⟨0, by have := regime.dimension_ge_three; omega⟩) :
    ∀ θ : ℝ, 0 < θ → CommonRankAt M τ θ := by
  classical
  have hd3 := regime.dimension_ge_three
  intro θ hθ ρ hρ
  set b0 := M.b ⟨0, by have := regime.dimension_ge_three; omega⟩ with hb0def
  have hτb0 : τ < b0 := hτ
  set ξ : ℝ := (b0 - τ) / 2 with hξdef
  have hξ : 0 < ξ := by dsimp [ξ]; linarith
  have hOnPlateau : TrackD.OnPlateau M.b 0 ξ τ :=
    common_initial_OnPlateau M τ hτ
  -- Product testing inputs for the `T ≥ 1` branch (`K = 1`, bad fraction `ρ/2`).
  obtain ⟨θ1, hθ1, η, hη, hηξ, ρ0, hρ0, s1, hproduct⟩ :=
    TrackD.prof_product_testing_labels_with_margin d hd3 (ρ / 2) (by positivity) ξ hξ 1 le_rfl
  have hPoolGood_ev : ∀ᶠ i in atTop,
      TrackD.PoolGood (regime.P i) θ1 η 1 (ρ0 / 2) (T.sources i) (M.s i) M.b ∧
      TrackD.PoolGood (regime.P i) θ1 η 1 (ρ0 / 2) (T.targets i) (M.s i) M.b := by
    have hρ02 : (0 : ℝ) < ρ0 / 2 := by positivity
    filter_upwards [M.good θ1 hθ1 η hη 1 le_rfl (ρ0 / 2) hρ02] with i hi
    exact hi
  have hwidth_ge : ∀ᶠ i in atTop, s1 ≤ M.s i :=
    M.width_grows.eventually_ge_atTop s1
  -- Absorption for the `T ≥ 1` final (`h = 2d-1`, `c = 1/h!`).
  set hInit : ℕ := 2 * d - 1 with hhInitdef
  have hInit_eq : hInit = 2 * d - 1 := rfl
  have hfac_pos : (0 : ℝ) < (Nat.factorial hInit : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  set cInit : ℝ := 1 / (Nat.factorial hInit : ℝ) with hcInitdef
  have hcInit_pos : 0 < cInit := by dsimp [cInit]; positivity
  have h4hc_pos : (0 : ℝ) < 4 ^ hInit / cInit := by positivity
  have hθ2 : (0 : ℝ) < θ / 2 := by positivity
  have habs_eq := common_absorb_eventually M (4 ^ hInit / cInit) (θ / 2) h4hc_pos hθ2
  have hSpos_ev : ∀ᶠ i in atTop, 0 < ((TrackD.poolPts (T.sources i)).card : ℝ) := by
    have hlow := M.source_size.1 1 one_pos
    filter_upwards [hlow] with i hi
    have hNpos := regime.N_pos i
    have hexp_pos2 := Real.exp_pos (-1 * M.s i)
    have hprod_pos : (0 : ℝ) < regime.N i * Real.exp (-1 * M.s i) :=
      mul_pos hNpos hexp_pos2
    have hle := hi ()
    linarith
  have hTpool_ev : ∀ᶠ i in atTop, 0 < ((TrackD.poolPts (T.targets i)).card : ℝ) := by
    have hlow := M.target_size.1 1 one_pos
    filter_upwards [hlow] with i hi
    have hNpos := regime.N_pos i
    have hexp_pos2 := Real.exp_pos (-1 * M.s i)
    have hprod_pos : (0 : ℝ) < regime.N i * Real.exp (-1 * M.s i) :=
      mul_pos hNpos hexp_pos2
    have hle := hi ()
    linarith
  filter_upwards [hPoolGood_ev, hwidth_ge, habs_eq, hSpos_ev, hTpool_ev] with i hi_PoolGood hi_width hi_abs hi_Spool hi_Tpool
  intro i₀ Γ hΓ hchart hdense
  set Tdeg := TrackD.testDeg (regime.B i) (M.s i) τ with hTdef
  set Lnat : ℕ := ⌊Tdeg⌋₊ with hLdef
  have hTpos : 0 < Tdeg := TrackD.RankCore.testDeg_pos (regime.B_pos i) _ _
  have hTnn : (0 : ℝ) ≤ Tdeg := hTpos.le
  have hspos := M.width_pos i
  by_cases hTlt : Tdeg < 1
  · have hEeq0 : Lnat = 0 := by
      rw [hLdef]
      exact Nat.floor_eq_zero.mpr hTlt
    have hΓposR : (0 : ℝ) < (Γ.card : ℝ) := by
      have hprod_pos : (0 : ℝ) < ρ * ((TrackD.poolPts (T.sources i)).card : ℝ) *
          ((TrackD.poolPts (T.targets i)).card : ℝ) :=
        mul_pos (mul_pos hρ hi_Spool) hi_Tpool
      exact lt_of_lt_of_le hprod_pos hdense
    have hΓcard_pos : 0 < Γ.card := Nat.cast_pos.mp hΓposR
    have hΓne : Γ.Nonempty := Finset.card_pos.mp hΓcard_pos
    have hrank_ge1 : (1 : ℝ) ≤ (commonLabelRank i₀ Γ Lnat : ℝ) := by
      rw [hEeq0]
      have h1 : 1 ≤ commonLabelRank i₀ Γ 0 :=
        commonLabelRank_zero_ge_one d i₀ Γ hΓne
      exact_mod_cast h1
    have hsigma_eq := common_sigma_initial_eq M τ hτ i
    set D0 := TrackD.cutScale (regime.B i) (M.s i) M.b
      ⟨0, by have := regime.dimension_ge_three; omega⟩ with hD0def
    set D1 := TrackD.cutScale (regime.B i) (M.s i) M.b
      ⟨1, by have := regime.dimension_ge_three; omega⟩ with hD1def
    have htarget_eq : commonRankTarget M i τ =
        (Tdeg ^ d) ^ 2 * min 1 (Tdeg / (D0 * D1)) := by
      unfold commonRankTarget
      rw [hsigma_eq]
    have htarget_le_pow : commonRankTarget M i τ ≤ Tdeg ^ (2 * d) := by
      have hmin_le : min 1 (Tdeg / (D0 * D1)) ≤ 1 := min_le_left _ _
      have hsq_nn : (0 : ℝ) ≤ (Tdeg ^ d) ^ 2 := sq_nonneg _
      have hle : (Tdeg ^ d) ^ 2 * min 1 (Tdeg / (D0 * D1)) ≤ (Tdeg ^ d) ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hmin_le hsq_nn
      have hpow : (Tdeg ^ d) ^ 2 = Tdeg ^ (2 * d) := by
        rw [← pow_mul]
        congr 1
        ring
      calc commonRankTarget M i τ = (Tdeg ^ d) ^ 2 * min 1 (Tdeg / (D0 * D1)) :=
          htarget_eq
        _ ≤ (Tdeg ^ d) ^ 2 * 1 := hle
        _ = Tdeg ^ (2 * d) := by rw [hpow, mul_one]
    have hdpos : 0 < d := by omega
    have h2d_ne : 2 * d ≠ 0 := by omega
    have hTpow_lt1 : Tdeg ^ (2 * d) < 1 :=
      pow_lt_one₀ hTnn hTlt h2d_ne
    have htarget_lt1 : commonRankTarget M i τ < 1 :=
      lt_of_le_of_lt htarget_le_pow hTpow_lt1
    have hE1_le : Real.exp (-θ * M.s i) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have hle : -θ * M.s i ≤ 0 := by
        have hprod : (0 : ℝ) ≤ θ * M.s i := mul_nonneg hθ.le hspos.le
        linarith
      exact hle
    calc commonRankTarget M i τ * Real.exp (-θ * M.s i)
        ≤ 1 * 1 :=
          mul_le_mul (le_of_lt htarget_lt1) hE1_le (Real.exp_nonneg _) zero_le_one
      _ = 1 := mul_one _
      _ ≤ (commonLabelRank i₀ Γ Lnat : ℝ) := hrank_ge1
  · have hTge1 : 1 ≤ Tdeg := le_of_not_gt hTlt
    have hLge1 : 1 ≤ Lnat := Nat.le_floor (by simpa using hTge1)
    have hLge : Tdeg / 2 ≤ (Lnat : ℝ) := common_floor_ge_half hTge1
    have hsigma_eq := common_sigma_initial_eq M τ hτ i
    set D0 := TrackD.cutScale (regime.B i) (M.s i) M.b
      ⟨0, by have := regime.dimension_ge_three; omega⟩ with hD0def
    set D1 := TrackD.cutScale (regime.B i) (M.s i) M.b
      ⟨1, by have := regime.dimension_ge_three; omega⟩ with hD1def
    have hD0pos : 0 < D0 := TrackD.RankCore.testDeg_pos (regime.B_pos i) _ _
    have hD1pos : 0 < D1 := TrackD.RankCore.testDeg_pos (regime.B_pos i) _ _
    have hD0nn : (0 : ℝ) ≤ D0 := hD0pos.le
    have hD1nn : (0 : ℝ) ≤ D1 := hD1pos.le
    have hTD0 : Tdeg ≤ D0 := by
      have hle : τ ≤ M.b ⟨0, by have := regime.dimension_ge_three; omega⟩ :=
        le_of_lt hτ
      have h0le : (⟨0, by have := regime.dimension_ge_three; omega⟩ : Fin d) ≤
          ⟨0, by have := regime.dimension_ge_three; omega⟩ := le_rfl
      unfold D0 Tdeg
      exact TrackD.RankCore.testDeg_mono (regime.B_pos i).le hspos.le hle
    have hTD1 : Tdeg ≤ D1 := by
      have hle : τ ≤ M.b ⟨1, by have := regime.dimension_ge_three; omega⟩ := by
        have h0le : (⟨0, by have := regime.dimension_ge_three; omega⟩ : Fin d) ≤
            ⟨1, by have := regime.dimension_ge_three; omega⟩ :=
          Fin.le_def.mpr (Nat.zero_le _)
        have hba := M.sorted h0le
        exact le_trans (le_of_lt hτ) hba
      unfold D1 Tdeg
      exact TrackD.RankCore.testDeg_mono (regime.B_pos i).le hspos.le hle
    have hD0D1_ge : Tdeg ^ 2 ≤ D0 * D1 := by
      have hle : Tdeg * Tdeg ≤ D0 * D1 :=
        mul_le_mul hTD0 hTD1 hTnn hD0nn
      rwa [← pow_two] at hle
    have htarget_eq : commonRankTarget M i τ =
        (Tdeg ^ d) ^ 2 * min 1 (Tdeg / (D0 * D1)) := by
      unfold commonRankTarget
      rw [hsigma_eq]
    have htarget_upper : commonRankTarget M i τ ≤ Tdeg ^ hInit := by
      have hpow2d : (Tdeg ^ d) ^ 2 = Tdeg ^ (2 * d) := by
        rw [← pow_mul]
        congr 1
        ring
      have hmin_le : min 1 (Tdeg / (D0 * D1)) ≤ Tdeg / (D0 * D1) :=
        min_le_right _ _
      have hsq_nn : (0 : ℝ) ≤ (Tdeg ^ d) ^ 2 := sq_nonneg _
      have hle1 : (Tdeg ^ d) ^ 2 * min 1 (Tdeg / (D0 * D1)) ≤
          (Tdeg ^ d) ^ 2 * (Tdeg / (D0 * D1)) :=
        mul_le_mul_of_nonneg_left hmin_le hsq_nn
      have hTpow_pos : (0 : ℝ) < Tdeg ^ 2 := by positivity
      have hD01_pos : (0 : ℝ) < D0 * D1 := mul_pos hD0pos hD1pos
      have hT2d1_eq : Tdeg ^ (2 * d) * (Tdeg / (D0 * D1)) =
          (Tdeg ^ (2 * d + 1) / (D0 * D1)) := by ring
      -- `T^{2d} * (T/(D0D1)) = T^{2d+1}/(D0D1) ≤ T^{2d+1}/T^2 = T^{2d-1} = T^hInit`
      have hle2 : Tdeg ^ (2 * d) * (Tdeg / (D0 * D1)) ≤
          Tdeg ^ (2 * d + 1) / Tdeg ^ 2 := by
        have heq : Tdeg ^ (2 * d) * (Tdeg / (D0 * D1)) =
            Tdeg ^ (2 * d + 1) / (D0 * D1) := by
          have hpow_add : Tdeg ^ (2 * d) * Tdeg = Tdeg ^ (2 * d + 1) := by
            rw [← pow_succ]
          calc Tdeg ^ (2 * d) * (Tdeg / (D0 * D1))
              = (Tdeg ^ (2 * d) * Tdeg) / (D0 * D1) := by ring
            _ = Tdeg ^ (2 * d + 1) / (D0 * D1) := by rw [hpow_add]
        rw [heq]
        apply div_le_div_of_nonneg_left (by positivity) hTpow_pos hD0D1_ge
      have hpow_div : Tdeg ^ (2 * d + 1) / Tdeg ^ 2 = Tdeg ^ hInit := by
        have hpred : 2 * d + 1 = hInit + 2 := by omega
        rw [hpred]
        -- `T^{h+2}/T^2 = T^h`
        have hpow_add : Tdeg ^ (hInit + 2) = Tdeg ^ hInit * Tdeg ^ 2 := pow_add _ _ _
        rw [hpow_add]
        exact mul_div_cancel_right₀ _ (ne_of_gt hTpow_pos)
      calc commonRankTarget M i τ
          = (Tdeg ^ d) ^ 2 * min 1 (Tdeg / (D0 * D1)) := htarget_eq
        _ ≤ (Tdeg ^ d) ^ 2 * (Tdeg / (D0 * D1)) := hle1
        _ = Tdeg ^ (2 * d) * (Tdeg / (D0 * D1)) := by rw [hpow2d]
        _ ≤ Tdeg ^ (2 * d + 1) / Tdeg ^ 2 := hle2
        _ = Tdeg ^ hInit := hpow_div
    have hlow : cInit * 1 * Real.exp (-(θ / 2) * M.s i) * (Lnat : ℝ) ^ hInit ≤
        (commonLabelRank i₀ Γ Lnat : ℝ) := by
      have hC_le_rank : ((Lnat + hInit).choose hInit : ℝ) ≤
          (commonLabelRank i₀ Γ Lnat : ℝ) := by
        -- Chart in pair coordinates (all complex labels with `u_{i₀}=1`).
        set Chart : Set (Fin d ⊕ Fin d → ℂ) :=
          (fun xy : Point d × Point d => TrackD.labelPt i₀ xy.1 xy.2) ''
            {xy | (xy.2 - xy.1) i₀ ≠ 0} with hChartdef
        set SΓ : Set (Fin d ⊕ Fin d → ℂ) :=
          (fun pq : RPoint d × RPoint d =>
            TrackD.labelPt i₀ (TrackD.toC pq.1) (TrackD.toC pq.2)) ''
            (Γ : Set (RPoint d × RPoint d)) with hSΓdef
        have hRank_eq : commonLabelRank i₀ Γ Lnat = restrictionRank SΓ Lnat := rfl
        have hC_le_chart : ((Lnat + hInit).choose hInit : ℝ) ≤
            (restrictionRank Chart Lnat : ℝ) := by
          -- Remaining indices (all except `inr i₀`), card `= hInit = 2d-1`.
          let σ_rem : Type := {i : Fin d ⊕ Fin d // i ≠ Sum.inr i₀}
          have hcard_sum : Fintype.card (Fin d ⊕ Fin d) = d + d := by
            rw [Fintype.card_sum, Fintype.card_fin]
          have hcard_single : Fintype.card {x : Fin d ⊕ Fin d // x = Sum.inr i₀} = 1 :=
            Fintype.card_eq_one_iff.mpr ⟨⟨_, rfl⟩, fun y => Subtype.ext y.property⟩
          have hcard_rem : Fintype.card σ_rem = hInit := by
            have hcompl := Fintype.card_subtype_compl (fun x : Fin d ⊕ Fin d => x = Sum.inr i₀)
            -- `σ_rem = {x // ¬(x = a)}` definitionally (`≠` is `¬Eq`).
            have heq : Fintype.card σ_rem =
                Fintype.card (Fin d ⊕ Fin d) - Fintype.card {x : Fin d ⊕ Fin d // x = Sum.inr i₀} := hcompl
            rw [hcard_sum, hcard_single] at heq
            omega
          -- `e` embedding remaining → pair.
          let e : σ_rem → (Fin d ⊕ Fin d) := Subtype.val
          have he_inj : Function.Injective e := Subtype.val_injective
          -- `renameSub` lands in pair degree-`≤ Lnat` via `totalDegree_rename_le`.
          have hmem_rename : ∀ F : MvPolynomial.restrictTotalDegree σ_rem ℂ Lnat,
              (MvPolynomial.rename e) F.val ∈
                MvPolynomial.restrictTotalDegree (Fin d ⊕ Fin d) ℂ Lnat := by
            intro F
            have hdeg : F.val.totalDegree ≤ Lnat := by
              have hmem : F.val ∈ MvPolynomial.restrictTotalDegree σ_rem ℂ Lnat := F.property
              rwa [MvPolynomial.mem_restrictTotalDegree] at hmem
            have hle : ((MvPolynomial.rename e) F.val).totalDegree ≤ F.val.totalDegree :=
              MvPolynomial.totalDegree_rename_le _ _
            have hle2 : ((MvPolynomial.rename e) F.val).totalDegree ≤ Lnat :=
              hle.trans hdeg
            exact (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr hle2
          let renameSub : MvPolynomial.restrictTotalDegree σ_rem ℂ Lnat →ₗ[ℂ]
              MvPolynomial.restrictTotalDegree (Fin d ⊕ Fin d) ℂ Lnat :=
            LinearMap.codRestrict _ ((MvPolynomial.rename e).toLinearMap.comp
              (MvPolynomial.restrictTotalDegree σ_rem ℂ Lnat).subtype) hmem_rename
          -- Composition into chart functions.
          let Cmap : MvPolynomial.restrictTotalDegree σ_rem ℂ Lnat →ₗ[ℂ] (Chart → ℂ) :=
            (restrictionMap Chart Lnat).comp renameSub
          -- `Cmap` injective via `funext` + chart covering (`y = x+u`).
          have hC_inj : Function.Injective ⇑Cmap := by
            intro F1 F2 h12
            have hsub : Cmap (F1 - F2) = 0 := by
              rw [map_sub, h12, sub_self]
            have hF0 : F1 - F2 = 0 := by
              apply Subtype.ext
              -- suffices `((F1-F2).val : MvPolynomial ...) = 0` via `funext` on remaining.
              have hvan_all : ∀ v : σ_rem → ℂ, MvPolynomial.eval v (F1 - F2).val = 0 := by
                intro v
                -- Extend `v` to chart point `z` with removed coord `=1`.
                -- Source `x`, full direction `u` with `u i₀ =1`.
                let x : Point d := fun k => v ⟨Sum.inl k, Sum.inl_ne_inr⟩
                let u : Point d := fun j => if h : j = i₀ then 1 else v ⟨Sum.inr j, fun heq => h (Sum.inr.inj heq)⟩
                have hu0 : u i₀ = 1 := by simp [u]
                -- Actually `y = x+u`, `(y-x) = u`, `(y-x)i₀ =1 ≠0`.
                set y : Point d := x + u with hydef
                have hyx : y - x = u := by rw [hydef]; abel
                have hyx0 : (y - x) i₀ ≠ 0 := by rw [hyx, hu0]; exact one_ne_zero
                -- Pair point `z` extending `v` with removed coord `=1`.
                set z : Fin d ⊕ Fin d → ℂ := fun i =>
                  if h : i = Sum.inr i₀ then 1 else v ⟨i, h⟩ with hzdef
                have hz_mem : z ∈ Chart := by
                  rw [hChartdef]
                  refine ⟨(x, y), hyx0, ?_⟩
                  -- `labelPt x y = pairPt x u = z`.
                  have hlabel : TrackD.labelPt i₀ x y = TrackD.pairPt x u := by
                    unfold TrackD.labelPt
                    have heq : ((y - x) i₀)⁻¹ • (y - x) = u := by
                      rw [hyx, hu0, inv_one, one_smul]
                    rw [heq]
                  have hpair_eq : TrackD.pairPt x u = z := by
                    funext i
                    cases i with
                    | inl k =>
                      show (TrackD.pairPt x u) (Sum.inl k) = z (Sum.inl k)
                      simp only [TrackD.pairPt, Sum.elim_inl]
                      show x k = (if h : Sum.inl k = Sum.inr i₀ then 1 else v ⟨Sum.inl k, h⟩)
                      rw [dif_neg (Sum.inl_ne_inr)]
                    | inr j =>
                      show (TrackD.pairPt x u) (Sum.inr j) = z (Sum.inr j)
                      simp only [TrackD.pairPt, Sum.elim_inr]
                      show u j = (if h : Sum.inr j = Sum.inr i₀ then 1 else v ⟨Sum.inr j, h⟩)
                      by_cases hj : j = i₀
                      · have hjeq : (Sum.inr j : Fin d ⊕ Fin d) = Sum.inr i₀ := by rw [hj]
                        rw [dif_pos hjeq, hj]
                        exact hu0
                      · rw [dif_neg (fun heq => hj (Sum.inr.inj heq))]
                        show (if h : j = i₀ then 1 else v ⟨Sum.inr j, _⟩) = v ⟨Sum.inr j, _⟩
                        rw [dif_neg hj]
                  show TrackD.labelPt i₀ x y = z
                  rw [hlabel, hpair_eq]
                -- `Cmap (F1-F2) =0` gives `eval z ... =0`, transfer via `eval_rename` to `eval v ... =0`.
                have hC0 : Cmap (F1 - F2) ⟨z, hz_mem⟩ = 0 := by rw [hsub]; rfl
                -- `Cmap = restrChart ∘ renameSub`, evaluation is `aeval`, convert to `eval` via defeq.
                have htrans : MvPolynomial.eval v (F1 - F2).val = 0 := by
                  have haeval_eq : MvPolynomial.aeval z ((MvPolynomial.rename e) (F1 - F2).val) = 0 := hC0
                  have hrename_eq : MvPolynomial.aeval z ((MvPolynomial.rename e) (F1 - F2).val) =
                      MvPolynomial.aeval (z ∘ e) (F1 - F2).val :=
                    MvPolynomial.aeval_rename _ _ _
                  have hcoe_eq : z ∘ e = v := by
                    funext s
                    show z s.val = v s
                    have hs : s.val ≠ Sum.inr i₀ := s.property
                    simp only [hzdef]
                    rw [dif_neg hs]
                  rw [hrename_eq, hcoe_eq] at haeval_eq
                  simpa using haeval_eq
                exact htrans
              -- `∀ v, eval v (F1-F2).val =0` gives `(F1-F2).val =0` via `funext`, so `F1=F2`.
              have hval_eq : (F1 - F2).val = 0 := by
                have h0 : ∀ v : σ_rem → ℂ, MvPolynomial.eval v (F1 - F2).val =
                    MvPolynomial.eval v 0 := by
                  intro v
                  exact (hvan_all v).trans (map_zero _).symm
                exact MvPolynomial.funext h0
              simpa using hval_eq
            exact sub_eq_zero.mp hF0
          -- `finrank` of remaining domain `= C` via Aux + `hcard_rem`.
          have hfinrank_rem : Module.finrank ℂ
              (MvPolynomial.restrictTotalDegree σ_rem ℂ Lnat) =
              (Lnat + hInit).choose hInit := by
            have h := common_finrank_restrictTotalDegree_eq_choose σ_rem Lnat
            rw [hcard_rem] at h
            exact h
          -- `finrank(range Cmap) = finrank(domain)` via injectivity.
          have hrange_Cmap : Module.finrank ℂ ↥(LinearMap.range Cmap) =
              Module.finrank ℂ (MvPolynomial.restrictTotalDegree σ_rem ℂ Lnat) :=
            LinearMap.finrank_range_of_inj hC_inj
          -- `range Cmap ≤ range restrChart`.
          have hrange_le : LinearMap.range Cmap ≤
              LinearMap.range (restrictionMap Chart Lnat) := by
            intro y hy
            rcases hy with ⟨F, rfl⟩
            exact ⟨renameSub F, rfl⟩
          -- Finite instances for `finrank_mono` (ranges inherit via `Module.Finite.range`).
          haveI hfinite_dom : Module.Finite ℂ
              (MvPolynomial.restrictTotalDegree σ_rem ℂ Lnat) := by
            haveI hfin : Finite ↥{m : σ_rem →₀ ℕ | m.sum (fun _ e => e) ≤ Lnat} := by
              change Finite {m : σ_rem →₀ ℕ // m.sum (fun _ e => e) ≤ Lnat}
              exact finite_exponents_initial_aux σ_rem Lnat
            letI : Fintype ↥{m : σ_rem →₀ ℕ | m.sum (fun _ e => e) ≤ Lnat} :=
              Fintype.ofFinite _
            exact Module.Finite.of_basis
              (MvPolynomial.basisRestrictSupport ℂ
                {m | m.sum (fun _ e => e) ≤ Lnat})
          haveI hfin_pair : Module.Finite ℂ
              (MvPolynomial.restrictTotalDegree (Fin d ⊕ Fin d) ℂ Lnat) := by
            haveI hfin : Finite ↥{m : (Fin d ⊕ Fin d) →₀ ℕ | m.sum (fun _ e => e) ≤ Lnat} := by
              change Finite {m : (Fin d ⊕ Fin d) →₀ ℕ // m.sum (fun _ e => e) ≤ Lnat}
              exact finite_exponents_initial_aux (Fin d ⊕ Fin d) Lnat
            letI : Fintype ↥{m : (Fin d ⊕ Fin d) →₀ ℕ | m.sum (fun _ e => e) ≤ Lnat} :=
              Fintype.ofFinite _
            exact Module.Finite.of_basis
              (MvPolynomial.basisRestrictSupport ℂ
                {m | m.sum (fun _ e => e) ≤ Lnat})
          have hmono : Module.finrank ℂ ↥(LinearMap.range Cmap) ≤
              Module.finrank ℂ ↥(LinearMap.range (restrictionMap Chart Lnat)) :=
            Submodule.finrank_mono hrange_le
          -- Combine: `C = finrank(domain) = finrank(range Cmap) ≤ finrank(range Chart) = rank Chart`.
          have hC_eq : ((Lnat + hInit).choose hInit : ℝ) =
              ((Module.finrank ℂ (MvPolynomial.restrictTotalDegree σ_rem ℂ Lnat) : ℕ) : ℝ) := by
            rw [hfinrank_rem]
          calc ((Lnat + hInit).choose hInit : ℝ)
              = ((Module.finrank ℂ (MvPolynomial.restrictTotalDegree σ_rem ℂ Lnat) : ℕ) : ℝ) := hC_eq
            _ = ((Module.finrank ℂ ↥(LinearMap.range Cmap) : ℕ) : ℝ) := by
              rw [hrange_Cmap]
            _ ≤ ((Module.finrank ℂ ↥(LinearMap.range (restrictionMap Chart Lnat)) : ℕ) : ℝ) :=
              Nat.cast_le.mpr hmono
            _ = (restrictionRank Chart Lnat : ℝ) := by
              unfold restrictionRank
              rfl
        have hchart_le_rank : (restrictionRank Chart Lnat : ℝ) ≤
            (commonLabelRank i₀ Γ Lnat : ℝ) := by
          -- Kernel inclusion `ker SΓ ⊆ ker Chart` via product testing.
          have hker : LinearMap.ker (restrictionMap SΓ Lnat) ≤
              LinearMap.ker (restrictionMap Chart Lnat) := by
            intro F hF
            -- `F.val` has degree `≤ Lnat` and vanishes on `SΓ`, so `F.val ∈ 𝒢`.
            have hFdeg : F.val.totalDegree ≤ Lnat := by
              have hmem : F.val ∈ MvPolynomial.restrictTotalDegree (Fin d ⊕ Fin d) ℂ Lnat :=
                F.property
              rwa [MvPolynomial.mem_restrictTotalDegree] at hmem
            have hFvan : ∀ pq ∈ Γ, MvPolynomial.eval
                (TrackD.labelPt i₀ (TrackD.toC pq.1) (TrackD.toC pq.2)) F.val = 0 := by
              intro pq hpq
              have hmem : TrackD.labelPt i₀ (TrackD.toC pq.1) (TrackD.toC pq.2) ∈ SΓ :=
                Set.mem_image_of_mem _ (Finset.mem_coe.mpr hpq)
              have h0 := LinearMap.mem_ker.mp hF
              have h0z := congrFun h0 ⟨_, hmem⟩
              simpa [restrictionMap] using h0z
            -- Whole-space carriers for `0` cuts.
            obtain ⟨αx, hαx⟩ := common_zero_carrier_assignment (T.sources i)
            obtain ⟨αy, hαy⟩ := common_zero_carrier_assignment (T.targets i)
            -- Kernel set `𝒢` (all degree-`≤ Lnat` equations of `Γ`).
            set 𝒢 : Set (TrackD.PairPoly d) :=
              {G | G.totalDegree ≤ Lnat ∧ ∀ pq ∈ Γ, MvPolynomial.eval
                (TrackD.labelPt i₀ (TrackD.toC pq.1) (TrackD.toC pq.2)) G = 0} with h𝒢def
            have hFmem : F.val ∈ 𝒢 := ⟨hFdeg, hFvan⟩
            -- Degree bound `K = 1` for `𝒢`.
            have hBcfg : TrackD.cfgB (regime.P i) = regime.B i := rfl
            have hLle : ((Lnat : ℕ) : ℝ) ≤ Tdeg := Nat.floor_le hTpos.le
            have hdegree : ∀ G ∈ 𝒢, (G.totalDegree : ℝ) ≤
                1 * TrackD.testDeg (TrackD.cfgB (regime.P i)) (M.s i) τ := by
              intro G hG
              have hGle : G.totalDegree ≤ Lnat := hG.1
              have hcast : ((G.totalDegree : ℕ) : ℝ) ≤ ((Lnat : ℕ) : ℝ) :=
                Nat.cast_le.mpr hGle
              have hTcfg : TrackD.testDeg (TrackD.cfgB (regime.P i)) (M.s i) τ = Tdeg := by
                rw [hBcfg]
              calc ((G.totalDegree : ℕ) : ℝ) ≤ ((Lnat : ℕ) : ℝ) := hcast
                _ ≤ Tdeg := hLle
                _ = 1 * TrackD.testDeg (TrackD.cfgB (regime.P i)) (M.s i) τ := by
                  rw [hTcfg, one_mul]
            -- `Γ` vanishing premise for `𝒢`.
            have hgraph : ∀ pq ∈ Γ, (TrackD.toC pq.2 - TrackD.toC pq.1) i₀ ≠ 0 ∧
                ∀ G ∈ 𝒢, MvPolynomial.eval
                  (TrackD.labelPt i₀ (TrackD.toC pq.1) (TrackD.toC pq.2)) G = 0 := by
              intro pq hpq
              exact ⟨hchart pq hpq, fun G hG => hG.2 pq hpq⟩
            -- Product testing gives a small bad set.
            have hρ0le : ρ0 / 2 ≤ ρ0 := by linarith [hρ0]
            have hTcfg : 1 ≤ TrackD.testDeg (TrackD.cfgB (regime.P i)) (M.s i) τ := by
              have hB : TrackD.cfgB (regime.P i) = regime.B i := rfl
              rw [hB]
              simpa [hTdef] using hTge1
            have hbad_le := hproduct (regime.P i) (T.sources i) (T.targets i) (M.s i)
              (ρ0 / 2) M.b hρ0le hi_PoolGood.1 hi_PoolGood.2 hi_width 0 (by omega) τ
              hOnPlateau hTcfg αx αy hαx hαy i₀ 𝒢 hdegree Γ hΓ hgraph
            -- Good pair exists (`|Γ| ≥ ρ*...`, `|bad| ≤ (ρ/2)*...`, pools `>0`).
            set bad : Finset (RPoint d × RPoint d) := Γ.filter (fun pq =>
              ∃ G ∈ 𝒢, ∃ x ∈ αx pq.1, ∃ y ∈ αy pq.2,
                (y - x) i₀ ≠ 0 ∧ MvPolynomial.eval (TrackD.labelPt i₀ x y) G ≠ 0) with hbaddef
            have hbad_sub : bad ⊆ Γ := Finset.filter_subset _ _
            have hbad_card : ((bad.card : ℕ) : ℝ) ≤
                ρ / 2 * ((TrackD.poolPts (T.sources i)).card : ℝ) *
                ((TrackD.poolPts (T.targets i)).card : ℝ) := hbad_le
            have hprod_pos : (0 : ℝ) < ρ / 2 * ((TrackD.poolPts (T.sources i)).card : ℝ) *
                ((TrackD.poolPts (T.targets i)).card : ℝ) :=
              mul_pos (mul_pos (by positivity) hi_Spool) hi_Tpool
            have hΓpos : (0 : ℝ) < (Γ.card : ℝ) :=
              lt_of_lt_of_le (mul_pos (mul_pos hρ hi_Spool) hi_Tpool) hdense
            have hreal_lt : ((bad.card : ℕ) : ℝ) < ((Γ.card : ℕ) : ℝ) := by
              calc ((bad.card : ℕ) : ℝ)
                  ≤ ρ / 2 * _ * _ := hbad_card
                _ < ρ * _ * _ :=
                  mul_lt_mul_of_pos_right
                    (mul_lt_mul_of_pos_right (half_lt_self hρ) hi_Spool) hi_Tpool
                _ ≤ ((Γ.card : ℕ) : ℝ) := hdense
            have hcard_lt : bad.card < Γ.card := by exact_mod_cast hreal_lt
            have hne : bad ≠ Γ := by
              intro heq
              rw [heq] at hcard_lt
              exact lt_irrefl _ hcard_lt
            have hss : bad ⊂ Γ :=
              Finset.ssubset_iff_subset_ne.mpr ⟨hbad_sub, hne⟩
            obtain ⟨pq0, hpq0Γ, hpq0bad⟩ := Finset.exists_of_ssubset hss
            -- Good `pq0` forces every `G ∈ 𝒢` to vanish on the whole chart.
            have hgood : ∀ G ∈ 𝒢, ∀ x : Point d, ∀ y : Point d, (y - x) i₀ ≠ 0 →
                MvPolynomial.eval (TrackD.labelPt i₀ x y) G = 0 := by
              intro G hG x y hxy
              -- `αx pq0.1`, `αy pq0.2` are whole space (`ideal = ⊥`), so `x`, `y` belong.
              have hmemX : ∃ X ∈ T.sources i, pq0.1 ∈ X.pts := by
                have hmem : pq0.1 ∈ TrackD.poolPts (T.sources i) := by
                  have hsub : pq0 ∈ TrackD.poolPts (T.sources i) ×ˢ TrackD.poolPts (T.targets i) :=
                    hΓ hpq0Γ
                  simpa using (Finset.mem_product.mp hsub).1
                rw [TrackD.poolPts] at hmem
                simpa using Finset.mem_biUnion.mp hmem
              obtain ⟨X0, hX0, hx0⟩ := hmemX
              have hmemY : ∃ Y ∈ T.targets i, pq0.2 ∈ Y.pts := by
                have hmem : pq0.2 ∈ TrackD.poolPts (T.targets i) := by
                  have hsub : pq0 ∈ TrackD.poolPts (T.sources i) ×ˢ TrackD.poolPts (T.targets i) :=
                    hΓ hpq0Γ
                  simpa using (Finset.mem_product.mp hsub).2
                rw [TrackD.poolPts] at hmem
                simpa using Finset.mem_biUnion.mp hmem
              obtain ⟨Y0, hY0, hy0⟩ := hmemY
              have hcarX := hαx X0 hX0 pq0.1 hx0
              have hcarY := hαy Y0 hY0 pq0.2 hy0
              have hidealX : (αx pq0.1).ideal = ⊥ :=
                TrackD.regularity_zero_carrier _ _ hcarX.1
              have hidealY : (αy pq0.2).ideal = ⊥ :=
                TrackD.regularity_zero_carrier _ _ hcarY.1
              have hxmem : x ∈ αx pq0.1 := by
                show x ∈ (αx pq0.1).points
                intro f hf
                rw [hidealX] at hf
                rw [Ideal.mem_bot.mp hf]
                simp
              have hymem : y ∈ αy pq0.2 := by
                show y ∈ (αy pq0.2).points
                intro f hf
                rw [hidealY] at hf
                rw [Ideal.mem_bot.mp hf]
                simp
              have hgood_xy : MvPolynomial.eval (TrackD.labelPt i₀ x y) G = 0 := by
                by_contra hne
                have hex : ∃ G ∈ 𝒢, ∃ x ∈ αx pq0.1, ∃ y ∈ αy pq0.2,
                    (y - x) i₀ ≠ 0 ∧ MvPolynomial.eval (TrackD.labelPt i₀ x y) G ≠ 0 :=
                  ⟨G, hG, x, hxmem, y, hymem, hxy, hne⟩
                have hP : (fun pq =>
                    ∃ G ∈ 𝒢, ∃ x ∈ αx pq.1, ∃ y ∈ αy pq.2,
                      (y - x) i₀ ≠ 0 ∧ MvPolynomial.eval (TrackD.labelPt i₀ x y) G ≠ 0) pq0 :=
                  hex
                have hbad_mem : pq0 ∈ bad := Finset.mem_filter.mpr ⟨hpq0Γ, hP⟩
                exact hpq0bad hbad_mem
              simpa using hgood_xy
            -- Thus `F.val` vanishes on `Chart`, i.e. `F ∈ ker Chart`.
            rw [LinearMap.mem_ker]
            funext z
            rcases z with ⟨zval, hzmem⟩
            show MvPolynomial.aeval zval F.val = 0
            have hzChart : zval ∈ Chart := hzmem
            rw [hChartdef] at hzChart
            obtain ⟨xy, hxyMem, rfl⟩ := hzChart
            have hxyNe : (xy.2 - xy.1) i₀ ≠ 0 := hxyMem
            have hGmem : F.val ∈ 𝒢 := hFmem
            exact hgood F.val hGmem xy.1 xy.2 hxyNe
          -- Finrank comparison via kernels (same domain).
          have hAker := (restrictionMap SΓ Lnat).finrank_range_add_finrank_ker
          have hBker := (restrictionMap Chart Lnat).finrank_range_add_finrank_ker
          have hmono : Module.finrank ℂ ↥(LinearMap.ker (restrictionMap SΓ Lnat)) ≤
              Module.finrank ℂ ↥(LinearMap.ker (restrictionMap Chart Lnat)) :=
            Submodule.finrank_mono hker
          have hle_nat : restrictionRank Chart Lnat ≤ restrictionRank SΓ Lnat := by
            unfold restrictionRank
            omega
          have hle_real : ((restrictionRank Chart Lnat : ℕ) : ℝ) ≤
              ((restrictionRank SΓ Lnat : ℕ) : ℝ) :=
            Nat.cast_le.mpr hle_nat
          have hRankSΓ : commonLabelRank i₀ Γ Lnat = restrictionRank SΓ Lnat := rfl
          calc ((restrictionRank Chart Lnat : ℕ) : ℝ)
              ≤ ((restrictionRank SΓ Lnat : ℕ) : ℝ) := hle_real
            _ = (commonLabelRank i₀ Γ Lnat : ℝ) := by rw [← hRankSΓ]
        calc ((Lnat + hInit).choose hInit : ℝ)
            ≤ ((restrictionRank Chart Lnat : ℕ) : ℝ) := hC_le_chart
          _ ≤ (commonLabelRank i₀ Γ Lnat : ℝ) := hchart_le_rank
      have hCL : cInit * (Lnat : ℝ) ^ hInit ≤ ((Lnat + hInit).choose hInit : ℝ) := by
        have hnat : Lnat ^ hInit ≤ Nat.factorial hInit * (Lnat + hInit).choose hInit :=
          common_pow_le_factorial_mul_choose Lnat hInit
        have hfac_pos_nat : 0 < Nat.factorial hInit := Nat.factorial_pos _
        have hfac_posR : (0 : ℝ) < (Nat.factorial hInit : ℝ) := by
          exact_mod_cast hfac_pos_nat
        have hle : (Lnat : ℝ) ^ hInit ≤ (Nat.factorial hInit : ℝ) *
            (((Lnat + hInit).choose hInit : ℕ) : ℝ) := by
          exact_mod_cast hnat
        have hle' : (Lnat : ℝ) ^ hInit ≤ (((Lnat + hInit).choose hInit : ℕ) : ℝ) *
            (Nat.factorial hInit : ℝ) := by
          rw [mul_comm]
          exact hle
        have hc_eq : cInit = 1 / (Nat.factorial hInit : ℝ) := rfl
        rw [hc_eq]
        rw [div_mul_eq_mul_div, one_mul]
        exact (div_le_iff₀ hfac_posR).mpr hle'
      have hcL_le_rank : cInit * (Lnat : ℝ) ^ hInit ≤
          (commonLabelRank i₀ Γ Lnat : ℝ) :=
        hCL.trans hC_le_rank
      have hE1_le : Real.exp (-(θ / 2) * M.s i) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have hle : -(θ / 2) * M.s i ≤ 0 := by
          have hprod : (0 : ℝ) ≤ (θ / 2) * M.s i :=
            mul_nonneg (div_nonneg hθ.le (by norm_num)) hspos.le
          linarith
        exact hle
      have hLnn : (0 : ℝ) ≤ (Lnat : ℝ) := Nat.cast_nonneg _
      have hcL_nn : (0 : ℝ) ≤ cInit * (Lnat : ℝ) ^ hInit :=
        mul_nonneg hcInit_pos.le (pow_nonneg hLnn _)
      have hrank_nn : (0 : ℝ) ≤ (commonLabelRank i₀ Γ Lnat : ℝ) := Nat.cast_nonneg _
      calc cInit * 1 * Real.exp (-(θ / 2) * M.s i) * (Lnat : ℝ) ^ hInit
          = (cInit * (Lnat : ℝ) ^ hInit) * Real.exp (-(θ / 2) * M.s i) := by ring
        _ ≤ (commonLabelRank i₀ Γ Lnat : ℝ) * 1 :=
          mul_le_mul hcL_le_rank hE1_le (Real.exp_nonneg _) hrank_nn
        _ = (commonLabelRank i₀ Γ Lnat : ℝ) := mul_one _
    have htarg' : commonRankTarget M i τ ≤ 1 * Tdeg ^ hInit := by
      simpa using htarget_upper
    exact common_rank_equal_dim_final 1 Tdeg (Lnat : ℝ) hInit cInit θ (M.s i)
      (commonRankTarget M i τ) (commonLabelRank i₀ Γ Lnat : ℝ)
      one_pos hTpos hLge htarg' hlow hcInit_pos hi_abs

end
end DistinctDistances.SparseCones
