import DistinctDistances.TrackE.CommonRankAlternativeData
import DistinctDistances.TrackE.MERankAux

/-! Scalar propagation of the common label rank across one plateau,
sparse-cones.tex:262–316. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- A borrowing time just before `b_j`, within `κ` and off all cuts. -/
private theorem exists_plateau_borrow_time {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} (M : CommonPoolProfile T)
    (j : ℕ) (hj : j < d) (κ : ℝ) (hκ : 0 < κ) :
    ∃ τ' : ℝ, M.b ⟨j, hj⟩ - κ < τ' ∧ τ' < M.b ⟨j, hj⟩ ∧
      ∀ a : Fin d, M.b a ≠ τ' := by
  classical
  have hdpos_nat : 0 < d := by have := regime.dimension_ge_three; omega
  set bj := M.b ⟨j, hj⟩ with hbjdef
  set δ : ℝ := κ / 2 with hδdef
  have hδpos : 0 < δ := by positivity
  have hδκ : δ ≤ κ := by dsimp [δ]; linarith
  let t : ℕ → ℝ := fun k => bj - δ * (((k : ℝ) + 1) / ((d : ℝ) + 2))
  have hDpos : (0 : ℝ) < (d : ℝ) + 2 := by positivity
  have hDne : ((d : ℝ) + 2) ≠ 0 := ne_of_gt hDpos
  have hmem_of_le : ∀ k : ℕ, k ≤ d → bj - δ < t k ∧ t k < bj := by
    intro k hk
    have hkR : (k : ℝ) ≤ (d : ℝ) := by exact_mod_cast hk
    have h1 : (0 : ℝ) < ((k : ℝ) + 1) / ((d : ℝ) + 2) := by positivity
    have h2 : ((k : ℝ) + 1) / ((d : ℝ) + 2) < 1 := by
      rw [div_lt_one hDpos]
      linarith
    constructor
    · simp only [t]
      have hlt : δ * (((k : ℝ) + 1) / ((d : ℝ) + 2)) < δ := by
        calc δ * (((k : ℝ) + 1) / ((d : ℝ) + 2))
            < δ * 1 := mul_lt_mul_of_pos_left h2 hδpos
          _ = δ := mul_one _
      linarith
    · simp only [t]
      have hgt : 0 < δ * (((k : ℝ) + 1) / ((d : ℝ) + 2)) :=
        mul_pos hδpos h1
      linarith
  have htinj : Function.Injective t := by
    intro k l h
    simp only [t] at h
    have hsub : δ * (((k : ℝ) + 1) / ((d : ℝ) + 2)) =
        δ * (((l : ℝ) + 1) / ((d : ℝ) + 2)) := by
      have h' : bj - δ * (((k : ℝ) + 1) / ((d : ℝ) + 2)) =
          bj - δ * (((l : ℝ) + 1) / ((d : ℝ) + 2)) := h
      exact sub_right_inj.mp h'
    have hδne : δ ≠ 0 := ne_of_gt hδpos
    have hkl : ((k : ℝ) + 1) / ((d : ℝ) + 2) =
        ((l : ℝ) + 1) / ((d : ℝ) + 2) :=
      mul_left_cancel₀ hδne hsub
    have hmul : (((k : ℝ) + 1) / ((d : ℝ) + 2)) * ((d : ℝ) + 2) =
        (((l : ℝ) + 1) / ((d : ℝ) + 2)) * ((d : ℝ) + 2) := by
      rw [hkl]
    rw [div_mul_cancel₀ _ hDne, div_mul_cancel₀ _ hDne] at hmul
    have hkl2 : (k : ℝ) = (l : ℝ) := by linarith
    exact_mod_cast hkl2
  let S : Finset ℝ := (Finset.range (d + 1)).image t
  have hScard : S.card = d + 1 := by
    rw [Finset.card_image_of_injective _ htinj, Finset.card_range]
  let Cc : Finset ℝ := Finset.image M.b Finset.univ
  have hCcard : Cc.card ≤ d := by
    calc Cc.card ≤ Finset.univ.card := Finset.card_image_le
      _ = d := by rw [Finset.card_univ, Fintype.card_fin]
  have hnotsub : ¬ S ⊆ Cc := by
    intro hsub
    have hle := Finset.card_le_card hsub
    omega
  rw [Finset.not_subset] at hnotsub
  obtain ⟨τ', hτ'S, hτ'not⟩ := hnotsub
  rw [Finset.mem_image] at hτ'S
  obtain ⟨k, hkrange, rfl⟩ := hτ'S
  have hk_le : k ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hkrange)
  have hIoo := hmem_of_le k hk_le
  refine ⟨t k, by linarith [hIoo.1, hδκ], hIoo.2, ?_⟩
  intro a ha
  apply hτ'not
  show t k ∈ Cc
  unfold Cc
  rw [Finset.mem_image]
  exact ⟨a, Finset.mem_univ a, ha⟩

/-- Plateau upper bound for the rank target: `target ≤ e_{j+1}²·T^{2k}`. -/
private theorem common_target_plateau_upper {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} (M : CommonPoolProfile T)
    (j : ℕ) (hj : j + 1 < d) (τ : ℝ)
    (hτ : M.b ⟨j, Nat.lt_trans (Nat.lt_succ_self j) hj⟩ < τ ∧ τ < M.b ⟨j + 1, hj⟩) (i : ℕ) :
    commonRankTarget M i τ ≤
      (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2 *
        (TrackD.testDeg (regime.B i) (M.s i) τ) ^ (2 * (d - (j + 1))) := by
  have hsig := common_sigma_plateau_eq M j hj τ hτ i
  unfold commonRankTarget
  rw [hsig]
  have hmin : min 1 (TrackD.testDeg (regime.B i) (M.s i) τ /
      (TrackD.cutScale (regime.B i) (M.s i) M.b
        ⟨0, by have := regime.dimension_ge_three; omega⟩ *
       TrackD.cutScale (regime.B i) (M.s i) M.b
        ⟨1, by have := regime.dimension_ge_three; omega⟩)) ≤ 1 :=
    min_le_left _ _
  have hsq : (0 : ℝ) ≤ (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1) *
      TrackD.testDeg (regime.B i) (M.s i) τ ^ (d - (j + 1))) ^ 2 :=
    sq_nonneg _
  calc (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1) *
        TrackD.testDeg (regime.B i) (M.s i) τ ^ (d - (j + 1))) ^ 2 *
        min 1 _ ≤ (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1) *
        TrackD.testDeg (regime.B i) (M.s i) τ ^ (d - (j + 1))) ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left hmin hsq
    _ = _ := by
      rw [mul_one, mul_pow]
      congr 1
      rw [← pow_mul]
      congr 1
      omega

/-- First-plateau refinement: `target ≤ D₀·T^{2d-2}` using `T ≤ D₁`. -/
private theorem common_target_first_plateau_upper {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} (M : CommonPoolProfile T)
    (hj : 0 + 1 < d) (τ : ℝ)
    (hτ : M.b ⟨0, by omega⟩ < τ ∧ τ < M.b ⟨0 + 1, hj⟩) (i : ℕ) :
    commonRankTarget M i τ ≤
      TrackD.cutScale (regime.B i) (M.s i) M.b ⟨0, by have := regime.dimension_ge_three; omega⟩ *
        (TrackD.testDeg (regime.B i) (M.s i) τ) ^ (2 * d - 2) := by
  classical
  have hd3 := regime.dimension_ge_three
  have hspos := M.width_pos i
  have hBnn := (regime.B_pos i).le
  set Tdeg := TrackD.testDeg (regime.B i) (M.s i) τ with hTdef
  set D0 := TrackD.cutScale (regime.B i) (M.s i) M.b
    ⟨0, by have := regime.dimension_ge_three; omega⟩ with hD0def
  set D1 := TrackD.cutScale (regime.B i) (M.s i) M.b
    ⟨1, by have := regime.dimension_ge_three; omega⟩ with hD1def
  have hTpos : 0 < Tdeg := TrackD.RankCore.testDeg_pos (regime.B_pos i) _ _
  have hD0pos : 0 < D0 := TrackD.RankCore.testDeg_pos (regime.B_pos i) _ _
  have hD1pos : 0 < D1 := TrackD.RankCore.testDeg_pos (regime.B_pos i) _ _
  have hTD1 : Tdeg ≤ D1 := by
    have hle : τ ≤ M.b ⟨1, by omega⟩ := by
      have h1 : (⟨0 + 1, hj⟩ : Fin d) = (⟨1, by omega⟩ : Fin d) := by
        apply Fin.ext
        simp
      rw [h1] at hτ
      exact hτ.2.le
    unfold Tdeg D1 TrackD.cutScale
    exact TrackD.RankCore.testDeg_mono hBnn hspos.le hle
  have hsig := common_sigma_plateau_eq M 0 hj τ
    (by simpa using hτ) i
  have hk : d - (0 + 1) = d - 1 := by omega
  have he : TrackD.eScale (regime.B i) (M.s i) M.b (0 + 1) = D0 := by
    unfold TrackD.eScale
    have hfilt : (Finset.univ.filter (fun a : Fin d => a.val < 0 + 1)) =
        {(⟨0, by have := regime.dimension_ge_three; omega⟩ : Fin d)} := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro ha
        have ha1 : a.val < 1 := by omega
        exact Fin.ext (Nat.lt_one_iff.mp ha1)
      · intro ha
        rw [ha]
        simp
    rw [hfilt, Finset.prod_singleton]
  have hexp : 2 * d - 2 = 2 * (d - 1) := by omega
  rw [hexp]
  unfold commonRankTarget
  rw [hsig, hk, he]
  -- `min ≤ T/(D0*D1)`.
  have hmin : min 1 (Tdeg / (D0 * D1)) ≤ Tdeg / (D0 * D1) := min_le_right _ _
  have hsqnn : (0 : ℝ) ≤ (D0 * Tdeg ^ (d - 1)) ^ 2 := sq_nonneg _
  calc (D0 * Tdeg ^ (d - 1)) ^ 2 * min 1 (Tdeg / (D0 * D1))
      ≤ (D0 * Tdeg ^ (d - 1)) ^ 2 * (Tdeg / (D0 * D1)) :=
        mul_le_mul_of_nonneg_left hmin hsqnn
    _ = D0 * Tdeg ^ (2 * (d - 1)) * (Tdeg / D1 / D0 * D0) := by
        field_simp
        ring
    _ ≤ D0 * Tdeg ^ (2 * (d - 1)) := by
        have hTD : Tdeg / D1 ≤ 1 := (div_le_one₀ hD1pos).mpr hTD1
        have hnn : (0 : ℝ) ≤ D0 * Tdeg ^ (2 * (d - 1)) := by positivity
        calc D0 * Tdeg ^ (2 * (d - 1)) * (Tdeg / D1 / D0 * D0)
            = D0 * Tdeg ^ (2 * (d - 1)) * (Tdeg / D1) := by
              field_simp
          _ ≤ D0 * Tdeg ^ (2 * (d - 1)) * 1 :=
              mul_le_mul_of_nonneg_left hTD hnn
          _ = _ := mul_one _

/-- Target growth from `τ'` to `τ` across the `j`-th cut cluster of width `κ`:
`target(τ) ≤ target(τ')·(T/T')^{2k+1}·e^{2dκs}` with `k = d-(j+1)`. -/
private theorem common_target_growth {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} (M : CommonPoolProfile T)
    (j : ℕ) (hj : j + 1 < d) (τ' τ : ℝ) (κ : ℝ)
    (hτ' : τ' < M.b ⟨j, Nat.lt_trans (Nat.lt_succ_self j) hj⟩)
    (hτ : M.b ⟨j, Nat.lt_trans (Nat.lt_succ_self j) hj⟩ < τ ∧ τ < M.b ⟨j + 1, hj⟩)
    (hκ : M.b ⟨j, Nat.lt_trans (Nat.lt_succ_self j) hj⟩ - τ' ≤ κ) (i : ℕ) :
    commonRankTarget M i τ ≤
      commonRankTarget M i τ' *
        (TrackD.testDeg (regime.B i) (M.s i) τ / TrackD.testDeg (regime.B i) (M.s i) τ') ^
          (2 * (d - (j + 1)) + 1) *
        Real.exp (2 * (d : ℝ) * κ * M.s i) := by
  classical
  have hspos := M.width_pos i
  have hsnn := hspos.le
  have hBpos := regime.B_pos i
  have hBnn := hBpos.le
  have hBne : regime.B i ≠ 0 := ne_of_gt hBpos
  set B := regime.B i with hBdef
  set s := M.s i with hsdef
  set Tdeg := TrackD.testDeg B s τ with hTdef
  set Tdeg' := TrackD.testDeg B s τ' with hTdef'
  set D0 := TrackD.cutScale B s M.b ⟨0, by have := regime.dimension_ge_three; omega⟩ with hD0def
  set D1 := TrackD.cutScale B s M.b ⟨1, by have := regime.dimension_ge_three; omega⟩ with hD1def
  set D := D0 * D1 with hDdef
  have hTpos : 0 < Tdeg := TrackD.RankCore.testDeg_pos hBpos _ _
  have hT'pos : 0 < Tdeg' := TrackD.RankCore.testDeg_pos hBpos _ _
  have hTne : Tdeg ≠ 0 := ne_of_gt hTpos
  have hT'ne : Tdeg' ≠ 0 := ne_of_gt hT'pos
  have hD0pos : 0 < D0 := TrackD.RankCore.testDeg_pos hBpos _ _
  have hD1pos : 0 < D1 := TrackD.RankCore.testDeg_pos hBpos _ _
  have hDpos : 0 < D := mul_pos hD0pos hD1pos
  have hDne : D ≠ 0 := ne_of_gt hDpos
  have hDnn : (0 : ℝ) ≤ D := hDpos.le
  -- `σ` growth via `RankCore.sigma_cluster_growth` with `a = τ'`, `c = b_j`, `b = τ`.
  have hbj : M.b ⟨j, by omega⟩ ≤ M.b ⟨j, by omega⟩ := le_rfl
  have hac : τ' ≤ M.b ⟨j, by omega⟩ := le_of_lt hτ'
  have hcb : M.b ⟨j, by omega⟩ ≤ τ := le_of_lt hτ.1
  have hgap : M.b ⟨j, by omega⟩ - τ' ≤ κ := hκ
  have hc_plat : TrackD.OnPlateau M.b (j + 1) 0 (M.b ⟨j, by omega⟩) := by
    intro a
    constructor
    · intro ha
      have hval : a.val ≤ j := by omega
      have hle : M.b a ≤ M.b ⟨j, by omega⟩ :=
        M.sorted (Fin.le_def.mpr hval)
      simpa using hle
    · intro ha
      have hval : j ≤ a.val := by omega
      have hle : M.b ⟨j, by omega⟩ ≤ M.b a :=
        M.sorted (Fin.le_def.mpr hval)
      simpa using hle
  have hb_plat : TrackD.OnPlateau M.b (j + 1) 0 τ := by
    intro a
    constructor
    · intro ha
      have hval : a.val ≤ j := by omega
      have hle : M.b a ≤ M.b ⟨j, by omega⟩ :=
        M.sorted (Fin.le_def.mpr hval)
      have hlt : M.b ⟨j, by omega⟩ < τ := hτ.1
      have hle' : M.b a ≤ τ := le_trans hle hlt.le
      simpa using hle'
    · intro ha
      have hle : M.b ⟨j + 1, hj⟩ ≤ M.b a :=
        M.sorted (Fin.le_def.mpr ha)
      have hlt : τ < M.b ⟨j + 1, hj⟩ := hτ.2
      have hle' : τ ≤ M.b a := le_trans hlt.le hle
      simpa using hle'
  -- `σ` growth.
  have hsigma := TrackD.RankCore.sigma_cluster_growth hBnn hsnn
    hac hcb hgap M.b (j + 1) (by omega) hc_plat hb_plat
  -- `T/T' = e^{(τ-τ')s}`.
  have hTTeq : Tdeg / Tdeg' = Real.exp ((τ - τ') * s) := by
    unfold Tdeg Tdeg' TrackD.testDeg
    rw [mul_div_mul_left _ _ hBne, ← Real.exp_sub]
    congr 1
    ring
  set k := d - (j + 1) with hkdef
  have hTle : Tdeg' ≤ Tdeg :=
    TrackD.RankCore.testDeg_mono hBnn hsnn (le_of_lt (lt_trans hτ' hτ.1))
  have hTTpos : 0 < Tdeg / Tdeg' := div_pos hTpos hT'pos
  have hTTnn : 0 ≤ Tdeg / Tdeg' := hTTpos.le
  have hTTge1 : (1 : ℝ) ≤ Tdeg / Tdeg' := (le_div_iff₀ hT'pos).mpr (by simpa using hTle)
  have hTTpow : (Tdeg / Tdeg') ^ (2 * k) = Real.exp (((2 * k : ℕ) : ℝ) * ((τ - τ') * s)) := by
    rw [hTTeq, ← Real.exp_nat_mul]
  have hE2 : (Real.exp ((((k : ℝ)) * (τ - τ') + (d : ℝ) * κ) * s)) ^ 2
      = (Tdeg / Tdeg') ^ (2 * k) * Real.exp (2 * (d : ℝ) * κ * s) := by
    rw [hTTpow, pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    push_cast
    ring
  have hsig2 : (TrackD.sigma B s M.b τ) ^ 2 ≤ (TrackD.sigma B s M.b τ') ^ 2 *
      ((Tdeg / Tdeg') ^ (2 * k) * Real.exp (2 * (d : ℝ) * κ * s)) := by
    have h := pow_le_pow_left₀ (TrackD.RankCore.sigma_nonneg hBnn _ _ _) hsigma 2
    rw [mul_pow, hE2] at h
    exact h
  have hTD : (Tdeg / Tdeg') * (Tdeg' / D) = Tdeg / D := by
    field_simp
  have hmin : min 1 (Tdeg / D) ≤ (Tdeg / Tdeg') * min 1 (Tdeg' / D) := by
    have hmul : (Tdeg / Tdeg') * min 1 (Tdeg' / D) =
        min ((Tdeg / Tdeg') * 1) ((Tdeg / Tdeg') * (Tdeg' / D)) :=
      mul_min_of_nonneg _ _ hTTnn
    rw [hmul, mul_one, hTD]
    exact min_le_min hTTge1 le_rfl
  have htarg_eq : commonRankTarget M i τ =
      (TrackD.sigma B s M.b τ) ^ 2 * min 1 (Tdeg / D) := rfl
  have htarg'_eq : commonRankTarget M i τ' =
      (TrackD.sigma B s M.b τ') ^ 2 * min 1 (Tdeg' / D) := rfl
  have hpow : (Tdeg / Tdeg') ^ (2 * k + 1)
      = (Tdeg / Tdeg') ^ (2 * k) * (Tdeg / Tdeg') :=
    pow_succ _ _
  calc commonRankTarget M i τ
      = (TrackD.sigma B s M.b τ) ^ 2 * min 1 (Tdeg / D) := htarg_eq
    _ ≤ ((TrackD.sigma B s M.b τ') ^ 2 * ((Tdeg / Tdeg') ^ (2 * k) * Real.exp (2 * (d : ℝ) * κ * s))) *
        ((Tdeg / Tdeg') * min 1 (Tdeg' / D)) :=
        mul_le_mul hsig2 hmin (by positivity) (by positivity)
    _ = commonRankTarget M i τ' * (Tdeg / Tdeg') ^ (2 * k + 1) * Real.exp (2 * (d : ℝ) * κ * s) := by
        rw [htarg'_eq, hpow]
        ring

/-- sc:common-rank.propagate: the plateau alternative and the rank at all
earlier times off the cuts give the rank on the plateau after the zero-based
cut `j`, with every positive logarithmic tolerance. -/
theorem common_rank_step_of_alternative {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (M : CommonPoolProfile T)
    (j : ℕ) (hj : j + 1 < d)
    (hprev : ∀ τ' : ℝ, τ' < M.b ⟨j, by omega⟩ → (∀ a : Fin d, M.b a ≠ τ') →
      ∀ θ : ℝ, 0 < θ → CommonRankAt M τ' θ)
    (τ : ℝ) (hτ : M.b ⟨j, by omega⟩ < τ ∧ τ < M.b ⟨j + 1, hj⟩)
    (halt : CommonRankAlternative M j τ) :
    ∀ θ : ℝ, 0 < θ → CommonRankAt M τ θ := by
  classical
  have hd3 := regime.dimension_ge_three
  have hdpos : 0 < d := by omega
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
  intro θ hθ ρ hρ
  obtain ⟨c, hc, halt'⟩ := halt
  have hcpos : 0 < c := hc
  -- Dimensions.
  set k := d - (j + 1) with hkdef
  have hkj : j + 1 + k = d := by omega
  have hk_le : k ≤ d := Nat.sub_le _ _
  have hk_pos : 1 ≤ k := by omega
  -- Borrowing parameters.
  set κ : ℝ := θ / (8 * (d : ℝ) + 8) with hκdef
  have hdenom : (0 : ℝ) < 8 * (d : ℝ) + 8 := by positivity
  have hκpos : 0 < κ := by dsimp [κ]; positivity
  have hρdenom : (0 : ℝ) < 2 * (2 * (d : ℝ) + 1) := by positivity
  have hρ'pos : 0 < ρ / (2 * (2 * (d : ℝ) + 1)) := by positivity
  have hθ2 : (0 : ℝ) < θ / 2 := by positivity
  have hθ4 : (0 : ℝ) < θ / 4 := by positivity
  -- Borrowing time.
  obtain ⟨τ', hτ'mem, hτ'lt, hτ'off⟩ :=
    exists_plateau_borrow_time M j (by omega) κ hκpos
  have hprev_at := hprev τ' hτ'lt hτ'off (θ / 4) hθ4
  have halt_ev := halt' (θ / 2) hθ2 ρ hρ
  have prev_ev := hprev_at (ρ / (2 * (2 * (d : ℝ) + 1))) hρ'pos
  -- Absorption of fixed constants (use `4^(2d)/c` uniformly, since `h ≤ 2d`).
  have h4dd : (0 : ℝ) < 4 ^ (2 * d) / c := by positivity
  have habs_eq := common_absorb_eventually M (4 ^ (2 * d) / c) (θ / 2) h4dd hθ2
  have hexp_pos : (0 : ℝ) < 3 * θ / 4 - 2 * (d : ℝ) * κ := by
    dsimp [κ]
    have hne : (8 * (d : ℝ) + 8) ≠ 0 := ne_of_gt hdenom
    field_simp
    nlinarith [hdR, hθ]
  have habs_borrow := common_absorb_eventually M (4 ^ (2 * d) / c)
    (3 * θ / 4 - 2 * (d : ℝ) * κ) h4dd hexp_pos
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
  -- Combine.
  filter_upwards [halt_ev, prev_ev, habs_eq, habs_borrow, hSpos_ev, hTpool_ev] with i hi_halt hi_prev hi_abs1 hi_abs2 hi_Spool hi_Tpool
  intro i₀ Γ hΓ hchart hdense
  obtain ⟨h, hh1, hh2, Γ', hΓ', hdense', hor⟩ := hi_halt i₀ Γ hΓ hchart hdense
  have hk_eq : 2 * (d - (j + 1)) = 2 * k := by rw [hkdef]
  rw [hk_eq] at hh1 hor
  set Tdeg := TrackD.testDeg (regime.B i) (M.s i) τ with hTdef
  set Lnat : ℕ := ⌊Tdeg⌋₊ with hLdef
  have hTpos : 0 < Tdeg := TrackD.RankCore.testDeg_pos (regime.B_pos i) _ _
  have hTge1 : 1 ≤ Tdeg := common_plateau_test_degree_ge_one M ⟨j, by omega⟩ τ hτ.1 i
  have hLle : (Lnat : ℝ) ≤ Tdeg := Nat.floor_le hTpos.le
  have hLge : Tdeg / 2 ≤ (Lnat : ℝ) := common_floor_ge_half hTge1
  have hΓ'sub : Γ' ⊆ TrackD.poolPts (T.sources i) ×ˢ TrackD.poolPts (T.targets i) :=
    hΓ'.trans hΓ
  have hchart' : ∀ pq ∈ Γ', (TrackD.toC pq.2 - TrackD.toC pq.1) i₀ ≠ 0 := by
    intro pq hpq
    exact hchart pq (hΓ' hpq)
  rcases hor with ⟨heq, hlow_eq⟩ | ⟨hlt, hborrow⟩
  · -- Equal-dimension case `h = 2k`.
    have hk2 : h = 2 * k := heq
    have h2d : h ≤ 2 * d := hh2
    have h4h : (4 : ℝ) ^ h ≤ 4 ^ (2 * d) :=
      pow_le_pow_right₀ (by norm_num) h2d
    have habs : (4 : ℝ) ^ h / c ≤ Real.exp ((θ / 2) * M.s i) := by
      calc (4 : ℝ) ^ h / c ≤ 4 ^ (2 * d) / c :=
            div_le_div_of_nonneg_right h4h hcpos.le
        _ ≤ _ := hi_abs1
    by_cases hj0 : j = 0
    · subst hj0
      have hk1 : k = d - 1 := by omega
      have hexp : h = 2 * d - 2 := by omega
      have htarg0 := common_target_first_plateau_upper M hj τ hτ i
      have htarg0' : commonRankTarget M i τ ≤
          TrackD.cutScale (regime.B i) (M.s i) M.b
            ⟨0, by have := regime.dimension_ge_three; omega⟩ * Tdeg ^ h := by
        have h1 : (2 * d - 2 : ℕ) = h := hexp.symm
        rw [h1] at htarg0
        simpa [hTdef] using htarg0
      have hD0pos : 0 < TrackD.cutScale (regime.B i) (M.s i) M.b
          ⟨0, by have := regime.dimension_ge_three; omega⟩ :=
        TrackD.RankCore.testDeg_pos (regime.B_pos i) _ _
      have hlow0 : c * TrackD.cutScale (regime.B i) (M.s i) M.b
          ⟨0, by have := regime.dimension_ge_three; omega⟩ *
          Real.exp (-(θ / 2) * M.s i) * (Lnat : ℝ) ^ h ≤
          (commonLabelRank i₀ Γ Lnat : ℝ) := by
        have hlow_def : commonEqualDimLower M i 0 =
            TrackD.cutScale (regime.B i) (M.s i) M.b
              ⟨0, by have := regime.dimension_ge_three; omega⟩ := by
          simp [commonEqualDimLower]
        have h := hlow_eq
        rw [hlow_def] at h
        have hLrw : (⌊Tdeg⌋₊ : ℝ) = (Lnat : ℝ) := rfl
        rw [hLrw] at h
        exact_mod_cast h
      exact common_rank_equal_dim_final
        (TrackD.cutScale (regime.B i) (M.s i) M.b
          ⟨0, by have := regime.dimension_ge_three; omega⟩)
        Tdeg (Lnat : ℝ) h c θ (M.s i)
        (commonRankTarget M i τ) (commonLabelRank i₀ Γ Lnat : ℝ)
        hD0pos hTpos hLge htarg0' hlow0 hcpos habs
    · have hj1 : 1 ≤ j := by omega
      have hlower_eq : commonEqualDimLower M i j =
          (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2 := by
        unfold commonEqualDimLower
        rw [if_neg (by omega)]
      have hepos : 0 < TrackD.eScale (regime.B i) (M.s i) M.b (j + 1) := by
        unfold TrackD.eScale
        apply Finset.prod_pos
        intro a _
        exact TrackD.RankCore.testDeg_pos (regime.B_pos i) _ _
      have hlower_pos : 0 < (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2 :=
        sq_pos_of_pos hepos
      have htarg1 := common_target_plateau_upper M j hj τ hτ i
      have htarg1' : commonRankTarget M i τ ≤
          (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2 * Tdeg ^ h := by
        have h2k : (2 : ℕ) * (d - (j + 1)) = h := hk2.symm
        have hk' : d - (j + 1) = k := by omega
        rw [hk'] at htarg1
        have h2k' : 2 * (d - (j + 1)) = 2 * k := by omega
        rw [h2k'] at htarg1
        rw [← hk2] at htarg1
        simpa [hTdef] using htarg1
      have hlow1 : c * (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2 *
          Real.exp (-(θ / 2) * M.s i) * (Lnat : ℝ) ^ h ≤
          (commonLabelRank i₀ Γ Lnat : ℝ) := by
        have h := hlow_eq
        rw [hlower_eq] at h
        have hLrw : (⌊Tdeg⌋₊ : ℝ) = (Lnat : ℝ) := rfl
        rw [hLrw] at h
        exact_mod_cast h
      exact common_rank_equal_dim_final
        ((TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2)
        Tdeg (Lnat : ℝ) h c θ (M.s i)
        (commonRankTarget M i τ) (commonLabelRank i₀ Γ Lnat : ℝ)
        hlower_pos hTpos hLge htarg1' hlow1 hcpos habs
  · -- Borrowing case `h > 2k`.
    have hkh : 2 * k + 1 ≤ h := by omega
    set T'deg := TrackD.testDeg (regime.B i) (M.s i) τ' with hT'def
    set Enat : ℕ := ⌊T'deg⌋₊ with hEdef
    have hT'pos : 0 < T'deg := TrackD.RankCore.testDeg_pos (regime.B_pos i) _ _
    have hspos := M.width_pos i
    have hsnn := hspos.le
    have hBpos := regime.B_pos i
    have hBnn := hBpos.le
    have hT'Tle : T'deg ≤ Tdeg :=
      TrackD.RankCore.testDeg_mono hBnn hsnn (le_of_lt (lt_trans hτ'lt hτ.1))
    have hκle : M.b ⟨j, by omega⟩ - τ' ≤ κ := by linarith [hτ'mem]
    have hgrowth0 := common_target_growth M j hj τ' τ κ hτ'lt hτ hκle i
    have hk' : d - (j + 1) = k := hkdef.symm
    have hgrowth : commonRankTarget M i τ ≤
        commonRankTarget M i τ' * (Tdeg / T'deg) ^ (2 * k + 1) *
        Real.exp (2 * (d : ℝ) * κ * M.s i) := by
      have h1 : 2 * (d - (j + 1)) + 1 = 2 * k + 1 := by rw [hk']
      simpa [hTdef, hT'def, h1] using hgrowth0
    have hprev_le := hi_prev i₀ Γ' hΓ'sub hchart' hdense'
    have hborrow_E := hborrow Enat
    have hchoose := common_choose_le_pow Enat h
    have h4h : (4 : ℝ) ^ h ≤ 4 ^ (2 * d) := pow_le_pow_right₀ (by norm_num) hh2
    have habs : (4 : ℝ) ^ h / c ≤ Real.exp ((3 * θ / 4 - 2 * (d : ℝ) * κ) * M.s i) := by
      calc (4 : ℝ) ^ h / c ≤ 4 ^ (2 * d) / c :=
            div_le_div_of_nonneg_right h4h hcpos.le
        _ ≤ _ := hi_abs2
    have hD0pos : 0 < TrackD.cutScale (regime.B i) (M.s i) M.b
        ⟨0, by have := regime.dimension_ge_three; omega⟩ :=
      TrackD.RankCore.testDeg_pos (regime.B_pos i) _ _
    have hD1pos : 0 < TrackD.cutScale (regime.B i) (M.s i) M.b
        ⟨1, by have := regime.dimension_ge_three; omega⟩ :=
      TrackD.RankCore.testDeg_pos (regime.B_pos i) _ _
    have htarget_nn : 0 ≤ commonRankTarget M i τ' := by
      unfold commonRankTarget
      apply mul_nonneg (sq_nonneg _)
      apply le_min zero_le_one
      exact le_of_lt (div_pos hT'pos (mul_pos hD0pos hD1pos))
    have htarget_nn_tau : 0 ≤ commonRankTarget M i τ := by
      unfold commonRankTarget
      apply mul_nonneg (sq_nonneg _)
      apply le_min zero_le_one
      exact le_of_lt (div_pos hTpos (mul_pos hD0pos hD1pos))
    have hrank_nn : (0 : ℝ) ≤ (commonLabelRank i₀ Γ' Enat : ℝ) := Nat.cast_nonneg _
    by_cases hT'ge1 : 1 ≤ T'deg
    · have hE_le : (Enat : ℝ) ≤ T'deg := Nat.floor_le hT'pos.le
      have hE1_eq : ((Enat + 1 : ℕ) : ℝ) = (Enat : ℝ) + 1 := by push_cast; ring
      have hE1le : ((Enat + 1 : ℕ) : ℝ) ≤ 2 * T'deg := by
        rw [hE1_eq]
        linarith
      have hLrw : (⌊Tdeg⌋₊ : ℝ) = (Lnat : ℝ) := rfl
      have hErw : (⌊T'deg⌋₊ : ℝ) = (Enat : ℝ) := rfl
      -- Convert `hborrow_E`, `hprev_le`, `hgrowth` to the `Tdeg`/`Lnat`/`Enat` form
      -- (they are defeq via `set`, so `simpa` suffices for the casts).
      have hborrow_E' : c * (commonLabelRank i₀ Γ' Enat : ℝ) * (Lnat : ℝ) ^ h ≤
          (commonLabelRank i₀ Γ Lnat : ℝ) * ((Enat + h).choose h : ℝ) := by
        have h := hborrow_E
        simpa [hTdef, hLdef, hT'def, hEdef] using h
      have hprev_le' : commonRankTarget M i τ' * Real.exp (-(θ / 4) * M.s i) ≤
          (commonLabelRank i₀ Γ' Enat : ℝ) := by
        simpa [hT'def, hEdef] using hprev_le
      have hgrowth' : commonRankTarget M i τ ≤
          commonRankTarget M i τ' * (Tdeg / T'deg) ^ (2 * k + 1) *
          Real.exp (2 * (d : ℝ) * κ * M.s i) := hgrowth
      exact common_rank_borrow_ge_one Tdeg T'deg (Lnat : ℝ) Enat h k d c θ (M.s i) κ
        (commonRankTarget M i τ) (commonRankTarget M i τ')
        (commonLabelRank i₀ Γ Lnat : ℝ) (commonLabelRank i₀ Γ' Enat : ℝ)
        hTpos hT'pos hTge1 hT'ge1 hLge hE1le hT'Tle hkh hh2 hchoose hborrow_E'
        hprev_le' hgrowth' hcpos habs htarget_nn hrank_nn htarget_nn_tau
    · have hT'lt : T'deg < 1 := lt_of_not_ge hT'ge1
      have hEeq0 : Enat = 0 := by
        rw [hEdef]
        exact Nat.floor_eq_zero.mpr hT'lt
      have hCeq1 : ((Enat + h).choose h : ℝ) = 1 := by
        rw [hEeq0, Nat.zero_add, Nat.choose_self, Nat.cast_one]
      have hΓ'posR : (0 : ℝ) < (Γ'.card : ℝ) := by
        have hprod_pos : (0 : ℝ) <
            ρ / (2 * (2 * (d : ℝ) + 1)) * ((TrackD.poolPts (T.sources i)).card : ℝ) *
            ((TrackD.poolPts (T.targets i)).card : ℝ) :=
          mul_pos (mul_pos hρ'pos hi_Spool) hi_Tpool
        exact lt_of_lt_of_le hprod_pos hdense'
      have hΓ'card_pos : 0 < Γ'.card := Nat.cast_pos.mp hΓ'posR
      have hΓ'ne : Γ'.Nonempty := Finset.card_pos.mp hΓ'card_pos
      have hrank'_ge1 : (1 : ℝ) ≤ (commonLabelRank i₀ Γ' Enat : ℝ) := by
        rw [hEeq0]
        have h1 : 1 ≤ commonLabelRank i₀ Γ' 0 :=
          commonLabelRank_zero_ge_one d i₀ Γ' hΓ'ne
        exact_mod_cast h1
      have hborrow_E1 : c * (commonLabelRank i₀ Γ' Enat : ℝ) * (Lnat : ℝ) ^ h ≤
          (commonLabelRank i₀ Γ Lnat : ℝ) * 1 := by
        have h2 := hborrow_E
        rw [hCeq1] at h2
        simpa [hTdef, hLdef, hT'def, hEdef] using h2
      have hLnn : (0 : ℝ) ≤ (Lnat : ℝ) := Nat.cast_nonneg _
      have hcL_nn : (0 : ℝ) ≤ c * (Lnat : ℝ) ^ h :=
        mul_nonneg hcpos.le (pow_nonneg hLnn _)
      have hborrow0 : c * 1 * (Lnat : ℝ) ^ h ≤
          (commonLabelRank i₀ Γ Lnat : ℝ) * 1 := by
        have hle : c * 1 * (Lnat : ℝ) ^ h ≤
            c * (commonLabelRank i₀ Γ' Enat : ℝ) * (Lnat : ℝ) ^ h := by
          calc c * 1 * (Lnat : ℝ) ^ h = (c * (Lnat : ℝ) ^ h) * 1 := by ring
            _ ≤ (c * (Lnat : ℝ) ^ h) * (commonLabelRank i₀ Γ' Enat : ℝ) :=
              mul_le_mul_of_nonneg_left hrank'_ge1 hcL_nn
            _ = c * (commonLabelRank i₀ Γ' Enat : ℝ) * (Lnat : ℝ) ^ h := by ring
        exact hle.trans hborrow_E1
      have hDge1 : ∀ a : Fin d, 1 ≤ TrackD.cutScale (regime.B i) (M.s i) M.b a :=
        fun a => common_cutScale_ge_one M i a
      have hmin_eq : ∀ a : Fin d,
          min T'deg (TrackD.cutScale (regime.B i) (M.s i) M.b a) = T'deg := by
        intro a
        exact min_eq_left (le_trans (le_of_lt hT'lt) (hDge1 a))
      have hsigma_eq : TrackD.sigma (regime.B i) (M.s i) M.b τ' = T'deg ^ d := by
        unfold TrackD.sigma
        have h : ∀ a : Fin d,
            min (TrackD.testDeg (regime.B i) (M.s i) τ')
              (TrackD.cutScale (regime.B i) (M.s i) M.b a) = T'deg := by
          intro a
          have hT'eq : TrackD.testDeg (regime.B i) (M.s i) τ' = T'deg := rfl
          rw [hT'eq]
          exact hmin_eq a
        simp_rw [h]
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      have htarget'_le : commonRankTarget M i τ' ≤ T'deg ^ (2 * d) := by
        have hmin_le : min 1 (T'deg /
            (TrackD.cutScale (regime.B i) (M.s i) M.b
              ⟨0, by have := regime.dimension_ge_three; omega⟩ *
            TrackD.cutScale (regime.B i) (M.s i) M.b
              ⟨1, by have := regime.dimension_ge_three; omega⟩)) ≤ 1 :=
          min_le_left _ _
        have hsq : TrackD.sigma (regime.B i) (M.s i) M.b τ' ^ 2 ≤ (T'deg ^ d) ^ 2 := by
          rw [hsigma_eq]
        have hle : TrackD.sigma (regime.B i) (M.s i) M.b τ' ^ 2 *
            min 1 _ ≤ (T'deg ^ d) ^ 2 * 1 :=
          mul_le_mul hsq hmin_le (by positivity) (by positivity)
        have hpow : (T'deg ^ d) ^ 2 = T'deg ^ (2 * d) := by
          rw [← pow_mul]
          congr 1
          ring
        calc commonRankTarget M i τ'
            = TrackD.sigma (regime.B i) (M.s i) M.b τ' ^ 2 * min 1 _ := rfl
          _ ≤ (T'deg ^ d) ^ 2 * 1 := hle
          _ = T'deg ^ (2 * d) := by rw [hpow, mul_one]
      have hp2_eq : (2 * k + 1) + (2 * d - (2 * k + 1)) = 2 * d := by
        have hle2 : 2 * k + 1 ≤ 2 * d := by omega
        omega
      have hT'pow_eq : T'deg ^ (2 * d) =
          T'deg ^ (2 * k + 1) * T'deg ^ (2 * d - (2 * k + 1)) := by
        conv_lhs => rw [← hp2_eq]
        rw [pow_add]
      have hTpow_ne : T'deg ^ (2 * k + 1) ≠ 0 := pow_ne_zero _ (ne_of_gt hT'pos)
      have hT'pow_le_one : T'deg ^ (2 * d - (2 * k + 1)) ≤ 1 := by
        calc T'deg ^ (2 * d - (2 * k + 1)) ≤ (1 : ℝ) ^ (2 * d - (2 * k + 1)) :=
              pow_le_pow_left₀ hT'pos.le (le_of_lt hT'lt) _
          _ = 1 := one_pow _
      have hR_nn : (0 : ℝ) ≤ (Tdeg / T'deg) ^ (2 * k + 1) :=
        pow_nonneg (div_nonneg hTpos.le hT'pos.le) _
      have hE2_nn : (0 : ℝ) ≤ Real.exp (2 * (d : ℝ) * κ * M.s i) := Real.exp_nonneg _
      have htarg_mid : commonRankTarget M i τ' * (Tdeg / T'deg) ^ (2 * k + 1) ≤
          Tdeg ^ (2 * k + 1) * T'deg ^ (2 * d - (2 * k + 1)) := by
        have hR_eq : (Tdeg / T'deg) ^ (2 * k + 1) =
            Tdeg ^ (2 * k + 1) / T'deg ^ (2 * k + 1) := div_pow _ _ _
        have hle : T'deg ^ (2 * d) * (Tdeg ^ (2 * k + 1) / T'deg ^ (2 * k + 1)) =
            Tdeg ^ (2 * k + 1) * T'deg ^ (2 * d - (2 * k + 1)) := by
          rw [hT'pow_eq, div_eq_mul_inv]
          have hcancel : T'deg ^ (2 * k + 1) * (T'deg ^ (2 * k + 1))⁻¹ = 1 :=
            mul_inv_cancel₀ hTpow_ne
          calc T'deg ^ (2 * k + 1) * T'deg ^ (2 * d - (2 * k + 1)) *
                (Tdeg ^ (2 * k + 1) * (T'deg ^ (2 * k + 1))⁻¹)
              = Tdeg ^ (2 * k + 1) * T'deg ^ (2 * d - (2 * k + 1)) *
                (T'deg ^ (2 * k + 1) * (T'deg ^ (2 * k + 1))⁻¹) := by ring
            _ = Tdeg ^ (2 * k + 1) * T'deg ^ (2 * d - (2 * k + 1)) * 1 := by
              rw [hcancel]
            _ = Tdeg ^ (2 * k + 1) * T'deg ^ (2 * d - (2 * k + 1)) := mul_one _
        calc commonRankTarget M i τ' * (Tdeg / T'deg) ^ (2 * k + 1)
            ≤ T'deg ^ (2 * d) * (Tdeg ^ (2 * k + 1) / T'deg ^ (2 * k + 1)) := by
              rw [← hR_eq]
              exact mul_le_mul_of_nonneg_right htarget'_le hR_nn
          _ = Tdeg ^ (2 * k + 1) * T'deg ^ (2 * d - (2 * k + 1)) := hle
      have hTpow_nn : (0 : ℝ) ≤ Tdeg ^ (2 * k + 1) := pow_nonneg hTpos.le _
      have htarg0 : commonRankTarget M i τ ≤
          Real.exp (2 * (d : ℝ) * κ * M.s i) * Tdeg ^ (2 * k + 1) := by
        have hle1 : commonRankTarget M i τ ≤
            (Tdeg ^ (2 * k + 1) * T'deg ^ (2 * d - (2 * k + 1))) *
            Real.exp (2 * (d : ℝ) * κ * M.s i) := by
          calc commonRankTarget M i τ
              ≤ commonRankTarget M i τ' * (Tdeg / T'deg) ^ (2 * k + 1) *
                Real.exp (2 * (d : ℝ) * κ * M.s i) := hgrowth
            _ = (commonRankTarget M i τ' * (Tdeg / T'deg) ^ (2 * k + 1)) *
                Real.exp (2 * (d : ℝ) * κ * M.s i) := by ring
            _ ≤ (Tdeg ^ (2 * k + 1) * T'deg ^ (2 * d - (2 * k + 1))) *
                Real.exp (2 * (d : ℝ) * κ * M.s i) :=
              mul_le_mul_of_nonneg_right htarg_mid hE2_nn
        have hle2 : (Tdeg ^ (2 * k + 1) * T'deg ^ (2 * d - (2 * k + 1))) *
            Real.exp (2 * (d : ℝ) * κ * M.s i) ≤
            (Tdeg ^ (2 * k + 1) * 1) * Real.exp (2 * (d : ℝ) * κ * M.s i) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hT'pow_le_one hTpow_nn) hE2_nn
        calc commonRankTarget M i τ
            ≤ (Tdeg ^ (2 * k + 1) * T'deg ^ (2 * d - (2 * k + 1))) *
              Real.exp (2 * (d : ℝ) * κ * M.s i) := hle1
          _ ≤ (Tdeg ^ (2 * k + 1) * 1) * Real.exp (2 * (d : ℝ) * κ * M.s i) := hle2
          _ = Real.exp (2 * (d : ℝ) * κ * M.s i) * Tdeg ^ (2 * k + 1) := by ring
      exact common_rank_borrow_lt_one Tdeg (Lnat : ℝ) h k d c θ (M.s i) κ
        (commonRankTarget M i τ) (commonLabelRank i₀ Γ Lnat : ℝ)
        hTpos hTge1 hLge hkh hh2 hborrow0 htarg0 hcpos habs htarget_nn_tau
        hspos.le hθ.le

end
end DistinctDistances.SparseCones
