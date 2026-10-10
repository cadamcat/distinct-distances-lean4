import DistinctDistances.TrackE.OuterPool
import DistinctDistances.TrackE.CommonLabelEnvelope
import DistinctDistances.TrackE.CommonLabelGroup
import DistinctDistances.TrackE.CommonRankProof
import DistinctDistances.TrackA.Regularity
import DistinctDistances.TrackD.Profiles.Envelope
import DistinctDistances.TrackD.Profiles.RankCore

/-! Helpers for the outer-regularity leaves 189–191 (lane m-o-reg).
Filter/finset counting, real-exponent comparisons for `s = log B`,
and degree/mass conversions. No frozen declaration is proved here. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- `s = log B` gives `testDeg B s b = B ^ (1 + b)` as reals. -/
theorem testDeg_eq_rpow_of_logB (B s b : ℝ) (hB : 0 < B) (hs : s = Real.log B) :
    TrackD.testDeg B s b = B ^ ((1 : ℝ) + b) := by
  unfold TrackD.testDeg
  rw [hs, mul_comm b (Real.log B), ← Real.rpow_def_of_pos hB,
    add_comm (1 : ℝ) b, Real.rpow_add_one hB.ne']
  exact mul_comm _ _

/-- Testing degree tends to infinity when `1 + b > 0`, `B → ∞`, `s = log B`. -/
theorem testDeg_tendsto_atTop_of_logB {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} {M : CommonPoolProfile T}
    (hs : ∀ i, M.s i = Real.log (regime.B i)) (b : ℝ) (hb : 0 < 1 + b) :
    Tendsto (fun i => TrackD.testDeg (regime.B i) (M.s i) b) atTop atTop := by
  have hB := regime.B_tendsto
  have hexp : 0 < 1 + b := hb
  have : Tendsto (fun i => (regime.B i) ^ ((1 : ℝ) + b)) atTop atTop :=
    (tendsto_rpow_atTop hexp).comp hB
  apply this.congr
  intro i
  rw [testDeg_eq_rpow_of_logB _ _ _ (regime.B_pos i) (hs i)]

/-- Eventually `1 ≤ T_s(b)`, `2 ≤ T_s(b)` and `T/2 ≤ ⌊T⌋₊` plus `1 ≤ ⌊T⌋₊`. -/
theorem eventually_floor_ge_half {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} {M : CommonPoolProfile T}
    (hs : ∀ i, M.s i = Real.log (regime.B i)) (b : ℝ) (hb : 0 < 1 + b) :
    ∀ᶠ i in atTop, (1 : ℝ) ≤ TrackD.testDeg (regime.B i) (M.s i) b ∧
      TrackD.testDeg (regime.B i) (M.s i) b / 2 ≤
        (⌊TrackD.testDeg (regime.B i) (M.s i) b⌋₊ : ℝ) ∧
      1 ≤ ⌊TrackD.testDeg (regime.B i) (M.s i) b⌋₊ := by
  filter_upwards [(testDeg_tendsto_atTop_of_logB hs b hb).eventually_ge_atTop 2]
    with i hi
  refine ⟨by linarith, ?_, ?_⟩
  · have hfl : TrackD.testDeg (regime.B i) (M.s i) b - 1 <
        (⌊TrackD.testDeg (regime.B i) (M.s i) b⌋₊ : ℝ) := by
      have := Nat.sub_one_lt_floor (TrackD.testDeg (regime.B i) (M.s i) b)
      have hcast : ((⌊TrackD.testDeg (regime.B i) (M.s i) b⌋₊ : ℕ) : ℝ) =
          (⌊TrackD.testDeg (regime.B i) (M.s i) b⌋₊ : ℝ) := rfl
      linarith
    linarith
  · have hfl : TrackD.testDeg (regime.B i) (M.s i) b - 1 <
        (⌊TrackD.testDeg (regime.B i) (M.s i) b⌋₊ : ℝ) := by
      have := Nat.sub_one_lt_floor (TrackD.testDeg (regime.B i) (M.s i) b)
      have hcast : ((⌊TrackD.testDeg (regime.B i) (M.s i) b⌋₊ : ℕ) : ℝ) =
          (⌊TrackD.testDeg (regime.B i) (M.s i) b⌋₊ : ℝ) := rfl
      linarith
    have h1 : (1 : ℝ) < (⌊TrackD.testDeg (regime.B i) (M.s i) b⌋₊ : ℝ) := by
      linarith
    have h2 : (1 : ℝ) ≤ (⌊TrackD.testDeg (regime.B i) (M.s i) b⌋₊ : ℝ) :=
      le_of_lt h1
    exact_mod_cast h2

/-- Card of a union deletion is at most the sum. -/
theorem card_union_deletion_le (G D1 D2 : Finset (RPoint d × RPoint d)) :
    ((G \ (D1 ∪ D2)).card : ℝ) ≥ 0 := Nat.cast_nonneg _

/-- Splitting a deletion budget over two parts. -/
theorem deletion_split (S : ℝ) (_hS : 0 ≤ S) (ρ1 ρ2 : ℝ) (_h1 : 0 ≤ ρ1) (_h2 : 0 ≤ ρ2) :
    ρ1 * S ^ 2 + ρ2 * S ^ 2 = (ρ1 + ρ2) * S ^ 2 := by ring

/-- A family defined in degree `L` comes from a single list. -/
theorem fromLists_of_definedInDegree {n : ℕ} (F : AffineFamily.Family n) (L : ℕ)
    (hL : 1 ≤ L) (hdef : AffineFamily.ComponentsDefinedInDegree F L) :
    TrackA.FromAffineLists F L := by
  refine ⟨1, fun _ => F, fun _ => L, ?_, ?_, ?_⟩
  · intro i
    exact ⟨hL, hdef⟩
  · intro V
    constructor
    · intro hV
      exact ⟨⟨0, by omega⟩, by simpa using hV⟩
    · rintro ⟨⟨i, hi⟩, hV⟩
      have : i = 0 := by omega
      subst this
      simpa using hV
  · simp

/-- Degree is monotone under filtering when summands are nonnegative. -/
theorem degree_filter_le {n : ℕ} (F : AffineFamily.Family n)
    (p : AffineVariety n → Prop) [DecidablePred p]
    (hnn : ∀ V ∈ F, (0 : ℚ) ≤ V.degree) :
    AffineFamily.degree (F.filter p) ≤ AffineFamily.degree F := by
  unfold AffineFamily.degree
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro V hV
    exact (Finset.mem_filter.mp hV).1
  · intro V hV _
    exact hnn V hV

/-- The testing-degree ratio `T(t₁)/T(t₀) = B^(t₁-t₀)` tends to infinity
when `t₀ < t₁` and `s = log B → ∞`. -/
theorem testDeg_ratio_tendsto_atTop {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} {M : CommonPoolProfile T}
    (hs : ∀ i, M.s i = Real.log (regime.B i)) (t₀ t₁ : ℝ) (h : t₀ < t₁) :
    Tendsto (fun i => TrackD.testDeg (regime.B i) (M.s i) t₁ /
      TrackD.testDeg (regime.B i) (M.s i) t₀) atTop atTop := by
  have hratio : ∀ i, TrackD.testDeg (regime.B i) (M.s i) t₁ /
      TrackD.testDeg (regime.B i) (M.s i) t₀ =
      (regime.B i) ^ (t₁ - t₀) := by
    intro i
    have hB : 0 < regime.B i := regime.B_pos i
    unfold TrackD.testDeg
    rw [mul_div_mul_left _ _ hB.ne']
    rw [← Real.exp_sub]
    have heq : t₁ * M.s i - t₀ * M.s i = (t₁ - t₀) * M.s i := by ring
    rw [heq, hs i]
    rw [Real.rpow_def_of_pos hB]
    congr 1
    ring
  have hexp : (0 : ℝ) < t₁ - t₀ := by linarith
  have htend : Tendsto (fun i => (regime.B i) ^ (t₁ - t₀)) atTop atTop :=
    (tendsto_rpow_atTop hexp).comp regime.B_tendsto
  exact htend.congr (fun i => (hratio i).symm)

/-- Eventually `C * ⌊T₀⌋ ≤ ⌊T₁⌋` for fixed `C`, when `t₀ < t₁`
and both testing degrees diverge (`1 + t > 0`). -/
theorem eventually_regularity_degree_dominates {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} {M : CommonPoolProfile T}
    (hs : ∀ i, M.s i = Real.log (regime.B i)) (t₀ t₁ : ℝ) (h : t₀ < t₁)
    (hb₀ : (0 : ℝ) < 1 + t₀) (hb₁ : (0 : ℝ) < 1 + t₁)
    (C : ℕ) :
    ∀ᶠ i in atTop, C * ⌊TrackD.testDeg (regime.B i) (M.s i) t₀⌋₊ ≤
      ⌊TrackD.testDeg (regime.B i) (M.s i) t₁⌋₊ := by
  have hT0pos : ∀ᶠ i in atTop, 0 < TrackD.testDeg (regime.B i) (M.s i) t₀ := by
    filter_upwards with i
    unfold TrackD.testDeg
    exact mul_pos (regime.B_pos i) (Real.exp_pos _)
  have hratio := testDeg_ratio_tendsto_atTop hs t₀ t₁ h
  have hbig := hratio.eventually_ge_atTop (((2 * C + 2 : ℕ) : ℝ))
  have hT1ge := (testDeg_tendsto_atTop_of_logB hs t₁ hb₁).eventually_ge_atTop 2
  filter_upwards [hT0pos, hbig, hT1ge,
    eventually_floor_ge_half hs t₁ hb₁] with i hpos hbigi hT1gei hfloor1
  have hT0le : (⌊TrackD.testDeg (regime.B i) (M.s i) t₀⌋₊ : ℝ) ≤
      TrackD.testDeg (regime.B i) (M.s i) t₀ :=
    Nat.floor_le (le_of_lt hpos)
  have hT1half : TrackD.testDeg (regime.B i) (M.s i) t₁ / 2 ≤
      (⌊TrackD.testDeg (regime.B i) (M.s i) t₁⌋₊ : ℝ) := hfloor1.2.1
  have hT0pos' : (0 : ℝ) < TrackD.testDeg (regime.B i) (M.s i) t₀ := hpos
  have hratioi : (((2 * C + 2 : ℕ) : ℝ)) ≤ TrackD.testDeg (regime.B i) (M.s i) t₁ /
      TrackD.testDeg (regime.B i) (M.s i) t₀ := hbigi
  have hmul : (((2 * C + 2 : ℕ) : ℝ)) * TrackD.testDeg (regime.B i) (M.s i) t₀ ≤
      TrackD.testDeg (regime.B i) (M.s i) t₁ := by
    rwa [le_div_iff₀ hT0pos'] at hratioi
  have hC2 : ((2 * C + 2 : ℕ) : ℝ) = 2 * (C : ℝ) + 2 := by push_cast; ring
  have hC : (C : ℝ) * (⌊TrackD.testDeg (regime.B i) (M.s i) t₀⌋₊ : ℝ) ≤
      TrackD.testDeg (regime.B i) (M.s i) t₁ / 2 := by
    have hmul2 : (2 * (C : ℝ) + 2) * TrackD.testDeg (regime.B i) (M.s i) t₀ ≤
        TrackD.testDeg (regime.B i) (M.s i) t₁ := by
      rw [← hC2]
      exact hmul
    calc (C : ℝ) * _ ≤ (C : ℝ) * TrackD.testDeg (regime.B i) (M.s i) t₀ := by
          gcongr
        _ ≤ _ := by linarith
  have hfin : (C : ℝ) * (⌊TrackD.testDeg (regime.B i) (M.s i) t₀⌋₊ : ℝ) ≤
      (⌊TrackD.testDeg (regime.B i) (M.s i) t₁⌋₊ : ℝ) := hC.trans hT1half
  have hcast : (((C * ⌊TrackD.testDeg (regime.B i) (M.s i) t₀⌋₊ : ℕ)) : ℝ) =
      (C : ℝ) * (⌊TrackD.testDeg (regime.B i) (M.s i) t₀⌋₊ : ℝ) := by
    push_cast
    ring
  rw [← hcast] at hfin
  exact Nat.cast_le.mp hfin

/-- The regularity degree `T₁` fits in `B^(2-c)` when `1 + t₁ ≤ 2 - c` and `1 ≤ B`. -/
theorem regularity_degree_le_Bpow (B T₁ c t₁ : ℝ) (hB : 1 ≤ B)
    (hT : T₁ ≤ B ^ ((1 : ℝ) + t₁)) (hle : (1 : ℝ) + t₁ ≤ 2 - c) :
    T₁ ≤ B ^ (2 - c) :=
  hT.trans (Real.rpow_le_rpow_of_exponent_le hB hle)

/-- Pool points diverge: `|poolPts| → ∞` via `ExpLower` with `ε = 1`
(`N = B^d`, `s = log B`, `d ≥ 3` gives `d-1 > 0`). -/
theorem poolPts_card_tendsto_atTop {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} (M : CommonPoolProfile T)
    (hs : ∀ i, M.s i = Real.log (regime.B i)) :
    Tendsto (fun i => ((TrackD.poolPts (T.sources i)).card : ℝ)) atTop atTop := by
  have hd3 := regime.dimension_ge_three
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by
    have hdR : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd3
    linarith
  have hlow := M.source_size.1 1 one_pos
  have hB := regime.B_tendsto
  -- `|poolPts| ≥ N·exp(-s) = B^d·B^{-1} = B^{d-1} → ∞`
  have hbound : ∀ᶠ i in atTop, (regime.B i) ^ ((d : ℝ) - 1) ≤
      ((TrackD.poolPts (T.sources i)).card : ℝ) := by
    filter_upwards [hlow] with i hi
    have h1 := hi ()
    -- `h1 : N·exp(-1·s) ≤ |poolPts|`
    have hdne : (d : ℝ) ≠ 0 := by
      have hdR : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd3
      linarith
    have hNeq : regime.N i = (regime.B i) ^ (d : ℝ) := by
      have hBdef : regime.B i = (regime.N i) ^ ((1 : ℝ) / (d : ℝ)) := rfl
      have hNnn : (0 : ℝ) ≤ regime.N i := (regime.N_pos i).le
      have hmul : ((1 : ℝ) / (d : ℝ)) * (d : ℝ) = 1 := by field_simp
      have hBd : (regime.B i) ^ (d : ℝ) = regime.N i := by
        rw [hBdef, ← Real.rpow_mul hNnn, hmul, Real.rpow_one]
      exact hBd.symm
    have hseq : Real.exp (-1 * M.s i) = (regime.B i) ^ (-1 : ℝ) := by
      rw [hs i, Real.rpow_def_of_pos (regime.B_pos i)]
      congr 1
      ring
    calc (regime.B i) ^ ((d : ℝ) - 1)
        = regime.N i * Real.exp (-1 * M.s i) := by
          rw [hNeq, hseq, ← Real.rpow_add (regime.B_pos i)]
          congr 1
      _ ≤ _ := h1
  apply tendsto_atTop.2
  intro b
  filter_upwards [(((tendsto_rpow_atTop hd1).comp hB)).eventually_ge_atTop b,
    hbound] with i hi1 hi2
  exact hi1.trans hi2

/-- Borrow time just before a cut, off all cuts (copy of the private
`exists_plateau_borrow_time`, needed for 189 since that lemma is private). -/
theorem outer_borrow_time {F : ConeCoverageSequence regime}
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

/-- Reindexing of the pair label set (public copy of the private bridge in
`CommonLabelEnvelope.lean`, needed for 189 since that lemma is private). -/
theorem outer_rank_eq_hilbertOfSet (i₀ : Fin d)
    (Γ : Finset (RPoint d × RPoint d)) (L : ℕ) :
    commonLabelRank i₀ Γ L = hilbertOfSet (commonLabelPoints i₀ Γ) L := by
  classical
  let S : Set (Fin d ⊕ Fin d → ℂ) :=
    (fun pq : RPoint d × RPoint d =>
      TrackD.labelPt i₀ (TrackD.toC pq.1) (TrackD.toC pq.2)) '' (Γ : Set (RPoint d × RPoint d))
  have hS : S = (fun pq : RPoint d × RPoint d =>
      TrackD.labelPt i₀ (TrackD.toC pq.1) (TrackD.toC pq.2)) '' (Γ : Set (RPoint d × RPoint d)) := rfl
  have hRank : commonLabelRank i₀ Γ L = restrictionRank S L := by
    unfold commonLabelRank
    rfl
  have hPts : commonLabelPoints i₀ Γ =
      (fun x : Fin d ⊕ Fin d → ℂ => fun i => x (finSumFinEquiv.symm i)) '' S := by
    unfold commonLabelPoints S
    rw [Set.image_image]
  rw [hRank, hPts]
  let e : (Fin d ⊕ Fin d) ≃ Fin (d + d) := finSumFinEquiv
  let T' : Set (Point (d + d)) :=
    (fun x : Fin d ⊕ Fin d → ℂ => fun i => x (e.symm i)) '' S
  let V := AffineVariety.closure T'
  let rename := MvPolynomial.renameEquiv ℂ e
  let q : MvPolynomial.restrictTotalDegree (Fin d ⊕ Fin d) ℂ L →ₗ[ℂ] (Poly (d + d) ⧸ V.ideal) :=
    (Ideal.Quotient.mkₐ ℂ V.ideal).toLinearMap.comp
      (rename.toLinearMap.comp (MvPolynomial.restrictTotalDegree (Fin d ⊕ Fin d) ℂ L).subtype)
  have hrange : LinearMap.range q = V.restrictionSpace L := by
    ext y
    change (∃ f, q f = y) ↔ ∃ f,
      f ∈ OAI.QuarticPowerFree.totalSpace L ∧
        (Ideal.Quotient.mkₐ ℂ V.ideal).toLinearMap f = y
    constructor
    · rintro ⟨f, rfl⟩
      refine ⟨rename f.val, OAI.QuarticPowerFree.mem_totalSpace.mpr ?_, rfl⟩
      rw [MvPolynomial.totalDegree_renameEquiv]
      exact (MvPolynomial.mem_restrictTotalDegree _ _ _).mp f.property
    · rintro ⟨f, hf, rfl⟩
      have hdegree : (rename.symm f).totalDegree ≤ L := by
        rw [MvPolynomial.renameEquiv_symm, MvPolynomial.totalDegree_renameEquiv]
        exact OAI.QuarticPowerFree.mem_totalSpace.mp hf
      let p : MvPolynomial.restrictTotalDegree (Fin d ⊕ Fin d) ℂ L :=
        ⟨rename.symm f, (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr hdegree⟩
      refine ⟨p, ?_⟩
      change Ideal.Quotient.mk V.ideal (rename (rename.symm f)) =
        Ideal.Quotient.mk V.ideal f
      rw [rename.apply_symm_apply]
  have hker : LinearMap.ker (restrictionMap S L) = LinearMap.ker q := by
    ext f
    change (restrictionMap S L f = 0) ↔
      Ideal.Quotient.mk V.ideal (rename f.val) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    change (restrictionMap S L f = 0) ↔
      ∀ x ∈ T', MvPolynomial.aeval x (rename f.val) = 0
    constructor
    · intro hf x hx
      obtain ⟨z, hz, rfl⟩ := hx
      have hzero := congrFun hf ⟨z, hz⟩
      change MvPolynomial.aeval z f.val = 0 at hzero
      simpa only [rename, MvPolynomial.renameEquiv_apply, MvPolynomial.aeval_rename,
        Function.comp_def, Equiv.symm_apply_apply] using hzero
    · intro hf
      funext z
      have hzero := hf (fun i => z.val (e.symm i)) ⟨z.val, z.property, rfl⟩
      change MvPolynomial.aeval z.val f.val = 0
      simpa only [rename, MvPolynomial.renameEquiv_apply, MvPolynomial.aeval_rename,
        Function.comp_def, Equiv.symm_apply_apply] using hzero
  have he := (restrictionMap S L).finrank_range_add_finrank_ker
  have hq := q.finrank_range_add_finrank_ker
  rw [← hker] at hq
  change Module.finrank ℂ (LinearMap.range (restrictionMap S L)) =
    Module.finrank ℂ (V.restrictionSpace L)
  rw [← hrange]
  exact Nat.add_right_cancel (he.trans hq.symm)

/-- Lower bound for the profile `σ` just before the final cut: with
`k = d-(j+1)`, `σ(τ') ≥ e_{j+1}·T(τ')^k·exp(-d·κ·s)` when `τ'` lies within `κ`
below `β = b_j` (off cuts irrelevant here), later cuts are at `1`, `τ' < 1`,
`s > 0` and `B > 0`. Each of the first `j+1` factors loses at most `κ·s`
(`τ'-b_a ≥ -κ` via sortedness), the last `k` factors equal `T'`. -/
theorem outer_sigma_lower {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} (M : CommonPoolProfile T)
    (j k : ℕ) (hkj : k + j + 1 = d) (hj : j < d)
    (τ' κ : ℝ) (hκ : 0 < κ)
    (hmem : M.b ⟨j, hj⟩ - κ < τ' ∧ τ' < M.b ⟨j, hj⟩)
    (htop : ∀ a : Fin d, j < a.val → M.b a = 1)
    (hτ'1 : τ' < 1) (i : ℕ)
    (hspos : 0 < M.s i) (hBpos : 0 < regime.B i) :
    TrackD.eScale (regime.B i) (M.s i) M.b (j + 1) *
      (TrackD.testDeg (regime.B i) (M.s i) τ') ^ k *
      Real.exp (-(d : ℝ) * κ * M.s i) ≤
      TrackD.sigma (regime.B i) (M.s i) M.b τ' := by
  classical
  have hd3 := regime.dimension_ge_three
  have hj1le : j + 1 ≤ d := by omega
  have hk_eq : d - (j + 1) = k := by omega
  set B := regime.B i with hBdef
  set s := M.s i with hsdef
  set t : Fin d → ℝ := M.b with htdef
  set T' := TrackD.testDeg B s τ' with hT'def
  have hBne : B ≠ 0 := ne_of_gt hBpos
  have hsnn := hspos.le
  have hT'pos : 0 < T' := TrackD.RankCore.testDeg_pos hBpos _ _
  -- each cut scale is positive
  have hDpos : ∀ a : Fin d, 0 < TrackD.cutScale B s t a :=
    fun a => TrackD.RankCore.testDeg_pos hBpos _ _
  -- `τ' ≤ b_a` for `a ≥ j+1` (later cuts at 1), so `min = T'`
  have hmin_eq : ∀ a : Fin d, j + 1 ≤ a.val →
      min T' (TrackD.cutScale B s t a) = T' := by
    intro a ha
    apply min_eq_left
    have hb1 : t a = 1 := htop a (by omega)
    have hle : τ' ≤ t a := by rw [hb1]; exact le_of_lt hτ'1
    unfold T' TrackD.cutScale
    exact TrackD.RankCore.testDeg_mono hBpos.le hsnn hle
  -- for `a < j+1`, `min ≥ D_a·exp(-κs)` (`τ'-b_a ≥ -κ`, `s > 0`)
  have hmin_ge : ∀ a : Fin d, a.val < j + 1 →
      TrackD.cutScale B s t a * Real.exp (-κ * s) ≤ min T' (TrackD.cutScale B s t a) := by
    intro a ha
    have hval : a.val ≤ j := by omega
    have hle : t a ≤ t ⟨j, hj⟩ :=
      M.sorted (Fin.le_def.mpr hval)
    have hgap : -κ ≤ τ' - t a := by
      have h1 : t ⟨j, hj⟩ - κ < τ' := by
        have := hmem.1
        simpa [htdef] using this
      linarith
    have hexp_le : Real.exp (-κ * s) ≤ T' / TrackD.cutScale B s t a := by
      have hTeq : T' / TrackD.cutScale B s t a = Real.exp ((τ' - t a) * s) := by
        unfold T' TrackD.cutScale TrackD.testDeg
        rw [mul_div_mul_left _ _ hBne, ← Real.exp_sub]
        congr 1
        ring
      rw [hTeq]
      apply Real.exp_le_exp.mpr
      have hmul : -κ * s ≤ (τ' - t a) * s :=
        mul_le_mul_of_nonneg_right hgap hsnn
      linarith [hmul]
    have hexp1 : Real.exp (-κ * s) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : -κ * s ≤ 0 := by
        have hks : (0 : ℝ) ≤ κ * s := mul_nonneg hκ.le hsnn
        linarith
      linarith
    have hDpos_a := hDpos a
    apply le_min
    · calc TrackD.cutScale B s t a * Real.exp (-κ * s)
          ≤ TrackD.cutScale B s t a * (T' / TrackD.cutScale B s t a) :=
            mul_le_mul_of_nonneg_left hexp_le hDpos_a.le
        _ = T' := by field_simp
    · calc TrackD.cutScale B s t a * Real.exp (-κ * s)
          ≤ TrackD.cutScale B s t a * 1 :=
            mul_le_mul_of_nonneg_left hexp1 hDpos_a.le
        _ = _ := mul_one _
  -- split `σ` into first `j+1` factors and last `k` factors
  set F1 : Finset (Fin d) := Finset.univ.filter (fun a : Fin d => a.val < j + 1) with hF1def
  have hF1card_le : F1.card ≤ d := by
    calc F1.card ≤ Finset.univ.card := Finset.card_filter_le _ _
      _ = d := by rw [Finset.card_univ, Fintype.card_fin]
  have heScale_eq : TrackD.eScale B s t (j + 1) =
      ∏ a ∈ F1, TrackD.cutScale B s t a := rfl
  have hsigma_eq : TrackD.sigma B s t τ' =
      (∏ a ∈ F1, min T' (TrackD.cutScale B s t a)) *
      (∏ a ∈ Finset.univ.filter (fun a : Fin d => j + 1 ≤ a.val),
        min T' (TrackD.cutScale B s t a)) := by
    unfold TrackD.sigma
    have hsplit := Finset.prod_filter_mul_prod_filter_not
      (s := (Finset.univ : Finset (Fin d)))
      (f := fun a => min T' (TrackD.cutScale B s t a))
      (p := fun a : Fin d => a.val < j + 1)
    have hnot : Finset.univ.filter (fun a : Fin d => ¬ a.val < j + 1) =
        Finset.univ.filter (fun a : Fin d => j + 1 ≤ a.val) := by
      apply Finset.filter_congr
      intro a _
      exact Nat.not_lt
    rw [hnot] at hsplit
    simpa [hF1def] using hsplit.symm
  have hF2eq : ∏ a ∈ Finset.univ.filter (fun a : Fin d => j + 1 ≤ a.val),
      min T' (TrackD.cutScale B s t a) = T' ^ k := by
    have h1 : ∀ a ∈ Finset.univ.filter (fun a : Fin d => j + 1 ≤ a.val),
        min T' (TrackD.cutScale B s t a) = T' := by
      intro a ha
      exact hmin_eq a (Finset.mem_filter.mp ha).2
    rw [Finset.prod_congr rfl h1, Finset.prod_const]
    congr 1
    have hcard := TrackD.RankCore.card_after (d := d) (j + 1) hj1le
    omega
  have hF1ge : (∏ a ∈ F1, TrackD.cutScale B s t a * Real.exp (-κ * s)) ≤
      (∏ a ∈ F1, min T' (TrackD.cutScale B s t a)) := by
    apply Finset.prod_le_prod₀
    · intro a _
      exact mul_nonneg (hDpos a).le (Real.exp_nonneg _)
    · intro a ha
      exact hmin_ge a (Finset.mem_filter.mp ha).2
  have hF1prod : ∏ a ∈ F1, TrackD.cutScale B s t a * Real.exp (-κ * s) =
      (∏ a ∈ F1, TrackD.cutScale B s t a) * Real.exp (-(F1.card : ℝ) * κ * s) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const]
    congr 1
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hexp_ge : Real.exp (-(d : ℝ) * κ * s) ≤
      Real.exp (-(F1.card : ℝ) * κ * s) := by
    apply Real.exp_le_exp.mpr
    have hcardR : (F1.card : ℝ) ≤ (d : ℝ) := by exact_mod_cast hF1card_le
    have hks : (0 : ℝ) ≤ κ * s := mul_nonneg hκ.le hsnn
    nlinarith
  have hepos : 0 < ∏ a ∈ F1, TrackD.cutScale B s t a := by
    apply Finset.prod_pos
    intro a _
    exact hDpos a
  calc TrackD.eScale B s t (j + 1) * T' ^ k * Real.exp (-(d : ℝ) * κ * s)
      = (∏ a ∈ F1, TrackD.cutScale B s t a) * T' ^ k *
        Real.exp (-(d : ℝ) * κ * s) := by rw [heScale_eq]
    _ ≤ (∏ a ∈ F1, TrackD.cutScale B s t a) * T' ^ k *
        Real.exp (-(F1.card : ℝ) * κ * s) := by gcongr
    _ = (∏ a ∈ F1, TrackD.cutScale B s t a * Real.exp (-κ * s)) * T' ^ k := by
        rw [hF1prod]; ring
    _ ≤ (∏ a ∈ F1, min T' (TrackD.cutScale B s t a)) * T' ^ k := by gcongr
    _ = TrackD.sigma B s t τ' := by rw [hsigma_eq, hF2eq]

end
end DistinctDistances.SparseCones
