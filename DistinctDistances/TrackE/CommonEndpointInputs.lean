import DistinctDistances.TrackE.CommonRank
import DistinctDistances.TrackE.WindowBranches
import DistinctDistances.TrackE.SeparatedEndpointInputs
import DistinctDistances.TrackE.DepthDataCore
import DistinctDistances.TrackE.Contradiction

/-! Elementary and row-rank inputs for the strict common endpoint,
sparse-cones.tex:318–338. All point sets and cone families are unchanged. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- The dyadic physical width lies below the outer width. -/
theorem common_pool_width_le_logB {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} (M : CommonPoolProfile T) :
    ∀ i, M.s i ≤ Real.log (regime.B i) := by
  intro i
  obtain ⟨X, hX⟩ := (T.certificate i).sources_nonempty
  have hmem : X ∈ (T.partition i).pieces := (T.certificate i).sources_subset hX
  have hgood := ((T.certificate i).good.pieces_good X hmem).1
  obtain ⟨a, ha⟩ := hgood.width_dyadic
  have hwidth : X.width = M.s i :=
    M.width i X (Finset.mem_union_left _ hX)
  have hB : TrackD.cfgB (regime.P i) = regime.B i := rfl
  rw [hB] at ha
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ a := by positivity
  have h1le : (1 : ℝ) ≤ (2 : ℝ) ^ a := one_le_pow₀ (by norm_num)
  have hXpos : 0 < X.width := hwidth.symm ▸ M.width_pos i
  rw [ha] at hXpos
  have hlog_pos : 0 < Real.log (regime.B i) := by
    have hmul : Real.log (regime.B i) =
        (Real.log (regime.B i) / (2 : ℝ) ^ a) * (2 : ℝ) ^ a := by
      field_simp
    rw [hmul]
    exact mul_pos hXpos hpow_pos
  calc M.s i = Real.log (regime.B i) / (2 : ℝ) ^ a := by
        rw [← hwidth, ha]
    _ ≤ Real.log (regime.B i) := div_le_self hlog_pos.le h1le

/-- All positive-tolerance time bounds pass to the limiting common profile. -/
theorem common_profile_time_upper {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} (M : CommonPoolProfile T) :
    ∀ a : Fin d, M.b a ≤ 1 := by
  intro a
  apply le_of_forall_pos_le_add
  intro ε hε
  have hθ : (0 : ℝ) < ε / 2 := by positivity
  have hρ : (0 : ℝ) < ε / 2 := by positivity
  have hgood := M.good (ε / 2) hθ 1 zero_lt_one 1 le_rfl (ε / 2) hρ
  have hlim := M.limit (ε / 2) hρ
  obtain ⟨i, hgood_i, hlim_i⟩ := (hgood.and hlim).exists
  obtain ⟨X, hX⟩ := (T.certificate i).sources_nonempty
  have hXmem : X ∈ T.sources i ∪ T.targets i := Finset.mem_union_left _ hX
  have hpool : TrackD.PoolGood (regime.P i) (ε / 2) 1 1 (ε / 2)
      (T.sources i) (M.s i) M.b := hgood_i.1
  have hpiece : TrackD.PieceGood (regime.P i) (ε / 2) 1 1 X :=
    hpool.pieces X hX
  have htime := (hpiece.time_range a).2
  have hclose := hlim_i X hXmem a
  rw [abs_le] at hclose
  linarith

/-- At the final cut the literal limiting sigma is exactly the sample size. -/
theorem common_profile_sigma_last {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} (M : CommonPoolProfile T) (i : ℕ) :
    TrackD.sigma (regime.B i) (M.s i) M.b (commonLastTime M) = regime.N i := by
  have hd3 := regime.dimension_ge_three
  have hdpos_nat : 0 < d := by omega
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos_nat
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdpos
  have hBpos := regime.B_pos i
  have hNpos := regime.N_pos i
  have hspos := M.width_pos i
  have hlast : ∀ j : Fin d, M.b j ≤ commonLastTime M := by
    intro j
    unfold commonLastTime
    apply M.sorted
    show j ≤ ⟨d - 1, by omega⟩
    rw [Fin.le_def]
    simp only
    omega
  have hmin : ∀ j : Fin d,
      min (TrackD.testDeg (regime.B i) (M.s i) (commonLastTime M))
        (TrackD.cutScale (regime.B i) (M.s i) M.b j) =
      TrackD.cutScale (regime.B i) (M.s i) M.b j := by
    intro j
    apply min_eq_right
    show TrackD.cutScale (regime.B i) (M.s i) M.b j ≤
      TrackD.testDeg (regime.B i) (M.s i) (commonLastTime M)
    unfold TrackD.cutScale
    exact TrackD.RankCore.testDeg_mono hBpos.le hspos.le (hlast j)
  have hsig : TrackD.sigma (regime.B i) (M.s i) M.b (commonLastTime M) =
      ∏ j : Fin d, TrackD.cutScale (regime.B i) (M.s i) M.b j := by
    unfold TrackD.sigma
    apply Finset.prod_congr rfl
    intro j _
    exact hmin j
  rw [hsig]
  have hcut : ∀ j : Fin d, TrackD.cutScale (regime.B i) (M.s i) M.b j =
      regime.B i * Real.exp (M.b j * M.s i) := by
    intro j
    rfl
  simp_rw [hcut]
  rw [Finset.prod_mul_distrib]
  have hprodB : (∏ _ : Fin d, regime.B i) = regime.B i ^ d := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hprodB]
  have hexp : (∏ j : Fin d, Real.exp (M.b j * M.s i)) =
      Real.exp ((∑ j : Fin d, M.b j) * M.s i) := by
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.sum_mul]
  rw [hexp, M.sum_zero]
  simp only [zero_mul, Real.exp_zero, mul_one]
  -- B^d = N
  have hBdef : regime.B i = regime.N i ^ ((1 : ℝ) / (d : ℝ)) := rfl
  rw [hBdef]
  have hrpow : (regime.N i ^ ((1 : ℝ) / (d : ℝ))) ^ d =
      regime.N i ^ (((1 : ℝ) / (d : ℝ)) * (d : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
  rw [hrpow]
  have hone : ((1 : ℝ) / (d : ℝ)) * (d : ℝ) = 1 := by
    field_simp
  rw [hone, Real.rpow_one]

/-- A nonouter dyadic common singleton width is at most half the outer width. -/
theorem common_singleton_width_half {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (M : CommonPoolProfile T)
    (hcommon : ∀ i, T.IsCommon i) :
    ∀ i, 2 * M.s i ≤ Real.log (regime.B i) := by
  intro i
  obtain ⟨X, Y, hXs, hYs, hXYw, hbound⟩ := hcommon i
  have hXsrc : X ∈ T.sources i := by rw [hXs]; exact Finset.mem_singleton_self X
  have hmem : X ∈ (T.partition i).pieces := (T.certificate i).sources_subset hXsrc
  have hgood := ((T.certificate i).good.pieces_good X hmem).1
  obtain ⟨a, ha⟩ := hgood.width_dyadic
  have hB : TrackD.cfgB (regime.P i) = regime.B i := rfl
  rw [hB] at ha
  have hwidth : X.width = M.s i :=
    M.width i X (Finset.mem_union_left _ hXsrc)
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ a := by positivity
  have hspos := M.width_pos i
  have hXpos : 0 < X.width := hwidth.symm ▸ hspos
  rw [ha] at hXpos hwidth hbound
  -- ha rewritten: hXpos : 0 < log / 2^a, hwidth : log / 2^a = s, hbound : log/2^a < log
  have hlog_pos : 0 < Real.log (regime.B i) := by
    have hmul : Real.log (regime.B i) =
        (Real.log (regime.B i) / (2 : ℝ) ^ a) * (2 : ℝ) ^ a := by
      field_simp
    rw [hmul]
    exact mul_pos hXpos hpow_pos
  have hane : a ≠ 0 := by
    intro h
    subst h
    simp at hbound
  have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr hane
  have h2le : (2 : ℝ) ≤ (2 : ℝ) ^ a := by
    calc (2 : ℝ) = (2 : ℝ) ^ 1 := by simp
      _ ≤ (2 : ℝ) ^ a := pow_le_pow_right₀ (by norm_num) ha1
  have hfrac : (2 : ℝ) / (2 : ℝ) ^ a ≤ 1 := (div_le_one hpow_pos).mpr h2le
  have h2s : 2 * M.s i = Real.log (regime.B i) * ((2 : ℝ) / (2 : ℝ) ^ a) := by
    rw [← hwidth]
    ring
  rw [h2s]
  calc Real.log (regime.B i) * ((2 : ℝ) / (2 : ℝ) ^ a)
      ≤ Real.log (regime.B i) * 1 :=
        mul_le_mul_of_nonneg_left hfrac hlog_pos.le
    _ = Real.log (regime.B i) := mul_one _

/-- Choose an interior time arbitrarily close to the last cut, avoiding all
finitely many limiting cut times, before choosing a chart or graph. -/
theorem exists_common_endpoint_test {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} (M : CommonPoolProfile T)
    (c : ℝ) (hc : 0 < c) :
    ∃ τ : ℝ, 0 < τ ∧ τ < commonLastTime M ∧
      (∀ a : Fin d, M.b a ≠ τ) ∧
      2 * (d : ℝ) * (commonLastTime M - τ) < c / 2 := by
  obtain ⟨cb, hcb, _, hblast, _⟩ := M.balance
  have hlast_pos : 0 < commonLastTime M :=
    lt_of_lt_of_le hcb hblast
  have hdpos_nat : 0 < d := by have := regime.dimension_ge_three; omega
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos_nat
  have h8d : (0 : ℝ) < 8 * (d : ℝ) := by positivity
  set last := commonLastTime M with hlastdef
  set δ : ℝ := min (last / 2) (c / (8 * (d : ℝ))) with hδdef
  have hδpos : 0 < δ := lt_min (by linarith) (by positivity)
  have hδ1 : δ ≤ last / 2 := min_le_left _ _
  have hδ2 : δ ≤ c / (8 * (d : ℝ)) := min_le_right _ _
  have hDpos : (0 : ℝ) < (d : ℝ) + 2 := by positivity
  have hDne : ((d : ℝ) + 2) ≠ 0 := ne_of_gt hDpos
  -- d+1 sample points in (last-δ, last)
  let t : ℕ → ℝ := fun k => last - δ * (((k : ℝ) + 1) / ((d : ℝ) + 2))
  have hmem_of_le : ∀ k : ℕ, k ≤ d →
      last - δ < t k ∧ t k < last := by
    intro k hk
    have hkR : (k : ℝ) ≤ (d : ℝ) := by exact_mod_cast hk
    have h1 : (0 : ℝ) < ((k : ℝ) + 1) / ((d : ℝ) + 2) := by positivity
    have h2 : ((k : ℝ) + 1) / ((d : ℝ) + 2) < 1 := by
      rw [div_lt_one hDpos]
      linarith
    constructor
    · simp only [t]
      have : δ * (((k : ℝ) + 1) / ((d : ℝ) + 2)) < δ := by
        calc δ * (((k : ℝ) + 1) / ((d : ℝ) + 2))
            < δ * 1 := mul_lt_mul_of_pos_left h2 hδpos
          _ = δ := mul_one _
      linarith
    · simp only [t]
      have : 0 < δ * (((k : ℝ) + 1) / ((d : ℝ) + 2)) :=
        mul_pos hδpos h1
      linarith
  have htinj : Function.Injective t := by
    intro k l h
    simp only [t] at h
    have hsub : δ * (((k : ℝ) + 1) / ((d : ℝ) + 2)) =
        δ * (((l : ℝ) + 1) / ((d : ℝ) + 2)) := by
      have h' : last - δ * (((k : ℝ) + 1) / ((d : ℝ) + 2)) =
          last - δ * (((l : ℝ) + 1) / ((d : ℝ) + 2)) := h
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
  let F : Finset ℝ := Finset.image M.b Finset.univ
  have hFcard : F.card ≤ d := by
    calc F.card ≤ Finset.univ.card := Finset.card_image_le
      _ = d := by rw [Finset.card_univ, Fintype.card_fin]
  have hnotsub : ¬ S ⊆ F := by
    intro hsub
    have hle := Finset.card_le_card hsub
    omega
  rw [Finset.not_subset] at hnotsub
  obtain ⟨τ, hτS, hτnot⟩ := hnotsub
  rw [Finset.mem_image] at hτS
  obtain ⟨k, hkrange, rfl⟩ := hτS
  have hk_le : k ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hkrange)
  have hIoo := hmem_of_le k hk_le
  have hτpos : 0 < t k := by
    have hge : last / 2 ≤ last - δ := by linarith
    have hpos2 : 0 < last / 2 := by linarith
    linarith
  have hτlt : t k < last := hIoo.2
  have hgap_lt : last - t k < δ := by linarith
  have h2d : (0 : ℝ) < 2 * (d : ℝ) := by positivity
  have hbound : 2 * (d : ℝ) * (last - t k) < c / 2 := by
    have hdne' : (d : ℝ) ≠ 0 := ne_of_gt hdpos
    calc 2 * (d : ℝ) * (last - t k) < 2 * (d : ℝ) * δ :=
          mul_lt_mul_of_pos_left hgap_lt h2d
      _ ≤ 2 * (d : ℝ) * (c / (8 * (d : ℝ))) :=
          mul_le_mul_of_nonneg_left hδ2 h2d.le
      _ = c / 4 := by field_simp; ring
      _ < c / 2 := by linarith
  refine ⟨t k, hτpos, hτlt, ?_, hbound⟩
  intro a ha
  apply hτnot
  show t k ∈ F
  unfold F
  rw [Finset.mem_image]
  exact ⟨a, Finset.mem_univ a, ha⟩

/-- Cover the off-diagonal graph by d coordinate charts and retain one
chart with at least a 1/d fraction of the original physical pairs. -/
theorem exists_dense_common_chart (hd : 1 ≤ d)
    (Γ : Finset (RPoint d × RPoint d)) (hneq : ∀ pq ∈ Γ, pq.1 ≠ pq.2) :
    ∃ i₀ : Fin d, ∃ Γ' : Finset (RPoint d × RPoint d), Γ' ⊆ Γ ∧
      (∀ pq ∈ Γ', (TrackD.toC pq.2 - TrackD.toC pq.1) i₀ ≠ 0) ∧
      (Γ.card : ℝ) / (d : ℝ) ≤ Γ'.card := by
  classical
  have hdpos_nat : 0 < d := by omega
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos_nat
  have htoC_inj : Function.Injective (TrackD.toC (d := d)) :=
    profile_toC_injective
  -- charts cover Γ
  have hcover : ∀ pq ∈ Γ, ∃ i₀ : Fin d,
      (TrackD.toC pq.2 - TrackD.toC pq.1) i₀ ≠ 0 := by
    intro pq hpq
    have hne : pq.1 ≠ pq.2 := hneq pq hpq
    have htoCne : TrackD.toC pq.1 ≠ TrackD.toC pq.2 :=
      fun h => hne (htoC_inj h)
    obtain ⟨i, hi⟩ := Function.ne_iff.mp htoCne
    have hne' : TrackD.toC pq.2 i ≠ TrackD.toC pq.1 i :=
      fun heq => hi heq.symm
    exact ⟨i, by simpa [Pi.sub_apply] using sub_ne_zero.mpr hne'⟩
  let F : Fin d → Finset (RPoint d × RPoint d) :=
    fun i₀ => Γ.filter (fun pq => (TrackD.toC pq.2 - TrackD.toC pq.1) i₀ ≠ 0)
  have hsub : Γ ⊆ Finset.univ.biUnion F := by
    intro pq hpq
    rw [Finset.mem_biUnion]
    obtain ⟨i₀, hi₀⟩ := hcover pq hpq
    exact ⟨i₀, Finset.mem_univ i₀, Finset.mem_filter.mpr ⟨hpq, hi₀⟩⟩
  have hcard_le : Γ.card ≤ ∑ i₀ ∈ Finset.univ, (F i₀).card := by
    calc Γ.card ≤ (Finset.univ.biUnion F).card := Finset.card_le_card hsub
      _ ≤ ∑ i₀ ∈ Finset.univ, (F i₀).card :=
          Finset.card_biUnion_le
  have hcast : (Γ.card : ℝ) ≤ ∑ i₀ ∈ Finset.univ, ((F i₀).card : ℝ) := by
    calc (Γ.card : ℝ) ≤ (((∑ i₀ ∈ Finset.univ, (F i₀).card : ℕ)) : ℝ) := by
            exact_mod_cast hcard_le
      _ = ∑ i₀ ∈ Finset.univ, ((F i₀).card : ℝ) := by
            rw [Nat.cast_sum]
  by_contra hnone
  rw [not_exists] at hnone
  have hlt : ∀ i₀ : Fin d, ((F i₀).card : ℝ) < (Γ.card : ℝ) / (d : ℝ) := by
    intro i₀
    by_contra hge
    rw [not_lt] at hge
    have hsubF : F i₀ ⊆ Γ := Finset.filter_subset _ _
    have hchartF : ∀ pq ∈ F i₀,
        (TrackD.toC pq.2 - TrackD.toC pq.1) i₀ ≠ 0 := by
      intro pq hpq
      exact (Finset.mem_filter.mp hpq).2
    exact hnone i₀ ⟨F i₀, hsubF, hchartF, hge⟩
  have hsum_lt : ∑ i₀ ∈ Finset.univ, ((F i₀).card : ℝ) < (Γ.card : ℝ) := by
    calc ∑ i₀ ∈ Finset.univ, ((F i₀).card : ℝ)
        < ∑ _i₀ ∈ Finset.univ, ((Γ.card : ℝ) / (d : ℝ)) :=
          Finset.sum_lt_sum (fun i₀ _ => (hlt i₀).le)
            (by
              obtain ⟨i₀⟩ : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
              exact ⟨i₀, Finset.mem_univ i₀, hlt i₀⟩)
      _ = (Γ.card : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
  linarith

/-- Per-row label rank is bounded by the homogeneous row rank.
Substitution of the constant source coordinate and homogenization in the
chart direction preserve vanishing up to the nonzero chart scaling. -/
theorem commonLabelRank_row_le (i₀ : Fin d) (p : RPoint d)
    (Γp : Finset (RPoint d × RPoint d))
    (hfirst : ∀ pq ∈ Γp, pq.1 = p)
    (hchart : ∀ pq ∈ Γp, (TrackD.toC pq.2 - TrackD.toC pq.1) i₀ ≠ 0)
    (L : ℕ) :
    restrictionRank ((fun pq : RPoint d × RPoint d =>
      TrackD.labelPt i₀ (TrackD.toC pq.1) (TrackD.toC pq.2)) '' (↑Γp : Set (RPoint d × RPoint d))) L ≤
    rowDirectionRank (TrackD.toC p)
      (Γp.image Prod.snd) L := by
  classical
  -- Fixed source and chart data.
  let Xp : Fin d → ℂ := TrackD.toC p
  -- Substitution of source constants: 2d vars -> d vars.
  let e : Fin d ⊕ Fin d → MvPolynomial (Fin d) ℂ :=
    fun i => match i with
      | Sum.inl k => MvPolynomial.C (Xp k)
      | Sum.inr k => MvPolynomial.X k
  let phi' : MvPolynomial (Fin d ⊕ Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ :=
    (MvPolynomial.aeval e).toLinearMap
  -- Homogenization to exact degree L via X_i₀ powers (explicit to keep sums in polynomial form).
  let etaFun : MvPolynomial (Fin d) ℂ → MvPolynomial (Fin d) ℂ :=
    fun G => ∑ j ∈ Finset.range (L + 1),
      (MvPolynomial.homogeneousComponent j G * MvPolynomial.X i₀ ^ (L - j))
  have heta_add : ∀ G1 G2 : MvPolynomial (Fin d) ℂ,
      etaFun (G1 + G2) = etaFun G1 + etaFun G2 := by
    intro G1 G2
    simp only [etaFun, map_add, add_mul, Finset.sum_add_distrib]
  have heta_smul : ∀ (c : ℂ) (G : MvPolynomial (Fin d) ℂ),
      etaFun (c • G) = c • etaFun G := by
    intro c G
    simp only [etaFun, map_smul, smul_mul_assoc, Finset.smul_sum]
  let eta' : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ :=
    { toFun := etaFun, map_add' := heta_add, map_smul' := heta_smul }
  let psi' : MvPolynomial (Fin d ⊕ Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ :=
    eta'.comp phi'
  -- Substitution does not increase total degree (each target has degree ≤ 1).
  have he_deg : ∀ i : Fin d ⊕ Fin d, (e i).totalDegree ≤ 1 := by
    intro i
    cases i with
    | inl k => simp [e, MvPolynomial.totalDegree_C]
    | inr k => simp [e, MvPolynomial.totalDegree_X]
  have hphi_deg : ∀ F : MvPolynomial (Fin d ⊕ Fin d) ℂ,
      (phi' F).totalDegree ≤ F.totalDegree := by
    intro F
    -- Same argument as OAI totalDegree_aeval_le_of_linear.
    conv_lhs => rw [show phi' F = MvPolynomial.aeval e F from rfl]
    conv_lhs => rw [F.as_sum]
    rw [map_sum]
    apply MvPolynomial.totalDegree_finsetSum_le
    intro m hm
    rw [MvPolynomial.aeval_monomial]
    have hmul := MvPolynomial.totalDegree_mul (MvPolynomial.C (F.coeff m))
      (m.prod fun i k => e i ^ k)
    simp only [MvPolynomial.totalDegree_C, zero_add] at hmul
    apply hmul.trans
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
    apply le_trans _ (MvPolynomial.le_totalDegree hm)
    apply Finset.sum_le_sum
    intro i _
    simpa only [Nat.mul_one] using
      (MvPolynomial.totalDegree_pow (e i) (m i)).trans
        (Nat.mul_le_mul_left (m i) (he_deg i))
  -- Homogenization lands in exact degree L.
  have heta_hom : ∀ G : MvPolynomial (Fin d) ℂ,
      (eta' G).IsHomogeneous L := by
    intro G
    show etaFun G |>.IsHomogeneous L
    unfold etaFun
    apply MvPolynomial.IsHomogeneous.sum
    intro j hj
    have hjL : j ≤ L := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have h1 : (MvPolynomial.homogeneousComponent j G).IsHomogeneous j :=
      MvPolynomial.homogeneousComponent_isHomogeneous j G
    have h2 : (MvPolynomial.X i₀ ^ (L - j) : MvPolynomial (Fin d) ℂ).IsHomogeneous (L - j) := by
      have hX : (MvPolynomial.X i₀ : MvPolynomial (Fin d) ℂ).IsHomogeneous 1 :=
        MvPolynomial.isHomogeneous_X ℂ i₀
      have := hX.pow (L - j)
      simpa using this
    have hmul := h1.mul h2
    have heq : j + (L - j) = L := Nat.add_sub_of_le hjL
    rwa [heq] at hmul
  -- Homogeneous scaling of evaluation.
  have hhom_smul : ∀ (H : MvPolynomial (Fin d) ℂ) (j : ℕ),
      H.IsHomogeneous j → ∀ (c : ℂ) (u : Fin d → ℂ),
        MvPolynomial.aeval (c • u) H = c ^ j * MvPolynomial.aeval u H := by
    intro H j hH c u
    conv_lhs => rw [H.as_sum]
    rw [map_sum]
    conv_rhs => rw [H.as_sum]
    rw [map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    have hdeg : m.degree = j := by
      have h := hH (Finsupp.mem_support_iff.mp hm)
      have h' : Finsupp.weight (fun _ : Fin d => (1 : ℕ)) m = j := by
        simpa only [Pi.one_def] using h
      rw [← Finsupp.degree_eq_weight_one] at h'
      exact h'
    have hsmul : ∀ i : Fin d, (c • u) i = c * u i := fun i => by
      simp [Pi.smul_apply, smul_eq_mul]
    have hprod : m.prod (fun i k => (c • u) i ^ k) =
        c ^ j * m.prod (fun i k => u i ^ k) := by
      simp_rw [hsmul]
      show (∏ i ∈ m.support, (c * u i) ^ m i) = c ^ j * ∏ i ∈ m.support, u i ^ m i
      calc (∏ i ∈ m.support, (c * u i) ^ m i) =
          ∏ i ∈ m.support, c ^ m i * u i ^ m i := by
            apply Finset.prod_congr rfl
            intro i hi
            rw [mul_pow]
        _ = (∏ i ∈ m.support, c ^ m i) * ∏ i ∈ m.support, u i ^ m i := by
            rw [Finset.prod_mul_distrib]
        _ = c ^ j * ∏ i ∈ m.support, u i ^ m i := by
            rw [Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_apply, hdeg]
    simp only [MvPolynomial.aeval_monomial, map_mul,
      MvPolynomial.aeval_C]
    rw [hprod]
    ring
  -- Substitution evaluation: (aeval e F) at u equals F at (Xp, u).
  -- Both sides are AlgHoms in F, so check on generators.
  have hsubst : ∀ (F : MvPolynomial (Fin d ⊕ Fin d) ℂ) (u : Fin d → ℂ),
      MvPolynomial.aeval u (phi' F) =
        MvPolynomial.aeval (Sum.elim Xp u) F := by
    intro F u
    have hhom : (MvPolynomial.aeval u).comp (MvPolynomial.aeval e) =
        MvPolynomial.aeval (Sum.elim Xp u) := by
      apply MvPolynomial.algHom_ext
      intro i
      simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]
      have heq : MvPolynomial.aeval u (e i) = Sum.elim Xp u i := by
        cases i with
        | inl k =>
            simp [e, Sum.elim_inl, Xp]
        | inr k =>
            simp [e, MvPolynomial.aeval_X, Sum.elim_inr]
      exact heq
    calc MvPolynomial.aeval u (phi' F)
        = ((MvPolynomial.aeval u).comp (MvPolynomial.aeval e)) F := by
          simp [phi']
      _ = MvPolynomial.aeval (Sum.elim Xp u) F := by rw [hhom]
  -- Homogenization evaluation scaling.
  have hhom_eval : ∀ (G : MvPolynomial (Fin d) ℂ),
      G.totalDegree ≤ L → ∀ (c₀ : ℂ) (u v : Fin d → ℂ),
        v = c₀ • u → u i₀ = 1 →
        MvPolynomial.aeval v (eta' G) = c₀ ^ L * MvPolynomial.aeval u G := by
    intro G hG c₀ u v hv hu
    have hv0 : v i₀ = c₀ := by
      rw [hv]
      simp [Pi.smul_apply, smul_eq_mul, hu]
    show MvPolynomial.aeval v (etaFun G) = _ 
    unfold etaFun
    rw [map_sum]
    have hterm : ∀ j ∈ Finset.range (L + 1),
        MvPolynomial.aeval v
          (MvPolynomial.homogeneousComponent j G * MvPolynomial.X i₀ ^ (L - j)) =
        c₀ ^ L * MvPolynomial.aeval u (MvPolynomial.homogeneousComponent j G) := by
      intro j hj
      have hjL : j ≤ L := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      rw [map_mul, map_pow, MvPolynomial.aeval_X]
      rw [hv]
      rw [hhom_smul _ j (MvPolynomial.homogeneousComponent_isHomogeneous j G) c₀ u]
      have hv0' : ((c₀ • u) i₀) = c₀ := by
        simp [Pi.smul_apply, smul_eq_mul, hu]
      rw [hv0']
      have hpow : c₀ ^ j * c₀ ^ (L - j) = c₀ ^ L := by
        rw [← pow_add]
        congr 1
        exact Nat.add_sub_of_le hjL
      calc c₀ ^ j * MvPolynomial.aeval u ((MvPolynomial.homogeneousComponent j) G) * c₀ ^ (L - j)
          = (c₀ ^ j * c₀ ^ (L - j)) * MvPolynomial.aeval u ((MvPolynomial.homogeneousComponent j) G) := by
            ring
        _ = c₀ ^ L * MvPolynomial.aeval u ((MvPolynomial.homogeneousComponent j) G) := by
            rw [hpow]
    rw [Finset.sum_congr rfl (fun j hj => hterm j hj)]
    rw [← Finset.mul_sum]
    congr 1
    -- ∑ hc_j(u) = G(u) since G has degree ≤ L.
    have hsum : ∑ j ∈ Finset.range (L + 1),
        MvPolynomial.aeval u (MvPolynomial.homogeneousComponent j G) =
        MvPolynomial.aeval u G := by
      conv_rhs => rw [← MvPolynomial.sum_homogeneousComponent G]
      rw [map_sum]
      symm
      apply Finset.sum_subset
      · -- range (deg+1) ⊆ range (L+1) since deg ≤ L.
        apply Finset.range_mono
        omega
      · intro j hj1 hj2
        -- j ∈ range(L+1), j ∉ range(deg+1) → deg < j → hc_j = 0.
        have hjdeg : G.totalDegree < j := by
          have h1 : ¬ (j < G.totalDegree + 1) := by
            simpa [Finset.mem_range] using hj2
          omega
        rw [MvPolynomial.homogeneousComponent_eq_zero j G hjdeg]
        simp
    exact hsum
  -- Combined scaling: psi'(F) at v equals c₀^L times F at the label.
  -- For F in V1 (degree ≤ L), G = phi'(F) has degree ≤ L, so hhom_eval applies.
  have hscale : ∀ (F : MvPolynomial (Fin d ⊕ Fin d) ℂ),
      F.totalDegree ≤ L → ∀ pq ∈ Γp,
        let y := TrackD.toC pq.2
        let v : Fin d → ℂ := y - Xp
        let c₀ : ℂ := v i₀
        MvPolynomial.aeval v (psi' F) =
          c₀ ^ L * MvPolynomial.aeval
            (TrackD.labelPt i₀ Xp y) F := by
    intro F hF pq hpq
    have hp1 : pq.1 = p := hfirst pq hpq
    have hXp : TrackD.toC pq.1 = Xp := by rw [hp1]
    have hchartpq := hchart pq hpq
    rw [hXp] at hchartpq
    -- v, c₀, u as above; u normalized with i₀ = 1.
    set y : Fin d → ℂ := TrackD.toC pq.2 with hy
    set v : Fin d → ℂ := y - Xp with hv
    have hc₀ : v i₀ ≠ 0 := hchartpq
    set c₀ : ℂ := v i₀ with hc₀def
    have hc₀ne : c₀ ≠ 0 := hc₀
    set u : Fin d → ℂ := c₀⁻¹ • v with hugeo
    have hu0 : u i₀ = 1 := by
      simp only [hugeo, Pi.smul_apply, smul_eq_mul, hc₀def]
      exact inv_mul_cancel₀ hc₀
    have hv_eq : v = c₀ • u := by
      rw [hugeo]
      simp only [smul_smul]
      have : c₀ * c₀⁻¹ = 1 := mul_inv_cancel₀ hc₀ne
      simp only [this, one_smul]
    -- G has degree ≤ L.
    have hGdeg : (phi' F).totalDegree ≤ L :=
      (hphi_deg F).trans hF
    have hG : phi' F = phi' F := rfl
    -- eta eval scaling via hhom_eval.
    have heta := hhom_eval (phi' F) hGdeg c₀ u v hv_eq hu0
    -- phi eval via hsubst: G(u) = F(label), where label = Sum.elim Xp u.
    have hsub := hsubst F u
    -- Identify labelPt with Sum.elim.
    have hlabel : TrackD.labelPt i₀ Xp y = Sum.elim Xp u := rfl
    calc MvPolynomial.aeval v (psi' F)
        = MvPolynomial.aeval v (eta' (phi' F)) := rfl
      _ = c₀ ^ L * MvPolynomial.aeval u (phi' F) := heta
      _ = c₀ ^ L * MvPolynomial.aeval (Sum.elim Xp u) F := by rw [hsub]
      _ = c₀ ^ L * MvPolynomial.aeval (TrackD.labelPt i₀ Xp y) F := by rw [hlabel]
  -- Submodules and evaluation maps for the rank comparison.
  -- V1: degree ≤ L in pair vars; H: homogeneous degree L in direction vars.
  let V1sub : Submodule ℂ (MvPolynomial (Fin d ⊕ Fin d) ℂ) :=
    MvPolynomial.restrictTotalDegree (Fin d ⊕ Fin d) ℂ L
  let Hsub : Submodule ℂ (MvPolynomial (Fin d) ℂ) :=
    MvPolynomial.homogeneousSubmodule (Fin d) ℂ L
  -- Label set and partner set for this row.
  let TpSet : Set (Fin d ⊕ Fin d → ℂ) :=
    (fun pq : RPoint d × RPoint d =>
      TrackD.labelPt i₀ (TrackD.toC pq.1) (TrackD.toC pq.2)) '' (↑Γp : Set (RPoint d × RPoint d))
  let Q : Finset (RPoint d) := Γp.image Prod.snd
  -- A: label restriction; B: homogeneous evaluation at difference reps.
  let A : ↥V1sub →ₗ[ℂ] (TpSet → ℂ) :=
    DistinctDistances.restrictionMap TpSet L
  -- B needs reps v_q = toC q - Xp for q ∈ Q.
  -- For q : ↥Q, q.val ∈ Q, so q.val = pq.2 for some pq ∈ Γp with pq.1 = p.
  -- v_q is well-defined from q (depends only on q, not the witness pq).
  let Brep : ↥Q → (Fin d → ℂ) := fun q => TrackD.toC (q.val) - Xp
  let B : ↥Hsub →ₗ[ℂ] (↥Q → ℂ) :=
    { toFun := fun H q => MvPolynomial.aeval (Brep q) (H.val),
      map_add' := by intro x y; funext q; simp [map_add],
      map_smul' := by intro c x; funext q; simp [map_smul] }
  -- psi restricted to V1 -> H (lands in H by heta_hom for all inputs).
  have hpsi_mem : ∀ F : ↥V1sub, (psi' (F.val)) ∈ Hsub := by
    intro F
    simp only [Hsub]
    rw [MvPolynomial.mem_homogeneousSubmodule]
    exact heta_hom (phi' (F.val))
  let psiSub : ↥V1sub →ₗ[ℂ] ↥Hsub :=
    LinearMap.codRestrict Hsub (psi'.comp V1sub.subtype) hpsi_mem
  -- Kernel inclusion: vanishing of homogenized evaluations implies vanishing of labels.
  have hker : LinearMap.ker (B.comp psiSub) ≤ LinearMap.ker A := by
    intro F hF
    have hB0 : ∀ q : ↥Q, B (psiSub F) q = 0 := by
      have h0 : (B.comp psiSub) F = 0 := LinearMap.mem_ker.mp hF
      intro q
      have h0q := congrFun h0 q
      simpa [LinearMap.comp_apply] using h0q
    rw [LinearMap.mem_ker]
    funext ℓ
    rcases ℓ with ⟨ℓval, hℓ⟩
    simp only [TpSet] at hℓ
    rcases hℓ with ⟨pq, hpq, rfl⟩
    have hpqF : pq ∈ Γp := Finset.mem_coe.mp hpq
    have hp1 : pq.1 = p := hfirst pq hpqF
    have hqQ : pq.2 ∈ Q := Finset.mem_image.mpr ⟨pq, hpqF, rfl⟩
    let q : ↥Q := ⟨pq.2, hqQ⟩
    have hBq : B (psiSub F) q = 0 := hB0 q
    have hFdeg : (F.val).totalDegree ≤ L := by
      have hmem : F.val ∈ V1sub := F.property
      rwa [MvPolynomial.mem_restrictTotalDegree] at hmem
    have hsc := hscale (F.val) hFdeg pq hpqF
    have hchartpq := hchart pq hpqF
    have hXp : TrackD.toC pq.1 = Xp := by rw [hp1]
    rw [hXp] at hchartpq
    have hc₀ne : ((TrackD.toC pq.2 - Xp) i₀) ≠ 0 := hchartpq
    have hpowne : ((TrackD.toC pq.2 - Xp) i₀) ^ L ≠ 0 :=
      pow_ne_zero L hc₀ne
    have hBq_aeval : MvPolynomial.aeval (TrackD.toC (q.val) - Xp) (psi' (F.val)) = 0 := hBq
    have heq : MvPolynomial.aeval (TrackD.toC pq.2 - Xp) (psi' (F.val)) =
        ((TrackD.toC pq.2 - Xp) i₀) ^ L *
          MvPolynomial.aeval
            (TrackD.labelPt i₀ (TrackD.toC pq.1) (TrackD.toC pq.2)) (F.val) := by
      have hsc' := hsc
      rw [← hXp] at hsc' ⊢
      exact hsc'
    have hqq : TrackD.toC (q.val) - Xp = TrackD.toC pq.2 - Xp := rfl
    rw [hqq, heq] at hBq_aeval
    show (A F) ⟨TrackD.labelPt i₀ (TrackD.toC pq.1) (TrackD.toC pq.2),
      Set.mem_image_of_mem _ hpq⟩ = 0
    have hA_aeval : (A F) ⟨TrackD.labelPt i₀ (TrackD.toC pq.1) (TrackD.toC pq.2),
        Set.mem_image_of_mem _ hpq⟩ =
        MvPolynomial.aeval (TrackD.labelPt i₀ (TrackD.toC pq.1) (TrackD.toC pq.2)) (F.val) := rfl
    rcases mul_eq_zero.mp hBq_aeval with hzero | hzero
    · exact absurd hzero hpowne
    · have hgoal : MvPolynomial.aeval
          (TrackD.labelPt i₀ (TrackD.toC pq.1) (TrackD.toC pq.2)) (F.val) = 0 := hzero
      show MvPolynomial.aeval _ (F.val) = 0
      exact hgoal
  -- Finite-rank comparison via kernels (V1 is finite-dimensional).
  have hrank1 : Module.finrank ℂ ↥(LinearMap.range A) ≤
      Module.finrank ℂ ↥(LinearMap.range (B.comp psiSub)) := by
    have hAker := (B.comp psiSub).finrank_range_add_finrank_ker
    have hBker := A.finrank_range_add_finrank_ker
    have hmono : Module.finrank ℂ ↥(LinearMap.ker (B.comp psiSub)) ≤
        Module.finrank ℂ ↥(LinearMap.ker A) := by
      apply Submodule.finrank_mono hker
    omega
  -- Image of composition is contained in image of B.
  have hrank2 : Module.finrank ℂ ↥(LinearMap.range (B.comp psiSub)) ≤
      Module.finrank ℂ ↥(LinearMap.range B) := by
    have hsub : LinearMap.range (B.comp psiSub) ≤ LinearMap.range B := by
      intro y hy
      rcases hy with ⟨F, rfl⟩
      exact ⟨psiSub F, rfl⟩
    exact Submodule.finrank_mono hsub
  -- Projective closure of this row's directions and its quotient map.
  let RDirs : Set (ProjectivePoint d) := rowDirections Xp Q
  let Clos : ProjectiveVariety d := ProjectiveVariety.closure RDirs
  -- Qmap: Homog -> restrictionSpace (image of Homog under quotient).
  have hQmem : ∀ H : ↥Hsub,
      (Ideal.Quotient.mkₐ ℂ Clos.ideal).toLinearMap (H.val) ∈
        Clos.restrictionSpace L := by
    intro H
    simp only [ProjectiveVariety.restrictionSpace]
    -- quotientSection = Homog.map quotient.mk, so mem via H.val ∈ Homog.
    apply Submodule.mem_map.mpr
    exact ⟨H.val, H.property, rfl⟩
  let Qmap : ↥Hsub →ₗ[ℂ] ↥(Clos.restrictionSpace L) :=
    LinearMap.codRestrict (Clos.restrictionSpace L)
      ((Ideal.Quotient.mkₐ ℂ Clos.ideal).toLinearMap.comp Hsub.subtype) hQmem
  -- Kernel of Qmap is contained in kernel of B (ideal vanishes on reps).
  have hkerQ : LinearMap.ker Qmap ≤ LinearMap.ker B := by
    intro H hH
    -- H : ↥Hsub, hH : Qmap H = 0, i.e., quotient.mk(H.val) = 0, so H.val ∈ ideal.
    -- Need B H = 0, i.e., ∀ q ∈ Q, aeval (rep_q) H.val = 0.
    have hmem : (H.val) ∈ Clos.ideal := by
      have h0 : Qmap H = 0 := LinearMap.mem_ker.mp hH
      have h0q : (Ideal.Quotient.mkₐ ℂ Clos.ideal).toLinearMap (H.val) = 0 :=
        congrArg Subtype.val h0
      have h0mk : (Ideal.Quotient.mk Clos.ideal) (H.val) = 0 := h0q
      rwa [Ideal.Quotient.eq_zero_iff_mem] at h0mk
    -- Clos.ideal is the vanishing ideal of RDirs by definition of closure.
    have hvan : H.val ∈ ProjectiveVariety.vanishingIdeal RDirs := hmem
    rw [LinearMap.mem_ker]
    funext q
    -- q : ↥Q, need B H q = aeval (Brep q) H.val = 0 via vanishing on rep.
    show MvPolynomial.aeval (Brep q) (H.val) = 0
    have hqQ : q.val ∈ Q := q.property
    -- Obtain witness pq ∈ Γp with pq.2 = q.val.
    rcases Finset.mem_image.mp hqQ with ⟨pq, hpqF, hq⟩
    -- hpqF : pq ∈ Γp, hq : Prod.snd pq = q.val, i.e., pq.2 = q.val.
    have hp1 : pq.1 = p := hfirst pq hpqF
    have hchartpq := hchart pq hpqF
    have hXp : TrackD.toC pq.1 = Xp := by rw [hp1]
    rw [hXp] at hchartpq
    -- Brep q = toC q.val - Xp = toC pq.2 - Xp (since q.val = pq.2).
    have hqeq : q.val = pq.2 := by simpa using hq.symm
    -- Actually hq : Prod.snd pq = q.val, so q.val = pq.2? hq : pq.2 = q.val? From mem_image: ⟨pq, hpqF, rfl⟩? The rfl is `Prod.snd pq = q.val`? Since image with Prod.snd, mem_image gives ∃ pq, pq∈Γp ∧ Prod.snd pq = q.val. Our pattern ⟨pq, hpqF, hq⟩ where hq : Prod.snd pq = q.val. Good. So q.val = pq.2? Since Prod.snd pq = pq.2 definitionally? `Prod.snd (a,b) = b` rfl. Good. So hq : pq.2 = q.val. Then q.val = pq.2 via symm. Good.
    have hq2 : q.val = pq.2 := hq.symm
    -- v = Brep q is nonzero (chart coordinate nonzero) and represents a row direction.
    have hrep_ne : Brep q ≠ 0 := by
      intro h0
      have h0i : (Brep q) i₀ = 0 := by rw [h0]; rfl
      -- Brep q = toC q.val - Xp = toC pq.2 - Xp (via hq2), whose i₀ ≠ 0 by hchartpq.
      have hchart' : (TrackD.toC (q.val) - Xp) i₀ ≠ 0 := by
        rw [hq2]
        exact hchartpq
      -- Brep q unfolds to toC q.val - Xp (by definition Brep, defeq), so contradiction.
      exact hchart' h0i
    have hdir_mem : Projectivization.mk ℂ (Brep q) hrep_ne ∈ RDirs := by
      show Projectivization.mk ℂ (Brep q) hrep_ne ∈ rowDirections Xp Q
      unfold rowDirections
      simp only [Set.mem_setOf_eq]
      refine ⟨q.val, hqQ, ?_, ?_⟩
      · -- toC q.val ≠ Xp (since difference nonzero).
        intro hcontra
        apply hrep_ne
        show TrackD.toC (q.val) - Xp = 0
        rw [hcontra]
        simp
      · -- radialProjection = mk (toC q - Xp) = mk (Brep q) (same rep, proof irrelevance).
        unfold DistinctDistances.radialProjection
        rfl
    have hrep_mem : Brep q ∈ ProjectiveVariety.nonzeroRepresentatives RDirs := by
      exact ⟨hrep_ne, hdir_mem⟩
    -- VanishingIdeal mem gives aeval = 0.
    have hvan_aff : H.val ∈ MvPolynomial.vanishingIdeal ℂ
        (ProjectiveVariety.nonzeroRepresentatives RDirs) := by
      -- vanishingIdeal RDirs unfolds to affine vanishingIdeal of nonzeroReps (by definition).
      -- hvan : H.val ∈ vanishingIdeal RDirs, which is defined as that. So defeq, exact.
      exact hvan
    exact (MvPolynomial.mem_vanishingIdeal_iff.mp hvan_aff) _ hrep_mem
  -- Qmap is surjective onto the restriction space (by definition as an image).
  have hQsurj : Function.Surjective Qmap := by
    intro s
    -- s ∈ restrictionSpace = Homog.map quotient.mk, so obtain preimage in Homog.
    have hmem : s.val ∈ Clos.restrictionSpace L := s.property
    simp only [ProjectiveVariety.restrictionSpace] at hmem
    -- OAI quotientSection uses mkₐ; our Qmap uses mkₐ, same. mem_map gives preimage.
    rcases Submodule.mem_map.mp hmem with ⟨H, hH, hs⟩
    -- H ∈ Homog (as MvPolynomial, with proof hH : H ∈ homogeneousSubmodule).
    -- Need H : ↥Hsub (subtype with proof), then Qmap H = s (as subtype elements? Need val equality + proof irrelevance? Since both in restrictionSpace, equality as subtypes follows from val equality (proofs irrelevant? Actually subtype equality needs val equality, proofs automatic via proof irrelevance? Since restrictionSpace membership is Prop, any two proofs equal? For Subtype equality, `Subtype.ext` needs val equality. Good.)
    refine ⟨⟨H, hH⟩, ?_⟩
    apply Subtype.ext
    show ((Ideal.Quotient.mkₐ ℂ Clos.ideal).toLinearMap.comp Hsub.subtype) ⟨H, hH⟩ = s.val
    simp only [LinearMap.comp_apply, Submodule.coe_subtype]
    -- LHS = quotient.mkₐ(H), RHS s.val = quotient.mkₐ(H) via hs (hs : quotient.mkₐ(H) = s.val? From mem_map: hs : ... = s.val? Actually mem_map gives ⟨H, hH, hs⟩ where hs : ... = s.val? Let's see: mem_map for `Homog.map f` with f = quotient.mkₐ.toLinearMap: s.val ∈ map ↔ ∃ H ∈ Homog, f(H) = s.val. So hs : f(H) = s.val. Good. So LHS = f(H) = s.val via hs. Good.)
    exact hs
  -- Lift B through Qmap to the restriction space (kernel inclusion).
  -- Qmap surjective, so range(B) is image of restrictionSpace, giving finrank bound.
  have hQrange : LinearMap.range Qmap = ⊤ := by
    rw [LinearMap.range_eq_top.mpr hQsurj]
  let Qquot := Hsub ⧸ LinearMap.ker Qmap
  let Blift : Qquot →ₗ[ℂ] (↥Q → ℂ) :=
    Submodule.liftQ (LinearMap.ker Qmap) B hkerQ
  -- range(B) = range(Blift ∘ mkQ)? Actually B = Blift ∘ mkQ via liftQ property.
  have hBlift_eq : ∀ H : ↥Hsub, Blift (Submodule.mkQ _ H) = B H := by
    intro H
    rfl
  -- range(B) ⊆ Blift.map ⊤? Actually range(B) = Blift.map ⊤? Since mkQ surjective onto Qquot?
  -- mkQ (quotient.mk) is surjective (Quotient.mk surjective). Good.
  -- So range(B) = Blift.range (since B = Blift∘mkQ and mkQ surjective).
  have hrange_eq : LinearMap.range B = LinearMap.range Blift := by
    apply le_antisymm
    · intro y hy
      rcases hy with ⟨H, rfl⟩
      exact ⟨Submodule.mkQ _ H, hBlift_eq H⟩
    · intro y hy
      rcases hy with ⟨q, rfl⟩
      obtain ⟨H, rfl⟩ := Submodule.mkQ_surjective _ q
      exact ⟨H, (hBlift_eq H).symm⟩
  -- Iso: Qquot ≃ range(Qmap) = ⊤ ≃ restrictionSpace (via quotKerEquivRange + top).
  -- For finrank, suffices: finrank(Qquot) = finrank(restrictionSpace) = hilbert.
  -- Since Qmap surjective with kernel K, H/K ≅ image = top.
  -- Use LinearMap.quotKerEquivRange : H ⧸ ker(f) ≃ range(f).
  let iso1 : Qquot ≃ₗ[ℂ] ↥(LinearMap.range Qmap) :=
    LinearMap.quotKerEquivRange Qmap
  have hrange_top : LinearMap.range Qmap = ⊤ := hQrange
  -- Transport finrank via iso1 + top (range = top as submodule of restrictionSpace).
  -- finrank(Qquot) = finrank(range Qmap) = finrank(⊤) = finrank(restrictionSpace).
  have hfin_Qquot : Module.finrank ℂ Qquot =
      Module.finrank ℂ ↥(Clos.restrictionSpace L) := by
    have h1 : Module.finrank ℂ Qquot = Module.finrank ℂ ↥(LinearMap.range Qmap) :=
      LinearEquiv.finrank_eq iso1
    rw [h1, hrange_top]
    exact LinearEquiv.finrank_eq Submodule.topEquiv
  -- Final chain: restrictionRank(Tp) = rank(A) ≤ rank(B∘ψ) ≤ rank(B) = rank(Blift) ≤ finrank(Qquot) = hilbert = rowDirectionRank.
  -- rank(A) = finrank(range A), etc. We have hrank1 (A ≤ B∘ψ), hrank2 (B∘ψ ≤ B).
  -- Need rank(B) ≤ finrank(Qquot) (= hilbert) via Blift: range(B) = range(Blift)? Actually range(B) = range(Blift)? From hrange_eq (range B = range Blift, where Blift : Qquot → P). Good. Then finrank(range Blift) ≤ finrank(Qquot) via LinearMap.finrank_range_le? Or Submodule.finrank_map_le? Since range(Blift) = Blift.map ⊤? Actually range = map top. Then finrank(map) ≤ finrank(domain)? Via `Submodule.finrank_map_le`? Need domain Qquot finite? Qquot finrank = hilbert finite (via hfin_Qquot + restrictionSpace finite instance). Good. So finrank(range Blift) ≤ finrank(Qquot). Good.
  haveI : Module.Finite ℂ Qquot := by
    have htop : ↥(LinearMap.range Qmap) ≃ₗ[ℂ] ↥(Clos.restrictionSpace L) := by
      have heq : LinearMap.range Qmap = ⊤ := hrange_top
      rw [heq]
      exact Submodule.topEquiv
    have hiso : Qquot ≃ₗ[ℂ] ↥(Clos.restrictionSpace L) := iso1.trans htop
    exact Module.Finite.equiv hiso.symm
  have hrank3 : Module.finrank ℂ ↥(LinearMap.range B) ≤
      Module.finrank ℂ ↥(Clos.restrictionSpace L) := by
    rw [hrange_eq]
    calc Module.finrank ℂ ↥(LinearMap.range Blift)
        ≤ Module.finrank ℂ Qquot := LinearMap.finrank_range_le Blift
      _ = Module.finrank ℂ ↥(Clos.restrictionSpace L) := hfin_Qquot
  -- Combine: rank(A) ≤ ... ≤ hilbert = rowDirectionRank. Need to identify restrictionRank(Tp) = rank(A) and rowDirectionRank = hilbert.
  -- A = restrictionMap TpSet L, so rank(A) = restrictionRank TpSet L (by definition restrictionRank = finrank range restrictionMap). Good. Our goal is restrictionRank (... image ...) ≤ rowDirectionRank ... . Note TpSet is exactly that image (by definition TpSet = image ...). Good. And rowDirectionRank = (closure ...).hilbert L = finrank restrictionSpace (by definition hilbert = finrank restrictionSpace). Good. Our Clos = closure RDirs with RDirs = rowDirections Xp Q, and Q = image snd. Good. So rowDirectionRank = finrank restrictionSpace. Good.
  -- Chain hrank1, hrank2, hrank3 gives finrank(range A) ≤ finrank(restrictionSpace). Then convert to Nats (restrictionRank, hilbert) via rfl (definitions) and rowDirectionRank unfolding.
  have hfinal : restrictionRank TpSet L ≤ rowDirectionRank Xp Q L := by
    unfold rowDirectionRank
    -- rowDirectionRank = (closure ...).hilbert L = finrank restrictionSpace. Need to unfold hilbert? hilbert V D = finrank (V.restrictionSpace D). Good. So goal becomes restrictionRank ... ≤ finrank ... . Since restrictionRank = finrank range A (by definition? restrictionRank T D = finrank range (restrictionMap T D). Good. Our A = restrictionMap TpSet L, so restrictionRank TpSet L = finrank range A definitionally (rfl). Good. Similarly rowDirectionRank unfolds to hilbert, which unfolds to finrank restrictionSpace. Good. So convert via unfolding + hrank chain.
    show Module.finrank ℂ ↥(LinearMap.range A) ≤
      Module.finrank ℂ ↥((ProjectiveVariety.closure (rowDirections Xp Q)).restrictionSpace L)
    -- Our Clos = closure RDirs with RDirs = rowDirections Xp Q (by definition RDirs, Q). Good. So Clos.restrictionSpace = ... . Need to align Clos with closure ... (defeq via lets? RDirs let-bound as rowDirections Xp Q, Clos let-bound as closure RDirs, so defeq. Good. So show converts? Might need to unfold lets? Since RDirs, Clos, Q, TpSet are lets, defeq holds via delta? `show` should work if we write exact unfolded form? Our show already writes unfolded form (closure ...). Since Clos is let-bound as closure RDirs, and RDirs let-bound as rowDirections..., they are defeq, so show should succeed (changing goal from helper's statement with TpSet/Q? Wait helper's goal uses TpSet? No, helper's goal is `restrictionRank (... image ...) ≤ rowDirectionRank ...` with image written explicitly, not via TpSet/Q lets? Actually helper statement uses `... '' (↑Γp ...)` and `Γp.image ...`, while our TpSet/Q lets are defined as those exact expressions? TpSet let-bound as image ..., Q let-bound as image snd. Good. So defeq holds. Good.)
    -- Chain hrank1, hrank2, hrank3: rank(A) ≤ rank(B∘ψ) ≤ rank(B) ≤ finrank(restrictionSpace).
    calc Module.finrank ℂ ↥(LinearMap.range A)
        ≤ Module.finrank ℂ ↥(LinearMap.range (B.comp psiSub)) := hrank1
      _ ≤ Module.finrank ℂ ↥(LinearMap.range B) := hrank2
      _ ≤ Module.finrank ℂ ↥(Clos.restrictionSpace L) := hrank3
  -- Convert hfinal (with TpSet/Q lets) to helper's statement (with explicit images). Since defeq via lets, exact.
  exact hfinal

/-- Specializing at each physical center bounds affine label rank by the
sum of homogeneous row ranks: homogenize each row polynomial using its
direction coordinate i₀=1. Center repetitions and repeated labels are allowed. -/
theorem covered_common_label_rank_upper (P : Finset (RPoint d))
    (C : RPoint d → ProjectiveFamily.Family d)
    (hC : ∀ p ∈ P, TrackD.IsDirectionalFamily (C p))
    (E : ℝ) (hE : 0 ≤ E)
    (hdegree : ∀ p ∈ P, (ProjectiveFamily.degree (C p) : ℝ) ≤ E)
    (i₀ : Fin d) (Γ : Finset (RPoint d × RPoint d))
    (hP : ∀ pq ∈ Γ, pq.1 ∈ P)
    (hchart : ∀ pq ∈ Γ, (TrackD.toC pq.2 - TrackD.toC pq.1) i₀ ≠ 0)
    (hcovered : ∀ pq ∈ Γ, TrackD.DirIn (C pq.1) pq.1 pq.2) (L : ℕ) :
    (commonLabelRank i₀ Γ L : ℝ) ≤ (P.card : ℝ) * E * (L + 1 : ℝ) := by
  classical
  let Gp : RPoint d → Finset (RPoint d × RPoint d) :=
    fun p => Γ.filter (fun pq => pq.1 = p)
  let Tp : RPoint d → Set (Fin d ⊕ Fin d → ℂ) := fun p =>
    (fun pq : RPoint d × RPoint d =>
      TrackD.labelPt i₀ (TrackD.toC pq.1) (TrackD.toC pq.2)) '' (↑(Gp p) : Set (RPoint d × RPoint d))
  have hGpsub : ∀ p, Gp p ⊆ Γ := fun p => Finset.filter_subset _ _
  have hunion : (fun pq : RPoint d × RPoint d =>
      TrackD.labelPt i₀ (TrackD.toC pq.1) (TrackD.toC pq.2)) '' (↑Γ : Set (RPoint d × RPoint d)) =
      ⋃ p ∈ P, Tp p := by
    ext z
    constructor
    · rintro ⟨pq, hpq, rfl⟩
      have hpP : pq.1 ∈ P := hP pq hpq
      refine Set.mem_iUnion.mpr ⟨pq.1, ?_⟩
      refine Set.mem_iUnion.mpr ⟨hpP, ?_⟩
      show TrackD.labelPt i₀ (TrackD.toC pq.1) (TrackD.toC pq.2) ∈ Tp pq.1
      show _ ∈ _ '' (↑(Gp pq.1) : Set (RPoint d × RPoint d))
      refine Set.mem_image_of_mem _ ?_
      show pq ∈ (↑(Gp pq.1) : Set (RPoint d × RPoint d))
      have hfin : pq ∈ Gp pq.1 := Finset.mem_filter.mpr ⟨hpq, rfl⟩
      exact Finset.mem_coe.mpr hfin
    · intro hz
      rcases Set.mem_iUnion.mp hz with ⟨p, hz2⟩
      rcases Set.mem_iUnion.mp hz2 with ⟨_, hz3⟩
      -- hz3 : z ∈ Tp p
      rcases hz3 with ⟨pq, hpq, rfl⟩
      -- hpq : pq ∈ (Gp p : Set ...)
      have hpqΓ : pq ∈ (↑Γ : Set (RPoint d × RPoint d)) := by
        have hmem : pq ∈ Gp p := by simpa using hpq
        exact hGpsub p hmem
      exact ⟨pq, hpqΓ, rfl⟩
  have hrank_eq : commonLabelRank i₀ Γ L =
      restrictionRank (⋃ p ∈ P, Tp p) L := by
    unfold commonLabelRank
    rw [hunion]
  rw [hrank_eq]
  have hbi := _root_.DistinctDistances.Reduction.restrictionRank_biUnion_le P Tp L
  -- Per-row real bound.
  have hrow : ∀ p ∈ P, (restrictionRank (Tp p) L : ℝ) ≤ E * (L + 1 : ℝ) := by
    intro p hp
    have hfirst : ∀ pq ∈ Gp p, pq.1 = p := by
      intro pq hpq
      exact (Finset.mem_filter.mp hpq).2
    have hchartp : ∀ pq ∈ Gp p,
        (TrackD.toC pq.2 - TrackD.toC pq.1) i₀ ≠ 0 := by
      intro pq hpq
      exact hchart pq (hGpsub p hpq)
    have hle := commonLabelRank_row_le i₀ p (Gp p) hfirst hchartp L
    -- Tp p is exactly the set in hle.
    have hQ : ∀ q ∈ (Gp p).image Prod.snd, TrackD.DirIn (C p) p q := by
      intro q hq
      rcases Finset.mem_image.mp hq with ⟨pq, hpqΓp, rfl⟩
      have hpqΓ : pq ∈ Γ := hGpsub p hpqΓp
      have hp1 : pq.1 = p := hfirst pq hpqΓp
      have hdir := hcovered pq hpqΓ
      rw [hp1] at hdir
      -- hdir : DirIn (C p) p pq.2; need with q = pq.2, and Prod.snd (pq.1,pq.2)=pq.2
      simpa using hdir
    have hrow := covered_row_direction_rank_upper (C p) (hC p hp) p
      ((Gp p).image Prod.snd) hQ L
    have hdeg := hdegree p hp
    have hL : (0 : ℝ) ≤ (L : ℝ) + 1 := by positivity
    calc (restrictionRank (Tp p) L : ℝ)
        ≤ (rowDirectionRank (TrackD.toC p) ((Gp p).image Prod.snd) L : ℝ) := by
          have hle' : restrictionRank ((fun pq : RPoint d × RPoint d =>
              TrackD.labelPt i₀ (TrackD.toC pq.1) (TrackD.toC pq.2)) ''
              (↑(Gp p) : Set (RPoint d × RPoint d))) L ≤
              rowDirectionRank (TrackD.toC p) ((Gp p).image Prod.snd) L := hle
          have heq : Tp p = (fun pq : RPoint d × RPoint d =>
              TrackD.labelPt i₀ (TrackD.toC pq.1) (TrackD.toC pq.2)) ''
              (↑(Gp p) : Set (RPoint d × RPoint d)) := rfl
          rw [heq]
          exact_mod_cast hle'
      _ ≤ (ProjectiveFamily.degree (C p) : ℝ) * (L + 1 : ℝ) := hrow
      _ ≤ E * (L + 1 : ℝ) := mul_le_mul_of_nonneg_right hdeg hL
  calc (restrictionRank (⋃ p ∈ P, Tp p) L : ℝ)
      ≤ (∑ p ∈ P, restrictionRank (Tp p) L : ℕ) := by
        exact_mod_cast hbi
    _ = ∑ p ∈ P, (restrictionRank (Tp p) L : ℝ) := by
        rw [Nat.cast_sum]
    _ ≤ ∑ _p ∈ P, (E * (L + 1 : ℝ)) := Finset.sum_le_sum hrow
    _ = (P.card : ℝ) * E * (L + 1 : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring

end
end DistinctDistances.SparseCones
