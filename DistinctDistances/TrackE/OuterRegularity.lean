import DistinctDistances.TrackE.OuterPool
import DistinctDistances.TrackE.CommonRank
import DistinctDistances.TrackE.MORegAux
import DistinctDistances.TrackE.MOR191Aux
import DistinctDistances.TrackE.MOR190Aux
import DistinctDistances.TrackE.OuterTangentAux

/-! Regular product images at the outer endpoint (sparse-cones.tex:426–561).

`outer_envelope_larger_components_sparse` (sc:442–490) deletes the mass
assigned to envelope components of dimension `> 2k`, borrowing
`common_label_rank_proved` on an auxiliary dense graph; `outer_smooth_subfamily`
(sc:492–524) applies `TrackA.poly_regularity` and product testing to get the
smooth system; `outer_tangent_tests` (sc:526–561) establishes the tangent
injectivity/inequality data consumed by the lift. Deletion bounds are
asymptotic, so 189–191 conclude `∀ᶠ` statements; 190 and 191 take their input
at every budget `ρ''` and spend half of the output budget on their own
deletions. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- The label point of a pair in shared coordinates. -/
def outerLabelPt (i₀ : Fin d) (pq : RPoint d × RPoint d) : Point (d + d) :=
  fun kk => TrackD.labelPt i₀ (TrackD.toC pq.1) (TrackD.toC pq.2) (finSumFinEquiv.symm kk)

/-- The envelope degree `⌊T_s(t₀)⌋` of the image family at time `t₀`. -/
def outerEnvDeg (B s : ℕ → ℝ) (t₀ : ℝ) (i : ℕ) : ℕ :=
  ⌊TrackD.testDeg (B i) (s i) t₀⌋₊

/-- The smooth regular data at the outer endpoint (sc:outer-regularity): the
common label equations `Eqs` with their degree bound `Bdeg`, the good-pair
predicate (bad pairs of the chart graph cost at most `ρ'` of `|S|²`), vanishing
of every equation on the complete owner image of each good pair, and the
smooth-`2k`-fold Jacobian rank at each good label. -/
structure OuterRegularityCert {F : ConeCoverageSequence regime} (T : SelectedProfileSequence F)
    (M : CommonPoolProfile T) (k i j : ℕ) (i₀ : Fin d) (ρ ε ρ' Bdeg τ : ℝ) where
  chart : OuterChartCert T M k i j i₀ ρ ε ρ' τ
  Eqs : Finset (TrackD.PairPoly d)
  good : RPoint d × RPoint d → Prop
  hEqdeg : ∀ G ∈ Eqs, (G.totalDegree : ℝ) ≤ Bdeg
  hbad : ((chart.G.filter (fun pq => ¬ good pq)).card : ℝ) ≤
    ρ' * (chart.pool.S.card : ℝ) ^ 2
  hvanish : ∀ pq ∈ chart.G, good pq → ∀ G ∈ Eqs,
    commonPairEquation G ∈
      (commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2)).ideal
  hsmooth : ∀ pq ∈ chart.G, good pq →
    Module.finrank ℂ (TrackD.jacKer (Eqs.image commonPairEquation)
      (outerLabelPt i₀ pq)) = 2 * k

set_option maxHeartbeats 1000000
/-- sc:outer-regularity.larger-components (sparse-cones.tex:442–490).
Put `V = Env_{T₀}(U)` (`T₀ = T_s(t₀)`, envelope of the union of the
images). Images assigned to components of `V` of dimension `h ≥ 2k+1` carry
only a `ρ'`-fraction of `|S|²`, so after deleting their pairs every remaining
owner image is itself an irreducible component of `V`. Proof: else some `h`
group has fixed positive mass along a subsequence; form `Λ_h` from all actual
ordered pairs of `S × S` whose owner image is assigned to that group, minus the
diagonal (`≤ n` pairs); `Λ_h` is dense and independent of `Γ`, so
`common_label_rank_proved` (CommonRankProof.lean, arbitrary-graph scope)
applies at a time just before `β = M.b j` (off the finitely many cuts; if no
earlier testing degree is `≥ 1`, the rank-one boundary convention of
`common_rank_initial`). On the final plateau `σ(b) = e_j T_s(b)^k`; propagating
with `h ≥ 2k+1` (as in `common_rank_step_of_alternative`) gives
`H_V(T₀) ≥ e_j² T₀^{2k} min(T₀/T_s(β), T₀/(D₁D₂)) e^{-ξs}`, with strict margins
`t₀ - β` and `t₀ - (1+b₁+b₂)` (hypotheses `ht₀β`, `ht₀b`, `hεβ`, `hεb`),
against `H_V(T₀) = H_U(T₀) ≤ C e_j² T₀^{2k} e^{εs}` (envelope equality and the
pure-`2k` upper Hilbert bound, from `hUdeg`; replay of
`common_label_group_rank`). Follow `common_label_dense_group`
(CommonLabelGroup.lean). The global physical sequence `W` is threaded through
unchanged (input and output satisfy `chart.W = W`); 191 consumes the pin to get
uniform test-degree bounds from the single `W.tests`. -/
theorem outer_envelope_larger_components_sparse {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (M : CommonPoolProfile T)
    (houter : ∀ i, T.IsOuter i) (hs : ∀ i, M.s i = Real.log (regime.B i))
    (k j : ℕ) (hj : j < d) (hkj : k + j + 1 = d) (hk : 1 ≤ k ∧ k + 1 < d)
    (htop : ∀ a : Fin d, j < a.val → M.b a = 1)
    (i₀ : Fin d) (ρ ε ρ' : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1) (hε : 0 < ε)
    (hρ' : 0 < ρ') (τ t₀ : ℝ) (ht₀1 : t₀ < 1)
    (ht₀β : M.b ⟨j, hj⟩ < t₀)
    (ht₀b : 1 + M.b ⟨0, by omega⟩ + M.b ⟨1, by omega⟩ < t₀)
    (hεβ : 4 * ε < t₀ - M.b ⟨j, hj⟩)
    (hεb : 4 * ε < t₀ - (1 + M.b ⟨0, by omega⟩ + M.b ⟨1, by omega⟩))
    (W : CommonPhysicalSequence T M (j + 1) τ)
    (hchart : ∀ᶠ i in atTop,
      ∃ chart : OuterChartCert T M k i j i₀ ρ ε ρ' τ, chart.W = W) :
    ∀ᶠ i in atTop, ∃ (chart : OuterChartCert T M k i j i₀ ρ ε ρ' τ)
      (D : Finset (RPoint d × RPoint d)),
      chart.W = W ∧ D ⊆ chart.G ∧
      ((D.card : ℝ)) ≤ ρ' * (chart.pool.S.card : ℝ) ^ 2 ∧
      ∀ pq ∈ chart.G \ D,
        commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈
          Bridges.envelopeComponents (⋃ Z ∈ chart.U, Z.points)
            (outerEnvDeg regime.B M.s t₀ i) := by
  classical
  have hd3 := regime.dimension_ge_three
  have hβlow : -1 ≤ M.b ⟨j, hj⟩ := common_profile_time_lower M _
  have h10 : (0 : ℝ) < 1 + t₀ := by linarith
  -- Fixed borrowing parameters (independent of i/chart): κ small O(ε), τ' just before β
  -- off cuts, θ=ε for rank lower, ρ_h for Λ density with half budget + (1-ρ)² conversion.
  have hdposR : (0 : ℝ) < (d : ℝ) := by
    have : 0 < d := by omega
    exact_mod_cast this
  set κ : ℝ := ε / (8 * (d : ℝ) + 8) with hκdef
  have hκpos : 0 < κ := by dsimp [κ]; positivity
  obtain ⟨τ', hτ'mem, hτ'lt, hτ'off⟩ := outer_borrow_time M j hj κ hκpos
  have hρhpos : (0 : ℝ) < ρ' / (2 * (2 * (d : ℝ) + 1)) * (1 - ρ) ^ 2 := by positivity
  -- Rank at τ' (via proved rank or initial if τ'≤-1 with τ'<b₀); fixed ∀ᶠ independent of chart.
  have hRankEv : ∀ᶠ i in atTop, ∀ (i₀ : Fin d) (Γ : Finset (RPoint d × RPoint d)),
      Γ ⊆ TrackD.poolPts (T.sources i) ×ˢ TrackD.poolPts (T.targets i) →
      (∀ pq ∈ Γ, (TrackD.toC pq.2 - TrackD.toC pq.1) i₀ ≠ 0) →
      ρ' / (2 * (2 * (d : ℝ) + 1)) * (1 - ρ) ^ 2 *
        ((TrackD.poolPts (T.sources i)).card : ℝ) *
        (TrackD.poolPts (T.targets i)).card ≤ Γ.card →
      commonRankTarget M i τ' * Real.exp (-ε * M.s i) ≤
        commonLabelRank i₀ Γ ⌊TrackD.testDeg (regime.B i) (M.s i) τ'⌋₊ := by
    by_cases hτ'neg : -1 < τ'
    · -- general plateau rank (proved)
      have hτ'last : τ' < commonLastTime M := by
        have hlast1 : commonLastTime M = 1 := by
          unfold commonLastTime
          have hj1 : j < d - 1 := by omega
          have htop1 := htop ⟨d - 1, by omega⟩ (by omega)
          simpa using htop1
        rw [hlast1]
        linarith
      have hRank := common_label_rank_proved T M τ' hτ'neg hτ'last hτ'off ε hε
        (ρ' / (2 * (2 * (d : ℝ) + 1)) * (1 - ρ) ^ 2) hρhpos
      exact hRank
    · -- initial plateau (τ' ≤ -1 with τ' < b₀ via off-cuts + time_lower)
      push Not at hτ'neg
      have hb0 : M.b ⟨0, by omega⟩ ≠ τ' := hτ'off ⟨0, by omega⟩
      have hb0low : -1 ≤ M.b ⟨0, by omega⟩ := common_profile_time_lower M _
      have hτ'b0 : τ' < M.b ⟨0, by omega⟩ :=
        lt_of_le_of_ne (le_trans hτ'neg hb0low) hb0.symm
      have hRankInit := common_rank_initial T M τ' hτ'b0 ε hε
        (ρ' / (2 * (2 * (d : ℝ) + 1)) * (1 - ρ) ^ 2) hρhpos
      exact hRankInit
  -- testing degree diverges at t₀; envelope degree ≥1 eventually; pool diverges
  -- (pool threshold for diagonal absorption with half budget: |S|≥2·count/ρ',
  --  count≤2d+1, via |S|≥(1-ρ)|poolPts|)
  have hTtend := testDeg_tendsto_atTop_of_logB hs t₀ h10
  have hPtend := poolPts_card_tendsto_atTop M hs
  have h1ρ : (0 : ℝ) < 1 - ρ := by linarith
  have hcountpos : (0 : ℝ) < 2 * (2 * (d : ℝ) + 1) / ρ' := by positivity
  have hPthresh : (0 : ℝ) < (2 * (2 * (d : ℝ) + 1) / ρ') / (1 - ρ) := by positivity
  obtain ⟨c0, hc0pos, hcomp⟩ := TrackD.envelope_hilbert_comparison (d + d)
  have hκle : 2 * (d : ℝ) * κ ≤ ε / 4 := by
    have hdenom : (0 : ℝ) < 8 * (d : ℝ) + 8 := by positivity
    have hnpos : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
    rw [hκdef, ← mul_div_assoc, div_le_iff₀ hdenom]
    nlinarith [hε, hnpos, hdposR]
  have hcmin : 4 * ε < min (t₀ - M.b ⟨j, hj⟩) (t₀ - (1 + M.b ⟨0, by omega⟩ + M.b ⟨1, by omega⟩)) :=
    lt_min hεβ hεb
  set δ : ℝ := min (t₀ - M.b ⟨j, hj⟩) (t₀ - (1 + M.b ⟨0, by omega⟩ + M.b ⟨1, by omega⟩)) -
    (2 * ε + 2 * (d : ℝ) * κ + (2 * (k : ℝ) + 1) * κ) with hδdef
  have hδpos : 0 < δ := by
    have h1 : 2 * ε + 2 * (d : ℝ) * κ + (2 * (k : ℝ) + 1) * κ ≤
        2 * ε + ε / 4 + ε / 4 := by
      have hk_le : (k : ℝ) ≤ (d : ℝ) := by
        have : k ≤ d := by omega
        exact_mod_cast this
      have h1a : 2 * (d : ℝ) * κ ≤ ε / 4 := by linarith [hκle]
      have h1b : (2 * (k : ℝ) + 1) * κ ≤ ε / 4 := by
        have hdenom : (0 : ℝ) < 8 * (d : ℝ) + 8 := by positivity
        rw [hκdef, ← mul_div_assoc, div_le_iff₀ hdenom]
        have hk2 : 2 * (k : ℝ) + 1 ≤ 2 * (d : ℝ) + 1 := by linarith [hk_le]
        nlinarith [hε, hk2, hdposR, hκle]
      linarith [h1a, h1b]
    have h2 : 2 * ε + ε / 4 + ε / 4 < 4 * ε := by linarith [hε]
    linarith [hcmin, h1, h2]
  have hC0pos : (0 : ℝ) < (1 + ρ) * (2 : ℝ) ^ (6 * d) / c0 := by positivity
  set C0 : ℝ := (1 + ρ) * (2 : ℝ) ^ (6 * d) / c0 with hC0def
  set S0 : ℝ := (Real.log C0 + 1) / δ with hS0def
  filter_upwards [hchart, hTtend.eventually_ge_atTop 2,
    eventually_floor_ge_half hs t₀ h10,
    hPtend.eventually_ge_atTop ((2 * (2 * (d : ℝ) + 1) / ρ') / (1 - ρ)),
    hRankEv, regime.B_tendsto.eventually_ge_atTop 2,
    M.width_grows.eventually_ge_atTop S0] with
    i hi hTge hfl hPge hRank hBge hsge
  obtain ⟨chart, hchartW⟩ := hi
  set T0n : ℕ := outerEnvDeg regime.B M.s t₀ i with hT0ndef
  have hT0eq : T0n = ⌊TrackD.testDeg (regime.B i) (M.s i) t₀⌋₊ := rfl
  have hT01 : 1 ≤ T0n := hfl.2.2
  -- The bad pairs (images not themselves envelope components) satisfy the
  -- remaining condition by definition; it remains to bound their mass.
  -- If frequently large, pigeonhole gives h∈[2k+1,2d] with fixed positive mass
  -- (max per i, varying h still ≥2k+1 uniformly); Λ_h minus diagonal is dense;
  -- borrowing rank just before β (rank-one boundary if β=-1/T'<1) and final-plateau
  -- propagation h≥2k+1 with margins t₀-β, t₀-(1+b₀+b₁) contradict H_V upper via hUdeg.
  set Bad : Finset (RPoint d × RPoint d) :=
    chart.G.filter (fun pq => commonProductImage i₀ (chart.W.owner i pq.1)
      (chart.W.owner i pq.2) ∉ Bridges.envelopeComponents
        (⋃ Z ∈ chart.U, Z.points) T0n) with hBaddef
  have hBadsub : Bad ⊆ chart.G := Finset.filter_subset _ _
  have hBadrem : ∀ pq ∈ chart.G \ Bad,
      commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈
        Bridges.envelopeComponents (⋃ Z ∈ chart.U, Z.points) T0n := by
    intro pq hpq
    have hmem := Finset.mem_sdiff.mp hpq
    have hnotbad : pq ∉ Bad := hmem.2
    rw [hBaddef] at hnotbad
    have hG : pq ∈ chart.G := hmem.1
    by_contra hcon
    exact hnotbad (Finset.mem_filter.mpr ⟨hG, hcon⟩)
  -- It suffices to show |Bad| ≤ ρ'|S|² (then D:=Bad works)
  have hBadcard : ((Bad.card : ℝ)) ≤ ρ' * (chart.pool.S.card : ℝ) ^ 2 := by
    -- Containing components for bad images (dim ≥2k+1, as in dense-group hWex)
    have hUmem : ∀ pq ∈ chart.G, commonProductImage i₀ (chart.W.owner i pq.1)
        (chart.W.owner i pq.2) ∈ chart.U := fun pq hpq => chart.hUmem pq hpq
    have hUirr_dim : ∀ Z ∈ chart.U, Z.IsIrreducible ∧ Z.dimension = 2 * k := by
      intro Z hZ
      exact chart.hU Z hZ
    set Tup : Set (Point (d + d)) := ⋃ Z ∈ chart.U, Z.points with hTupdef
    set Venv : AffineVariety (d + d) := DistinctDistances.envelope Tup T0n with hVdef
    have hTsubV : Tup ⊆ Venv.points :=
      Bridges.subset_envelope Tup T0n
    have hWex : ∀ pq ∈ Bad, ∃ W : AffineVariety (d + d),
        W ∈ Bridges.envelopeComponents Tup T0n ∧
        (commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2)).Subvariety W ∧
        2 * k + 1 ≤ W.dimension ∧ W.dimension ≤ 2 * d ∧
        W.IsIrreducible := by
      intro pq hpq
      have hpqG : pq ∈ chart.G := hBadsub hpq
      have hZmemU : commonProductImage i₀ (chart.W.owner i pq.1)
          (chart.W.owner i pq.2) ∈ chart.U := hUmem pq hpqG
      obtain ⟨hZirr, hZdim⟩ := hUirr_dim _ hZmemU
      have hZpts_sub : (commonProductImage i₀ (chart.W.owner i pq.1)
          (chart.W.owner i pq.2)).points ⊆ Tup := by
        intro y hy
        rw [hTupdef]
        exact Set.mem_biUnion hZmemU hy
      have hZsubV : (commonProductImage i₀ (chart.W.owner i pq.1)
          (chart.W.owner i pq.2)).Subvariety Venv := by
        apply (AffineVariety.subvariety_iff_points_subset _ _).mpr
        exact hZpts_sub.trans hTsubV
      have hle : Venv.ideal ≤ (commonProductImage i₀ (chart.W.owner i pq.1)
          (chart.W.owner i pq.2)).ideal := hZsubV
      haveI : (commonProductImage i₀ (chart.W.owner i pq.1)
          (chart.W.owner i pq.2)).ideal.IsPrime := hZirr
      obtain ⟨Q, hQmin, hQle⟩ := Ideal.exists_minimalPrimes_le hle
      let C : Venv.Component := ⟨Q, hQmin⟩
      have hCmem : C.variety ∈ Bridges.envelopeComponents Tup T0n := by
        unfold Bridges.envelopeComponents
        exact Finset.mem_image_of_mem _ (Finset.mem_univ C)
      have hCsub : (commonProductImage i₀ (chart.W.owner i pq.1)
          (chart.W.owner i pq.2)).Subvariety C.variety := hQle
      have hCirr : C.variety.IsIrreducible := C.irreducible
      have hCdim_lo : 2 * k ≤ C.variety.dimension := by
        rw [← hZdim]
        exact TrackD.irreducible_dimension_mono _ _ hZirr hCirr hCsub
      have hCdim_hi : C.variety.dimension ≤ 2 * d := by
        have hle_amb := TrackA.pooling_dimension_le_ambient C.variety hCirr
        omega
      have hCdim_ne : C.variety.dimension ≠ 2 * k := by
        intro heq
        have hpos : 0 < C.variety.dimension := by omega
        have hZeq : (commonProductImage i₀ (chart.W.owner i pq.1)
            (chart.W.owner i pq.2)) = C.variety :=
          TrackD.irreducible_subvariety_eq_of_pos_dimension_eq _ _ hZirr hCirr
            hCsub hpos (by omega)
        have hZmemComp : commonProductImage i₀ (chart.W.owner i pq.1)
            (chart.W.owner i pq.2) ∈ Bridges.envelopeComponents Tup T0n := by
          rw [hZeq]
          exact hCmem
        have hpqBad : pq ∈ Bad := hpq
        rw [hBaddef] at hpqBad
        have hcon := (Finset.mem_filter.mp hpqBad).2
        exact hcon hZmemComp
      have hCdim_ge : 2 * k + 1 ≤ C.variety.dimension := by omega
      exact ⟨C.variety, hCmem, hCsub, hCdim_ge, hCdim_hi, hCirr⟩
    -- Choose containing components, pigeonhole max h, density, borrow, rank, propagation
    have hWall : ∀ pq : RPoint d × RPoint d, ∃ W : AffineVariety (d + d),
        pq ∈ Bad →
          (W ∈ Bridges.envelopeComponents Tup T0n ∧
          (commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2)).Subvariety W ∧
          2 * k + 1 ≤ W.dimension ∧ W.dimension ≤ 2 * d ∧
          W.IsIrreducible) := by
      intro pq
      by_cases h : pq ∈ Bad
      · obtain ⟨W, h1, h2, h3, h4, h5⟩ := hWex pq h
        exact ⟨W, fun _ => ⟨h1, h2, h3, h4, h5⟩⟩
      · exact ⟨AffineVariety.whole, fun h' => absurd h' h⟩
    choose V hV using hWall
    have hVmem : ∀ pq ∈ Bad, V pq ∈ Bridges.envelopeComponents Tup T0n :=
      fun pq hpq => (hV pq hpq).1
    have hVsub : ∀ pq ∈ Bad, (commonProductImage i₀ (chart.W.owner i pq.1)
        (chart.W.owner i pq.2)).Subvariety (V pq) :=
      fun pq hpq => (hV pq hpq).2.1
    have hVlo : ∀ pq ∈ Bad, 2 * k + 1 ≤ (V pq).dimension :=
      fun pq hpq => (hV pq hpq).2.2.1
    have hVhi : ∀ pq ∈ Bad, (V pq).dimension ≤ 2 * d :=
      fun pq hpq => (hV pq hpq).2.2.2.1
    have hVirr : ∀ pq ∈ Bad, (V pq).IsIrreducible :=
      fun pq hpq => (hV pq hpq).2.2.2.2
    have hIcc_ne : (Finset.Icc (2 * k + 1) (2 * d)).Nonempty :=
      Finset.nonempty_Icc.mpr (by omega)
    have hHs_mem : ∀ pq ∈ Bad, (V pq).dimension ∈ Finset.Icc (2 * k + 1) (2 * d) := by
      intro pq hpq
      exact Finset.mem_Icc.mpr ⟨hVlo pq hpq, hVhi pq hpq⟩
    have hsum_nat : Bad.card =
        ∑ h ∈ Finset.Icc (2 * k + 1) (2 * d),
          (Bad.filter (fun pq => (V pq).dimension = h)).card := by
      have hmap : Set.MapsTo (fun pq => (V pq).dimension) (Bad : Set (RPoint d × RPoint d))
          ((Finset.Icc (2 * k + 1) (2 * d) : Finset ℕ) : Set ℕ) := by
        intro pq hpq
        exact Finset.mem_coe.mpr (hHs_mem pq (Finset.mem_coe.mp hpq))
      have h := Finset.card_eq_sum_card_fiberwise (s := Bad)
        (t := Finset.Icc (2 * k + 1) (2 * d))
        (f := fun pq => (V pq).dimension) hmap
      simpa using h
    obtain ⟨h, hhHs, hmax⟩ := Finset.exists_max_image
      (Finset.Icc (2 * k + 1) (2 * d))
      (fun h => (Bad.filter (fun pq => (V pq).dimension = h)).card) hIcc_ne
    have hhIcc : 2 * k + 1 ≤ h ∧ h ≤ 2 * d := Finset.mem_Icc.mp hhHs
    set Badh : Finset (RPoint d × RPoint d) :=
      Bad.filter (fun pq => (V pq).dimension = h) with hBadhdef
    have hBadh_sub : Badh ⊆ Bad := Finset.filter_subset _ _
    have hBad_eq_sum : Bad.card =
        ∑ h' ∈ Finset.Icc (2 * k + 1) (2 * d),
          (Bad.filter (fun pq => (V pq).dimension = h')).card := hsum_nat
    have hIcc_card_le : (Finset.Icc (2 * k + 1) (2 * d)).card ≤ 2 * d + 1 := by
      rw [Nat.card_Icc]
      omega
    have hSpos : (0 : ℝ) < (chart.pool.S.card : ℝ) := by
      have hSc := chart.pool.hScard
      have h1ρ' : (0 : ℝ) < 1 - ρ := by linarith
      have hSge : (2 * (2 * (d : ℝ) + 1) / ρ') ≤ (chart.pool.S.card : ℝ) := by
        have hPge_le := hPge
        calc (2 * (2 * (d : ℝ) + 1) / ρ')
            = (1 - ρ) * (((2 * (2 * (d : ℝ) + 1) / ρ') / (1 - ρ))) := by
              field_simp
          _ ≤ (1 - ρ) * ((TrackD.poolPts (T.sources i)).card : ℝ) :=
              mul_le_mul_of_nonneg_left hPge_le h1ρ'.le
          _ ≤ (chart.pool.S.card : ℝ) := hSc
      have hthresh_pos : (0 : ℝ) < 2 * (2 * (d : ℝ) + 1) / ρ' := by positivity
      linarith
    by_contra hBadlarge
    push Not at hBadlarge
    -- Pigeonhole: |Bad| ≤ |Icc|·|Badh| with |Icc| ≤ 2d+1.
    have hsum_le : ∑ h' ∈ Finset.Icc (2 * k + 1) (2 * d),
          (Bad.filter (fun pq => (V pq).dimension = h')).card ≤
        (Finset.Icc (2 * k + 1) (2 * d)).card * Badh.card := by
      calc ∑ h' ∈ Finset.Icc (2 * k + 1) (2 * d),
              (Bad.filter (fun pq => (V pq).dimension = h')).card
          ≤ ∑ _h' ∈ Finset.Icc (2 * k + 1) (2 * d), Badh.card :=
            Finset.sum_le_sum (fun h' hh' => hmax h' hh')
        _ = (Finset.Icc (2 * k + 1) (2 * d)).card * Badh.card := by
            simp [Finset.sum_const]
    have hBad_le : (Bad.card : ℝ) ≤
        (((Finset.Icc (2 * k + 1) (2 * d)).card : ℕ) : ℝ) * (Badh.card : ℝ) := by
      have hn : Bad.card ≤ (Finset.Icc (2 * k + 1) (2 * d)).card * Badh.card :=
        hBad_eq_sum ▸ hsum_le
      exact_mod_cast hn
    have hCpos : (0 : ℝ) < (((Finset.Icc (2 * k + 1) (2 * d)).card : ℕ) : ℝ) := by
      have hne : (Finset.Icc (2 * k + 1) (2 * d)).card ≠ 0 := by
        rw [Finset.card_ne_zero]
        exact hIcc_ne
      exact_mod_cast Nat.pos_of_ne_zero hne
    have hCnt_le : (((Finset.Icc (2 * k + 1) (2 * d)).card : ℕ) : ℝ) ≤
        2 * (d : ℝ) + 1 := by
      exact_mod_cast hIcc_card_le
    -- Quantitative |S| lower bound for diagonal absorption (re-derived here
    -- since hSge inside hSpos is out of scope).
    have hSge2 : (2 * (2 * (d : ℝ) + 1) / ρ') ≤ (chart.pool.S.card : ℝ) := by
      have hSc := chart.pool.hScard
      have hPge_le := hPge
      calc (2 * (2 * (d : ℝ) + 1) / ρ')
          = (1 - ρ) * (((2 * (2 * (d : ℝ) + 1) / ρ') / (1 - ρ))) := by
            field_simp
        _ ≤ (1 - ρ) * ((TrackD.poolPts (T.sources i)).card : ℝ) :=
            mul_le_mul_of_nonneg_left hPge_le h1ρ.le
        _ ≤ (chart.pool.S.card : ℝ) := hSc
    -- Diagonal in Badh has at most |S| pairs; absorb with half the budget.
    set Diag : Finset (RPoint d × RPoint d) :=
      Badh.filter (fun pq => pq.1 = pq.2) with hDiagdef
    have hDiag_img : Diag.image Prod.fst ⊆ chart.pool.S := by
      intro p hp
      obtain ⟨pq, hpq, rfl⟩ := Finset.mem_image.mp hp
      have hmem : pq ∈ Badh := (Finset.mem_filter.mp hpq).1
      have hG : pq ∈ chart.G :=
        hBadsub (hBadh_sub hmem)
      exact (chart.hGmem pq hG).1
    have hDiag_inj : Set.InjOn Prod.fst (Diag : Set (RPoint d × RPoint d)) := by
      intro a ha b hb hab
      have ha2 : a.1 = a.2 := (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
      have hb2 : b.1 = b.2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2
      have h11 : a.1 = b.1 := hab
      exact Prod.ext h11 (ha2.symm.trans (h11.trans hb2))
    have hDiag_le : (Diag.card : ℝ) ≤ (chart.pool.S.card : ℝ) := by
      have hc : Diag.card ≤ chart.pool.S.card := by
        calc Diag.card = (Diag.image Prod.fst).card :=
              (Finset.card_image_of_injOn hDiag_inj).symm
          _ ≤ chart.pool.S.card := Finset.card_le_card hDiag_img
      exact_mod_cast hc
    -- Λ := Badh minus diagonal; density with half budget.
    set Lam : Finset (RPoint d × RPoint d) :=
      Badh.filter (fun pq => pq.1 ≠ pq.2) with hLamdef
    have hLam_sub : Lam ⊆ Badh := Finset.filter_subset _ _
    have hLam_card : Lam.card + Diag.card = Badh.card := by
      have hdisj : Disjoint Lam Diag := by
        rw [Finset.disjoint_left]
        intro pq hLamMem
        intro hDiagMem
        obtain ⟨_, hne⟩ := Finset.mem_filter.mp hLamMem
        obtain ⟨_, heq⟩ := Finset.mem_filter.mp hDiagMem
        exact hne heq
      have hunion : Lam ∪ Diag = Badh := by
        rw [hLamdef, hDiagdef]
        ext pq
        simp only [Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro (⟨hm, hne⟩ | ⟨hm, heq⟩) <;> exact hm
        · intro hm
          by_cases he : pq.1 = pq.2
          · exact Or.inr ⟨hm, he⟩
          · exact Or.inl ⟨hm, he⟩
      have h := Finset.card_union_of_disjoint hdisj
      rw [hunion] at h
      omega
    -- hBadlarge : ρ' * |S|² < |Bad| (after push Not).
    have hBadh_gt : ρ' / (((Finset.Icc (2 * k + 1) (2 * d)).card : ℕ) : ℝ) *
        (chart.pool.S.card : ℝ) ^ 2 < (Badh.card : ℝ) := by
      have h1 : ρ' * (chart.pool.S.card : ℝ) ^ 2 <
          (((Finset.Icc (2 * k + 1) (2 * d)).card : ℕ) : ℝ) * (Badh.card : ℝ) :=
        hBadlarge.trans_le hBad_le
      rw [div_mul_eq_mul_div, div_lt_iff₀ hCpos]
      linarith [h1]
    have hDiag_half : (Diag.card : ℝ) ≤
        ρ' / (2 * (((Finset.Icc (2 * k + 1) (2 * d)).card : ℕ) : ℝ)) *
          (chart.pool.S.card : ℝ) ^ 2 := by
      have hSnn : (0 : ℝ) ≤ (chart.pool.S.card : ℝ) := Nat.cast_nonneg _
      have hCnn : (0 : ℝ) ≤ (((Finset.Icc (2 * k + 1) (2 * d)).card : ℕ) : ℝ) :=
        Nat.cast_nonneg _
      have h1 : (1 : ℝ) ≤ ρ' / (2 * (((Finset.Icc (2 * k + 1) (2 * d)).card : ℕ) : ℝ)) *
          (chart.pool.S.card : ℝ) := by
        have hSge_nn : (0 : ℝ) ≤ (chart.pool.S.card : ℝ) := hSnn
        have hC2pos : (0 : ℝ) < 2 * (((Finset.Icc (2 * k + 1) (2 * d)).card : ℕ) : ℝ) := by
          positivity
        -- From hSge2 with count ≤ 2d+1: |S| ≥ 2·count'/ρ' where count' = 2d+1 ≥ count.
        have hCntR : (((Finset.Icc (2 * k + 1) (2 * d)).card : ℕ) : ℝ) ≤
            2 * (d : ℝ) + 1 := hCnt_le
        have hSgeC : (2 * (((Finset.Icc (2 * k + 1) (2 * d)).card : ℕ) : ℝ) / ρ') ≤
            (chart.pool.S.card : ℝ) := by
          calc (2 * (((Finset.Icc (2 * k + 1) (2 * d)).card : ℕ) : ℝ) / ρ')
              ≤ (2 * (2 * (d : ℝ) + 1) / ρ') := by
                gcongr
            _ ≤ (chart.pool.S.card : ℝ) := hSge2
        rw [div_mul_eq_mul_div, le_div_iff₀ hC2pos]
        calc (1:ℝ) * (2 * (((Finset.Icc (2 * k + 1) (2 * d)).card : ℕ) : ℝ))
            = 2 * (((Finset.Icc (2 * k + 1) (2 * d)).card : ℕ) : ℝ) := one_mul _
          _ ≤ ρ' * (chart.pool.S.card : ℝ) := by
              rw [div_le_iff₀ (by positivity : (0:ℝ) < ρ')] at hSgeC
              linarith [hSgeC]
      calc (Diag.card : ℝ) ≤ (chart.pool.S.card : ℝ) := hDiag_le
        _ = (chart.pool.S.card : ℝ) * 1 := by ring
        _ ≤ (chart.pool.S.card : ℝ) *
            (ρ' / (2 * (((Finset.Icc (2 * k + 1) (2 * d)).card : ℕ) : ℝ)) *
              (chart.pool.S.card : ℝ)) := by
              gcongr
        _ = ρ' / (2 * (((Finset.Icc (2 * k + 1) (2 * d)).card : ℕ) : ℝ)) *
            (chart.pool.S.card : ℝ) ^ 2 := by ring
    have hLam_gt : ρ' / (2 * (((Finset.Icc (2 * k + 1) (2 * d)).card : ℕ) : ℝ)) *
        (chart.pool.S.card : ℝ) ^ 2 < (Lam.card : ℝ) := by
      have hcardR : ((Lam.card : ℝ)) + (Diag.card : ℝ) = (Badh.card : ℝ) := by
        exact_mod_cast hLam_card
      have hC2pos : (0 : ℝ) < 2 * (((Finset.Icc (2 * k + 1) (2 * d)).card : ℕ) : ℝ) := by
        positivity
      have hhalf : ρ' / (((Finset.Icc (2 * k + 1) (2 * d)).card : ℕ) : ℝ) *
          (chart.pool.S.card : ℝ) ^ 2 =
          ρ' / (2 * (((Finset.Icc (2 * k + 1) (2 * d)).card : ℕ) : ℝ)) *
            (chart.pool.S.card : ℝ) ^ 2 +
          ρ' / (2 * (((Finset.Icc (2 * k + 1) (2 * d)).card : ℕ) : ℝ)) *
            (chart.pool.S.card : ℝ) ^ 2 := by
        ring
      linarith [hBadh_gt, hDiag_half, hcardR, hhalf]
    -- Convert |S|² to poolPts via hScard + IsOuter (sources = targets).
    have houter_eq : T.sources i = T.targets i := (houter i).1
    have hPt_eq : ((TrackD.poolPts (T.targets i)).card : ℝ) =
        ((TrackD.poolPts (T.sources i)).card : ℝ) := by rw [houter_eq]
    have hSq_conv : (1 - ρ) ^ 2 *
        ((TrackD.poolPts (T.sources i)).card : ℝ) *
        ((TrackD.poolPts (T.targets i)).card : ℝ) ≤
        (chart.pool.S.card : ℝ) ^ 2 := by
      rw [hPt_eq]
      have e : (1 - ρ) ^ 2 *
          ((TrackD.poolPts (T.sources i)).card : ℝ) *
          ((TrackD.poolPts (T.sources i)).card : ℝ) =
          (((1 - ρ) * ((TrackD.poolPts (T.sources i)).card : ℝ)) ^ 2) := by
        ring
      rw [e]
      exact pow_le_pow_left₀
        (mul_nonneg h1ρ.le (Nat.cast_nonneg _)) chart.pool.hScard 2
    have hLam_dense : ρ' / (2 * (2 * (d : ℝ) + 1)) * (1 - ρ) ^ 2 *
        ((TrackD.poolPts (T.sources i)).card : ℝ) *
        ((TrackD.poolPts (T.targets i)).card : ℝ) ≤ (Lam.card : ℝ) := by
      have hCle : (((Finset.Icc (2 * k + 1) (2 * d)).card : ℕ) : ℝ) ≤
          2 * (d : ℝ) + 1 := hCnt_le
      have hnn : (0 : ℝ) ≤ ρ' * (chart.pool.S.card : ℝ) ^ 2 :=
        mul_nonneg hρ'.le (sq_nonneg _)
      have hstep : ρ' / (2 * (2 * (d : ℝ) + 1)) * (chart.pool.S.card : ℝ) ^ 2 ≤
          ρ' / (2 * (((Finset.Icc (2 * k + 1) (2 * d)).card : ℕ) : ℝ)) *
            (chart.pool.S.card : ℝ) ^ 2 := by
        have h2Cle : 2 * (((Finset.Icc (2 * k + 1) (2 * d)).card : ℕ) : ℝ) ≤
            2 * (2 * (d : ℝ) + 1) := by
          have hCle' : (((Finset.Icc (2 * k + 1) (2 * d)).card : ℕ) : ℝ) ≤
              2 * (d : ℝ) + 1 := hCnt_le
          linarith
        have hDpos : (0 : ℝ) < 2 * (2 * (d : ℝ) + 1) := by positivity
        have hC2pos' : (0 : ℝ) <
            2 * (((Finset.Icc (2 * k + 1) (2 * d)).card : ℕ) : ℝ) :=
          mul_pos two_pos hCpos
        have hle : ρ' / (2 * (2 * (d : ℝ) + 1)) ≤
            ρ' / (2 * (((Finset.Icc (2 * k + 1) (2 * d)).card : ℕ) : ℝ)) :=
          div_le_div_of_nonneg_left hρ'.le hC2pos' h2Cle
        exact mul_le_mul_of_nonneg_right hle (sq_nonneg _)
      have hmid : ρ' / (2 * (2 * (d : ℝ) + 1)) * ((1 - ρ) ^ 2 *
          ((TrackD.poolPts (T.sources i)).card : ℝ) *
          ((TrackD.poolPts (T.targets i)).card : ℝ)) ≤
          ρ' / (2 * (((Finset.Icc (2 * k + 1) (2 * d)).card : ℕ) : ℝ)) *
            (chart.pool.S.card : ℝ) ^ 2 :=
        (mul_le_mul_of_nonneg_left hSq_conv
          (div_nonneg hρ'.le (le_of_lt (show (0:ℝ) < 2 * (2 * (d:ℝ) + 1) by
            linarith [hdposR])))).trans hstep
      have hfin : ρ' / (2 * (2 * (d : ℝ) + 1)) * ((1 - ρ) ^ 2 *
          ((TrackD.poolPts (T.sources i)).card : ℝ) *
          ((TrackD.poolPts (T.targets i)).card : ℝ)) < (Lam.card : ℝ) :=
        lt_of_le_of_lt hmid hLam_gt
      have hrearr : ρ' / (2 * (2 * (d : ℝ) + 1)) * (1 - ρ) ^ 2 *
          ((TrackD.poolPts (T.sources i)).card : ℝ) *
          ((TrackD.poolPts (T.targets i)).card : ℝ) =
          ρ' / (2 * (2 * (d : ℝ) + 1)) * ((1 - ρ) ^ 2 *
            ((TrackD.poolPts (T.sources i)).card : ℝ) *
            ((TrackD.poolPts (T.targets i)).card : ℝ)) := by ring
      rw [hrearr]
      exact le_of_lt hfin
    -- Λ sits in the pool product and satisfies the chart test.
    have hLam_prod : Lam ⊆ TrackD.poolPts (T.sources i) ×ˢ TrackD.poolPts (T.targets i) := by
      intro pq hpq
      have hmem : pq ∈ Badh := hLam_sub hpq
      have hG : pq ∈ chart.G := hBadsub (hBadh_sub hmem)
      have h12 := chart.hGmem pq hG
      have hS1 : pq.1 ∈ TrackD.poolPts (T.sources i) :=
        chart.pool.hSsub h12.1
      have hS2 : pq.2 ∈ TrackD.poolPts (T.targets i) := by
        rw [← houter_eq]
        exact chart.pool.hSsub h12.2
      exact Finset.mem_product.mpr ⟨hS1, hS2⟩
    have hLam_chart : ∀ pq ∈ Lam, (TrackD.toC pq.2 - TrackD.toC pq.1) i₀ ≠ 0 := by
      intro pq hpq
      have hmem : pq ∈ Badh := by
        rw [hLamdef] at hpq
        exact (Finset.mem_filter.mp hpq).1
      have hG : pq ∈ chart.G := hBadsub (hBadh_sub hmem)
      exact chart.hchart pq hG
    have hRankLe : commonRankTarget M i τ' * Real.exp (-ε * M.s i) ≤
        commonLabelRank i₀ Lam ⌊TrackD.testDeg (regime.B i) (M.s i) τ'⌋₊ :=
      hRank i₀ Lam hLam_prod hLam_chart hLam_dense
    -- Propagation: `H_V` lower via `Gh` vs upper via `U`; `s`-large contradiction.
    -- Set `B,s,T₀,T',L₀,E',e,D` and positivity.
    set B : ℝ := regime.B i with hBdef
    set s : ℝ := M.s i with hsdef
    have hBs : s = Real.log B := hs i
    have hBge2 : (2 : ℝ) ≤ B := hBge
    have hBpos : (0 : ℝ) < B := by linarith
    have hB1 : (1 : ℝ) < B := by linarith
    have hspos : (0 : ℝ) < s := by
      rw [hBs]
      exact Real.log_pos hB1
    have hBne : B ≠ 0 := ne_of_gt hBpos
    have hexpB : Real.exp s = B := by
      rw [hBs]
      exact Real.exp_log hBpos
    set T0 : ℝ := TrackD.testDeg B s t₀ with hT0def
    set T' : ℝ := TrackD.testDeg B s τ' with hT'def
    have hT0pos : (0 : ℝ) < T0 := TrackD.RankCore.testDeg_pos hBpos _ _
    have hT'pos : (0 : ℝ) < T' := TrackD.RankCore.testDeg_pos hBpos _ _
    have hT0ge2 : (2 : ℝ) ≤ T0 := hTge
    have hT0ge1 : (1 : ℝ) ≤ T0 := by linarith
    set L0 : ℕ := T0n with hL0def
    have hL0eq : L0 = ⌊T0⌋₊ := hT0eq
    have hL0ge : T0 / 2 ≤ (L0 : ℝ) := hfl.2.1
    have hL0pos1 : (1 : ℝ) ≤ (L0 : ℝ) := by
      have := hT01
      exact_mod_cast this
    set E' : ℕ := ⌊T'⌋₊ with hE'def
    have hE'le : (E' : ℝ) ≤ T' := Nat.floor_le hT'pos.le
    set e : ℝ := TrackD.eScale B s M.b (j + 1) with hedef
    have hepos : (0 : ℝ) < e := by
      unfold e TrackD.eScale
      apply Finset.prod_pos
      intro a _
      exact TrackD.RankCore.testDeg_pos hBpos _ _
    have henn : (0 : ℝ) ≤ e := hepos.le
    set D0 : ℝ := TrackD.cutScale B s M.b ⟨0, by omega⟩ with hD0def
    set D1 : ℝ := TrackD.cutScale B s M.b ⟨1, by omega⟩ with hD1def
    have hD0pos : (0 : ℝ) < D0 := TrackD.RankCore.testDeg_pos hBpos _ _
    have hD1pos : (0 : ℝ) < D1 := TrackD.RankCore.testDeg_pos hBpos _ _
    have hDpos : (0 : ℝ) < D0 * D1 := mul_pos hD0pos hD1pos
    have hDge1 : (1 : ℝ) ≤ D0 * D1 := by
      have hb0low : (-1 : ℝ) ≤ M.b ⟨0, by omega⟩ := common_profile_time_lower M _
      have hb1low : (-1 : ℝ) ≤ M.b ⟨1, by omega⟩ := common_profile_time_lower M _
      have hD0ge1 : (1 : ℝ) ≤ D0 := by
        unfold D0 TrackD.cutScale TrackD.testDeg
        have : (0 : ℝ) ≤ (M.b ⟨0, by omega⟩ + 1) * s := by
          have h1 : (0 : ℝ) ≤ M.b ⟨0, by omega⟩ + 1 := by linarith
          exact mul_nonneg h1 hspos.le
        calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
          _ ≤ Real.exp ((M.b ⟨0, by omega⟩ + 1) * s) := Real.exp_le_exp.mpr (by linarith)
          _ = B * Real.exp (M.b ⟨0, by omega⟩ * s) := by
              rw [show (M.b ⟨0, by omega⟩ + 1) * s = M.b ⟨0, by omega⟩ * s + s by ring,
                Real.exp_add, hexpB]
              ring
      have hD1ge1 : (1 : ℝ) ≤ D1 := by
        unfold D1 TrackD.cutScale TrackD.testDeg
        have : (0 : ℝ) ≤ (M.b ⟨1, by omega⟩ + 1) * s := by
          have h1 : (0 : ℝ) ≤ M.b ⟨1, by omega⟩ + 1 := by linarith
          exact mul_nonneg h1 hspos.le
        calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
          _ ≤ Real.exp ((M.b ⟨1, by omega⟩ + 1) * s) := Real.exp_le_exp.mpr (by linarith)
          _ = B * Real.exp (M.b ⟨1, by omega⟩ * s) := by
              rw [show (M.b ⟨1, by omega⟩ + 1) * s = M.b ⟨1, by omega⟩ * s + s by ring,
                Real.exp_add, hexpB]
              ring
      calc (1 : ℝ) = 1 * 1 := (mul_one _).symm
        _ ≤ D0 * D1 := mul_le_mul hD0ge1 hD1ge1 zero_le_one (le_trans zero_le_one hD0ge1)
    have hj_lt : j < d := hj
    have hkj' : k + j + 1 = d := hkj
    have hk1 : 1 ≤ k := hk.1
    have hk_eq : d - (j + 1) = k := by omega
    have hτ'1 : τ' < 1 := by
      have hβt0 : M.b ⟨j, hj⟩ < t₀ := ht₀β
      have h1 : τ' < M.b ⟨j, hj⟩ := hτ'lt
      linarith [ht₀1, hβt0, h1]
    have hT0T'ge1 : (1 : ℝ) ≤ T0 / T' := by
      rw [le_div_iff₀ hT'pos]
      have hle : τ' ≤ t₀ := by
        have h1 : τ' < M.b ⟨j, hj⟩ := hτ'lt
        have h2 : M.b ⟨j, hj⟩ < t₀ := ht₀β
        linarith
      have := TrackD.RankCore.testDeg_mono hBpos.le hspos.le hle (B := B) (s := s)
      simpa [hT0def, hT'def] using this
    have hT0T'pos : (0 : ℝ) < T0 / T' := lt_of_lt_of_le (by norm_num) hT0T'ge1
    -- `Gh`: envelope components carrying `Badh`.
    set Gh : AffineFamily.Family (d + d) := Badh.image V with hGhdef
    have hGh_subB' : Gh ⊆ Bridges.envelopeComponents Tup T0n := by
      intro W hW
      obtain ⟨pq, hpq, rfl⟩ := Finset.mem_image.mp hW
      have hpqBad : pq ∈ Bad := hBadh_sub hpq
      exact hVmem pq hpqBad
    have hGh_sub : Gh ⊆ TrackD.envelopeComponents Tup T0n := hGh_subB'
    have hGh_pure : AffineFamily.IsPure Gh h := by
      intro W hW
      obtain ⟨pq, hpq, rfl⟩ := Finset.mem_image.mp hW
      have hpqBad : pq ∈ Bad := hBadh_sub hpq
      have hdim : (V pq).dimension = h := (Finset.mem_filter.mp hpq).2
      exact ⟨hVirr pq hpqBad, hdim⟩
    -- Labels of `Lam` lie in `locus Gh`.
    have hlabels_sub : commonLabelPoints i₀ Lam ⊆ (AffineFamily.locus Gh).points := by
      intro y hy
      obtain ⟨pq, hpq, rfl⟩ := hy
      have hpqcoe : pq ∈ (Badh : Set (RPoint d × RPoint d)) := by
        have : pq ∈ Lam := Finset.mem_coe.mp hpq
        exact hLam_sub this
      have hpqBadh : pq ∈ Badh := Finset.mem_coe.mp hpqcoe
      have hpqBad : pq ∈ Bad := hBadh_sub hpqBadh
      have hpqG : pq ∈ chart.G := hBadsub hpqBad
      have hlab : (fun kk => TrackD.labelPt i₀ (TrackD.toC pq.1) (TrackD.toC pq.2)
          (finSumFinEquiv.symm kk)) ∈
          (commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2)).points :=
        chart.hlabel pq hpqG
      have hsub : (commonProductImage i₀ (chart.W.owner i pq.1)
          (chart.W.owner i pq.2)).points ⊆ (V pq).points :=
        (AffineVariety.subvariety_iff_points_subset _ _).mp (hVsub pq hpqBad)
      have hyV : (fun kk => TrackD.labelPt i₀ (TrackD.toC pq.1) (TrackD.toC pq.2)
          (finSumFinEquiv.symm kk)) ∈ (V pq).points := hsub hlab
      have hVmemGh : V pq ∈ Gh := Finset.mem_image_of_mem V hpqBadh
      rw [AffineFamily.points_locus]
      exact Set.mem_iUnion₂.mpr ⟨V pq, hVmemGh, hyV⟩
    -- Hilbert comparison for `Gh` (lower for `Tup`, upper for labels).
    have hcomp_inst := hcomp Tup (commonLabelPoints i₀ Lam) T0n h hT01 Gh hGh_sub hGh_pure hlabels_sub
    obtain ⟨hlower, hupper⟩ := hcomp_inst
    -- Bridge rank = Hilbert.
    have hbridge : commonLabelRank i₀ Lam E' = hilbertOfSet (commonLabelPoints i₀ Lam) E' :=
      outer_rank_eq_hilbertOfSet i₀ Lam E'
    -- `σ` lower bound at `τ'`.
    have hτ'mem' : M.b ⟨j, hj⟩ - κ < τ' ∧ τ' < M.b ⟨j, hj⟩ := ⟨hτ'mem, hτ'lt⟩
    have hsigma_lo := outer_sigma_lower M j k hkj hj τ' κ hκpos hτ'mem' htop hτ'1 i hspos hBpos
    -- Target factorization at `τ'`.
    have htarg_eq : commonRankTarget M i τ' =
        (TrackD.sigma (regime.B i) (M.s i) M.b τ') ^ 2 *
        min 1 (T' / (D0 * D1)) := rfl
    have hD_eq : D0 * D1 = TrackD.cutScale (regime.B i) (M.s i) M.b ⟨0, by omega⟩ *
        TrackD.cutScale (regime.B i) (M.s i) M.b ⟨1, by omega⟩ := rfl
    -- Degree lower from rank.
    have hchoose_pos : (0 : ℝ) < (((E' + h).choose h : ℕ) : ℝ) := by
      have : 0 < (E' + h).choose h := Nat.choose_pos (Nat.le_add_left _ _)
      exact_mod_cast this
    have hrank_up : ((commonLabelRank i₀ Lam E' : ℕ) : ℝ) ≤
        ((AffineFamily.degree Gh : ℚ) : ℝ) * (((E' + h).choose h : ℕ) : ℝ) := by
      have h1 := hupper E'
      rw [← hbridge] at h1
      exact h1
    have hdeg_lo : commonRankTarget M i τ' * Real.exp (-ε * s) /
        (((E' + h).choose h : ℕ) : ℝ) ≤ ((AffineFamily.degree Gh : ℚ) : ℝ) := by
      rw [div_le_iff₀ hchoose_pos]
      calc commonRankTarget M i τ' * Real.exp (-ε * s)
          ≤ ((commonLabelRank i₀ Lam E' : ℕ) : ℝ) := by
            have h2 : commonRankTarget M i τ' * Real.exp (-ε * M.s i) ≤
                ((commonLabelRank i₀ Lam E' : ℕ) : ℝ) := by
              have := hRankLe
              simpa [hsdef, hE'def] using this
            simpa [hsdef] using h2
        _ ≤ ((AffineFamily.degree Gh : ℚ) : ℝ) * (((E' + h).choose h : ℕ) : ℝ) := hrank_up
    -- `H` upper via `U`.
    have hUpure : AffineFamily.IsPure chart.U (2 * k) := by
      intro W hW
      exact chart.hU W hW
    have hTup_eq : Tup = (AffineFamily.locus chart.U).points := by
      rw [AffineFamily.points_locus]
    have hclosure_le : (AffineVariety.closure Tup).Subvariety (AffineFamily.locus chart.U) :=
      TrackD.closure_subvariety_of_subset _ (hTup_eq ▸ Set.Subset.rfl)
    have hHle_hilbertU : (hilbertOfSet Tup T0n : ℝ) ≤ ((AffineFamily.hilbert chart.U T0n : ℕ) : ℝ) := by
      have hmono := AffineVariety.hilbert_mono (AffineVariety.closure Tup)
        (AffineFamily.locus chart.U) hclosure_le T0n
      exact_mod_cast hmono
    have hhilbU_up : ((AffineFamily.hilbert chart.U T0n : ℕ) : ℝ) ≤
        ((AffineFamily.degree chart.U : ℚ) : ℝ) * (((T0n + 2 * k).choose (2 * k) : ℕ) : ℝ) := by
      have hupQ := TrackA.poly_hilbert_upper (n := d + d) chart.U (2 * k) hUpure T0n
      have hmove : ((((AffineFamily.hilbert chart.U T0n : ℕ) : ℚ)) : ℝ) ≤
          ((AffineFamily.degree chart.U * (((T0n + 2 * k).choose (2 * k) : ℕ) : ℚ) : ℚ) : ℝ) := by
        exact_mod_cast hupQ
      simpa [Rat.cast_natCast] using hmove
    have hdegU_le : ((AffineFamily.degree chart.U : ℚ) : ℝ) ≤
        (1 + ρ) * e ^ 2 * Real.exp (ε * s) := by
      have h1 := chart.hUdeg
      have he_eq2 : TrackD.eScale (regime.B i) (M.s i) M.b (j + 1) = e := rfl
      simpa [he_eq2, hsdef, hBdef] using h1
    have henv_eq : (DistinctDistances.envelope Tup T0n).hilbert T0n = hilbertOfSet Tup T0n :=
      DistinctDistances.envelope_hilbert Tup T0n
    -- Combine into `min` inequality; split on `T' ≥ 1`.
    have hVenv_eq : Venv = DistinctDistances.envelope Tup T0n := rfl
    by_cases hT'ge1 : (1 : ℝ) ≤ T'
    · -- `T' ≥ 1`: both chooses bounded by `(2T')^h`, `(2T₀)^{2k}`.
      have hE'ge1 : 1 ≤ E' := Nat.le_floor (by simpa [hE'def] using hT'ge1)
      have hE'leT' : (E' : ℝ) ≤ T' := hE'le
      have hchoose1_le : (((E' + h).choose h : ℕ) : ℝ) ≤ (2 * T') ^ h := by
        have h1 := common_choose_le_pow E' h
        have hE1le : ((E' + 1 : ℕ) : ℝ) ≤ 2 * T' := by
          have hE1 : ((E' + 1 : ℕ) : ℝ) = (E' : ℝ) + 1 := by push_cast; ring
          rw [hE1]
          linarith [hE'leT', hT'ge1]
        calc (((E' + h).choose h : ℕ) : ℝ) ≤ ((E' + 1 : ℕ) : ℝ) ^ h := h1
          _ ≤ (2 * T') ^ h := pow_le_pow_left₀ (by positivity) hE1le _
      have hchoose2_le : (((T0n + 2 * k).choose (2 * k) : ℕ) : ℝ) ≤ (2 * T0) ^ (2 * k) := by
        have h1 := common_choose_le_pow T0n (2 * k)
        have hT1le : ((T0n + 1 : ℕ) : ℝ) ≤ 2 * T0 := by
          have hT0n_le : (T0n : ℝ) ≤ T0 := Nat.floor_le hT0pos.le
          have h1le : (1 : ℝ) ≤ T0 := hT0ge1
          have hcast : ((T0n + 1 : ℕ) : ℝ) = (T0n : ℝ) + 1 := by push_cast; ring
          rw [hcast]
          linarith
        calc (((T0n + 2 * k).choose (2 * k) : ℕ) : ℝ) ≤ ((T0n + 1 : ℕ) : ℝ) ^ (2 * k) := h1
          _ ≤ (2 * T0) ^ (2 * k) := pow_le_pow_left₀ (by positivity) hT1le _
      have hL0pow : (T0 / 2) ^ h ≤ (L0 : ℝ) ^ h :=
        pow_le_pow_left₀ (by positivity) hL0ge _
      -- `σ'` lower gives target lower with `e²`.
      have htarget_lo : e ^ 2 * T' ^ (2 * k) * Real.exp (-2 * (d : ℝ) * κ * s) *
          min 1 (T' / (D0 * D1)) ≤ commonRankTarget M i τ' := by
        rw [htarg_eq]
        have hsig2 : (e * T' ^ k * Real.exp (-(d : ℝ) * κ * s)) ^ 2 ≤
            (TrackD.sigma (regime.B i) (M.s i) M.b τ') ^ 2 := by
          apply pow_le_pow_left₀ (by positivity) hsigma_lo 2
        calc e ^ 2 * T' ^ (2 * k) * Real.exp (-2 * (d : ℝ) * κ * s) * min 1 (T' / (D0 * D1))
            = (e * T' ^ k * Real.exp (-(d : ℝ) * κ * s)) ^ 2 * min 1 (T' / (D0 * D1)) := by
              have hT : T' ^ (2 * k) = (T' ^ k) ^ 2 := by
                rw [mul_comm 2 k, pow_mul]
              have hE : Real.exp (-2 * (d : ℝ) * κ * s) =
                  (Real.exp (-(d : ℝ) * κ * s)) ^ 2 := by
                rw [pow_two, ← Real.exp_add]
                congr 1
                ring
              rw [hT, hE, mul_pow, mul_pow]
          _ ≤ _ := mul_le_mul_of_nonneg_right hsig2 (le_min zero_le_one (le_of_lt (div_pos hT'pos hDpos)))
      -- Chain to `min(T₀/T',T₀/D)` bound.
      have hmain : c0 * (T0 / T') ^ (h - 2 * k) * min 1 (T' / (D0 * D1)) ≤
          (1 + ρ) * (2 : ℝ) ^ (2 * h + 2 * k) * Real.exp ((2 * ε + 2 * (d : ℝ) * κ) * s) := by
        have h2k_le_h : 2 * k ≤ h := by omega
        have he2pos' : (0 : ℝ) < e ^ 2 := sq_pos_of_pos hepos
        have hC1pos' : (0 : ℝ) < (((E' + h).choose h : ℕ) : ℝ) := hchoose_pos
        have hT'ne : T' ≠ 0 := ne_of_gt hT'pos
        have hc0nn : (0 : ℝ) ≤ c0 := hc0pos.le
        -- Upper bound for `H(Tup)`.
        have hHup : (hilbertOfSet Tup T0n : ℝ) ≤
            (1 + ρ) * e ^ 2 * Real.exp (ε * s) * (2 * T0) ^ (2 * k) := by
          calc (hilbertOfSet Tup T0n : ℝ)
              ≤ ((AffineFamily.hilbert chart.U T0n : ℕ) : ℝ) := hHle_hilbertU
            _ ≤ ((AffineFamily.degree chart.U : ℚ) : ℝ) *
                (((T0n + 2 * k).choose (2 * k) : ℕ) : ℝ) := hhilbU_up
            _ ≤ ((1 + ρ) * e ^ 2 * Real.exp (ε * s)) * (2 * T0) ^ (2 * k) := by
                apply mul_le_mul hdegU_le hchoose2_le (Nat.cast_nonneg _) (by positivity)
        -- Family degree of `Gh` is nonnegative.
        have hdegGh_nn : (0 : ℝ) ≤ ((AffineFamily.degree Gh : ℚ) : ℝ) := by
          have h1 : (0 : ℚ) ≤ AffineFamily.degree Gh := by
            unfold AffineFamily.degree
            apply Finset.sum_nonneg
            intro V hV
            obtain ⟨hirr, _⟩ := hGh_pure V hV
            have hprime : V.ideal.IsPrime := hirr
            have hle : (1 : ℚ) ≤ V.degree :=
              V.one_le_degree (Ideal.IsPrime.ne_top hprime)
            linarith
          exact_mod_cast h1
        have hL0nn : (0 : ℝ) ≤ (L0 : ℝ) ^ h := pow_nonneg (Nat.cast_nonneg _) _
        have hexp_eps_nn : (0 : ℝ) ≤ Real.exp (-ε * s) := Real.exp_nonneg _
        -- `c₀·deg·L₀^h ≤ H`.
        have hHlow : c0 * ((AffineFamily.degree Gh : ℚ) : ℝ) * (L0 : ℝ) ^ h ≤
            (hilbertOfSet Tup T0n : ℝ) := by
          have h2 := hlower
          simpa [hL0def] using h2
        -- Replace `deg` by the rank lower bound.
        have hstep_deg : c0 * (commonRankTarget M i τ' * Real.exp (-ε * s) /
            (((E' + h).choose h : ℕ) : ℝ)) * (L0 : ℝ) ^ h ≤
            (hilbertOfSet Tup T0n : ℝ) := by
          calc c0 * (commonRankTarget M i τ' * Real.exp (-ε * s) /
                (((E' + h).choose h : ℕ) : ℝ)) * (L0 : ℝ) ^ h
              ≤ c0 * ((AffineFamily.degree Gh : ℚ) : ℝ) * (L0 : ℝ) ^ h := by
                apply mul_le_mul_of_nonneg_right _ hL0nn
                exact mul_le_mul_of_nonneg_left hdeg_lo hc0nn
            _ ≤ _ := hHlow
        -- Replace `target'` by the `e²` lower bound (same denominator).
        have hstep_tgt : c0 * ((e ^ 2 * T' ^ (2 * k) * Real.exp (-2 * (d : ℝ) * κ * s) *
            min 1 (T' / (D0 * D1))) * Real.exp (-ε * s) /
            (((E' + h).choose h : ℕ) : ℝ)) * (L0 : ℝ) ^ h ≤
            (hilbertOfSet Tup T0n : ℝ) := by
          have hle : (e ^ 2 * T' ^ (2 * k) * Real.exp (-2 * (d : ℝ) * κ * s) *
              min 1 (T' / (D0 * D1))) * Real.exp (-ε * s) /
              (((E' + h).choose h : ℕ) : ℝ) ≤
              commonRankTarget M i τ' * Real.exp (-ε * s) /
              (((E' + h).choose h : ℕ) : ℝ) :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right htarget_lo hexp_eps_nn) hC1pos'.le
          calc c0 * (((e ^ 2 * T' ^ (2 * k) * Real.exp (-2 * (d : ℝ) * κ * s) *
                min 1 (T' / (D0 * D1))) * Real.exp (-ε * s) /
                (((E' + h).choose h : ℕ) : ℝ))) * (L0 : ℝ) ^ h
              ≤ c0 * (commonRankTarget M i τ' * Real.exp (-ε * s) /
                (((E' + h).choose h : ℕ) : ℝ)) * (L0 : ℝ) ^ h := by
                apply mul_le_mul_of_nonneg_right _ hL0nn
                exact mul_le_mul_of_nonneg_left hle hc0nn
            _ ≤ _ := hstep_deg
        -- Replace `L₀^h / C₁` by `(T₀/2)^h / (2T')^h`.
        have hfrac_ge : (T0 / 2) ^ h / (2 * T') ^ h ≤
            (L0 : ℝ) ^ h / (((E' + h).choose h : ℕ) : ℝ) :=
          div_le_div₀ hL0nn hL0pow hC1pos' hchoose1_le
        have hnum_nn : (0 : ℝ) ≤ (e ^ 2 * T' ^ (2 * k) * Real.exp (-2 * (d : ℝ) * κ * s) *
            min 1 (T' / (D0 * D1))) * Real.exp (-ε * s) := by positivity
        have hstep_frac : c0 * ((e ^ 2 * T' ^ (2 * k) * Real.exp (-2 * (d : ℝ) * κ * s) *
            min 1 (T' / (D0 * D1))) * Real.exp (-ε * s)) * ((T0 / 2) ^ h / (2 * T') ^ h) ≤
            (hilbertOfSet Tup T0n : ℝ) := by
          calc c0 * ((e ^ 2 * T' ^ (2 * k) * Real.exp (-2 * (d : ℝ) * κ * s) *
              min 1 (T' / (D0 * D1))) * Real.exp (-ε * s)) * ((T0 / 2) ^ h / (2 * T') ^ h)
              ≤ c0 * ((e ^ 2 * T' ^ (2 * k) * Real.exp (-2 * (d : ℝ) * κ * s) *
              min 1 (T' / (D0 * D1))) * Real.exp (-ε * s)) *
              ((L0 : ℝ) ^ h / (((E' + h).choose h : ℕ) : ℝ)) :=
              mul_le_mul_of_nonneg_left hfrac_ge (mul_nonneg hc0nn hnum_nn)
            _ = c0 * (((e ^ 2 * T' ^ (2 * k) * Real.exp (-2 * (d : ℝ) * κ * s) *
              min 1 (T' / (D0 * D1))) * Real.exp (-ε * s) /
              (((E' + h).choose h : ℕ) : ℝ))) * (L0 : ℝ) ^ h := by ring
            _ ≤ _ := hstep_tgt
        -- Power identities.
        have hpow_div : (T0 / 2) ^ h / (2 * T') ^ h = (T0 / T') ^ h / (4 : ℝ) ^ h := by
          have h4 : (4 : ℝ) ^ h = (2 : ℝ) ^ h * (2 : ℝ) ^ h := by
            rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
          have hden : (2 : ℝ) ^ h * (2 ^ h * T' ^ h) = T' ^ h * (2 ^ h * 2 ^ h) := by ring
          rw [div_pow, div_pow, mul_pow, h4, div_div, div_div, hden]
        have hsplit : (T0 / T') ^ h = (T0 / T') ^ (2 * k) * (T0 / T') ^ (h - 2 * k) := by
          conv_lhs => rw [← Nat.add_sub_cancel' h2k_le_h]
          rw [pow_add]
        have hbase : T' ^ (2 * k) * (T0 / T') ^ (2 * k) = T0 ^ (2 * k) := by
          rw [← mul_pow]
          have hcancel : T' * (T0 / T') = T0 := mul_div_cancel₀ T0 hT'ne
          rw [hcancel]
        have hcombine : T' ^ (2 * k) * (T0 / T') ^ h =
            T0 ^ (2 * k) * (T0 / T') ^ (h - 2 * k) := by
          rw [hsplit, ← mul_assoc, hbase]
        have hexp_merge : Real.exp (-2 * (d : ℝ) * κ * s) * Real.exp (-ε * s) =
            Real.exp (-(ε + 2 * (d : ℝ) * κ) * s) := by
          rw [← Real.exp_add]
          congr 1
          ring
        -- Fold to a single lower bound with `E₁ = exp(-(ε+2dκ)s)`.
        set E1 : ℝ := Real.exp (-(ε + 2 * (d : ℝ) * κ) * s) with hE1def
        have hE1pos : (0 : ℝ) < E1 := Real.exp_pos _
        have hHlow2 : c0 * (T0 ^ (2 * k) * (T0 / T') ^ (h - 2 * k)) *
            min 1 (T' / (D0 * D1)) * E1 * (e ^ 2 / (4 : ℝ) ^ h) ≤
            (hilbertOfSet Tup T0n : ℝ) := by
          have hbridge : c0 * (T0 ^ (2 * k) * (T0 / T') ^ (h - 2 * k)) *
              min 1 (T' / (D0 * D1)) * E1 * (e ^ 2 / (4 : ℝ) ^ h) =
              c0 * (((e ^ 2 * T' ^ (2 * k) * Real.exp (-2 * (d : ℝ) * κ * s) *
              min 1 (T' / (D0 * D1))) * Real.exp (-ε * s)) * ((T0 / T') ^ h / (4 : ℝ) ^ h)) := by
            rw [← hexp_merge, ← hcombine]
            ring
          have hfrom_frac : c0 * (((e ^ 2 * T' ^ (2 * k) * Real.exp (-2 * (d : ℝ) * κ * s) *
              min 1 (T' / (D0 * D1))) * Real.exp (-ε * s)) * ((T0 / T') ^ h / (4 : ℝ) ^ h)) ≤
              (hilbertOfSet Tup T0n : ℝ) := by
            have htmp : c0 * (((e ^ 2 * T' ^ (2 * k) * Real.exp (-2 * (d : ℝ) * κ * s) *
                min 1 (T' / (D0 * D1))) * Real.exp (-ε * s)) * ((T0 / 2) ^ h / (2 * T') ^ h)) ≤
                (hilbertOfSet Tup T0n : ℝ) := by
              have heq0 : ((e ^ 2 * T' ^ (2 * k) * Real.exp (-2 * (d : ℝ) * κ * s) *
                  min 1 (T' / (D0 * D1))) * Real.exp (-ε * s)) * ((T0 / 2) ^ h / (2 * T') ^ h) =
                  ((e ^ 2 * T' ^ (2 * k) * Real.exp (-2 * (d : ℝ) * κ * s) *
                  min 1 (T' / (D0 * D1))) * Real.exp (-ε * s)) * ((T0 / 2) ^ h / (2 * T') ^ h) := rfl
              calc c0 * (((e ^ 2 * T' ^ (2 * k) * Real.exp (-2 * (d : ℝ) * κ * s) *
                  min 1 (T' / (D0 * D1))) * Real.exp (-ε * s)) * ((T0 / 2) ^ h / (2 * T') ^ h))
                  = c0 * ((e ^ 2 * T' ^ (2 * k) * Real.exp (-2 * (d : ℝ) * κ * s) *
                  min 1 (T' / (D0 * D1))) * Real.exp (-ε * s)) * ((T0 / 2) ^ h / (2 * T') ^ h) := by
                    ring
                _ ≤ _ := hstep_frac
            calc c0 * (((e ^ 2 * T' ^ (2 * k) * Real.exp (-2 * (d : ℝ) * κ * s) *
                min 1 (T' / (D0 * D1))) * Real.exp (-ε * s)) * ((T0 / T') ^ h / (4 : ℝ) ^ h))
                = c0 * (((e ^ 2 * T' ^ (2 * k) * Real.exp (-2 * (d : ℝ) * κ * s) *
                min 1 (T' / (D0 * D1))) * Real.exp (-ε * s)) * ((T0 / 2) ^ h / (2 * T') ^ h)) := by
                  rw [hpow_div]
                _ ≤ _ := htmp
          rw [hbridge]
          exact hfrom_frac
        -- Write the upper bound with `(2T₀)^{2k} = 2^{2k}T₀^{2k}`.
        have h2T0 : (2 * T0) ^ (2 * k) = (2 : ℝ) ^ (2 * k) * T0 ^ (2 * k) := by
          rw [mul_pow]
        rw [h2T0] at hHup
        have h4eq : (4 : ℝ) ^ h = (2 : ℝ) ^ (2 * h) := by
          rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← pow_mul]
        have h2add : (2 : ℝ) ^ (2 * h + 2 * k) = (2 : ℝ) ^ (2 * h) * (2 : ℝ) ^ (2 * k) := by
          rw [pow_add]
        -- Cancel the common positive factor `C = e²·T₀^{2k}/4^h`.
        set C0f : ℝ := e ^ 2 * T0 ^ (2 * k) / (4 : ℝ) ^ h with hC0fdef
        have hC0fpos : (0 : ℝ) < C0f := by positivity
        have hLHS_eq : c0 * (T0 ^ (2 * k) * (T0 / T') ^ (h - 2 * k)) *
            min 1 (T' / (D0 * D1)) * E1 * (e ^ 2 / (4 : ℝ) ^ h) =
            (c0 * (T0 / T') ^ (h - 2 * k) * min 1 (T' / (D0 * D1)) * E1) * C0f := by
          rw [hC0fdef]
          ring
        have hRHS_eq : (1 + ρ) * e ^ 2 * Real.exp (ε * s) * ((2 : ℝ) ^ (2 * k) * T0 ^ (2 * k)) =
            ((1 + ρ) * (2 : ℝ) ^ (2 * h + 2 * k) * Real.exp (ε * s)) * C0f := by
          rw [hC0fdef, h2add, h4eq]
          field_simp
        have hle2 : (c0 * (T0 / T') ^ (h - 2 * k) * min 1 (T' / (D0 * D1)) * E1) * C0f ≤
            ((1 + ρ) * (2 : ℝ) ^ (2 * h + 2 * k) * Real.exp (ε * s)) * C0f := by
          rw [← hLHS_eq, ← hRHS_eq]
          exact hHlow2.trans hHup
        have hmid : c0 * (T0 / T') ^ (h - 2 * k) * min 1 (T' / (D0 * D1)) * E1 ≤
            (1 + ρ) * (2 : ℝ) ^ (2 * h + 2 * k) * Real.exp (ε * s) :=
          le_of_mul_le_mul_right hle2 hC0fpos
        -- Multiply by `exp((ε+2dκ)s) = E₁⁻¹` to obtain `hmain`.
        have hE1inv : E1 * Real.exp ((ε + 2 * (d : ℝ) * κ) * s) = 1 := by
          rw [hE1def, ← Real.exp_add]
          have hz : -(ε + 2 * (d : ℝ) * κ) * s + (ε + 2 * (d : ℝ) * κ) * s = 0 := by ring
          rw [hz, Real.exp_zero]
        calc c0 * (T0 / T') ^ (h - 2 * k) * min 1 (T' / (D0 * D1))
            = (c0 * (T0 / T') ^ (h - 2 * k) * min 1 (T' / (D0 * D1)) * E1) *
              Real.exp ((ε + 2 * (d : ℝ) * κ) * s) := by
              have hback : (c0 * (T0 / T') ^ (h - 2 * k) * min 1 (T' / (D0 * D1)) * E1) *
                  Real.exp ((ε + 2 * (d : ℝ) * κ) * s) =
                  c0 * (T0 / T') ^ (h - 2 * k) * min 1 (T' / (D0 * D1)) := by
                calc (c0 * (T0 / T') ^ (h - 2 * k) * min 1 (T' / (D0 * D1)) * E1) *
                    Real.exp ((ε + 2 * (d : ℝ) * κ) * s)
                    = c0 * (T0 / T') ^ (h - 2 * k) * min 1 (T' / (D0 * D1)) *
                      (E1 * Real.exp ((ε + 2 * (d : ℝ) * κ) * s)) := by ring
                  _ = c0 * (T0 / T') ^ (h - 2 * k) * min 1 (T' / (D0 * D1)) * 1 := by
                      rw [hE1inv]
                  _ = c0 * (T0 / T') ^ (h - 2 * k) * min 1 (T' / (D0 * D1)) := by ring
              exact hback.symm
          _ ≤ ((1 + ρ) * (2 : ℝ) ^ (2 * h + 2 * k) * Real.exp (ε * s)) *
              Real.exp ((ε + 2 * (d : ℝ) * κ) * s) :=
              mul_le_mul_of_nonneg_right hmid (Real.exp_nonneg _)
          _ = (1 + ρ) * (2 : ℝ) ^ (2 * h + 2 * k) *
              Real.exp ((2 * ε + 2 * (d : ℝ) * κ) * s) := by
              rw [mul_assoc, ← Real.exp_add]
              congr 1
              ring
      -- Squeezing `hmain` against `S0` gives `False`.
      have hT0exp : T0 = Real.exp ((1 + t₀) * s) := by
        rw [hT0def]
        unfold TrackD.testDeg
        rw [← hexpB, ← Real.exp_add]
        congr 1
        ring
      have hTpexp : T' = Real.exp ((1 + τ') * s) := by
        rw [hT'def]
        unfold TrackD.testDeg
        rw [← hexpB, ← Real.exp_add]
        congr 1
        ring
      have hD0exp : D0 = Real.exp ((1 + M.b ⟨0, by omega⟩) * s) := by
        rw [hD0def]
        unfold TrackD.cutScale TrackD.testDeg
        rw [← hexpB, ← Real.exp_add]
        congr 1
        ring
      have hD1exp : D1 = Real.exp ((1 + M.b ⟨1, by omega⟩) * s) := by
        rw [hD1def]
        unfold TrackD.cutScale TrackD.testDeg
        rw [← hexpB, ← Real.exp_add]
        congr 1
        ring
      have hTT' : T0 / T' = Real.exp ((t₀ - τ') * s) := by
        rw [hT0exp, hTpexp, ← Real.exp_sub]
        congr 1
        ring
      have hDprod : D0 * D1 =
          Real.exp ((2 + M.b ⟨0, by omega⟩ + M.b ⟨1, by omega⟩) * s) := by
        rw [hD0exp, hD1exp, ← Real.exp_add]
        congr 1
        ring
      have hT0D : T0 / (D0 * D1) =
          Real.exp ((t₀ - (1 + M.b ⟨0, by omega⟩ + M.b ⟨1, by omega⟩)) * s) := by
        rw [hT0exp, hDprod, ← Real.exp_sub]
        congr 1
        ring
      have hq_ge : Real.exp ((t₀ - M.b ⟨j, hj⟩) * s) ≤ T0 / T' := by
        rw [hTT']
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_right _ hspos.le
        linarith [hτ'lt]
      have hD_ge : Real.exp ((t₀ - (1 + M.b ⟨0, by omega⟩ + M.b ⟨1, by omega⟩)) * s) ≤
          T0 / (D0 * D1) := by
        rw [hT0D]
      have hexp_min : Real.exp (min (t₀ - M.b ⟨j, hj⟩)
          (t₀ - (1 + M.b ⟨0, by omega⟩ + M.b ⟨1, by omega⟩)) * s) ≤
          min (T0 / T') (T0 / (D0 * D1)) := by
        apply le_min
        · calc Real.exp (min (t₀ - M.b ⟨j, hj⟩)
                (t₀ - (1 + M.b ⟨0, by omega⟩ + M.b ⟨1, by omega⟩)) * s) ≤
                Real.exp ((t₀ - M.b ⟨j, hj⟩) * s) := by
                apply Real.exp_le_exp.mpr
                apply mul_le_mul_of_nonneg_right _ hspos.le
                exact min_le_left _ _
            _ ≤ _ := hq_ge
        · calc Real.exp (min (t₀ - M.b ⟨j, hj⟩)
                (t₀ - (1 + M.b ⟨0, by omega⟩ + M.b ⟨1, by omega⟩)) * s) ≤
                Real.exp ((t₀ - (1 + M.b ⟨0, by omega⟩ + M.b ⟨1, by omega⟩)) * s) := by
                apply Real.exp_le_exp.mpr
                apply mul_le_mul_of_nonneg_right _ hspos.le
                exact min_le_right _ _
            _ ≤ _ := hD_ge
      have hR_ge : T0 / T' ≤ (T0 / T') ^ (h - 2 * k) := by
        have h1 : 1 ≤ h - 2 * k := by omega
        calc T0 / T' = (T0 / T') ^ 1 := (pow_one _).symm
          _ ≤ _ := pow_le_pow_right₀ hT0T'ge1 h1
      have hT'ne2 : T' ≠ 0 := ne_of_gt hT'pos
      have hmin_nn' : (0 : ℝ) ≤ min 1 (T' / (D0 * D1)) :=
        le_min zero_le_one (le_of_lt (div_pos hT'pos hDpos))
      have hRmin : min (T0 / T') (T0 / (D0 * D1)) ≤
          (T0 / T') ^ (h - 2 * k) * min 1 (T' / (D0 * D1)) := by
        have hq_nn : (0 : ℝ) ≤ T0 / T' := le_of_lt (div_pos hT0pos hT'pos)
        have hqr : (T0 / T') * (T' / (D0 * D1)) = T0 / (D0 * D1) := by
          calc (T0 / T') * (T' / (D0 * D1)) = T0 * (T' / T') / (D0 * D1) := by ring
            _ = T0 * 1 / (D0 * D1) := by rw [div_self hT'ne2]
            _ = T0 / (D0 * D1) := by ring
        calc min (T0 / T') (T0 / (D0 * D1))
            = min (T0 / T') ((T0 / T') * (T' / (D0 * D1))) := by rw [hqr]
          _ = min ((T0 / T') * 1) ((T0 / T') * (T' / (D0 * D1))) := by rw [mul_one]
          _ = (T0 / T') * min 1 (T' / (D0 * D1)) := (mul_min_of_nonneg _ _ hq_nn).symm
          _ ≤ (T0 / T') ^ (h - 2 * k) * min 1 (T' / (D0 * D1)) :=
              mul_le_mul_of_nonneg_right hR_ge hmin_nn'
      have hA : c0 * Real.exp (min (t₀ - M.b ⟨j, hj⟩)
          (t₀ - (1 + M.b ⟨0, by omega⟩ + M.b ⟨1, by omega⟩)) * s) ≤
          (1 + ρ) * 2 ^ (2 * h + 2 * k) * Real.exp ((2 * ε + 2 * (d : ℝ) * κ) * s) := by
        have hle : Real.exp (min (t₀ - M.b ⟨j, hj⟩)
            (t₀ - (1 + M.b ⟨0, by omega⟩ + M.b ⟨1, by omega⟩)) * s) ≤
            (T0 / T') ^ (h - 2 * k) * min 1 (T' / (D0 * D1)) :=
          hexp_min.trans hRmin
        calc c0 * Real.exp (min (t₀ - M.b ⟨j, hj⟩)
              (t₀ - (1 + M.b ⟨0, by omega⟩ + M.b ⟨1, by omega⟩)) * s)
            ≤ c0 * ((T0 / T') ^ (h - 2 * k) * min 1 (T' / (D0 * D1))) :=
              mul_le_mul_of_nonneg_left hle hc0pos.le
          _ = c0 * (T0 / T') ^ (h - 2 * k) * min 1 (T' / (D0 * D1)) := by ring
          _ ≤ _ := hmain
      have hsge' : S0 ≤ s := by simpa [hsdef] using hsge
      have hkk : (0 : ℝ) ≤ (2 * (k : ℝ) + 1) * κ := mul_nonneg (by positivity) hκpos.le
      have hexp_δ_le : Real.exp (δ * s) ≤
          Real.exp ((min (t₀ - M.b ⟨j, hj⟩)
            (t₀ - (1 + M.b ⟨0, by omega⟩ + M.b ⟨1, by omega⟩)) - (2 * ε + 2 * (d : ℝ) * κ)) * s) := by
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_right _ hspos.le
        rw [hδdef]
        linarith [hkk]
      have hpow : (2 : ℝ) ^ (2 * h + 2 * k) ≤ (2 : ℝ) ^ (6 * d) := by
        apply pow_le_pow_right₀ (by norm_num)
        omega
      have hc0ne : c0 ≠ 0 := ne_of_gt hc0pos
      have hC1le : (1 + ρ) * (2 : ℝ) ^ (2 * h + 2 * k) ≤ c0 * C0 := by
        have heq : c0 * C0 = (1 + ρ) * (2 : ℝ) ^ (6 * d) := by
          rw [hC0def]
          field_simp
        rw [heq]
        exact mul_le_mul_of_nonneg_left hpow (by positivity)
      have hexp_le_C0 : Real.exp ((min (t₀ - M.b ⟨j, hj⟩)
          (t₀ - (1 + M.b ⟨0, by omega⟩ + M.b ⟨1, by omega⟩)) - (2 * ε + 2 * (d : ℝ) * κ)) * s) ≤
          C0 := by
        have hD : Real.exp ((min (t₀ - M.b ⟨j, hj⟩)
            (t₀ - (1 + M.b ⟨0, by omega⟩ + M.b ⟨1, by omega⟩)) - (2 * ε + 2 * (d : ℝ) * κ)) * s) *
            Real.exp ((2 * ε + 2 * (d : ℝ) * κ) * s) =
            Real.exp (min (t₀ - M.b ⟨j, hj⟩)
              (t₀ - (1 + M.b ⟨0, by omega⟩ + M.b ⟨1, by omega⟩)) * s) := by
          rw [← Real.exp_add]
          congr 1
          ring
        have hA2 : (c0 * Real.exp ((min (t₀ - M.b ⟨j, hj⟩)
            (t₀ - (1 + M.b ⟨0, by omega⟩ + M.b ⟨1, by omega⟩)) - (2 * ε + 2 * (d : ℝ) * κ)) * s)) *
            Real.exp ((2 * ε + 2 * (d : ℝ) * κ) * s) ≤ (c0 * C0) *
            Real.exp ((2 * ε + 2 * (d : ℝ) * κ) * s) := by
          have heq2 : (c0 * Real.exp ((min (t₀ - M.b ⟨j, hj⟩)
              (t₀ - (1 + M.b ⟨0, by omega⟩ + M.b ⟨1, by omega⟩)) - (2 * ε + 2 * (d : ℝ) * κ)) * s)) *
              Real.exp ((2 * ε + 2 * (d : ℝ) * κ) * s) = c0 * Real.exp (min (t₀ - M.b ⟨j, hj⟩)
              (t₀ - (1 + M.b ⟨0, by omega⟩ + M.b ⟨1, by omega⟩)) * s) := by
            rw [mul_assoc, hD]
          have hle2 : c0 * Real.exp (min (t₀ - M.b ⟨j, hj⟩)
              (t₀ - (1 + M.b ⟨0, by omega⟩ + M.b ⟨1, by omega⟩)) * s) ≤ (c0 * C0) *
              Real.exp ((2 * ε + 2 * (d : ℝ) * κ) * s) := by
            calc c0 * Real.exp (min (t₀ - M.b ⟨j, hj⟩)
                  (t₀ - (1 + M.b ⟨0, by omega⟩ + M.b ⟨1, by omega⟩)) * s) ≤
                  (1 + ρ) * 2 ^ (2 * h + 2 * k) *
                  Real.exp ((2 * ε + 2 * (d : ℝ) * κ) * s) := hA
              _ = ((1 + ρ) * 2 ^ (2 * h + 2 * k)) *
                  Real.exp ((2 * ε + 2 * (d : ℝ) * κ) * s) := by ring
              _ ≤ (c0 * C0) * Real.exp ((2 * ε + 2 * (d : ℝ) * κ) * s) :=
                  mul_le_mul_of_nonneg_right hC1le (Real.exp_nonneg _)
          rw [heq2]
          exact hle2
        have hmid2 : c0 * Real.exp ((min (t₀ - M.b ⟨j, hj⟩)
            (t₀ - (1 + M.b ⟨0, by omega⟩ + M.b ⟨1, by omega⟩)) - (2 * ε + 2 * (d : ℝ) * κ)) * s) ≤
            c0 * C0 :=
          le_of_mul_le_mul_right hA2 (Real.exp_pos _)
        exact le_of_mul_le_mul_left hmid2 hc0pos
      have hδne : δ ≠ 0 := ne_of_gt hδpos
      have hS0ge : Real.log C0 + 1 ≤ δ * s := by
        have hδs : S0 * δ = Real.log C0 + 1 := by
          rw [hS0def]
          field_simp
        have hle : S0 * δ ≤ s * δ := mul_le_mul_of_nonneg_right hsge' hδpos.le
        have hcomm : s * δ = δ * s := mul_comm _ _
        linarith
      have hexp1gt : (1 : ℝ) < Real.exp 1 := by
        have h := Real.add_one_le_exp (1 : ℝ)
        linarith
      have hC0lt : C0 < C0 * Real.exp 1 := by
        have h := mul_lt_mul_of_pos_left hexp1gt hC0pos
        simpa using h
      have hexp_log : Real.exp (Real.log C0 + 1) = C0 * Real.exp 1 := by
        rw [Real.exp_add, Real.exp_log hC0pos]
      have hge : Real.exp (Real.log C0 + 1) ≤ Real.exp (δ * s) :=
        Real.exp_le_exp.mpr hS0ge
      linarith [hC0lt, hexp_log, hge, hexp_δ_le, hexp_le_C0]
    · -- `T' < 1`: `E' = 0`, `choose = 1`, use `T₀/D` margin.
      push_neg at hT'ge1
      have hE'eq0 : E' = 0 := Nat.floor_eq_zero.mpr (by linarith [hT'pos])
      -- `C' = 1`, `rank(Lam,0) ≥ 1`, so `deg(Gh) ≥ 1`.
      have hLam_ne : Lam.Nonempty := by
        have hsrc_pos : (0 : ℝ) < ((TrackD.poolPts (T.sources i)).card : ℝ) :=
          lt_of_lt_of_le hPthresh hPge
        have htgt_pos : (0 : ℝ) < ((TrackD.poolPts (T.targets i)).card : ℝ) := by
          rw [hPt_eq]
          exact hsrc_pos
        have hpos : (0 : ℝ) < (Lam.card : ℝ) := by
          have h1 : (0 : ℝ) < ρ' / (2 * (2 * (d : ℝ) + 1)) * (1 - ρ) ^ 2 *
              ((TrackD.poolPts (T.sources i)).card : ℝ) *
              ((TrackD.poolPts (T.targets i)).card : ℝ) :=
            mul_pos (mul_pos (mul_pos (by positivity) (by positivity)) hsrc_pos) htgt_pos
          exact lt_of_lt_of_le h1 hLam_dense
        exact Finset.card_pos.mp (Nat.cast_pos.mp hpos)
      have hrank0_ge1 : (1 : ℝ) ≤ ((commonLabelRank i₀ Lam 0 : ℕ) : ℝ) := by
        have h1 : 1 ≤ commonLabelRank i₀ Lam 0 :=
          commonLabelRank_zero_ge_one d i₀ Lam hLam_ne
        exact_mod_cast h1
      have hdeg_ge1 : (1 : ℝ) ≤ ((AffineFamily.degree Gh : ℚ) : ℝ) := by
        have h3 := hrank_up
        rw [hE'eq0] at h3
        have hC0 : ((((0 + h).choose h : ℕ)) : ℝ) = 1 := by
          rw [Nat.zero_add, Nat.choose_self, Nat.cast_one]
        rw [hC0, mul_one] at h3
        exact hrank0_ge1.trans h3
      -- `H ≥ c₀·L₀^h` via `deg ≥ 1`.
      have hHlow1 : c0 * (L0 : ℝ) ^ h ≤ (hilbertOfSet Tup T0n : ℝ) := by
        have hbase : c0 * ((AffineFamily.degree Gh : ℚ) : ℝ) * (L0 : ℝ) ^ h ≤
            (hilbertOfSet Tup T0n : ℝ) := by
          have h2 := hlower
          simpa [hL0def] using h2
        have hL0nn0 : (0 : ℝ) ≤ (L0 : ℝ) ^ h := pow_nonneg (Nat.cast_nonneg _) _
        calc c0 * (L0 : ℝ) ^ h = c0 * (L0 : ℝ) ^ h * 1 := by ring
          _ ≤ c0 * (L0 : ℝ) ^ h * ((AffineFamily.degree Gh : ℚ) : ℝ) :=
              mul_le_mul_of_nonneg_left hdeg_ge1 (mul_nonneg hc0pos.le hL0nn0)
          _ = c0 * ((AffineFamily.degree Gh : ℚ) : ℝ) * (L0 : ℝ) ^ h := by ring
          _ ≤ _ := hbase
      -- Upper bound (re-derive `choose₂`, which was `T'≥1`-local).
      have hchoose2_le' : (((T0n + 2 * k).choose (2 * k) : ℕ) : ℝ) ≤ (2 * T0) ^ (2 * k) := by
        have h1 := common_choose_le_pow T0n (2 * k)
        have hT1le : ((T0n + 1 : ℕ) : ℝ) ≤ 2 * T0 := by
          have hT0n_le : (T0n : ℝ) ≤ T0 := Nat.floor_le hT0pos.le
          have h1le : (1 : ℝ) ≤ T0 := hT0ge1
          have hcast : ((T0n + 1 : ℕ) : ℝ) = (T0n : ℝ) + 1 := by push_cast; ring
          rw [hcast]
          linarith
        calc (((T0n + 2 * k).choose (2 * k) : ℕ) : ℝ) ≤ ((T0n + 1 : ℕ) : ℝ) ^ (2 * k) := h1
          _ ≤ (2 * T0) ^ (2 * k) := pow_le_pow_left₀ (by positivity) hT1le _
      have hHup' : (hilbertOfSet Tup T0n : ℝ) ≤
          (1 + ρ) * e ^ 2 * Real.exp (ε * s) * (2 * T0) ^ (2 * k) := by
        calc (hilbertOfSet Tup T0n : ℝ)
            ≤ ((AffineFamily.hilbert chart.U T0n : ℕ) : ℝ) := hHle_hilbertU
          _ ≤ ((AffineFamily.degree chart.U : ℚ) : ℝ) *
              (((T0n + 2 * k).choose (2 * k) : ℕ) : ℝ) := hhilbU_up
          _ ≤ ((1 + ρ) * e ^ 2 * Real.exp (ε * s)) * (2 * T0) ^ (2 * k) := by
              apply mul_le_mul hdegU_le hchoose2_le' (Nat.cast_nonneg _) (by positivity)
      have hL0pow' : (T0 / 2) ^ h ≤ (L0 : ℝ) ^ h :=
        pow_le_pow_left₀ (by positivity) hL0ge _
      -- `T' < 1` forces `τ' < -1`, so early cuts are `< -1+κ` and `e` is small.
      have hTpexp' : T' = Real.exp ((1 + τ') * s) := by
        rw [hT'def]
        unfold TrackD.testDeg
        rw [← hexpB, ← Real.exp_add]
        congr 1
        ring
      have hexp_lt1 : Real.exp ((1 + τ') * s) < 1 := by
        rw [← hTpexp']
        exact hT'ge1
      have hprod_neg : (1 + τ') * s < 0 := Real.exp_lt_one_iff.mp hexp_lt1
      have h1τneg : 1 + τ' < 0 := by
        by_contra hcon
        push Not at hcon
        have hnn : 0 ≤ (1 + τ') * s := mul_nonneg hcon hspos.le
        linarith [hprod_neg, hnn]
      have hτ'neg1 : τ' < -1 := by linarith [h1τneg]
      have hbj_neg : M.b ⟨j, hj⟩ < -1 + κ := by linarith [hτ'mem, hτ'neg1]
      set F1 : Finset (Fin d) := Finset.univ.filter (fun a : Fin d => a.val < j + 1) with hF1def
      have heScale_eq : e = ∏ a ∈ F1, TrackD.cutScale B s M.b a := rfl
      have hF1card : F1.card ≤ d := by
        calc F1.card ≤ Finset.univ.card := Finset.card_filter_le _ _
          _ = d := by rw [Finset.card_univ, Fintype.card_fin]
      have hDapos : ∀ a ∈ F1, 0 ≤ TrackD.cutScale B s M.b a := by
        intro a _
        exact (TrackD.RankCore.testDeg_pos hBpos _ _).le
      have hDale : ∀ a ∈ F1, TrackD.cutScale B s M.b a ≤ Real.exp (κ * s) := by
        intro a ha
        have hval : a.val ≤ j := by
          have hmem := (Finset.mem_filter.mp ha).2
          omega
        have hle : M.b a ≤ M.b ⟨j, hj⟩ := M.sorted (Fin.le_def.mpr hval)
        have hbκ : M.b a < -1 + κ := by linarith [hle, hbj_neg]
        have h1ba : 1 + M.b a ≤ κ := by linarith [hbκ]
        have hDaexp : TrackD.cutScale B s M.b a = Real.exp ((1 + M.b a) * s) := by
          unfold TrackD.cutScale TrackD.testDeg
          rw [← hexpB, ← Real.exp_add]
          congr 1
          ring
        rw [hDaexp]
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_right h1ba hspos.le
      have he_le : e ≤ Real.exp ((F1.card : ℝ) * (κ * s)) := by
        rw [heScale_eq]
        calc ∏ a ∈ F1, TrackD.cutScale B s M.b a ≤ ∏ _a ∈ F1, Real.exp (κ * s) :=
              Finset.prod_le_prod₀ hDapos hDale
          _ = Real.exp ((F1.card : ℝ) * (κ * s)) := by
              rw [Finset.prod_const, ← Real.exp_nat_mul]
      have he2bound : e ^ 2 ≤ Real.exp (2 * (d : ℝ) * κ * s) := by
        have he_card : (F1.card : ℝ) ≤ (d : ℝ) := by exact_mod_cast hF1card
        have hks_nn : (0 : ℝ) ≤ κ * s := mul_nonneg hκpos.le hspos.le
        have h1 : e ≤ Real.exp ((d : ℝ) * κ * s) := by
          calc e ≤ Real.exp ((F1.card : ℝ) * (κ * s)) := he_le
            _ ≤ Real.exp ((d : ℝ) * κ * s) := by
                apply Real.exp_le_exp.mpr
                calc (F1.card : ℝ) * (κ * s) ≤ (d : ℝ) * (κ * s) :=
                      mul_le_mul_of_nonneg_right he_card hks_nn
                  _ = (d : ℝ) * κ * s := by ring
        calc e ^ 2 ≤ (Real.exp ((d : ℝ) * κ * s)) ^ 2 :=
              pow_le_pow_left₀ hepos.le h1 _
          _ = Real.exp (2 * (d : ℝ) * κ * s) := by
              rw [pow_two, ← Real.exp_add]
              congr 1
              ring
      have hHup2 : (hilbertOfSet Tup T0n : ℝ) ≤
          (1 + ρ) * Real.exp (2 * (d : ℝ) * κ * s) * Real.exp (ε * s) * (2 * T0) ^ (2 * k) := by
        calc (hilbertOfSet Tup T0n : ℝ)
            ≤ (1 + ρ) * e ^ 2 * Real.exp (ε * s) * (2 * T0) ^ (2 * k) := hHup'
          _ = e ^ 2 * ((1 + ρ) * Real.exp (ε * s) * (2 * T0) ^ (2 * k)) := by ring
          _ ≤ Real.exp (2 * (d : ℝ) * κ * s) *
              ((1 + ρ) * Real.exp (ε * s) * (2 * T0) ^ (2 * k)) :=
              mul_le_mul_of_nonneg_right he2bound (by positivity)
          _ = (1 + ρ) * Real.exp (2 * (d : ℝ) * κ * s) * Real.exp (ε * s) * (2 * T0) ^ (2 * k) := by
              ring
      -- T0 power facts.
      have hT0exp' : T0 = Real.exp ((1 + t₀) * s) := by
        rw [hT0def]
        unfold TrackD.testDeg
        rw [← hexpB, ← Real.exp_add]
        congr 1
        ring
      have h2k_le_h' : 2 * k ≤ h := by omega
      have hT0pow_split' : T0 ^ h = T0 ^ (2 * k) * T0 ^ (h - 2 * k) := by
        conv_lhs => rw [← Nat.add_sub_cancel' h2k_le_h']
        rw [pow_add]
      have hhalf' : (T0 / 2) ^ h = T0 ^ (2 * k) * T0 ^ (h - 2 * k) / (2 : ℝ) ^ h := by
        rw [div_pow, hT0pow_split']
      have hT0pow1 : T0 ≤ T0 ^ (h - 2 * k) := by
        calc T0 = T0 ^ 1 := (pow_one _).symm
          _ ≤ T0 ^ (h - 2 * k) := pow_le_pow_right₀ hT0ge1 (by omega)
      have h2T0' : (2 * T0) ^ (2 * k) = (2 : ℝ) ^ (2 * k) * T0 ^ (2 * k) := by
        rw [mul_pow]
      have h2cancel : (2 : ℝ) ^ (h + 2 * k) / (2 : ℝ) ^ h = (2 : ℝ) ^ (2 * k) := by
        rw [pow_add, mul_div_cancel_left₀ _ (by positivity)]
      -- Merge the right-hand exponentials (standalone).
      have hexpE2 : Real.exp (2 * (d : ℝ) * κ * s) * Real.exp (ε * s) =
          Real.exp ((2 * (d : ℝ) * κ + ε) * s) := by
        rw [← Real.exp_add]
        congr 1
        ring
      -- Lower side factored by `T₀^{2k}/2^h`.
      have hstep1a : c0 * (T0 / 2) ^ h ≤ (hilbertOfSet Tup T0n : ℝ) := by
        calc c0 * (T0 / 2) ^ h ≤ c0 * (L0 : ℝ) ^ h :=
              mul_le_mul_of_nonneg_left hL0pow' hc0pos.le
          _ ≤ _ := hHlow1
      have hleF : c0 * (T0 ^ (2 * k) * T0 / (2 : ℝ) ^ h) ≤ c0 * (T0 / 2) ^ h := by
        have hleF0 : T0 ^ (2 * k) * T0 / (2 : ℝ) ^ h ≤ (T0 / 2) ^ h := by
          rw [hhalf']
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hT0pow1 (pow_nonneg hT0pos.le _)
        exact mul_le_mul_of_nonneg_left hleF0 hc0pos.le
      have hlowF2 : (c0 * T0) * (T0 ^ (2 * k) / (2 : ℝ) ^ h) ≤
          (hilbertOfSet Tup T0n : ℝ) := by
        calc (c0 * T0) * (T0 ^ (2 * k) / (2 : ℝ) ^ h)
            = c0 * (T0 ^ (2 * k) * T0 / (2 : ℝ) ^ h) := by ring
          _ ≤ c0 * (T0 / 2) ^ h := hleF
          _ ≤ _ := hstep1a
      -- Upper side with the same factor (exps merged once).
      have hHup2m : (hilbertOfSet Tup T0n : ℝ) ≤
          (1 + ρ) * Real.exp ((2 * (d : ℝ) * κ + ε) * s) * (2 * T0) ^ (2 * k) := by
        calc (hilbertOfSet Tup T0n : ℝ)
            ≤ (1 + ρ) * Real.exp (2 * (d : ℝ) * κ * s) * Real.exp (ε * s) * (2 * T0) ^ (2 * k) :=
              hHup2
          _ = (1 + ρ) * (Real.exp (2 * (d : ℝ) * κ * s) * Real.exp (ε * s)) * (2 * T0) ^ (2 * k) := by
              ring
          _ = (1 + ρ) * Real.exp ((2 * (d : ℝ) * κ + ε) * s) * (2 * T0) ^ (2 * k) := by
              rw [hexpE2]
      have hupF2 : (hilbertOfSet Tup T0n : ℝ) ≤
          ((1 + ρ) * (2 : ℝ) ^ (h + 2 * k) * Real.exp ((2 * (d : ℝ) * κ + ε) * s)) *
            (T0 ^ (2 * k) / (2 : ℝ) ^ h) := by
        calc (hilbertOfSet Tup T0n : ℝ)
            ≤ (1 + ρ) * Real.exp ((2 * (d : ℝ) * κ + ε) * s) * (2 * T0) ^ (2 * k) := hHup2m
          _ = (1 + ρ) * Real.exp ((2 * (d : ℝ) * κ + ε) * s) *
              ((2 : ℝ) ^ (2 * k) * T0 ^ (2 * k)) := by rw [h2T0']
          _ = ((1 + ρ) * (2 : ℝ) ^ (h + 2 * k) * Real.exp ((2 * (d : ℝ) * κ + ε) * s)) *
              (T0 ^ (2 * k) / (2 : ℝ) ^ h) := by
              rw [← h2cancel]
              ring
      have hF2pos : (0 : ℝ) < T0 ^ (2 * k) / (2 : ℝ) ^ h := by positivity
      have hcoreT0 : c0 * T0 ≤
          (1 + ρ) * (2 : ℝ) ^ (h + 2 * k) * Real.exp ((2 * (d : ℝ) * κ + ε) * s) :=
        le_of_mul_le_mul_right (hlowF2.trans hupF2) hF2pos
      -- Isolate `exp(margin''·s)` with `margin'' = (1+t₀)-2dκ-ε`.
      have hmargin_iso : Real.exp (((1 + t₀) - 2 * (d : ℝ) * κ - ε) * s) ≤ C0 := by
        have hD2 : Real.exp (((1 + t₀) - 2 * (d : ℝ) * κ - ε) * s) *
            Real.exp ((2 * (d : ℝ) * κ + ε) * s) = Real.exp ((1 + t₀) * s) := by
          rw [← Real.exp_add]
          congr 1
          ring
        have hC1le' : (1 + ρ) * (2 : ℝ) ^ (h + 2 * k) ≤ c0 * C0 := by
          have hpow' : (2 : ℝ) ^ (h + 2 * k) ≤ (2 : ℝ) ^ (6 * d) := by
            apply pow_le_pow_right₀ (by norm_num)
            omega
          have hc0ne' : c0 ≠ 0 := ne_of_gt hc0pos
          have heq' : c0 * C0 = (1 + ρ) * (2 : ℝ) ^ (6 * d) := by
            rw [hC0def]
            field_simp
          rw [heq']
          exact mul_le_mul_of_nonneg_left hpow' (by positivity)
        have hA2b : (c0 * Real.exp (((1 + t₀) - 2 * (d : ℝ) * κ - ε) * s)) *
            Real.exp ((2 * (d : ℝ) * κ + ε) * s) ≤ (c0 * C0) *
            Real.exp ((2 * (d : ℝ) * κ + ε) * s) := by
          have heq2b : (c0 * Real.exp (((1 + t₀) - 2 * (d : ℝ) * κ - ε) * s)) *
              Real.exp ((2 * (d : ℝ) * κ + ε) * s) = c0 * Real.exp ((1 + t₀) * s) := by
            rw [mul_assoc, hD2]
          have hle2b : c0 * Real.exp ((1 + t₀) * s) ≤ (c0 * C0) *
              Real.exp ((2 * (d : ℝ) * κ + ε) * s) := by
            calc c0 * Real.exp ((1 + t₀) * s) = c0 * T0 := by rw [hT0exp']
              _ ≤ (1 + ρ) * (2 : ℝ) ^ (h + 2 * k) *
                  Real.exp ((2 * (d : ℝ) * κ + ε) * s) := hcoreT0
              _ = ((1 + ρ) * (2 : ℝ) ^ (h + 2 * k)) *
                  Real.exp ((2 * (d : ℝ) * κ + ε) * s) := by ring
              _ ≤ (c0 * C0) * Real.exp ((2 * (d : ℝ) * κ + ε) * s) :=
                  mul_le_mul_of_nonneg_right hC1le' (Real.exp_nonneg _)
          rwa [heq2b]
        have hmid2b : c0 * Real.exp (((1 + t₀) - 2 * (d : ℝ) * κ - ε) * s) ≤ c0 * C0 :=
          le_of_mul_le_mul_right hA2b (Real.exp_pos _)
        exact le_of_mul_le_mul_left hmid2b hc0pos
      -- `δ ≤ margin''` since `min ≤ t₀+1`.
      have hm_t01 : min (t₀ - M.b ⟨j, hj⟩) (t₀ - (1 + M.b ⟨0, by omega⟩ + M.b ⟨1, by omega⟩)) ≤
          t₀ + 1 := by
        calc min (t₀ - M.b ⟨j, hj⟩) (t₀ - (1 + M.b ⟨0, by omega⟩ + M.b ⟨1, by omega⟩))
            ≤ t₀ - M.b ⟨j, hj⟩ := min_le_left _ _
          _ ≤ t₀ + 1 := by linarith [hβlow]
      have hkk' : (0 : ℝ) ≤ (2 * (k : ℝ) + 1) * κ := mul_nonneg (by positivity) hκpos.le
      have hexp_δ_le' : Real.exp (δ * s) ≤
          Real.exp (((1 + t₀) - 2 * (d : ℝ) * κ - ε) * s) := by
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_right _ hspos.le
        rw [hδdef]
        linarith [hm_t01, hkk', hε.le]
      -- `S0` finale (identical to the `T'≥1` branch).
      have hsge'' : S0 ≤ s := by simpa [hsdef] using hsge
      have hδne' : δ ≠ 0 := ne_of_gt hδpos
      have hS0ge' : Real.log C0 + 1 ≤ δ * s := by
        have hδs : S0 * δ = Real.log C0 + 1 := by
          rw [hS0def]
          field_simp
        have hle : S0 * δ ≤ s * δ := mul_le_mul_of_nonneg_right hsge'' hδpos.le
        have hcomm : s * δ = δ * s := mul_comm _ _
        linarith
      have hexp1gt' : (1 : ℝ) < Real.exp 1 := by
        have h := Real.add_one_le_exp (1 : ℝ)
        linarith
      have hC0lt' : C0 < C0 * Real.exp 1 := by
        have h := mul_lt_mul_of_pos_left hexp1gt' hC0pos
        simpa using h
      have hexp_log' : Real.exp (Real.log C0 + 1) = C0 * Real.exp 1 := by
        rw [Real.exp_add, Real.exp_log hC0pos]
      have hge' : Real.exp (Real.log C0 + 1) ≤ Real.exp (δ * s) :=
        Real.exp_le_exp.mpr hS0ge'
      linarith [hC0lt', hexp_log', hge', hexp_δ_le', hmargin_iso]
  exact ⟨chart, Bad, hchartW, hBadsub, hBadcard, hBadrem⟩

set_option maxHeartbeats 1000000 in
/-- Helper for 190 with the missing plateau hypotheses made explicit
Adds `hj`, `houter`, `htop`, `ht₀β` to the
frozen 190 hypotheses. The setup below mirrors 190's draft (regularity
application); the exceptional/g-zero/Jacobian steps need those
hyps (`(t₁,t₂) ⊆ (β,1)` for product testing, `IsOuter` for `|pool|²→|S|²`).
Fully proved (main `0<1+t₀` branch plus degenerate `1+t₀≤0` via `ht₀β`). -/
theorem outer_smooth_subfamily_of_plateau {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (M : CommonPoolProfile T)
    (hs : ∀ i, M.s i = Real.log (regime.B i))
    (k j : ℕ) (hj : j < d) (hkj : k + j + 1 = d) (hk : 1 ≤ k ∧ k + 1 < d)
    (houter : ∀ i, T.IsOuter i)
    (htop : ∀ a : Fin d, j < a.val → M.b a = 1)
    (i₀ : Fin d) (ρ ε : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1) (hε : 0 < ε)
    (τ t₀ : ℝ) (ht₀1 : t₀ < 1) (ht₀β : M.b ⟨j, hj⟩ < t₀)
    (hεt : 4 * ε < 1 - t₀)
    (h189 : ∀ ρ'' : ℝ, 0 < ρ'' → ∀ᶠ i in atTop,
      ∃ (chart : OuterChartCert T M k i j i₀ ρ ε ρ'' τ)
        (D : Finset (RPoint d × RPoint d)),
        D ⊆ chart.G ∧
        ((D.card : ℝ)) ≤ ρ'' * (chart.pool.S.card : ℝ) ^ 2 ∧
        ∀ pq ∈ chart.G \ D,
          commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈
            Bridges.envelopeComponents (⋃ Z ∈ chart.U, Z.points)
              (outerEnvDeg regime.B M.s t₀ i)) :
    ∃ c : ℝ, 0 < c ∧ ∀ ρ' : ℝ, 0 < ρ' → ∀ᶠ i in atTop,
      Nonempty (OuterRegularityCert T M k i j i₀ ρ ε ρ'
        ((regime.B i) ^ (2 - c)) τ) := by
  classical
  set t₁ : ℝ := (1 + t₀) / 2 with ht₁def
  have ht₀t₁ : t₀ < t₁ := by linarith
  have ht₁1 : t₁ < 1 := by linarith
  set c : ℝ := (1 - t₁) / 2 with hcdef
  have hcpos : 0 < c := by linarith
  refine ⟨c, hcpos, ?_⟩
  intro ρ' hρ'
  obtain ⟨Creg, hCregpos, hpolyreg⟩ := TrackA.poly_regularity (d + d)
  -- Fixed exponent gap for the exceptional bound (`hεt` gives `δ>0`).
  set δ : ℝ := (1 - t₀) / 2 - 2 * ε with hδdef
  have hδpos : 0 < δ := by linarith
  have hCregRpos : (0 : ℝ) < (Creg : ℝ) := by exact_mod_cast hCregpos
  have h1mρpos : (0 : ℝ) < 1 - ρ := by linarith
  have h1pρpos : (0 : ℝ) < 1 + ρ := by linarith
  set Cexc : ℝ := (ρ' / 3) * (1 - ρ) ^ 2 / (2 * (Creg : ℝ) * (1 + ρ)) with hCexcdef
  have hCexcpos : 0 < Cexc := by positivity
  have hexpEv : ∀ᶠ i in atTop, Real.exp (-δ * M.s i) ≤ Cexc := by
    have hpos : Filter.Tendsto (fun i => δ * M.s i) atTop atTop :=
      M.width_grows.const_mul_atTop hδpos
    have hExpTendsto : Filter.Tendsto (fun i => Real.exp (-δ * M.s i)) atTop (𝓝 0) := by
      have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp hpos
      simpa only [Function.comp_def, mul_neg, neg_mul] using h
    exact hExpTendsto.eventually (Iic_mem_nhds hCexcpos)
  have hBge1 : ∀ᶠ i in atTop, (1 : ℝ) ≤ regime.B i :=
    regime.B_tendsto.eventually_ge_atTop 1
  -- Product-testing time `τg ∈ (t₁,t₂)` off cuts, plateau margin, and uniform
  -- parameters (all independent of `i`; `htop`+`ht₀β` put `(t₁,t₂)` on
  -- plateau `j+1`, so the same `τg` works with every per-`i` chart `W`).
  have hj1 : j + 1 < d := by omega
  set t₂ : ℝ := (1 + t₁) / 2 with ht₂def
  have ht₁t₂ : t₁ < t₂ := by linarith
  obtain ⟨τg, ht₁τg, hτgt₂, _⟩ :=
    exists_time_avoiding_cuts M.b t₁ t₂ ht₁t₂
  have hβτg : M.b ⟨j, hj⟩ < τg := by linarith [ht₀β, ht₀t₁, ht₁τg]
  have hτg1 : τg < 1 := by linarith [hτgt₂, ht₁1]
  set ξ : ℝ := min (τg - M.b ⟨j, hj⟩) (1 - τg) with hξdef
  have hξ : 0 < ξ := by
    rw [hξdef]
    exact lt_min (sub_pos.mpr hβτg) (sub_pos.mpr hτg1)
  have hplateau : TrackD.OnPlateau M.b (j + 1) ξ τg := by
    intro a
    constructor
    · intro ha
      have hle : M.b a ≤ M.b ⟨j, hj⟩ := M.sorted (show a.val ≤ j by omega)
      have e1 : ξ ≤ τg - M.b ⟨j, hj⟩ := by
        rw [hξdef]
        exact min_le_left _ _
      linarith
    · intro ha
      have htopa : M.b a = 1 := htop a (by omega)
      have e2 : ξ ≤ 1 - τg := by
        rw [hξdef]
        exact min_le_right _ _
      rw [htopa]
      linarith [e2]
  set θg : ℝ := (ρ' / 3) * (1 - ρ) ^ 2 with hθgdef
  have hθg : 0 < θg := by positivity
  have hCreg1 : 1 ≤ Creg := hCregpos
  have hKg1 : (1 : ℝ) ≤ (Creg : ℝ) := by exact_mod_cast hCreg1
  obtain ⟨θ₁, hθ₁, η, hη, hηξ, ρ₀, hρ₀, s₁, hproduct⟩ :=
    TrackD.prof_product_testing_labels_with_margin d regime.dimension_ge_three
      θg hθg ξ hξ (Creg : ℝ) hKg1
  have hpoolEv : ∀ᶠ i in atTop,
      TrackD.PoolGood (regime.P i) θ₁ η 1 (ρ₀ / 2) (T.sources i) (M.s i) M.b ∧
      TrackD.PoolGood (regime.P i) θ₁ η 1 (ρ₀ / 2) (T.targets i) (M.s i) M.b :=
    M.good θ₁ hθ₁ η hη 1 le_rfl (ρ₀ / 2) (by positivity)
  have hwidthEv : ∀ᶠ i in atTop, s₁ ≤ M.s i :=
    M.width_grows.eventually_ge_atTop s₁
  by_cases h10 : (0 : ℝ) < 1 + t₀
  · have hb₁ : (0 : ℝ) < 1 + t₁ := by linarith
    have h189u := h189 (ρ' / 3) (by positivity)
    have ht1pos : (0 : ℝ) < t₁ := by linarith
    have hτg : -1 < τg := by linarith [ht₁τg]
    have htestEv : ∀ᶠ i in atTop, 1 ≤ TrackD.testDeg (TrackD.cfgB (regime.P i)) (M.s i) τg :=
      common_physical_test_degree_one M τg hτg
    filter_upwards [h189u,
      eventually_regularity_degree_dominates hs t₀ t₁ ht₀t₁ h10 hb₁ Creg,
      eventually_floor_ge_half hs t₀ h10,
      eventually_floor_ge_half hs t₁ hb₁, hexpEv, hBge1, hpoolEv, hwidthEv, htestEv] with i hi hdom hfl0 hfl1 hexp hB1 hpool hsW hTdeg
    obtain ⟨chart, D189, hDsub, hDcard, hDmem⟩ := hi
    set T0n : ℕ := outerEnvDeg regime.B M.s t₀ i with hT0ndef
    set T1n : ℕ := ⌊TrackD.testDeg (regime.B i) (M.s i) t₁⌋₊ with hT1ndef
    have hT0eq : T0n = ⌊TrackD.testDeg (regime.B i) (M.s i) t₀⌋₊ := rfl
    set Famsurv : AffineFamily.Family (d + d) :=
      chart.U.filter (fun Z => Z ∈ Bridges.envelopeComponents
        (⋃ Z ∈ chart.U, Z.points) T0n) with hFamdef
    have hFamsubU : Famsurv ⊆ chart.U := Finset.filter_subset _ _
    have hFamsubEnv : Famsurv ⊆ Bridges.envelopeComponents
        (⋃ Z ∈ chart.U, Z.points) T0n := fun Z hZ => (Finset.mem_filter.mp hZ).2
    have hFampure : AffineFamily.IsPure Famsurv (2 * k) := by
      intro V hV
      obtain ⟨hVU, _⟩ := Finset.mem_filter.mp hV
      exact chart.hU V hVU
    have hFamLists : TrackA.FromAffineLists Famsurv T0n := by
      have hdef := TrackD.envelope_components_defined
        (⋃ Z ∈ chart.U, Z.points) T0n Famsurv hFamsubEnv
      have h1 : 1 ≤ T0n := hfl0.2.2
      exact fromLists_of_definedInDegree Famsurv T0n h1 hdef
    have hT0pos1 : 1 ≤ T0n := hfl0.2.2
    obtain ⟨bad, E, g, hbadsub, hbaddeg, hE, hgdeg, hgspan, hggood, hgerm⟩ :=
      hpolyreg Famsurv (2 * k) T0n T1n (by omega) hFampure hT0pos1 hFamLists hdom
    -- (`τg`, `t₂` fixed before `by_cases`; see above.)
    -- Widened chart (budget `ρ'/3 ≤ ρ'`), equations from `E`, good predicate
    -- excluding the 189 deletion, exceptional images and `g`-zeros.
    -- Bounds (`D_exc`, `D_g` each `≤ ρ'/3·|S|²`), degree, vanishing and
    -- smoothness follow below (using `houter`/`htop`/`ht₀β`).
    set chart' : OuterChartCert T M k i j i₀ ρ ε ρ' τ :=
      chart.mono (by linarith) with hchart'def
    set Eqs : Finset (TrackD.PairPoly d) :=
      (E.map (fun f => MvPolynomial.rename finSumFinEquiv.symm f)).toFinset with hEqsdef
    set good : RPoint d × RPoint d → Prop := fun pq =>
      pq ∈ chart.G ∧ pq ∉ D189 ∧
        commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∉ bad ∧
        MvPolynomial.eval (outerLabelPt i₀ pq) g ≠ 0 with hgooddef
    have hbadU : bad ⊆ chart.U := hbadsub.trans hFamsubU
    -- Exceptional pairs via `hmassW` + `hexp`/`hB1`/`houter` (full proof next).
    have hDexc : ((chart.G.filter (fun pq =>
        commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈ bad)).card : ℝ) ≤
        (ρ' / 3) * (chart.pool.S.card : ℝ) ^ 2 := by
      -- Degree nonnegativity from irreducibility (`one_le_degree`).
      have hdegNN_U : ∀ V ∈ chart.U, (0 : ℚ) ≤ V.degree := by
        intro V hV
        obtain ⟨hirr, _⟩ := chart.hU V hV
        have h1 : (1 : ℚ) ≤ V.degree := AffineVariety.one_le_degree V hirr.ne_top
        linarith
      have hFamdeg_le : AffineFamily.degree Famsurv ≤ AffineFamily.degree chart.U :=
        degree_filter_le _ _ hdegNN_U
      -- `hmassW` at `J = bad` + sum `≤ degree bad`.
      have hJsub : bad ⊆ chart.U := hbadU
      have hsum_le : ((∑ Z ∈ (commonChartImages chart.W chart.L i i₀).filter
          (fun Z => Z ∈ bad), (Z.degree : ℚ)) : ℚ) ≤ AffineFamily.degree bad := by
        have hdegNN_bad : ∀ V ∈ bad, (0 : ℚ) ≤ V.degree := by
          intro V hV
          have hVFam : V ∈ Famsurv := hbadsub hV
          obtain ⟨hirr, _⟩ := hFampure V hVFam
          have h1 : (1 : ℚ) ≤ V.degree := AffineVariety.one_le_degree V hirr.ne_top
          linarith
        have hsub : (commonChartImages chart.W chart.L i i₀).filter
            (fun Z => Z ∈ bad) ⊆ bad := by
          intro Z hZ
          exact (Finset.mem_filter.mp hZ).2
        unfold AffineFamily.degree
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun Z hZ _ => hdegNN_bad Z hZ)
      have hmass : ((chart.G.filter (fun pq =>
          commonProductImage i₀ (chart.W.owner i pq.1)
            (chart.W.owner i pq.2) ∈ bad)).card : ℝ) ≤
          Real.exp (ε * M.s i) *
            (((chart.W.sources i).card : ℝ) * (chart.W.targets i).card /
              (commonCarrierScale M (j + 1) i) ^ 2) *
            ((∑ Z ∈ (commonChartImages chart.W chart.L i i₀).filter
              (fun Z => Z ∈ bad), (Z.degree : ℚ)) : ℝ) :=
        chart.hmassW bad hbadU
      have hUdegR : ((AffineFamily.degree chart.U : ℚ) : ℝ) ≤
          (1 + ρ) * (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2 *
            Real.exp (ε * M.s i) :=
        chart.hUdeg
      have hFamdegR : ((AffineFamily.degree Famsurv : ℚ) : ℝ) ≤
          (1 + ρ) * (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2 *
            Real.exp (ε * M.s i) :=
        le_trans (by exact_mod_cast hFamdeg_le) hUdegR
      have hbaddegR : ((AffineFamily.degree bad : ℚ) : ℝ) ≤
          (Creg : ℝ) * ((AffineFamily.degree Famsurv : ℚ) : ℝ) *
            ((T0n : ℕ) : ℝ) / ((T1n : ℕ) : ℝ) := by
        exact_mod_cast hbaddeg
      -- Testing-degree facts at this index.
      have hBpos : (0 : ℝ) < regime.B i := by linarith [hB1]
      have hBne : regime.B i ≠ 0 := ne_of_gt hBpos
      have hT0nn : (0 : ℝ) ≤ TrackD.testDeg (regime.B i) (M.s i) t₀ :=
        le_trans zero_le_one hfl0.1
      have hT1pos : (0 : ℝ) < TrackD.testDeg (regime.B i) (M.s i) t₁ := by
        linarith [hfl1.1]
      have hT1n_posR : (0 : ℝ) < ((T1n : ℕ) : ℝ) := by
        have h1 : 1 ≤ T1n := hfl1.2.2
        exact_mod_cast Nat.pos_of_ne_zero (by omega)
      have hT0n_le : ((T0n : ℕ) : ℝ) ≤ TrackD.testDeg (regime.B i) (M.s i) t₀ := by
        rw [hT0eq]
        exact Nat.floor_le hT0nn
      have hT0T1 : TrackD.testDeg (regime.B i) (M.s i) t₀ /
          TrackD.testDeg (regime.B i) (M.s i) t₁ =
          Real.exp ((t₀ - t₁) * M.s i) := by
        unfold TrackD.testDeg
        rw [mul_div_mul_left _ _ hBne, ← Real.exp_sub]
        congr 1
        ring
      have hRatio : ((T0n : ℕ) : ℝ) / ((T1n : ℕ) : ℝ) ≤
          2 * Real.exp ((t₀ - t₁) * M.s i) := by
        have hT0nn : (0 : ℝ) ≤ TrackD.testDeg (regime.B i) (M.s i) t₀ :=
          le_trans zero_le_one hfl0.1
        have hT1nn : (0 : ℝ) ≤ TrackD.testDeg (regime.B i) (M.s i) t₁ :=
          le_trans zero_le_one hfl1.1
        have hhalf_pos : (0 : ℝ) < TrackD.testDeg (regime.B i) (M.s i) t₁ / 2 := by
          linarith [hfl1.1]
        have hle : ((T0n : ℕ) : ℝ) * (TrackD.testDeg (regime.B i) (M.s i) t₁ / 2) ≤
            TrackD.testDeg (regime.B i) (M.s i) t₀ * ((T1n : ℕ) : ℝ) :=
          calc ((T0n : ℕ) : ℝ) * (TrackD.testDeg (regime.B i) (M.s i) t₁ / 2)
              ≤ TrackD.testDeg (regime.B i) (M.s i) t₀ *
                (TrackD.testDeg (regime.B i) (M.s i) t₁ / 2) :=
                mul_le_mul_of_nonneg_right hT0n_le (le_of_lt hhalf_pos)
            _ ≤ TrackD.testDeg (regime.B i) (M.s i) t₀ * ((T1n : ℕ) : ℝ) :=
                mul_le_mul_of_nonneg_left hfl1.2.1 hT0nn
        have hstep : ((T0n : ℕ) : ℝ) / ((T1n : ℕ) : ℝ) ≤
            TrackD.testDeg (regime.B i) (M.s i) t₀ /
              (TrackD.testDeg (regime.B i) (M.s i) t₁ / 2) := by
          rw [div_le_div_iff₀ hT1n_posR hhalf_pos]
          exact hle
        have hT1ne : TrackD.testDeg (regime.B i) (M.s i) t₁ ≠ 0 :=
          ne_of_gt (by linarith [hfl1.1])
        have h2 : TrackD.testDeg (regime.B i) (M.s i) t₀ /
              (TrackD.testDeg (regime.B i) (M.s i) t₁ / 2) =
            2 * (TrackD.testDeg (regime.B i) (M.s i) t₀ /
              TrackD.testDeg (regime.B i) (M.s i) t₁) := by
          field_simp
        calc ((T0n : ℕ) : ℝ) / ((T1n : ℕ) : ℝ)
            ≤ TrackD.testDeg (regime.B i) (M.s i) t₀ /
              (TrackD.testDeg (regime.B i) (M.s i) t₁ / 2) := hstep
          _ = 2 * (TrackD.testDeg (regime.B i) (M.s i) t₀ /
              TrackD.testDeg (regime.B i) (M.s i) t₁) := h2
          _ = 2 * Real.exp ((t₀ - t₁) * M.s i) := by rw [hT0T1]
      -- eScale positivity and carrier-scale identification.
      have he_pos : (0 : ℝ) < TrackD.eScale (regime.B i) (M.s i) M.b (j + 1) := by
        unfold TrackD.eScale TrackD.cutScale TrackD.testDeg
        apply Finset.prod_pos
        intro a _
        exact mul_pos hBpos (Real.exp_pos _)
      have he_ne : TrackD.eScale (regime.B i) (M.s i) M.b (j + 1) ≠ 0 :=
        ne_of_gt he_pos
      have he2_ne : (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2 ≠ 0 :=
        pow_ne_zero 2 he_ne
      have hcommon_eq : commonCarrierScale M (j + 1) i =
          TrackD.eScale (regime.B i) (M.s i) M.b (j + 1) := rfl
      rw [hcommon_eq] at hmass
      -- Cast of the filtered sum bound to `ℝ`.
      have hsumR : ((∑ Z ∈ (commonChartImages chart.W chart.L i i₀).filter
          (fun Z => Z ∈ bad), (Z.degree : ℚ)) : ℝ) ≤
          ((AffineFamily.degree bad : ℚ) : ℝ) := by
        exact_mod_cast hsum_le
      -- Bridge for the bad-degree ratio shape.
      have hbaddegR' : ((AffineFamily.degree bad : ℚ) : ℝ) ≤
          ((Creg : ℝ) * ((AffineFamily.degree Famsurv : ℚ) : ℝ)) *
            (((T0n : ℕ) : ℝ) / ((T1n : ℕ) : ℝ)) := by
        rwa [mul_div_assoc] at hbaddegR
      have hr_nn : (0 : ℝ) ≤ ((T0n : ℕ) : ℝ) / ((T1n : ℕ) : ℝ) :=
        div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      have hCFd_le : (Creg : ℝ) * ((AffineFamily.degree Famsurv : ℚ) : ℝ) ≤
          (Creg : ℝ) * ((1 + ρ) * (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2 *
            Real.exp (ε * M.s i)) :=
        mul_le_mul_of_nonneg_left hFamdegR hCregRpos.le
      have hCU2nn : (0 : ℝ) ≤ (Creg : ℝ) *
          ((1 + ρ) * (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2 *
            Real.exp (ε * M.s i)) :=
        mul_nonneg hCregRpos.le
          (mul_nonneg (mul_nonneg h1pρpos.le (sq_nonneg _)) (Real.exp_nonneg _))
      have hDr_le : ((Creg : ℝ) * ((AffineFamily.degree Famsurv : ℚ) : ℝ)) *
          (((T0n : ℕ) : ℝ) / ((T1n : ℕ) : ℝ)) ≤
          ((Creg : ℝ) * ((1 + ρ) * (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2 *
            Real.exp (ε * M.s i))) * (2 * Real.exp ((t₀ - t₁) * M.s i)) := by
        have h1 : ((Creg : ℝ) * ((AffineFamily.degree Famsurv : ℚ) : ℝ)) *
            (((T0n : ℕ) : ℝ) / ((T1n : ℕ) : ℝ)) ≤
            ((Creg : ℝ) * ((1 + ρ) * (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2 *
              Real.exp (ε * M.s i))) * (((T0n : ℕ) : ℝ) / ((T1n : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right hCFd_le hr_nn
        have h2 : ((Creg : ℝ) * ((1 + ρ) * (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2 *
            Real.exp (ε * M.s i))) * (((T0n : ℕ) : ℝ) / ((T1n : ℕ) : ℝ)) ≤
            ((Creg : ℝ) * ((1 + ρ) * (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2 *
              Real.exp (ε * M.s i))) * (2 * Real.exp ((t₀ - t₁) * M.s i)) :=
          mul_le_mul_of_nonneg_left hRatio hCU2nn
        exact h1.trans h2
      -- Exponent combination `2ε + (t₀-t₁) = -δ`.
      have hexp_combine : Real.exp (ε * M.s i) * Real.exp (ε * M.s i) *
          Real.exp ((t₀ - t₁) * M.s i) = Real.exp (-δ * M.s i) := by
        have harg : ε * M.s i + ε * M.s i + (t₀ - t₁) * M.s i = -δ * M.s i := by
          rw [hδdef, ht₁def]
          ring
        calc Real.exp (ε * M.s i) * Real.exp (ε * M.s i) *
              Real.exp ((t₀ - t₁) * M.s i)
            = Real.exp (ε * M.s i + ε * M.s i + (t₀ - t₁) * M.s i) := by
              rw [← Real.exp_add, ← Real.exp_add]
          _ = Real.exp (-δ * M.s i) := by rw [harg]
      -- Pool-size conversion via `IsOuter`.
      have houter_eq : T.sources i = T.targets i := (houter i).1
      have hpool_eq : TrackD.poolPts (T.sources i) =
          TrackD.poolPts (T.targets i) := by rw [houter_eq]
      have hWs_le : ((chart.W.sources i).card : ℝ) ≤
          ((TrackD.poolPts (T.sources i)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
      have hWt_le : ((chart.W.targets i).card : ℝ) ≤
          ((TrackD.poolPts (T.sources i)).card : ℝ) := by
        calc ((chart.W.targets i).card : ℝ)
            ≤ ((TrackD.poolPts (T.targets i)).card : ℝ) := by
              exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
          _ = ((TrackD.poolPts (T.sources i)).card : ℝ) := by rw [hpool_eq]
      have hpoolS_le : ((TrackD.poolPts (T.sources i)).card : ℝ) ≤
          (chart.pool.S.card : ℝ) / (1 - ρ) := by
        rw [le_div_iff₀ h1mρpos, mul_comm]
        exact chart.pool.hScard
      have hWp_le : ((chart.W.sources i).card : ℝ) * ((chart.W.targets i).card : ℝ) ≤
          (chart.pool.S.card : ℝ) ^ 2 / (1 - ρ) ^ 2 := by
        have h1 : ((chart.W.sources i).card : ℝ) * ((chart.W.targets i).card : ℝ) ≤
            ((TrackD.poolPts (T.sources i)).card : ℝ) *
              ((TrackD.poolPts (T.sources i)).card : ℝ) :=
          mul_le_mul hWs_le hWt_le (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        have h2 : ((TrackD.poolPts (T.sources i)).card : ℝ) *
            ((TrackD.poolPts (T.sources i)).card : ℝ) ≤
            ((chart.pool.S.card : ℝ) / (1 - ρ)) * ((chart.pool.S.card : ℝ) / (1 - ρ)) :=
          mul_le_mul hpoolS_le hpoolS_le (Nat.cast_nonneg _)
            (div_nonneg (Nat.cast_nonneg _) h1mρpos.le)
        have h3 : ((chart.pool.S.card : ℝ) / (1 - ρ)) *
            ((chart.pool.S.card : ℝ) / (1 - ρ)) =
            (chart.pool.S.card : ℝ) ^ 2 / (1 - ρ) ^ 2 := by
          rw [div_mul_div_comm, ← pow_two, ← pow_two]
        rw [h3] at h2
        exact h1.trans h2
      have hCreg_ne : (Creg : ℝ) ≠ 0 := ne_of_gt hCregRpos
      have h1pρ_ne : (1 + ρ : ℝ) ≠ 0 := ne_of_gt h1pρpos
      have hden_ne : (2 : ℝ) * (Creg : ℝ) * (1 + ρ) ≠ 0 :=
        ne_of_gt (mul_pos (mul_pos (by norm_num) hCregRpos) h1pρpos)
      have h1mρsq_ne : (1 - ρ : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt h1mρpos)
      -- Coefficient nonnegativity facts.
      have hcoeff1nn : (0 : ℝ) ≤ Real.exp (ε * M.s i) *
          ((((chart.W.sources i).card : ℝ) * ((chart.W.targets i).card : ℝ)) /
            (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2) :=
        mul_nonneg (Real.exp_nonneg _)
          (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (sq_nonneg _))
      have hKnn : (0 : ℝ) ≤ 2 * (Creg : ℝ) * (1 + ρ) :=
        mul_nonneg (mul_nonneg (by norm_num) hCregRpos.le) h1pρpos.le
      have hK2nn : (0 : ℝ) ≤ 2 * (Creg : ℝ) * (1 + ρ) *
          ((chart.pool.S.card : ℝ) ^ 2 / (1 - ρ) ^ 2) :=
        mul_nonneg hKnn (div_nonneg (sq_nonneg _) (sq_nonneg _))
      -- Final chain.
      calc ((chart.G.filter (fun pq =>
            commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈ bad)).card : ℝ)
          ≤ Real.exp (ε * M.s i) *
            ((((chart.W.sources i).card : ℝ) * ((chart.W.targets i).card : ℝ)) /
              (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2) *
            ((AffineFamily.degree bad : ℚ) : ℝ) := by
            have h1 : Real.exp (ε * M.s i) *
                ((((chart.W.sources i).card : ℝ) * ((chart.W.targets i).card : ℝ)) /
                  (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2) *
                ((∑ Z ∈ (commonChartImages chart.W chart.L i i₀).filter
                  (fun Z => Z ∈ bad), (Z.degree : ℚ)) : ℝ) ≤
                Real.exp (ε * M.s i) *
                ((((chart.W.sources i).card : ℝ) * ((chart.W.targets i).card : ℝ)) /
                  (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2) *
                ((AffineFamily.degree bad : ℚ) : ℝ) :=
              mul_le_mul_of_nonneg_left hsumR hcoeff1nn
            -- `hmass` was rewritten to `eScale`; its middle now matches.
            exact hmass.trans h1
        _ ≤ 2 * (Creg : ℝ) * (1 + ρ) *
            ((chart.pool.S.card : ℝ) ^ 2 / (1 - ρ) ^ 2) *
            Real.exp (-δ * M.s i) := by
            have h1 : ((AffineFamily.degree bad : ℚ) : ℝ) ≤
                ((Creg : ℝ) * ((AffineFamily.degree Famsurv : ℚ) : ℝ)) *
                  (((T0n : ℕ) : ℝ) / ((T1n : ℕ) : ℝ)) := hbaddegR'
            have hX : Real.exp (ε * M.s i) *
                ((((chart.W.sources i).card : ℝ) * ((chart.W.targets i).card : ℝ)) /
                  (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2) *
                ((AffineFamily.degree bad : ℚ) : ℝ) ≤
                Real.exp (ε * M.s i) *
                ((((chart.W.sources i).card : ℝ) * ((chart.W.targets i).card : ℝ)) /
                  (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2) *
                (((Creg : ℝ) * ((AffineFamily.degree Famsurv : ℚ) : ℝ)) *
                  (((T0n : ℕ) : ℝ) / ((T1n : ℕ) : ℝ))) :=
              mul_le_mul_of_nonneg_left h1 hcoeff1nn
            -- Reassociate `FamdegR` into the middle factor.
            have h2 : ((Creg : ℝ) * ((AffineFamily.degree Famsurv : ℚ) : ℝ)) *
                (((T0n : ℕ) : ℝ) / ((T1n : ℕ) : ℝ)) ≤
                ((Creg : ℝ) * ((1 + ρ) * (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2 *
                  Real.exp (ε * M.s i))) * (2 * Real.exp ((t₀ - t₁) * M.s i)) :=
              hDr_le
            have h3 : Real.exp (ε * M.s i) *
                ((((chart.W.sources i).card : ℝ) * ((chart.W.targets i).card : ℝ)) /
                  (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2) *
                (((Creg : ℝ) * ((AffineFamily.degree Famsurv : ℚ) : ℝ)) *
                  (((T0n : ℕ) : ℝ) / ((T1n : ℕ) : ℝ))) ≤
                Real.exp (ε * M.s i) *
                ((((chart.W.sources i).card : ℝ) * ((chart.W.targets i).card : ℝ)) /
                  (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2) *
                (((Creg : ℝ) * ((1 + ρ) * (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2 *
                  Real.exp (ε * M.s i))) * (2 * Real.exp ((t₀ - t₁) * M.s i))) :=
              mul_le_mul_of_nonneg_left h2 hcoeff1nn
            -- Collapse `eScale²` and exponents.
            have heq : Real.exp (ε * M.s i) *
                ((((chart.W.sources i).card : ℝ) * ((chart.W.targets i).card : ℝ)) /
                  (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2) *
                (((Creg : ℝ) * ((1 + ρ) * (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2 *
                  Real.exp (ε * M.s i))) * (2 * Real.exp ((t₀ - t₁) * M.s i))) =
                2 * (Creg : ℝ) * (1 + ρ) *
                  (((chart.W.sources i).card : ℝ) * ((chart.W.targets i).card : ℝ)) *
                  (Real.exp (ε * M.s i) * Real.exp (ε * M.s i) *
                    Real.exp ((t₀ - t₁) * M.s i)) :=
              cancel_escale_sq _ _ _ _ _ _ he_ne
            have h4 : Real.exp (ε * M.s i) *
                ((((chart.W.sources i).card : ℝ) * ((chart.W.targets i).card : ℝ)) /
                  (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2) *
                (((Creg : ℝ) * ((1 + ρ) * (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2 *
                  Real.exp (ε * M.s i))) * (2 * Real.exp ((t₀ - t₁) * M.s i))) ≤
                2 * (Creg : ℝ) * (1 + ρ) *
                  ((chart.pool.S.card : ℝ) ^ 2 / (1 - ρ) ^ 2) *
                  Real.exp (-δ * M.s i) := by
              have h4a : Real.exp (ε * M.s i) *
                  ((((chart.W.sources i).card : ℝ) * ((chart.W.targets i).card : ℝ)) /
                    (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2) *
                  (((Creg : ℝ) * ((1 + ρ) * (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2 *
                    Real.exp (ε * M.s i))) * (2 * Real.exp ((t₀ - t₁) * M.s i))) =
                  2 * (Creg : ℝ) * (1 + ρ) *
                    (((chart.W.sources i).card : ℝ) * ((chart.W.targets i).card : ℝ)) *
                    (Real.exp (ε * M.s i) * Real.exp (ε * M.s i) *
                      Real.exp ((t₀ - t₁) * M.s i)) := heq
              have h4b : 2 * (Creg : ℝ) * (1 + ρ) *
                  (((chart.W.sources i).card : ℝ) * ((chart.W.targets i).card : ℝ)) *
                  (Real.exp (ε * M.s i) * Real.exp (ε * M.s i) *
                    Real.exp ((t₀ - t₁) * M.s i)) =
                  2 * (Creg : ℝ) * (1 + ρ) *
                    (((chart.W.sources i).card : ℝ) * ((chart.W.targets i).card : ℝ)) *
                    Real.exp (-δ * M.s i) := by
                rw [hexp_combine]
              have h4c : 2 * (Creg : ℝ) * (1 + ρ) *
                  (((chart.W.sources i).card : ℝ) * ((chart.W.targets i).card : ℝ)) *
                  Real.exp (-δ * M.s i) ≤
                  2 * (Creg : ℝ) * (1 + ρ) *
                    ((chart.pool.S.card : ℝ) ^ 2 / (1 - ρ) ^ 2) *
                    Real.exp (-δ * M.s i) := by
                have hinner : 2 * (Creg : ℝ) * (1 + ρ) *
                    (((chart.W.sources i).card : ℝ) * ((chart.W.targets i).card : ℝ)) ≤
                    2 * (Creg : ℝ) * (1 + ρ) *
                      ((chart.pool.S.card : ℝ) ^ 2 / (1 - ρ) ^ 2) :=
                  mul_le_mul_of_nonneg_left hWp_le hKnn
                exact mul_le_mul_of_nonneg_right hinner (Real.exp_nonneg _)
              calc Real.exp (ε * M.s i) *
                    ((((chart.W.sources i).card : ℝ) * ((chart.W.targets i).card : ℝ)) /
                      (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2) *
                    (((Creg : ℝ) * ((1 + ρ) * (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2 *
                      Real.exp (ε * M.s i))) * (2 * Real.exp ((t₀ - t₁) * M.s i)))
                  = 2 * (Creg : ℝ) * (1 + ρ) *
                      (((chart.W.sources i).card : ℝ) * ((chart.W.targets i).card : ℝ)) *
                      (Real.exp (ε * M.s i) * Real.exp (ε * M.s i) *
                        Real.exp ((t₀ - t₁) * M.s i)) := heq
                _ = 2 * (Creg : ℝ) * (1 + ρ) *
                      (((chart.W.sources i).card : ℝ) * ((chart.W.targets i).card : ℝ)) *
                      Real.exp (-δ * M.s i) := h4b
                _ ≤ 2 * (Creg : ℝ) * (1 + ρ) *
                      ((chart.pool.S.card : ℝ) ^ 2 / (1 - ρ) ^ 2) *
                      Real.exp (-δ * M.s i) := h4c
            calc Real.exp (ε * M.s i) *
                  ((((chart.W.sources i).card : ℝ) * ((chart.W.targets i).card : ℝ)) /
                    (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2) *
                  ((AffineFamily.degree bad : ℚ) : ℝ)
                ≤ Real.exp (ε * M.s i) *
                  ((((chart.W.sources i).card : ℝ) * ((chart.W.targets i).card : ℝ)) /
                    (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2) *
                  (((Creg : ℝ) * ((AffineFamily.degree Famsurv : ℚ) : ℝ)) *
                    (((T0n : ℕ) : ℝ) / ((T1n : ℕ) : ℝ))) := hX
              _ ≤ 2 * (Creg : ℝ) * (1 + ρ) *
                    ((chart.pool.S.card : ℝ) ^ 2 / (1 - ρ) ^ 2) *
                    Real.exp (-δ * M.s i) := h3.trans h4
          _ ≤ 2 * (Creg : ℝ) * (1 + ρ) *
              ((chart.pool.S.card : ℝ) ^ 2 / (1 - ρ) ^ 2) *
              Cexc := by
              have hK2 : (0 : ℝ) ≤ 2 * (Creg : ℝ) * (1 + ρ) *
                  ((chart.pool.S.card : ℝ) ^ 2 / (1 - ρ) ^ 2) := hK2nn
              exact mul_le_mul_of_nonneg_left hexp hK2
          _ = (ρ' / 3) * (chart.pool.S.card : ℝ) ^ 2 := by
              rw [hCexcdef, hθgdef]
              field_simp
    set Γg : Finset (RPoint d × RPoint d) :=
      chart.G.filter (fun pq => MvPolynomial.eval (outerLabelPt i₀ pq) g = 0) with hΓgdef
    set DgSet : Finset (RPoint d × RPoint d) :=
      Γg.filter (fun pq => commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈ Famsurv ∧
        commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∉ bad) with hDgSetdef
    -- `g` transported to pair coordinates: degree and eval match `g`.
    have hGg_eq : commonPairEquation (MvPolynomial.rename finSumFinEquiv.symm g) = g := by
      unfold commonPairEquation
      rw [MvPolynomial.rename_rename, Equiv.self_comp_symm]
      exact MvPolynomial.rename_id_apply _
    have heval_corr : ∀ pq : RPoint d × RPoint d,
        MvPolynomial.eval (TrackD.labelPt i₀ (TrackD.toC pq.1) (TrackD.toC pq.2))
          (MvPolynomial.rename finSumFinEquiv.symm g) =
          MvPolynomial.eval (outerLabelPt i₀ pq) g := by
      intro pq
      rw [MvPolynomial.eval_rename]
      congr 1
    have hBpos : (0 : ℝ) < regime.B i := by linarith [hB1]
    have hBcfg : regime.B i = TrackD.cfgB (regime.P i) := rfl
    have hsource : TrackD.CarrierAssignment (T.sources i) (j + 1) (chart.W.owner i) := by
      intro X hX q hq
      exact chart.W.supported i X (Finset.mem_union_left _ hX) q hq
    have htarget : TrackD.CarrierAssignment (T.targets i) (j + 1) (chart.W.owner i) := by
      intro Y hY q hq
      exact chart.W.supported i Y (Finset.mem_union_right _ hY) q hq
    have hGgdeg : ∀ G ∈ ({MvPolynomial.rename finSumFinEquiv.symm g} : Set (TrackD.PairPoly d)),
        (G.totalDegree : ℝ) ≤ (Creg : ℝ) * TrackD.testDeg (TrackD.cfgB (regime.P i)) (M.s i) τg := by
      intro G hG
      rw [Set.mem_singleton_iff] at hG
      subst hG
      have c1 : ((MvPolynomial.rename finSumFinEquiv.symm g).totalDegree : ℝ) ≤
          ((g.totalDegree : ℕ) : ℝ) := by
        exact_mod_cast MvPolynomial.totalDegree_rename_le _ _
      have c2 : ((g.totalDegree : ℕ) : ℝ) ≤ (Creg : ℝ) * ((T1n : ℕ) : ℝ) := by
        exact_mod_cast hgdeg
      have c3 : ((T1n : ℕ) : ℝ) ≤ TrackD.testDeg (regime.B i) (M.s i) t₁ := by
        rw [hT1ndef]
        exact Nat.floor_le (le_trans zero_le_one hfl1.1)
      have c4 : TrackD.testDeg (regime.B i) (M.s i) t₁ ≤
          TrackD.testDeg (regime.B i) (M.s i) τg := by
        unfold TrackD.testDeg
        refine mul_le_mul_of_nonneg_left ?_ hBpos.le
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_right ht₁τg.le (M.width_pos i).le
      have c5 : (Creg : ℝ) * ((T1n : ℕ) : ℝ) ≤
          (Creg : ℝ) * TrackD.testDeg (regime.B i) (M.s i) τg :=
        mul_le_mul_of_nonneg_left (c3.trans c4) hCregRpos.le
      have c6 : ((MvPolynomial.rename finSumFinEquiv.symm g).totalDegree : ℝ) ≤
          (Creg : ℝ) * TrackD.testDeg (regime.B i) (M.s i) τg :=
        c1.trans (c2.trans c5)
      rwa [hBcfg] at c6
    have hΓsub : Γg ⊆ TrackD.poolPts (T.sources i) ×ˢ TrackD.poolPts (T.targets i) := by
      intro pq hpq
      have hG : pq ∈ chart.G := (Finset.mem_filter.mp hpq).1
      obtain ⟨h1S, h2S⟩ := chart.hGmem pq hG
      have h1P : pq.1 ∈ TrackD.poolPts (T.sources i) := chart.pool.hSsub h1S
      have h2P : pq.2 ∈ TrackD.poolPts (T.sources i) := chart.pool.hSsub h2S
      have houter_eq : T.sources i = T.targets i := (houter i).1
      have h2Pt : pq.2 ∈ TrackD.poolPts (T.targets i) := houter_eq ▸ h2P
      exact Finset.mem_product.mpr ⟨h1P, h2Pt⟩
    have hgraph : ∀ pq ∈ Γg, (TrackD.toC pq.2 - TrackD.toC pq.1) i₀ ≠ 0 ∧
        ∀ G ∈ ({MvPolynomial.rename finSumFinEquiv.symm g} : Set (TrackD.PairPoly d)),
          MvPolynomial.eval (TrackD.labelPt i₀ (TrackD.toC pq.1) (TrackD.toC pq.2)) G = 0 := by
      intro pq hpq
      have hG : pq ∈ chart.G := (Finset.mem_filter.mp hpq).1
      have hz : MvPolynomial.eval (outerLabelPt i₀ pq) g = 0 :=
        (Finset.mem_filter.mp hpq).2
      refine ⟨chart.hchart pq hG, ?_⟩
      intro G hGmem
      rw [Set.mem_singleton_iff] at hGmem
      subst hGmem
      rw [heval_corr pq]
      exact hz
    have hBad := hproduct (regime.P i) (T.sources i) (T.targets i)
      (M.s i) (ρ₀ / 2) M.b (by linarith) hpool.1 hpool.2 hsW (j + 1) hj1 τg hplateau
      hTdeg (chart.W.owner i) (chart.W.owner i) hsource htarget i₀
      ({MvPolynomial.rename finSumFinEquiv.symm g} : Set (TrackD.PairPoly d))
      hGgdeg Γg hΓsub hgraph
    have hDgSub : DgSet ⊆ Γg.filter (fun pq => ∃ G ∈
        ({MvPolynomial.rename finSumFinEquiv.symm g} : Set (TrackD.PairPoly d)),
        ∃ x ∈ chart.W.owner i pq.1, ∃ y ∈ chart.W.owner i pq.2,
          (y - x) i₀ ≠ 0 ∧ MvPolynomial.eval (TrackD.labelPt i₀ x y) G ≠ 0) := by
      intro pq hpq
      have hΓ : pq ∈ Γg := (Finset.mem_filter.mp hpq).1
      have hVmem : commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈ Famsurv :=
        (Finset.mem_filter.mp hpq).2.1
      have hVnb : commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∉ bad :=
        (Finset.mem_filter.mp hpq).2.2
      have hnim : commonPairEquation (MvPolynomial.rename finSumFinEquiv.symm g) ∉
          (commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2)).ideal := by
        rw [hGg_eq]
        exact hggood _ hVmem hVnb
      have hnpair : ∃ x ∈ chart.W.owner i pq.1, ∃ y ∈ chart.W.owner i pq.2,
          (y - x) i₀ ≠ 0 ∧
            MvPolynomial.eval (TrackD.labelPt i₀ x y)
              (MvPolynomial.rename finSumFinEquiv.symm g) ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact hnim ((common_product_image_equation_iff i₀
          (chart.W.owner i pq.1) (chart.W.owner i pq.2)
          (MvPolynomial.rename finSumFinEquiv.symm g)).mpr hcon)
      obtain ⟨x, hx, y, hy, hchart, hzero⟩ := hnpair
      exact Finset.mem_filter.mpr ⟨hΓ, MvPolynomial.rename finSumFinEquiv.symm g,
        Set.mem_singleton_iff.mpr rfl, x, hx, y, hy, hchart, hzero⟩
    have hcardmono : (DgSet.card : ℝ) ≤
        ((Γg.filter (fun pq => ∃ G ∈
          ({MvPolynomial.rename finSumFinEquiv.symm g} : Set (TrackD.PairPoly d)),
          ∃ x ∈ chart.W.owner i pq.1, ∃ y ∈ chart.W.owner i pq.2,
            (y - x) i₀ ≠ 0 ∧ MvPolynomial.eval (TrackD.labelPt i₀ x y) G ≠ 0)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hDgSub
    have houter_eq2 : T.sources i = T.targets i := (houter i).1
    have hpool_eq2 : TrackD.poolPts (T.sources i) =
        TrackD.poolPts (T.targets i) := by rw [houter_eq2]
    have hcard_eq2 : ((TrackD.poolPts (T.targets i)).card : ℝ) =
        ((TrackD.poolPts (T.sources i)).card : ℝ) := by rw [hpool_eq2]
    have hS_le2 : ((TrackD.poolPts (T.sources i)).card : ℝ) ≤
        (chart.pool.S.card : ℝ) / (1 - ρ) := by
      rw [le_div_iff₀ h1mρpos, mul_comm]
      exact chart.pool.hScard
    have hconv : θg * ((TrackD.poolPts (T.sources i)).card : ℝ) *
        ((TrackD.poolPts (T.targets i)).card : ℝ) ≤
        (ρ' / 3) * (chart.pool.S.card : ℝ) ^ 2 := by
      have hPSPT : ((TrackD.poolPts (T.sources i)).card : ℝ) *
          ((TrackD.poolPts (T.targets i)).card : ℝ) ≤
          ((chart.pool.S.card : ℝ) / (1 - ρ)) * ((chart.pool.S.card : ℝ) / (1 - ρ)) := by
        rw [hcard_eq2]
        exact mul_le_mul hS_le2 hS_le2 (Nat.cast_nonneg _)
          (div_nonneg (Nat.cast_nonneg _) h1mρpos.le)
      have h1mρsq_ne : (1 - ρ : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt h1mρpos)
      have h1mρ_ne : (1 - ρ : ℝ) ≠ 0 := ne_of_gt h1mρpos
      calc θg * ((TrackD.poolPts (T.sources i)).card : ℝ) *
            ((TrackD.poolPts (T.targets i)).card : ℝ)
          = θg * (((TrackD.poolPts (T.sources i)).card : ℝ) *
            ((TrackD.poolPts (T.targets i)).card : ℝ)) := by ring
        _ ≤ θg * (((chart.pool.S.card : ℝ) / (1 - ρ)) *
            ((chart.pool.S.card : ℝ) / (1 - ρ))) :=
          mul_le_mul_of_nonneg_left hPSPT hθg.le
        _ = (ρ' / 3) * (chart.pool.S.card : ℝ) ^ 2 := by
          rw [hθgdef]
          exact cancel_theta_sq _ _ _ h1mρ_ne
    have hDg : ((DgSet).card : ℝ) ≤ (ρ' / 3) * (chart.pool.S.card : ℝ) ^ 2 :=
      hcardmono.trans (hBad.trans hconv)
    -- `Eqs` degree `≤ B^(2-c)` (via `T1n ≤ T_s(t₁) ≤ B^(2-c)`, `hB1`).
    have hEqdeg : ∀ G ∈ Eqs, (G.totalDegree : ℝ) ≤ (regime.B i) ^ (2 - c) := by
      intro G hG
      rw [hEqsdef] at hG
      rw [List.mem_toFinset] at hG
      obtain ⟨f, hfE, rfl⟩ := List.mem_map.mp hG
      have hBpos : (0 : ℝ) < regime.B i := by linarith [hB1]
      have c1 : ((MvPolynomial.rename finSumFinEquiv.symm f).totalDegree : ℝ) ≤
          ((f.totalDegree : ℕ) : ℝ) := by
        exact_mod_cast MvPolynomial.totalDegree_rename_le _ _
      have c2 : ((f.totalDegree : ℕ) : ℝ) ≤ ((T1n : ℕ) : ℝ) := by
        exact_mod_cast (hE f hfE).2
      have c3 : ((T1n : ℕ) : ℝ) ≤ TrackD.testDeg (regime.B i) (M.s i) t₁ := by
        rw [hT1ndef]
        exact Nat.floor_le (le_trans zero_le_one hfl1.1)
      have c4 : TrackD.testDeg (regime.B i) (M.s i) t₁ ≤
          (regime.B i) ^ ((1 : ℝ) + t₁) :=
        le_of_eq (testDeg_eq_rpow_of_logB _ _ _ hBpos (hs i))
      have c5 : (1 : ℝ) + t₁ ≤ 2 - c := by linarith
      have c6 : (regime.B i) ^ ((1 : ℝ) + t₁) ≤ (regime.B i) ^ (2 - c) :=
        regularity_degree_le_Bpow _ _ _ _ hB1 le_rfl c5
      exact c1.trans (c2.trans (c3.trans (c4.trans c6)))
    -- Vanishing on surviving images (locus ideal + prime).
    have hvanish : ∀ pq ∈ chart.G, good pq → ∀ G ∈ Eqs,
        commonPairEquation G ∈
          (commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2)).ideal := by
      have hvanishE : ∀ f ∈ E, ∀ V ∈ Famsurv, f ∈ V.ideal := by
        intro f hfE V hVFam
        rw [TrackD.mem_ideal_iff_eval_zero]
        intro x hx
        have hfL : f ∈ (AffineFamily.locus Famsurv).ideal := (hE f hfE).1
        have hxL : x ∈ (AffineFamily.locus Famsurv).points := by
          rw [AffineFamily.points_locus]
          exact Set.mem_biUnion hVFam hx
        have hz := (TrackD.mem_ideal_iff_eval_zero _ _).mp hfL _ hxL
        exact hz
      intro pq hpq hgoodpq G hG
      have hparts : pq ∈ chart.G ∧ pq ∉ D189 ∧
          commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∉ bad ∧
          MvPolynomial.eval (outerLabelPt i₀ pq) g ≠ 0 := hgoodpq
      obtain ⟨-, hnotD, hnim, hne⟩ := hparts
      have hUmemV : commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈ chart.U :=
        chart.hUmem pq hpq
      have hcompsV : commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈
          Bridges.envelopeComponents (⋃ Z ∈ chart.U, Z.points) T0n :=
        hDmem pq (Finset.mem_sdiff.mpr ⟨hpq, hnotD⟩)
      have hFamV : commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈ Famsurv :=
        Finset.mem_filter.mpr ⟨hUmemV, hcompsV⟩
      rw [hEqsdef] at hG
      rw [List.mem_toFinset] at hG
      obtain ⟨f, hfE, rfl⟩ := List.mem_map.mp hG
      have hround : commonPairEquation (MvPolynomial.rename finSumFinEquiv.symm f) = f := by
        unfold commonPairEquation
        rw [MvPolynomial.rename_rename, Equiv.self_comp_symm]
        exact MvPolynomial.rename_id_apply _
      rw [hround]
      exact hvanishE f hfE _ hFamV
    -- Smooth `2k`-fold at surviving labels (minor cert + tangent).
    have hsmooth : ∀ pq ∈ chart.G, good pq →
        Module.finrank ℂ (TrackD.jacKer (Eqs.image commonPairEquation)
          (outerLabelPt i₀ pq)) = 2 * k := by
      have hvanishE2 : ∀ f ∈ E, ∀ V ∈ Famsurv, f ∈ V.ideal := by
        intro f hfE V hVFam
        rw [TrackD.mem_ideal_iff_eval_zero]
        intro x hx
        have hfL : f ∈ (AffineFamily.locus Famsurv).ideal := (hE f hfE).1
        have hxL : x ∈ (AffineFamily.locus Famsurv).points := by
          rw [AffineFamily.points_locus]
          exact Set.mem_biUnion hVFam hx
        have hz := (TrackD.mem_ideal_iff_eval_zero _ _).mp hfL _ hxL
        exact hz
      have hround_all : ∀ f : Poly (d + d),
          commonPairEquation (MvPolynomial.rename finSumFinEquiv.symm f) = f := by
        intro f
        unfold commonPairEquation
        rw [MvPolynomial.rename_rename, Equiv.self_comp_symm]
        exact MvPolynomial.rename_id_apply _
      have hImEq : Finset.image commonPairEquation Eqs = E.toFinset := by
        ext y
        simp only [Finset.mem_image, List.mem_toFinset, hEqsdef]
        constructor
        · rintro ⟨G, hGmap, hGeq⟩
          obtain ⟨f, hfE, hfG⟩ := List.mem_map.mp hGmap
          have hyf : y = f := by rw [←hGeq, ←hfG, hround_all f]
          rwa [hyf]
        · intro hy
          exact ⟨MvPolynomial.rename finSumFinEquiv.symm y,
            List.mem_map.mpr ⟨y, hy, rfl⟩, hround_all y⟩
      intro pq hpq hgoodpq
      have hparts : pq ∈ chart.G ∧ pq ∉ D189 ∧
          commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∉ bad ∧
          MvPolynomial.eval (outerLabelPt i₀ pq) g ≠ 0 := hgoodpq
      obtain ⟨-, hnotD, hnim, hne⟩ := hparts
      have hUmemV : commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈ chart.U :=
        chart.hUmem pq hpq
      have hcompsV : commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈
          Bridges.envelopeComponents (⋃ Z ∈ chart.U, Z.points) T0n :=
        hDmem pq (Finset.mem_sdiff.mpr ⟨hpq, hnotD⟩)
      have hFamV : commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈ Famsurv :=
        Finset.mem_filter.mpr ⟨hUmemV, hcompsV⟩
      obtain ⟨hVirr, hVdim⟩ := hFampure _ hFamV
      have hx : outerLabelPt i₀ pq ∈
          commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) :=
        chart.hlabel pq hpq
      have hk2le : 2 * k ≤ d + d := by omega
      have hdim : (commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2)).dimension =
          (d + d) - ((d + d) - 2 * k) := by omega
      have hEV : ∀ f ∈ E,
          f ∈ (commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2)).ideal :=
        fun f hfE => hvanishE2 f hfE _ hFamV
      obtain ⟨hsm, heq⟩ := TrackD.carrier_smooth_of_minor
        (commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2))
        hVirr ((d + d) - 2 * k) (Nat.sub_le _ _) hdim E hEV g hgspan
        (outerLabelPt i₀ pq) hx hne
      rw [hImEq]
      obtain ⟨hmem, hfin⟩ := hsm
      rw [← heq, hfin,
        (commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2)).localDimension_eq_dimension
          (outerLabelPt i₀ pq) hVirr hx]
      exact hVdim
    -- Assemble the certificate: deletions `D189 ∪ Exc ∪ Dg` cost `ρ'|S|²`.
    have hG' : chart'.G = chart.G := rfl
    have hS' : chart'.pool.S = chart.pool.S := rfl
    have hsub : chart'.G.filter (fun pq => ¬ good pq) ⊆
        D189 ∪ chart.G.filter (fun pq =>
          commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈ bad) ∪
        DgSet := by
      intro pq hpq
      have hmem : pq ∈ chart'.G := (Finset.mem_filter.mp hpq).1
      rw [hG'] at hmem
      have hng : ¬ good pq := (Finset.mem_filter.mp hpq).2
      have hparts_neg : ¬ (pq ∈ chart.G ∧ pq ∉ D189 ∧
          commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∉ bad ∧
          MvPolynomial.eval (outerLabelPt i₀ pq) g ≠ 0) := hng
      by_cases hD : pq ∈ D189
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hD)))
      · by_cases hnb : commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈ bad
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr
            (Finset.mem_filter.mpr ⟨hmem, hnb⟩))))
        · have hE0 : MvPolynomial.eval (outerLabelPt i₀ pq) g = 0 := by
            by_contra hne
            exact hparts_neg ⟨hmem, hD, hnb, hne⟩
          have hUmemV : commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈ chart.U :=
            chart.hUmem pq hmem
          have hcompsV : commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈
              Bridges.envelopeComponents (⋃ Z ∈ chart.U, Z.points) T0n :=
            hDmem pq (Finset.mem_sdiff.mpr ⟨hmem, hD⟩)
          have hFamV : commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈ Famsurv :=
            Finset.mem_filter.mpr ⟨hUmemV, hcompsV⟩
          have hΓ : pq ∈ Γg :=
            Finset.mem_filter.mpr ⟨hmem, hE0⟩
          have hDgmem : pq ∈ DgSet :=
            Finset.mem_filter.mpr ⟨hΓ, hFamV, hnb⟩
          exact Finset.mem_union.mpr (Or.inr hDgmem)
    have hcardle : ((chart'.G.filter (fun pq => ¬ good pq)).card : ℝ) ≤
        ((D189.card : ℝ) + ((chart.G.filter (fun pq =>
          commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈ bad)).card : ℝ)) +
        ((DgSet).card : ℝ) := by
      have h1 : ((chart'.G.filter (fun pq => ¬ good pq)).card : ℝ) ≤
          ((D189 ∪ chart.G.filter (fun pq =>
            commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈ bad) ∪
            DgSet).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      have h2 : ((D189 ∪ chart.G.filter (fun pq =>
          commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈ bad) ∪
          DgSet).card : ℝ) ≤ (((D189.card : ℝ) +
          ((chart.G.filter (fun pq =>
            commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈ bad)).card : ℝ))) +
          ((DgSet).card : ℝ) := by
        have u1 : (D189 ∪ chart.G.filter (fun pq =>
            commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈ bad) ∪
            DgSet).card ≤ (D189 ∪ chart.G.filter (fun pq =>
            commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈ bad)).card +
            DgSet.card :=
          Finset.card_union_le _ _
        have u2 : (D189 ∪ chart.G.filter (fun pq =>
            commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈ bad)).card ≤
            D189.card + (chart.G.filter (fun pq =>
            commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈ bad)).card :=
          Finset.card_union_le _ _
        have u1R : ((D189 ∪ chart.G.filter (fun pq =>
            commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈ bad) ∪
            DgSet).card : ℝ) ≤
            ((D189 ∪ chart.G.filter (fun pq =>
            commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈ bad)).card : ℝ) +
            (DgSet.card : ℝ) := by
          exact_mod_cast u1
        have u2R : ((D189 ∪ chart.G.filter (fun pq =>
            commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈ bad)).card : ℝ) ≤
            (D189.card : ℝ) + ((chart.G.filter (fun pq =>
            commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈ bad)).card : ℝ) := by
          exact_mod_cast u2
        linarith
      linarith [h1, h2]
    have hbad : ((chart'.G.filter (fun pq => ¬ good pq)).card : ℝ) ≤
        ρ' * (chart'.pool.S.card : ℝ) ^ 2 := by
      rw [hS']
      linarith [hcardle, add_le_add (add_le_add hDcard hDexc) hDg]
    refine ⟨chart', Eqs, good, hEqdeg, ?_, hvanish, hsmooth⟩
    convert hbad using 2
    congr
  · push_neg at h10
    have hβlow : -1 ≤ M.b ⟨j, hj⟩ := common_profile_time_lower M _
    have hcon : False := by linarith
    exact False.elim hcon

/-- sc:outer-regularity.smooth-family (sparse-cones.tex:492–524).
Input: the surviving images are irreducible `2k`-dimensional components of
`V = Env_{T₀}(U)` (189, at every budget). Fix `t₁ = (1 + t₀)/2`,
`T₁ = T_s(t₁)`, and `c = (1 - t₁)/2`. Apply `TrackA.poly_regularity`
(Regularity.lean:59) to the pure family `ℐ` of surviving images at degree
`T₁` (`FromAffineLists ℐ T₀`): the exceptional subfamily has degree
`≤ C deg(ℐ) T₀/T₁ ≤ (1+ρ) e_j² e^{εs - (t₁-t₀)s}`; its pair mass via the chart's
`hmassW` is `≤ e^{2εs-(t₁-t₀)s}·|S|²·O(1) = o(|S|²)` (`hεt`). The regularity
certificate `g` (degree `O(T₁)`) is nonzero on each remaining image; its cleared
pullback numerator is nonidentically zero on every remaining carrier pair;
product testing (`TrackD.prof_product_testing_labels`, Profiles/Regularity.lean,
times in `(t₁, (1+t₁)/2)`) removes its actual zeros at cost `o(|S|²)`. At the
surviving labels the equations `E` (degree `≤ T₁ ≤ B^{2-c}`, since
`s = log B`) are a smooth `2k`-fold (`hsmooth`), and they vanish on every
surviving image. The good predicate excludes the 189 deletion, the exceptional
images and the product-testing zeros. The global physical sequence `W` is
threaded through unchanged (input charts and the output cert satisfy
`chart.W = W`); 191 consumes the pin. The plateau hypotheses `hj`, `houter`,
`htop`, `ht₀β` are those identified by lane m-o-r190 (product testing needs
`(t₁,t₂) ⊆ (β,1)` via `htop`+`ht₀β`, and the pool comparison needs `IsOuter`);
with them the body is the proved helper `outer_smooth_subfamily_of_plateau`
plus the `W`-pin threading. -/
theorem outer_smooth_subfamily {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (M : CommonPoolProfile T)
    (hs : ∀ i, M.s i = Real.log (regime.B i))
    (k j : ℕ) (hj : j < d) (hkj : k + j + 1 = d) (hk : 1 ≤ k ∧ k + 1 < d)
    (houter : ∀ i, T.IsOuter i)
    (htop : ∀ a : Fin d, j < a.val → M.b a = 1)
    (i₀ : Fin d) (ρ ε : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1) (hε : 0 < ε)
    (τ t₀ : ℝ) (ht₀1 : t₀ < 1) (ht₀β : M.b ⟨j, hj⟩ < t₀) (hεt : 4 * ε < 1 - t₀)
    (W : CommonPhysicalSequence T M (j + 1) τ)
    (h189 : ∀ ρ'' : ℝ, 0 < ρ'' → ∀ᶠ i in atTop,
      ∃ (chart : OuterChartCert T M k i j i₀ ρ ε ρ'' τ)
        (D : Finset (RPoint d × RPoint d)),
        chart.W = W ∧ D ⊆ chart.G ∧
        ((D.card : ℝ)) ≤ ρ'' * (chart.pool.S.card : ℝ) ^ 2 ∧
        ∀ pq ∈ chart.G \ D,
          commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈
            Bridges.envelopeComponents (⋃ Z ∈ chart.U, Z.points)
              (outerEnvDeg regime.B M.s t₀ i)) :
    ∃ c : ℝ, 0 < c ∧ ∀ ρ' : ℝ, 0 < ρ' → ∀ᶠ i in atTop,
      ∃ cert : OuterRegularityCert T M k i j i₀ ρ ε ρ'
        ((regime.B i) ^ (2 - c)) τ, cert.chart.W = W := by
  classical
  set t₁ : ℝ := (1 + t₀) / 2 with ht₁def
  have ht₀t₁ : t₀ < t₁ := by linarith
  have ht₁1 : t₁ < 1 := by linarith
  set c : ℝ := (1 - t₁) / 2 with hcdef
  have hcpos : 0 < c := by linarith
  refine ⟨c, hcpos, ?_⟩
  intro ρ' hρ'
  obtain ⟨Creg, hCregpos, hpolyreg⟩ := TrackA.poly_regularity (d + d)
  -- Fixed exponent gap for the exceptional bound (`hεt` gives `δ>0`).
  set δ : ℝ := (1 - t₀) / 2 - 2 * ε with hδdef
  have hδpos : 0 < δ := by linarith
  have hCregRpos : (0 : ℝ) < (Creg : ℝ) := by exact_mod_cast hCregpos
  have h1mρpos : (0 : ℝ) < 1 - ρ := by linarith
  have h1pρpos : (0 : ℝ) < 1 + ρ := by linarith
  set Cexc : ℝ := (ρ' / 3) * (1 - ρ) ^ 2 / (2 * (Creg : ℝ) * (1 + ρ)) with hCexcdef
  have hCexcpos : 0 < Cexc := by positivity
  have hexpEv : ∀ᶠ i in atTop, Real.exp (-δ * M.s i) ≤ Cexc := by
    have hpos : Filter.Tendsto (fun i => δ * M.s i) atTop atTop :=
      M.width_grows.const_mul_atTop hδpos
    have hExpTendsto : Filter.Tendsto (fun i => Real.exp (-δ * M.s i)) atTop (𝓝 0) := by
      have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp hpos
      simpa only [Function.comp_def, mul_neg, neg_mul] using h
    exact hExpTendsto.eventually (Iic_mem_nhds hCexcpos)
  have hBge1 : ∀ᶠ i in atTop, (1 : ℝ) ≤ regime.B i :=
    regime.B_tendsto.eventually_ge_atTop 1
  -- Product-testing time `τg ∈ (t₁,t₂)` off cuts, plateau margin, and uniform
  -- parameters (all independent of `i`; `htop`+`ht₀β` put `(t₁,t₂)` on
  -- plateau `j+1`, so the same `τg` works with every per-`i` chart `W`).
  have hj1 : j + 1 < d := by omega
  set t₂ : ℝ := (1 + t₁) / 2 with ht₂def
  have ht₁t₂ : t₁ < t₂ := by linarith
  obtain ⟨τg, ht₁τg, hτgt₂, _⟩ :=
    exists_time_avoiding_cuts M.b t₁ t₂ ht₁t₂
  have hβτg : M.b ⟨j, hj⟩ < τg := by linarith [ht₀β, ht₀t₁, ht₁τg]
  have hτg1 : τg < 1 := by linarith [hτgt₂, ht₁1]
  set ξ : ℝ := min (τg - M.b ⟨j, hj⟩) (1 - τg) with hξdef
  have hξ : 0 < ξ := by
    rw [hξdef]
    exact lt_min (sub_pos.mpr hβτg) (sub_pos.mpr hτg1)
  have hplateau : TrackD.OnPlateau M.b (j + 1) ξ τg := by
    intro a
    constructor
    · intro ha
      have hle : M.b a ≤ M.b ⟨j, hj⟩ := M.sorted (show a.val ≤ j by omega)
      have e1 : ξ ≤ τg - M.b ⟨j, hj⟩ := by
        rw [hξdef]
        exact min_le_left _ _
      linarith
    · intro ha
      have htopa : M.b a = 1 := htop a (by omega)
      have e2 : ξ ≤ 1 - τg := by
        rw [hξdef]
        exact min_le_right _ _
      rw [htopa]
      linarith [e2]
  set θg : ℝ := (ρ' / 3) * (1 - ρ) ^ 2 with hθgdef
  have hθg : 0 < θg := by positivity
  have hCreg1 : 1 ≤ Creg := hCregpos
  have hKg1 : (1 : ℝ) ≤ (Creg : ℝ) := by exact_mod_cast hCreg1
  obtain ⟨θ₁, hθ₁, η, hη, hηξ, ρ₀, hρ₀, s₁, hproduct⟩ :=
    TrackD.prof_product_testing_labels_with_margin d regime.dimension_ge_three
      θg hθg ξ hξ (Creg : ℝ) hKg1
  have hpoolEv : ∀ᶠ i in atTop,
      TrackD.PoolGood (regime.P i) θ₁ η 1 (ρ₀ / 2) (T.sources i) (M.s i) M.b ∧
      TrackD.PoolGood (regime.P i) θ₁ η 1 (ρ₀ / 2) (T.targets i) (M.s i) M.b :=
    M.good θ₁ hθ₁ η hη 1 le_rfl (ρ₀ / 2) (by positivity)
  have hwidthEv : ∀ᶠ i in atTop, s₁ ≤ M.s i :=
    M.width_grows.eventually_ge_atTop s₁
  by_cases h10 : (0 : ℝ) < 1 + t₀
  · have hb₁ : (0 : ℝ) < 1 + t₁ := by linarith
    have h189u := h189 (ρ' / 3) (by positivity)
    have ht1pos : (0 : ℝ) < t₁ := by linarith
    have hτg : -1 < τg := by linarith [ht₁τg]
    have htestEv : ∀ᶠ i in atTop, 1 ≤ TrackD.testDeg (TrackD.cfgB (regime.P i)) (M.s i) τg :=
      common_physical_test_degree_one M τg hτg
    filter_upwards [h189u,
      eventually_regularity_degree_dominates hs t₀ t₁ ht₀t₁ h10 hb₁ Creg,
      eventually_floor_ge_half hs t₀ h10,
      eventually_floor_ge_half hs t₁ hb₁, hexpEv, hBge1, hpoolEv, hwidthEv, htestEv] with i hi hdom hfl0 hfl1 hexp hB1 hpool hsW hTdeg
    obtain ⟨chart, D189, hchartW, hDsub, hDcard, hDmem⟩ := hi
    set T0n : ℕ := outerEnvDeg regime.B M.s t₀ i with hT0ndef
    set T1n : ℕ := ⌊TrackD.testDeg (regime.B i) (M.s i) t₁⌋₊ with hT1ndef
    have hT0eq : T0n = ⌊TrackD.testDeg (regime.B i) (M.s i) t₀⌋₊ := rfl
    set Famsurv : AffineFamily.Family (d + d) :=
      chart.U.filter (fun Z => Z ∈ Bridges.envelopeComponents
        (⋃ Z ∈ chart.U, Z.points) T0n) with hFamdef
    have hFamsubU : Famsurv ⊆ chart.U := Finset.filter_subset _ _
    have hFamsubEnv : Famsurv ⊆ Bridges.envelopeComponents
        (⋃ Z ∈ chart.U, Z.points) T0n := fun Z hZ => (Finset.mem_filter.mp hZ).2
    have hFampure : AffineFamily.IsPure Famsurv (2 * k) := by
      intro V hV
      obtain ⟨hVU, _⟩ := Finset.mem_filter.mp hV
      exact chart.hU V hVU
    have hFamLists : TrackA.FromAffineLists Famsurv T0n := by
      have hdef := TrackD.envelope_components_defined
        (⋃ Z ∈ chart.U, Z.points) T0n Famsurv hFamsubEnv
      have h1 : 1 ≤ T0n := hfl0.2.2
      exact fromLists_of_definedInDegree Famsurv T0n h1 hdef
    have hT0pos1 : 1 ≤ T0n := hfl0.2.2
    obtain ⟨bad, E, g, hbadsub, hbaddeg, hE, hgdeg, hgspan, hggood, hgerm⟩ :=
      hpolyreg Famsurv (2 * k) T0n T1n (by omega) hFampure hT0pos1 hFamLists hdom
    -- (`τg`, `t₂` fixed before `by_cases`; see above.)
    -- Widened chart (budget `ρ'/3 ≤ ρ'`), equations from `E`, good predicate
    -- excluding the 189 deletion, exceptional images and `g`-zeros.
    -- Bounds (`D_exc`, `D_g` each `≤ ρ'/3·|S|²`), degree, vanishing and
    -- smoothness follow below (using `houter`/`htop`/`ht₀β`).
    set chart' : OuterChartCert T M k i j i₀ ρ ε ρ' τ :=
      chart.mono (by linarith) with hchart'def
    set Eqs : Finset (TrackD.PairPoly d) :=
      (E.map (fun f => MvPolynomial.rename finSumFinEquiv.symm f)).toFinset with hEqsdef
    set good : RPoint d × RPoint d → Prop := fun pq =>
      pq ∈ chart.G ∧ pq ∉ D189 ∧
        commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∉ bad ∧
        MvPolynomial.eval (outerLabelPt i₀ pq) g ≠ 0 with hgooddef
    have hbadU : bad ⊆ chart.U := hbadsub.trans hFamsubU
    -- Exceptional pairs via `hmassW` + `hexp`/`hB1`/`houter` (full proof next).
    have hDexc : ((chart.G.filter (fun pq =>
        commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈ bad)).card : ℝ) ≤
        (ρ' / 3) * (chart.pool.S.card : ℝ) ^ 2 := by
      -- Degree nonnegativity from irreducibility (`one_le_degree`).
      have hdegNN_U : ∀ V ∈ chart.U, (0 : ℚ) ≤ V.degree := by
        intro V hV
        obtain ⟨hirr, _⟩ := chart.hU V hV
        have h1 : (1 : ℚ) ≤ V.degree := AffineVariety.one_le_degree V hirr.ne_top
        linarith
      have hFamdeg_le : AffineFamily.degree Famsurv ≤ AffineFamily.degree chart.U :=
        degree_filter_le _ _ hdegNN_U
      -- `hmassW` at `J = bad` + sum `≤ degree bad`.
      have hJsub : bad ⊆ chart.U := hbadU
      have hsum_le : ((∑ Z ∈ (commonChartImages chart.W chart.L i i₀).filter
          (fun Z => Z ∈ bad), (Z.degree : ℚ)) : ℚ) ≤ AffineFamily.degree bad := by
        have hdegNN_bad : ∀ V ∈ bad, (0 : ℚ) ≤ V.degree := by
          intro V hV
          have hVFam : V ∈ Famsurv := hbadsub hV
          obtain ⟨hirr, _⟩ := hFampure V hVFam
          have h1 : (1 : ℚ) ≤ V.degree := AffineVariety.one_le_degree V hirr.ne_top
          linarith
        have hsub : (commonChartImages chart.W chart.L i i₀).filter
            (fun Z => Z ∈ bad) ⊆ bad := by
          intro Z hZ
          exact (Finset.mem_filter.mp hZ).2
        unfold AffineFamily.degree
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun Z hZ _ => hdegNN_bad Z hZ)
      have hmass : ((chart.G.filter (fun pq =>
          commonProductImage i₀ (chart.W.owner i pq.1)
            (chart.W.owner i pq.2) ∈ bad)).card : ℝ) ≤
          Real.exp (ε * M.s i) *
            (((chart.W.sources i).card : ℝ) * (chart.W.targets i).card /
              (commonCarrierScale M (j + 1) i) ^ 2) *
            ((∑ Z ∈ (commonChartImages chart.W chart.L i i₀).filter
              (fun Z => Z ∈ bad), (Z.degree : ℚ)) : ℝ) :=
        chart.hmassW bad hbadU
      have hUdegR : ((AffineFamily.degree chart.U : ℚ) : ℝ) ≤
          (1 + ρ) * (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2 *
            Real.exp (ε * M.s i) :=
        chart.hUdeg
      have hFamdegR : ((AffineFamily.degree Famsurv : ℚ) : ℝ) ≤
          (1 + ρ) * (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2 *
            Real.exp (ε * M.s i) :=
        le_trans (by exact_mod_cast hFamdeg_le) hUdegR
      have hbaddegR : ((AffineFamily.degree bad : ℚ) : ℝ) ≤
          (Creg : ℝ) * ((AffineFamily.degree Famsurv : ℚ) : ℝ) *
            ((T0n : ℕ) : ℝ) / ((T1n : ℕ) : ℝ) := by
        exact_mod_cast hbaddeg
      -- Testing-degree facts at this index.
      have hBpos : (0 : ℝ) < regime.B i := by linarith [hB1]
      have hBne : regime.B i ≠ 0 := ne_of_gt hBpos
      have hT0nn : (0 : ℝ) ≤ TrackD.testDeg (regime.B i) (M.s i) t₀ :=
        le_trans zero_le_one hfl0.1
      have hT1pos : (0 : ℝ) < TrackD.testDeg (regime.B i) (M.s i) t₁ := by
        linarith [hfl1.1]
      have hT1n_posR : (0 : ℝ) < ((T1n : ℕ) : ℝ) := by
        have h1 : 1 ≤ T1n := hfl1.2.2
        exact_mod_cast Nat.pos_of_ne_zero (by omega)
      have hT0n_le : ((T0n : ℕ) : ℝ) ≤ TrackD.testDeg (regime.B i) (M.s i) t₀ := by
        rw [hT0eq]
        exact Nat.floor_le hT0nn
      have hT0T1 : TrackD.testDeg (regime.B i) (M.s i) t₀ /
          TrackD.testDeg (regime.B i) (M.s i) t₁ =
          Real.exp ((t₀ - t₁) * M.s i) := by
        unfold TrackD.testDeg
        rw [mul_div_mul_left _ _ hBne, ← Real.exp_sub]
        congr 1
        ring
      have hRatio : ((T0n : ℕ) : ℝ) / ((T1n : ℕ) : ℝ) ≤
          2 * Real.exp ((t₀ - t₁) * M.s i) := by
        have hT0nn : (0 : ℝ) ≤ TrackD.testDeg (regime.B i) (M.s i) t₀ :=
          le_trans zero_le_one hfl0.1
        have hT1nn : (0 : ℝ) ≤ TrackD.testDeg (regime.B i) (M.s i) t₁ :=
          le_trans zero_le_one hfl1.1
        have hhalf_pos : (0 : ℝ) < TrackD.testDeg (regime.B i) (M.s i) t₁ / 2 := by
          linarith [hfl1.1]
        have hle : ((T0n : ℕ) : ℝ) * (TrackD.testDeg (regime.B i) (M.s i) t₁ / 2) ≤
            TrackD.testDeg (regime.B i) (M.s i) t₀ * ((T1n : ℕ) : ℝ) :=
          calc ((T0n : ℕ) : ℝ) * (TrackD.testDeg (regime.B i) (M.s i) t₁ / 2)
              ≤ TrackD.testDeg (regime.B i) (M.s i) t₀ *
                (TrackD.testDeg (regime.B i) (M.s i) t₁ / 2) :=
                mul_le_mul_of_nonneg_right hT0n_le (le_of_lt hhalf_pos)
            _ ≤ TrackD.testDeg (regime.B i) (M.s i) t₀ * ((T1n : ℕ) : ℝ) :=
                mul_le_mul_of_nonneg_left hfl1.2.1 hT0nn
        have hstep : ((T0n : ℕ) : ℝ) / ((T1n : ℕ) : ℝ) ≤
            TrackD.testDeg (regime.B i) (M.s i) t₀ /
              (TrackD.testDeg (regime.B i) (M.s i) t₁ / 2) := by
          rw [div_le_div_iff₀ hT1n_posR hhalf_pos]
          exact hle
        have hT1ne : TrackD.testDeg (regime.B i) (M.s i) t₁ ≠ 0 :=
          ne_of_gt (by linarith [hfl1.1])
        have h2 : TrackD.testDeg (regime.B i) (M.s i) t₀ /
              (TrackD.testDeg (regime.B i) (M.s i) t₁ / 2) =
            2 * (TrackD.testDeg (regime.B i) (M.s i) t₀ /
              TrackD.testDeg (regime.B i) (M.s i) t₁) := by
          field_simp
        calc ((T0n : ℕ) : ℝ) / ((T1n : ℕ) : ℝ)
            ≤ TrackD.testDeg (regime.B i) (M.s i) t₀ /
              (TrackD.testDeg (regime.B i) (M.s i) t₁ / 2) := hstep
          _ = 2 * (TrackD.testDeg (regime.B i) (M.s i) t₀ /
              TrackD.testDeg (regime.B i) (M.s i) t₁) := h2
          _ = 2 * Real.exp ((t₀ - t₁) * M.s i) := by rw [hT0T1]
      -- eScale positivity and carrier-scale identification.
      have he_pos : (0 : ℝ) < TrackD.eScale (regime.B i) (M.s i) M.b (j + 1) := by
        unfold TrackD.eScale TrackD.cutScale TrackD.testDeg
        apply Finset.prod_pos
        intro a _
        exact mul_pos hBpos (Real.exp_pos _)
      have he_ne : TrackD.eScale (regime.B i) (M.s i) M.b (j + 1) ≠ 0 :=
        ne_of_gt he_pos
      have he2_ne : (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2 ≠ 0 :=
        pow_ne_zero 2 he_ne
      have hcommon_eq : commonCarrierScale M (j + 1) i =
          TrackD.eScale (regime.B i) (M.s i) M.b (j + 1) := rfl
      rw [hcommon_eq] at hmass
      -- Cast of the filtered sum bound to `ℝ`.
      have hsumR : ((∑ Z ∈ (commonChartImages chart.W chart.L i i₀).filter
          (fun Z => Z ∈ bad), (Z.degree : ℚ)) : ℝ) ≤
          ((AffineFamily.degree bad : ℚ) : ℝ) := by
        exact_mod_cast hsum_le
      -- Bridge for the bad-degree ratio shape.
      have hbaddegR' : ((AffineFamily.degree bad : ℚ) : ℝ) ≤
          ((Creg : ℝ) * ((AffineFamily.degree Famsurv : ℚ) : ℝ)) *
            (((T0n : ℕ) : ℝ) / ((T1n : ℕ) : ℝ)) := by
        rwa [mul_div_assoc] at hbaddegR
      have hr_nn : (0 : ℝ) ≤ ((T0n : ℕ) : ℝ) / ((T1n : ℕ) : ℝ) :=
        div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      have hCFd_le : (Creg : ℝ) * ((AffineFamily.degree Famsurv : ℚ) : ℝ) ≤
          (Creg : ℝ) * ((1 + ρ) * (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2 *
            Real.exp (ε * M.s i)) :=
        mul_le_mul_of_nonneg_left hFamdegR hCregRpos.le
      have hCU2nn : (0 : ℝ) ≤ (Creg : ℝ) *
          ((1 + ρ) * (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2 *
            Real.exp (ε * M.s i)) :=
        mul_nonneg hCregRpos.le
          (mul_nonneg (mul_nonneg h1pρpos.le (sq_nonneg _)) (Real.exp_nonneg _))
      have hDr_le : ((Creg : ℝ) * ((AffineFamily.degree Famsurv : ℚ) : ℝ)) *
          (((T0n : ℕ) : ℝ) / ((T1n : ℕ) : ℝ)) ≤
          ((Creg : ℝ) * ((1 + ρ) * (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2 *
            Real.exp (ε * M.s i))) * (2 * Real.exp ((t₀ - t₁) * M.s i)) := by
        have h1 : ((Creg : ℝ) * ((AffineFamily.degree Famsurv : ℚ) : ℝ)) *
            (((T0n : ℕ) : ℝ) / ((T1n : ℕ) : ℝ)) ≤
            ((Creg : ℝ) * ((1 + ρ) * (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2 *
              Real.exp (ε * M.s i))) * (((T0n : ℕ) : ℝ) / ((T1n : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right hCFd_le hr_nn
        have h2 : ((Creg : ℝ) * ((1 + ρ) * (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2 *
            Real.exp (ε * M.s i))) * (((T0n : ℕ) : ℝ) / ((T1n : ℕ) : ℝ)) ≤
            ((Creg : ℝ) * ((1 + ρ) * (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2 *
              Real.exp (ε * M.s i))) * (2 * Real.exp ((t₀ - t₁) * M.s i)) :=
          mul_le_mul_of_nonneg_left hRatio hCU2nn
        exact h1.trans h2
      -- Exponent combination `2ε + (t₀-t₁) = -δ`.
      have hexp_combine : Real.exp (ε * M.s i) * Real.exp (ε * M.s i) *
          Real.exp ((t₀ - t₁) * M.s i) = Real.exp (-δ * M.s i) := by
        have harg : ε * M.s i + ε * M.s i + (t₀ - t₁) * M.s i = -δ * M.s i := by
          rw [hδdef, ht₁def]
          ring
        calc Real.exp (ε * M.s i) * Real.exp (ε * M.s i) *
              Real.exp ((t₀ - t₁) * M.s i)
            = Real.exp (ε * M.s i + ε * M.s i + (t₀ - t₁) * M.s i) := by
              rw [← Real.exp_add, ← Real.exp_add]
          _ = Real.exp (-δ * M.s i) := by rw [harg]
      -- Pool-size conversion via `IsOuter`.
      have houter_eq : T.sources i = T.targets i := (houter i).1
      have hpool_eq : TrackD.poolPts (T.sources i) =
          TrackD.poolPts (T.targets i) := by rw [houter_eq]
      have hWs_le : ((chart.W.sources i).card : ℝ) ≤
          ((TrackD.poolPts (T.sources i)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
      have hWt_le : ((chart.W.targets i).card : ℝ) ≤
          ((TrackD.poolPts (T.sources i)).card : ℝ) := by
        calc ((chart.W.targets i).card : ℝ)
            ≤ ((TrackD.poolPts (T.targets i)).card : ℝ) := by
              exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
          _ = ((TrackD.poolPts (T.sources i)).card : ℝ) := by rw [hpool_eq]
      have hpoolS_le : ((TrackD.poolPts (T.sources i)).card : ℝ) ≤
          (chart.pool.S.card : ℝ) / (1 - ρ) := by
        rw [le_div_iff₀ h1mρpos, mul_comm]
        exact chart.pool.hScard
      have hWp_le : ((chart.W.sources i).card : ℝ) * ((chart.W.targets i).card : ℝ) ≤
          (chart.pool.S.card : ℝ) ^ 2 / (1 - ρ) ^ 2 := by
        have h1 : ((chart.W.sources i).card : ℝ) * ((chart.W.targets i).card : ℝ) ≤
            ((TrackD.poolPts (T.sources i)).card : ℝ) *
              ((TrackD.poolPts (T.sources i)).card : ℝ) :=
          mul_le_mul hWs_le hWt_le (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        have h2 : ((TrackD.poolPts (T.sources i)).card : ℝ) *
            ((TrackD.poolPts (T.sources i)).card : ℝ) ≤
            ((chart.pool.S.card : ℝ) / (1 - ρ)) * ((chart.pool.S.card : ℝ) / (1 - ρ)) :=
          mul_le_mul hpoolS_le hpoolS_le (Nat.cast_nonneg _)
            (div_nonneg (Nat.cast_nonneg _) h1mρpos.le)
        have h3 : ((chart.pool.S.card : ℝ) / (1 - ρ)) *
            ((chart.pool.S.card : ℝ) / (1 - ρ)) =
            (chart.pool.S.card : ℝ) ^ 2 / (1 - ρ) ^ 2 := by
          rw [div_mul_div_comm, ← pow_two, ← pow_two]
        rw [h3] at h2
        exact h1.trans h2
      have hCreg_ne : (Creg : ℝ) ≠ 0 := ne_of_gt hCregRpos
      have h1pρ_ne : (1 + ρ : ℝ) ≠ 0 := ne_of_gt h1pρpos
      have hden_ne : (2 : ℝ) * (Creg : ℝ) * (1 + ρ) ≠ 0 :=
        ne_of_gt (mul_pos (mul_pos (by norm_num) hCregRpos) h1pρpos)
      have h1mρsq_ne : (1 - ρ : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt h1mρpos)
      -- Coefficient nonnegativity facts.
      have hcoeff1nn : (0 : ℝ) ≤ Real.exp (ε * M.s i) *
          ((((chart.W.sources i).card : ℝ) * ((chart.W.targets i).card : ℝ)) /
            (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2) :=
        mul_nonneg (Real.exp_nonneg _)
          (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (sq_nonneg _))
      have hKnn : (0 : ℝ) ≤ 2 * (Creg : ℝ) * (1 + ρ) :=
        mul_nonneg (mul_nonneg (by norm_num) hCregRpos.le) h1pρpos.le
      have hK2nn : (0 : ℝ) ≤ 2 * (Creg : ℝ) * (1 + ρ) *
          ((chart.pool.S.card : ℝ) ^ 2 / (1 - ρ) ^ 2) :=
        mul_nonneg hKnn (div_nonneg (sq_nonneg _) (sq_nonneg _))
      -- Final chain.
      calc ((chart.G.filter (fun pq =>
            commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈ bad)).card : ℝ)
          ≤ Real.exp (ε * M.s i) *
            ((((chart.W.sources i).card : ℝ) * ((chart.W.targets i).card : ℝ)) /
              (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2) *
            ((AffineFamily.degree bad : ℚ) : ℝ) := by
            have h1 : Real.exp (ε * M.s i) *
                ((((chart.W.sources i).card : ℝ) * ((chart.W.targets i).card : ℝ)) /
                  (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2) *
                ((∑ Z ∈ (commonChartImages chart.W chart.L i i₀).filter
                  (fun Z => Z ∈ bad), (Z.degree : ℚ)) : ℝ) ≤
                Real.exp (ε * M.s i) *
                ((((chart.W.sources i).card : ℝ) * ((chart.W.targets i).card : ℝ)) /
                  (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2) *
                ((AffineFamily.degree bad : ℚ) : ℝ) :=
              mul_le_mul_of_nonneg_left hsumR hcoeff1nn
            -- `hmass` was rewritten to `eScale`; its middle now matches.
            exact hmass.trans h1
        _ ≤ 2 * (Creg : ℝ) * (1 + ρ) *
            ((chart.pool.S.card : ℝ) ^ 2 / (1 - ρ) ^ 2) *
            Real.exp (-δ * M.s i) := by
            have h1 : ((AffineFamily.degree bad : ℚ) : ℝ) ≤
                ((Creg : ℝ) * ((AffineFamily.degree Famsurv : ℚ) : ℝ)) *
                  (((T0n : ℕ) : ℝ) / ((T1n : ℕ) : ℝ)) := hbaddegR'
            have hX : Real.exp (ε * M.s i) *
                ((((chart.W.sources i).card : ℝ) * ((chart.W.targets i).card : ℝ)) /
                  (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2) *
                ((AffineFamily.degree bad : ℚ) : ℝ) ≤
                Real.exp (ε * M.s i) *
                ((((chart.W.sources i).card : ℝ) * ((chart.W.targets i).card : ℝ)) /
                  (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2) *
                (((Creg : ℝ) * ((AffineFamily.degree Famsurv : ℚ) : ℝ)) *
                  (((T0n : ℕ) : ℝ) / ((T1n : ℕ) : ℝ))) :=
              mul_le_mul_of_nonneg_left h1 hcoeff1nn
            -- Reassociate `FamdegR` into the middle factor.
            have h2 : ((Creg : ℝ) * ((AffineFamily.degree Famsurv : ℚ) : ℝ)) *
                (((T0n : ℕ) : ℝ) / ((T1n : ℕ) : ℝ)) ≤
                ((Creg : ℝ) * ((1 + ρ) * (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2 *
                  Real.exp (ε * M.s i))) * (2 * Real.exp ((t₀ - t₁) * M.s i)) :=
              hDr_le
            have h3 : Real.exp (ε * M.s i) *
                ((((chart.W.sources i).card : ℝ) * ((chart.W.targets i).card : ℝ)) /
                  (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2) *
                (((Creg : ℝ) * ((AffineFamily.degree Famsurv : ℚ) : ℝ)) *
                  (((T0n : ℕ) : ℝ) / ((T1n : ℕ) : ℝ))) ≤
                Real.exp (ε * M.s i) *
                ((((chart.W.sources i).card : ℝ) * ((chart.W.targets i).card : ℝ)) /
                  (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2) *
                (((Creg : ℝ) * ((1 + ρ) * (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2 *
                  Real.exp (ε * M.s i))) * (2 * Real.exp ((t₀ - t₁) * M.s i))) :=
              mul_le_mul_of_nonneg_left h2 hcoeff1nn
            -- Collapse `eScale²` and exponents.
            have heq : Real.exp (ε * M.s i) *
                ((((chart.W.sources i).card : ℝ) * ((chart.W.targets i).card : ℝ)) /
                  (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2) *
                (((Creg : ℝ) * ((1 + ρ) * (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2 *
                  Real.exp (ε * M.s i))) * (2 * Real.exp ((t₀ - t₁) * M.s i))) =
                2 * (Creg : ℝ) * (1 + ρ) *
                  (((chart.W.sources i).card : ℝ) * ((chart.W.targets i).card : ℝ)) *
                  (Real.exp (ε * M.s i) * Real.exp (ε * M.s i) *
                    Real.exp ((t₀ - t₁) * M.s i)) :=
              cancel_escale_sq _ _ _ _ _ _ he_ne
            have h4 : Real.exp (ε * M.s i) *
                ((((chart.W.sources i).card : ℝ) * ((chart.W.targets i).card : ℝ)) /
                  (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2) *
                (((Creg : ℝ) * ((1 + ρ) * (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2 *
                  Real.exp (ε * M.s i))) * (2 * Real.exp ((t₀ - t₁) * M.s i))) ≤
                2 * (Creg : ℝ) * (1 + ρ) *
                  ((chart.pool.S.card : ℝ) ^ 2 / (1 - ρ) ^ 2) *
                  Real.exp (-δ * M.s i) := by
              have h4a : Real.exp (ε * M.s i) *
                  ((((chart.W.sources i).card : ℝ) * ((chart.W.targets i).card : ℝ)) /
                    (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2) *
                  (((Creg : ℝ) * ((1 + ρ) * (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2 *
                    Real.exp (ε * M.s i))) * (2 * Real.exp ((t₀ - t₁) * M.s i))) =
                  2 * (Creg : ℝ) * (1 + ρ) *
                    (((chart.W.sources i).card : ℝ) * ((chart.W.targets i).card : ℝ)) *
                    (Real.exp (ε * M.s i) * Real.exp (ε * M.s i) *
                      Real.exp ((t₀ - t₁) * M.s i)) := heq
              have h4b : 2 * (Creg : ℝ) * (1 + ρ) *
                  (((chart.W.sources i).card : ℝ) * ((chart.W.targets i).card : ℝ)) *
                  (Real.exp (ε * M.s i) * Real.exp (ε * M.s i) *
                    Real.exp ((t₀ - t₁) * M.s i)) =
                  2 * (Creg : ℝ) * (1 + ρ) *
                    (((chart.W.sources i).card : ℝ) * ((chart.W.targets i).card : ℝ)) *
                    Real.exp (-δ * M.s i) := by
                rw [hexp_combine]
              have h4c : 2 * (Creg : ℝ) * (1 + ρ) *
                  (((chart.W.sources i).card : ℝ) * ((chart.W.targets i).card : ℝ)) *
                  Real.exp (-δ * M.s i) ≤
                  2 * (Creg : ℝ) * (1 + ρ) *
                    ((chart.pool.S.card : ℝ) ^ 2 / (1 - ρ) ^ 2) *
                    Real.exp (-δ * M.s i) := by
                have hinner : 2 * (Creg : ℝ) * (1 + ρ) *
                    (((chart.W.sources i).card : ℝ) * ((chart.W.targets i).card : ℝ)) ≤
                    2 * (Creg : ℝ) * (1 + ρ) *
                      ((chart.pool.S.card : ℝ) ^ 2 / (1 - ρ) ^ 2) :=
                  mul_le_mul_of_nonneg_left hWp_le hKnn
                exact mul_le_mul_of_nonneg_right hinner (Real.exp_nonneg _)
              calc Real.exp (ε * M.s i) *
                    ((((chart.W.sources i).card : ℝ) * ((chart.W.targets i).card : ℝ)) /
                      (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2) *
                    (((Creg : ℝ) * ((1 + ρ) * (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2 *
                      Real.exp (ε * M.s i))) * (2 * Real.exp ((t₀ - t₁) * M.s i)))
                  = 2 * (Creg : ℝ) * (1 + ρ) *
                      (((chart.W.sources i).card : ℝ) * ((chart.W.targets i).card : ℝ)) *
                      (Real.exp (ε * M.s i) * Real.exp (ε * M.s i) *
                        Real.exp ((t₀ - t₁) * M.s i)) := heq
                _ = 2 * (Creg : ℝ) * (1 + ρ) *
                      (((chart.W.sources i).card : ℝ) * ((chart.W.targets i).card : ℝ)) *
                      Real.exp (-δ * M.s i) := h4b
                _ ≤ 2 * (Creg : ℝ) * (1 + ρ) *
                      ((chart.pool.S.card : ℝ) ^ 2 / (1 - ρ) ^ 2) *
                      Real.exp (-δ * M.s i) := h4c
            calc Real.exp (ε * M.s i) *
                  ((((chart.W.sources i).card : ℝ) * ((chart.W.targets i).card : ℝ)) /
                    (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2) *
                  ((AffineFamily.degree bad : ℚ) : ℝ)
                ≤ Real.exp (ε * M.s i) *
                  ((((chart.W.sources i).card : ℝ) * ((chart.W.targets i).card : ℝ)) /
                    (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2) *
                  (((Creg : ℝ) * ((AffineFamily.degree Famsurv : ℚ) : ℝ)) *
                    (((T0n : ℕ) : ℝ) / ((T1n : ℕ) : ℝ))) := hX
              _ ≤ 2 * (Creg : ℝ) * (1 + ρ) *
                    ((chart.pool.S.card : ℝ) ^ 2 / (1 - ρ) ^ 2) *
                    Real.exp (-δ * M.s i) := h3.trans h4
          _ ≤ 2 * (Creg : ℝ) * (1 + ρ) *
              ((chart.pool.S.card : ℝ) ^ 2 / (1 - ρ) ^ 2) *
              Cexc := by
              have hK2 : (0 : ℝ) ≤ 2 * (Creg : ℝ) * (1 + ρ) *
                  ((chart.pool.S.card : ℝ) ^ 2 / (1 - ρ) ^ 2) := hK2nn
              exact mul_le_mul_of_nonneg_left hexp hK2
          _ = (ρ' / 3) * (chart.pool.S.card : ℝ) ^ 2 := by
              rw [hCexcdef, hθgdef]
              field_simp
    set Γg : Finset (RPoint d × RPoint d) :=
      chart.G.filter (fun pq => MvPolynomial.eval (outerLabelPt i₀ pq) g = 0) with hΓgdef
    set DgSet : Finset (RPoint d × RPoint d) :=
      Γg.filter (fun pq => commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈ Famsurv ∧
        commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∉ bad) with hDgSetdef
    -- `g` transported to pair coordinates: degree and eval match `g`.
    have hGg_eq : commonPairEquation (MvPolynomial.rename finSumFinEquiv.symm g) = g := by
      unfold commonPairEquation
      rw [MvPolynomial.rename_rename, Equiv.self_comp_symm]
      exact MvPolynomial.rename_id_apply _
    have heval_corr : ∀ pq : RPoint d × RPoint d,
        MvPolynomial.eval (TrackD.labelPt i₀ (TrackD.toC pq.1) (TrackD.toC pq.2))
          (MvPolynomial.rename finSumFinEquiv.symm g) =
          MvPolynomial.eval (outerLabelPt i₀ pq) g := by
      intro pq
      rw [MvPolynomial.eval_rename]
      congr 1
    have hBpos : (0 : ℝ) < regime.B i := by linarith [hB1]
    have hBcfg : regime.B i = TrackD.cfgB (regime.P i) := rfl
    have hsource : TrackD.CarrierAssignment (T.sources i) (j + 1) (chart.W.owner i) := by
      intro X hX q hq
      exact chart.W.supported i X (Finset.mem_union_left _ hX) q hq
    have htarget : TrackD.CarrierAssignment (T.targets i) (j + 1) (chart.W.owner i) := by
      intro Y hY q hq
      exact chart.W.supported i Y (Finset.mem_union_right _ hY) q hq
    have hGgdeg : ∀ G ∈ ({MvPolynomial.rename finSumFinEquiv.symm g} : Set (TrackD.PairPoly d)),
        (G.totalDegree : ℝ) ≤ (Creg : ℝ) * TrackD.testDeg (TrackD.cfgB (regime.P i)) (M.s i) τg := by
      intro G hG
      rw [Set.mem_singleton_iff] at hG
      subst hG
      have c1 : ((MvPolynomial.rename finSumFinEquiv.symm g).totalDegree : ℝ) ≤
          ((g.totalDegree : ℕ) : ℝ) := by
        exact_mod_cast MvPolynomial.totalDegree_rename_le _ _
      have c2 : ((g.totalDegree : ℕ) : ℝ) ≤ (Creg : ℝ) * ((T1n : ℕ) : ℝ) := by
        exact_mod_cast hgdeg
      have c3 : ((T1n : ℕ) : ℝ) ≤ TrackD.testDeg (regime.B i) (M.s i) t₁ := by
        rw [hT1ndef]
        exact Nat.floor_le (le_trans zero_le_one hfl1.1)
      have c4 : TrackD.testDeg (regime.B i) (M.s i) t₁ ≤
          TrackD.testDeg (regime.B i) (M.s i) τg := by
        unfold TrackD.testDeg
        refine mul_le_mul_of_nonneg_left ?_ hBpos.le
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_right ht₁τg.le (M.width_pos i).le
      have c5 : (Creg : ℝ) * ((T1n : ℕ) : ℝ) ≤
          (Creg : ℝ) * TrackD.testDeg (regime.B i) (M.s i) τg :=
        mul_le_mul_of_nonneg_left (c3.trans c4) hCregRpos.le
      have c6 : ((MvPolynomial.rename finSumFinEquiv.symm g).totalDegree : ℝ) ≤
          (Creg : ℝ) * TrackD.testDeg (regime.B i) (M.s i) τg :=
        c1.trans (c2.trans c5)
      rwa [hBcfg] at c6
    have hΓsub : Γg ⊆ TrackD.poolPts (T.sources i) ×ˢ TrackD.poolPts (T.targets i) := by
      intro pq hpq
      have hG : pq ∈ chart.G := (Finset.mem_filter.mp hpq).1
      obtain ⟨h1S, h2S⟩ := chart.hGmem pq hG
      have h1P : pq.1 ∈ TrackD.poolPts (T.sources i) := chart.pool.hSsub h1S
      have h2P : pq.2 ∈ TrackD.poolPts (T.sources i) := chart.pool.hSsub h2S
      have houter_eq : T.sources i = T.targets i := (houter i).1
      have h2Pt : pq.2 ∈ TrackD.poolPts (T.targets i) := houter_eq ▸ h2P
      exact Finset.mem_product.mpr ⟨h1P, h2Pt⟩
    have hgraph : ∀ pq ∈ Γg, (TrackD.toC pq.2 - TrackD.toC pq.1) i₀ ≠ 0 ∧
        ∀ G ∈ ({MvPolynomial.rename finSumFinEquiv.symm g} : Set (TrackD.PairPoly d)),
          MvPolynomial.eval (TrackD.labelPt i₀ (TrackD.toC pq.1) (TrackD.toC pq.2)) G = 0 := by
      intro pq hpq
      have hG : pq ∈ chart.G := (Finset.mem_filter.mp hpq).1
      have hz : MvPolynomial.eval (outerLabelPt i₀ pq) g = 0 :=
        (Finset.mem_filter.mp hpq).2
      refine ⟨chart.hchart pq hG, ?_⟩
      intro G hGmem
      rw [Set.mem_singleton_iff] at hGmem
      subst hGmem
      rw [heval_corr pq]
      exact hz
    have hBad := hproduct (regime.P i) (T.sources i) (T.targets i)
      (M.s i) (ρ₀ / 2) M.b (by linarith) hpool.1 hpool.2 hsW (j + 1) hj1 τg hplateau
      hTdeg (chart.W.owner i) (chart.W.owner i) hsource htarget i₀
      ({MvPolynomial.rename finSumFinEquiv.symm g} : Set (TrackD.PairPoly d))
      hGgdeg Γg hΓsub hgraph
    have hDgSub : DgSet ⊆ Γg.filter (fun pq => ∃ G ∈
        ({MvPolynomial.rename finSumFinEquiv.symm g} : Set (TrackD.PairPoly d)),
        ∃ x ∈ chart.W.owner i pq.1, ∃ y ∈ chart.W.owner i pq.2,
          (y - x) i₀ ≠ 0 ∧ MvPolynomial.eval (TrackD.labelPt i₀ x y) G ≠ 0) := by
      intro pq hpq
      have hΓ : pq ∈ Γg := (Finset.mem_filter.mp hpq).1
      have hVmem : commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈ Famsurv :=
        (Finset.mem_filter.mp hpq).2.1
      have hVnb : commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∉ bad :=
        (Finset.mem_filter.mp hpq).2.2
      have hnim : commonPairEquation (MvPolynomial.rename finSumFinEquiv.symm g) ∉
          (commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2)).ideal := by
        rw [hGg_eq]
        exact hggood _ hVmem hVnb
      have hnpair : ∃ x ∈ chart.W.owner i pq.1, ∃ y ∈ chart.W.owner i pq.2,
          (y - x) i₀ ≠ 0 ∧
            MvPolynomial.eval (TrackD.labelPt i₀ x y)
              (MvPolynomial.rename finSumFinEquiv.symm g) ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact hnim ((common_product_image_equation_iff i₀
          (chart.W.owner i pq.1) (chart.W.owner i pq.2)
          (MvPolynomial.rename finSumFinEquiv.symm g)).mpr hcon)
      obtain ⟨x, hx, y, hy, hchart, hzero⟩ := hnpair
      exact Finset.mem_filter.mpr ⟨hΓ, MvPolynomial.rename finSumFinEquiv.symm g,
        Set.mem_singleton_iff.mpr rfl, x, hx, y, hy, hchart, hzero⟩
    have hcardmono : (DgSet.card : ℝ) ≤
        ((Γg.filter (fun pq => ∃ G ∈
          ({MvPolynomial.rename finSumFinEquiv.symm g} : Set (TrackD.PairPoly d)),
          ∃ x ∈ chart.W.owner i pq.1, ∃ y ∈ chart.W.owner i pq.2,
            (y - x) i₀ ≠ 0 ∧ MvPolynomial.eval (TrackD.labelPt i₀ x y) G ≠ 0)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hDgSub
    have houter_eq2 : T.sources i = T.targets i := (houter i).1
    have hpool_eq2 : TrackD.poolPts (T.sources i) =
        TrackD.poolPts (T.targets i) := by rw [houter_eq2]
    have hcard_eq2 : ((TrackD.poolPts (T.targets i)).card : ℝ) =
        ((TrackD.poolPts (T.sources i)).card : ℝ) := by rw [hpool_eq2]
    have hS_le2 : ((TrackD.poolPts (T.sources i)).card : ℝ) ≤
        (chart.pool.S.card : ℝ) / (1 - ρ) := by
      rw [le_div_iff₀ h1mρpos, mul_comm]
      exact chart.pool.hScard
    have hconv : θg * ((TrackD.poolPts (T.sources i)).card : ℝ) *
        ((TrackD.poolPts (T.targets i)).card : ℝ) ≤
        (ρ' / 3) * (chart.pool.S.card : ℝ) ^ 2 := by
      have hPSPT : ((TrackD.poolPts (T.sources i)).card : ℝ) *
          ((TrackD.poolPts (T.targets i)).card : ℝ) ≤
          ((chart.pool.S.card : ℝ) / (1 - ρ)) * ((chart.pool.S.card : ℝ) / (1 - ρ)) := by
        rw [hcard_eq2]
        exact mul_le_mul hS_le2 hS_le2 (Nat.cast_nonneg _)
          (div_nonneg (Nat.cast_nonneg _) h1mρpos.le)
      have h1mρsq_ne : (1 - ρ : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt h1mρpos)
      have h1mρ_ne : (1 - ρ : ℝ) ≠ 0 := ne_of_gt h1mρpos
      calc θg * ((TrackD.poolPts (T.sources i)).card : ℝ) *
            ((TrackD.poolPts (T.targets i)).card : ℝ)
          = θg * (((TrackD.poolPts (T.sources i)).card : ℝ) *
            ((TrackD.poolPts (T.targets i)).card : ℝ)) := by ring
        _ ≤ θg * (((chart.pool.S.card : ℝ) / (1 - ρ)) *
            ((chart.pool.S.card : ℝ) / (1 - ρ))) :=
          mul_le_mul_of_nonneg_left hPSPT hθg.le
        _ = (ρ' / 3) * (chart.pool.S.card : ℝ) ^ 2 := by
          rw [hθgdef]
          exact cancel_theta_sq _ _ _ h1mρ_ne
    have hDg : ((DgSet).card : ℝ) ≤ (ρ' / 3) * (chart.pool.S.card : ℝ) ^ 2 :=
      hcardmono.trans (hBad.trans hconv)
    -- `Eqs` degree `≤ B^(2-c)` (via `T1n ≤ T_s(t₁) ≤ B^(2-c)`, `hB1`).
    have hEqdeg : ∀ G ∈ Eqs, (G.totalDegree : ℝ) ≤ (regime.B i) ^ (2 - c) := by
      intro G hG
      rw [hEqsdef] at hG
      rw [List.mem_toFinset] at hG
      obtain ⟨f, hfE, rfl⟩ := List.mem_map.mp hG
      have hBpos : (0 : ℝ) < regime.B i := by linarith [hB1]
      have c1 : ((MvPolynomial.rename finSumFinEquiv.symm f).totalDegree : ℝ) ≤
          ((f.totalDegree : ℕ) : ℝ) := by
        exact_mod_cast MvPolynomial.totalDegree_rename_le _ _
      have c2 : ((f.totalDegree : ℕ) : ℝ) ≤ ((T1n : ℕ) : ℝ) := by
        exact_mod_cast (hE f hfE).2
      have c3 : ((T1n : ℕ) : ℝ) ≤ TrackD.testDeg (regime.B i) (M.s i) t₁ := by
        rw [hT1ndef]
        exact Nat.floor_le (le_trans zero_le_one hfl1.1)
      have c4 : TrackD.testDeg (regime.B i) (M.s i) t₁ ≤
          (regime.B i) ^ ((1 : ℝ) + t₁) :=
        le_of_eq (testDeg_eq_rpow_of_logB _ _ _ hBpos (hs i))
      have c5 : (1 : ℝ) + t₁ ≤ 2 - c := by linarith
      have c6 : (regime.B i) ^ ((1 : ℝ) + t₁) ≤ (regime.B i) ^ (2 - c) :=
        regularity_degree_le_Bpow _ _ _ _ hB1 le_rfl c5
      exact c1.trans (c2.trans (c3.trans (c4.trans c6)))
    -- Vanishing on surviving images (locus ideal + prime).
    have hvanish : ∀ pq ∈ chart.G, good pq → ∀ G ∈ Eqs,
        commonPairEquation G ∈
          (commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2)).ideal := by
      have hvanishE : ∀ f ∈ E, ∀ V ∈ Famsurv, f ∈ V.ideal := by
        intro f hfE V hVFam
        rw [TrackD.mem_ideal_iff_eval_zero]
        intro x hx
        have hfL : f ∈ (AffineFamily.locus Famsurv).ideal := (hE f hfE).1
        have hxL : x ∈ (AffineFamily.locus Famsurv).points := by
          rw [AffineFamily.points_locus]
          exact Set.mem_biUnion hVFam hx
        have hz := (TrackD.mem_ideal_iff_eval_zero _ _).mp hfL _ hxL
        exact hz
      intro pq hpq hgoodpq G hG
      have hparts : pq ∈ chart.G ∧ pq ∉ D189 ∧
          commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∉ bad ∧
          MvPolynomial.eval (outerLabelPt i₀ pq) g ≠ 0 := hgoodpq
      obtain ⟨-, hnotD, hnim, hne⟩ := hparts
      have hUmemV : commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈ chart.U :=
        chart.hUmem pq hpq
      have hcompsV : commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈
          Bridges.envelopeComponents (⋃ Z ∈ chart.U, Z.points) T0n :=
        hDmem pq (Finset.mem_sdiff.mpr ⟨hpq, hnotD⟩)
      have hFamV : commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈ Famsurv :=
        Finset.mem_filter.mpr ⟨hUmemV, hcompsV⟩
      rw [hEqsdef] at hG
      rw [List.mem_toFinset] at hG
      obtain ⟨f, hfE, rfl⟩ := List.mem_map.mp hG
      have hround : commonPairEquation (MvPolynomial.rename finSumFinEquiv.symm f) = f := by
        unfold commonPairEquation
        rw [MvPolynomial.rename_rename, Equiv.self_comp_symm]
        exact MvPolynomial.rename_id_apply _
      rw [hround]
      exact hvanishE f hfE _ hFamV
    -- Smooth `2k`-fold at surviving labels (minor cert + tangent).
    have hsmooth : ∀ pq ∈ chart.G, good pq →
        Module.finrank ℂ (TrackD.jacKer (Eqs.image commonPairEquation)
          (outerLabelPt i₀ pq)) = 2 * k := by
      have hvanishE2 : ∀ f ∈ E, ∀ V ∈ Famsurv, f ∈ V.ideal := by
        intro f hfE V hVFam
        rw [TrackD.mem_ideal_iff_eval_zero]
        intro x hx
        have hfL : f ∈ (AffineFamily.locus Famsurv).ideal := (hE f hfE).1
        have hxL : x ∈ (AffineFamily.locus Famsurv).points := by
          rw [AffineFamily.points_locus]
          exact Set.mem_biUnion hVFam hx
        have hz := (TrackD.mem_ideal_iff_eval_zero _ _).mp hfL _ hxL
        exact hz
      have hround_all : ∀ f : Poly (d + d),
          commonPairEquation (MvPolynomial.rename finSumFinEquiv.symm f) = f := by
        intro f
        unfold commonPairEquation
        rw [MvPolynomial.rename_rename, Equiv.self_comp_symm]
        exact MvPolynomial.rename_id_apply _
      have hImEq : Finset.image commonPairEquation Eqs = E.toFinset := by
        ext y
        simp only [Finset.mem_image, List.mem_toFinset, hEqsdef]
        constructor
        · rintro ⟨G, hGmap, hGeq⟩
          obtain ⟨f, hfE, hfG⟩ := List.mem_map.mp hGmap
          have hyf : y = f := by rw [←hGeq, ←hfG, hround_all f]
          rwa [hyf]
        · intro hy
          exact ⟨MvPolynomial.rename finSumFinEquiv.symm y,
            List.mem_map.mpr ⟨y, hy, rfl⟩, hround_all y⟩
      intro pq hpq hgoodpq
      have hparts : pq ∈ chart.G ∧ pq ∉ D189 ∧
          commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∉ bad ∧
          MvPolynomial.eval (outerLabelPt i₀ pq) g ≠ 0 := hgoodpq
      obtain ⟨-, hnotD, hnim, hne⟩ := hparts
      have hUmemV : commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈ chart.U :=
        chart.hUmem pq hpq
      have hcompsV : commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈
          Bridges.envelopeComponents (⋃ Z ∈ chart.U, Z.points) T0n :=
        hDmem pq (Finset.mem_sdiff.mpr ⟨hpq, hnotD⟩)
      have hFamV : commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈ Famsurv :=
        Finset.mem_filter.mpr ⟨hUmemV, hcompsV⟩
      obtain ⟨hVirr, hVdim⟩ := hFampure _ hFamV
      have hx : outerLabelPt i₀ pq ∈
          commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) :=
        chart.hlabel pq hpq
      have hk2le : 2 * k ≤ d + d := by omega
      have hdim : (commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2)).dimension =
          (d + d) - ((d + d) - 2 * k) := by omega
      have hEV : ∀ f ∈ E,
          f ∈ (commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2)).ideal :=
        fun f hfE => hvanishE2 f hfE _ hFamV
      obtain ⟨hsm, heq⟩ := TrackD.carrier_smooth_of_minor
        (commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2))
        hVirr ((d + d) - 2 * k) (Nat.sub_le _ _) hdim E hEV g hgspan
        (outerLabelPt i₀ pq) hx hne
      rw [hImEq]
      obtain ⟨hmem, hfin⟩ := hsm
      rw [← heq, hfin,
        (commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2)).localDimension_eq_dimension
          (outerLabelPt i₀ pq) hVirr hx]
      exact hVdim
    -- Assemble the certificate: deletions `D189 ∪ Exc ∪ Dg` cost `ρ'|S|²`.
    have hG' : chart'.G = chart.G := rfl
    have hS' : chart'.pool.S = chart.pool.S := rfl
    have hsub : chart'.G.filter (fun pq => ¬ good pq) ⊆
        D189 ∪ chart.G.filter (fun pq =>
          commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈ bad) ∪
        DgSet := by
      intro pq hpq
      have hmem : pq ∈ chart'.G := (Finset.mem_filter.mp hpq).1
      rw [hG'] at hmem
      have hng : ¬ good pq := (Finset.mem_filter.mp hpq).2
      have hparts_neg : ¬ (pq ∈ chart.G ∧ pq ∉ D189 ∧
          commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∉ bad ∧
          MvPolynomial.eval (outerLabelPt i₀ pq) g ≠ 0) := hng
      by_cases hD : pq ∈ D189
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hD)))
      · by_cases hnb : commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈ bad
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr
            (Finset.mem_filter.mpr ⟨hmem, hnb⟩))))
        · have hE0 : MvPolynomial.eval (outerLabelPt i₀ pq) g = 0 := by
            by_contra hne
            exact hparts_neg ⟨hmem, hD, hnb, hne⟩
          have hUmemV : commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈ chart.U :=
            chart.hUmem pq hmem
          have hcompsV : commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈
              Bridges.envelopeComponents (⋃ Z ∈ chart.U, Z.points) T0n :=
            hDmem pq (Finset.mem_sdiff.mpr ⟨hmem, hD⟩)
          have hFamV : commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈ Famsurv :=
            Finset.mem_filter.mpr ⟨hUmemV, hcompsV⟩
          have hΓ : pq ∈ Γg :=
            Finset.mem_filter.mpr ⟨hmem, hE0⟩
          have hDgmem : pq ∈ DgSet :=
            Finset.mem_filter.mpr ⟨hΓ, hFamV, hnb⟩
          exact Finset.mem_union.mpr (Or.inr hDgmem)
    have hcardle : ((chart'.G.filter (fun pq => ¬ good pq)).card : ℝ) ≤
        ((D189.card : ℝ) + ((chart.G.filter (fun pq =>
          commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈ bad)).card : ℝ)) +
        ((DgSet).card : ℝ) := by
      have h1 : ((chart'.G.filter (fun pq => ¬ good pq)).card : ℝ) ≤
          ((D189 ∪ chart.G.filter (fun pq =>
            commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈ bad) ∪
            DgSet).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      have h2 : ((D189 ∪ chart.G.filter (fun pq =>
          commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈ bad) ∪
          DgSet).card : ℝ) ≤ (((D189.card : ℝ) +
          ((chart.G.filter (fun pq =>
            commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈ bad)).card : ℝ))) +
          ((DgSet).card : ℝ) := by
        have u1 : (D189 ∪ chart.G.filter (fun pq =>
            commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈ bad) ∪
            DgSet).card ≤ (D189 ∪ chart.G.filter (fun pq =>
            commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈ bad)).card +
            DgSet.card :=
          Finset.card_union_le _ _
        have u2 : (D189 ∪ chart.G.filter (fun pq =>
            commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈ bad)).card ≤
            D189.card + (chart.G.filter (fun pq =>
            commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈ bad)).card :=
          Finset.card_union_le _ _
        have u1R : ((D189 ∪ chart.G.filter (fun pq =>
            commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈ bad) ∪
            DgSet).card : ℝ) ≤
            ((D189 ∪ chart.G.filter (fun pq =>
            commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈ bad)).card : ℝ) +
            (DgSet.card : ℝ) := by
          exact_mod_cast u1
        have u2R : ((D189 ∪ chart.G.filter (fun pq =>
            commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈ bad)).card : ℝ) ≤
            (D189.card : ℝ) + ((chart.G.filter (fun pq =>
            commonProductImage i₀ (chart.W.owner i pq.1) (chart.W.owner i pq.2) ∈ bad)).card : ℝ) := by
          exact_mod_cast u2
        linarith
      linarith [h1, h2]
    have hbad : ((chart'.G.filter (fun pq => ¬ good pq)).card : ℝ) ≤
        ρ' * (chart'.pool.S.card : ℝ) ^ 2 := by
      rw [hS']
      linarith [hcardle, add_le_add (add_le_add hDcard hDexc) hDg]
    have hWpin : chart'.W = W := by simpa [hchart'def, OuterChartCert.mono] using hchartW
    refine ⟨⟨chart', Eqs, good, hEqdeg, ?_, hvanish, hsmooth⟩, hWpin⟩
    convert hbad using 2
    congr
  · push_neg at h10
    have hβlow : -1 ≤ M.b ⟨j, hj⟩ := common_profile_time_lower M _
    have hcon : False := by linarith
    exact False.elim hcon

/-- Pair coordinates `(u, v) ↦ (u, v)` in the shared label coordinates
`Fin (d + d)`. -/
def outerPairLinear : (Point d × Point d) →ₗ[ℂ] Point (d + d) :=
  LinearMap.pi fun kk => Sum.elim
    (fun a => (LinearMap.proj a).comp (LinearMap.fst ℂ (Point d) (Point d)))
    (fun a => (LinearMap.proj a).comp (LinearMap.snd ℂ (Point d) (Point d)))
    (finSumFinEquiv.symm kk)

/-- The tangent space of the common label system at the label of `(p, q)` in
chart `i₀`, in pair coordinates. It depends on `q` only through the label, so
all points `q'` on one ray from `p` share it. -/
def outerLabelTangent (Eqs : Finset (TrackD.PairPoly d)) (i₀ : Fin d) (p q : Point d) :
    Submodule ℂ (Point d × Point d) :=
  (TrackD.jacKer (Eqs.image commonPairEquation)
    (fun kk => TrackD.labelPt i₀ p q (finSumFinEquiv.symm kk))).comap outerPairLinear

/-- The per-pair tangent data for the lift, in chart `i₀` (`lam = proj i₀`):
source/target tangent spaces of rank `k` missing the secant, full differential
rank of the label map into the given label tangent space `TW` (of dimension
`2k`), and (for `k ≥ 2`) the projected-tangent inequality. With
`TW = outerLabelTangent Eqs i₀ p q` this is the hypothesis bundle of
`outer_roots_card_le_one` (OuterRoots.lean). -/
structure OuterTangentData (i₀ : Fin d) (p q : Point d) (X Y : AffineVariety d)
    (k : ℕ) (TW : Submodule ℂ (Point d × Point d)) where
  TX : Submodule ℂ (Point d)
  TY : Submodule ℂ (Point d)
  hchart : (q - p) i₀ ≠ 0
  hsrc : q - p ∉ TX
  htgt : q - p ∉ TY
  hdimX : Module.finrank ℂ TX = k
  hdimY : Module.finrank ℂ TY = k
  hrank : Module.finrank ℂ
    ((TX.prod TY).map (TrackD.labelDeriv (LinearMap.proj i₀) p q)) = k + k
  hdimW : Module.finrank ℂ TW = k + k
  hW : (TX.prod TY).map (TrackD.labelDeriv (LinearMap.proj i₀) p q) ≤ TW
  hneq : k ≥ 2 → TX ⊔ (ℂ ∙ (q - p)) ≠ TY ⊔ (ℂ ∙ (q - p))
  hTX : TX = X.tangentSpace p
  hTY : TY = Y.tangentSpace q

/-- The global tangent-test system at one index: the physical minor test and
the source/target joint test polynomials (in `(p, q)`, degree `O(T_s(τ))`).
One system serves all pairs; its nonvanishing at a pair yields tangent data. -/
structure OuterTestSystem where
  gph : Poly d
  srcTests : Finset (TrackD.PairPoly d)
  tgtTests : Finset (TrackD.PairPoly d)

/-- Nonvanishing of the test system at a (source, target) point pair. -/
def OuterTestsNonvanishing (sys : @OuterTestSystem d) (p q' : Point d) : Prop :=
  MvPolynomial.eval q' sys.gph ≠ 0 ∧
  (∀ F ∈ sys.srcTests, MvPolynomial.eval (Sum.elim p q') F ≠ 0) ∧
  (∀ F ∈ sys.tgtTests, MvPolynomial.eval (Sum.elim p q') F ≠ 0)

/-- Inverse of `outerPairLinear` on coordinates (helper for 191, lane m-o-r191). -/
def outerPairLinearInv : Point (d + d) →ₗ[ℂ] (Point d × Point d) where
  toFun w := (fun k => w (finSumFinEquiv (Sum.inl k)),
    fun k => w (finSumFinEquiv (Sum.inr k)))
  map_add' := by intro a b; rfl
  map_smul' := by intro c a; rfl

/-- `outerPairLinear` is injective (helper for 191). -/
theorem outerPairLinear_injective' : Function.Injective (@outerPairLinear d) := by
  intro a b hab
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  simp only [Prod.mk.injEq]
  constructor
  · funext k
    have hkk := congrFun hab (finSumFinEquiv (Sum.inl k))
    simp only [outerPairLinear, LinearMap.pi_apply, Equiv.symm_apply_apply] at hkk
    simpa using hkk
  · funext k
    have hkk := congrFun hab (finSumFinEquiv (Sum.inr k))
    simp only [outerPairLinear, LinearMap.pi_apply, Equiv.symm_apply_apply] at hkk
    simpa using hkk

/-- `outerPairLinear` is a linear equivalence (helper for 191). -/
def outerPairLinearEquiv' : (Point d × Point d) ≃ₗ[ℂ] Point (d + d) := by
  have h1 : Module.finrank ℂ (Point d × Point d) = d + d := by
    simp [Point, Module.finrank_prod, Fintype.card_fin]
  have h2 : Module.finrank ℂ (Point (d + d)) = d + d := by
    simp [Point]
  have heq : Module.finrank ℂ (Point d × Point d) =
      Module.finrank ℂ (Point (d + d)) := h1.trans h2.symm
  have hsurj : Function.Surjective (@outerPairLinear d) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).mp
      outerPairLinear_injective'
  exact LinearEquiv.ofBijective _ ⟨outerPairLinear_injective', hsurj⟩

/-- `outerPairLinear` equals the product coordinate equivalence (helper for 191). -/
theorem outerPairLinear_eq_productLinearEquiv :
    (@outerPairLinear d) = TrackD.productLinearEquiv.toLinearMap := by
  apply LinearMap.ext
  intro p
  obtain ⟨a, b⟩ := p
  funext kk
  cases hsym : finSumFinEquiv.symm kk with
  | inl k =>
    have hkk : kk = finSumFinEquiv (Sum.inl k) := by
      rw [← hsym, Equiv.apply_symm_apply]
    rw [hkk]
    have hleft : outerPairLinear (a, b) (finSumFinEquiv (Sum.inl k)) = a k := by
      simp only [outerPairLinear, LinearMap.pi_apply]
      rw [Equiv.symm_apply_apply]
      simp
    have hright : (TrackD.productLinearEquiv.toLinearMap (a, b))
        (finSumFinEquiv (Sum.inl k)) = a k := by
      show TrackD.productPoint a b (finSumFinEquiv (Sum.inl k)) = a k
      exact TrackD.productPoint_inl a b k
    rw [hleft, hright]
  | inr k =>
    have hkk : kk = finSumFinEquiv (Sum.inr k) := by
      rw [← hsym, Equiv.apply_symm_apply]
    rw [hkk]
    have hleft : outerPairLinear (a, b) (finSumFinEquiv (Sum.inr k)) = b k := by
      simp only [outerPairLinear, LinearMap.pi_apply]
      rw [Equiv.symm_apply_apply]
      simp
    have hright : (TrackD.productLinearEquiv.toLinearMap (a, b))
        (finSumFinEquiv (Sum.inr k)) = b k := by
      show TrackD.productPoint a b (finSumFinEquiv (Sum.inr k)) = b k
      exact TrackD.productPoint_inr a b k
    rw [hleft, hright]

/-- The comap defining `outerLabelTangent` preserves finrank (helper for 191). -/
theorem outerLabelTangent_finrank' (Eqs : Finset (TrackD.PairPoly d)) (i₀ : Fin d)
    (p q : Point d) :
    Module.finrank ℂ (outerLabelTangent Eqs i₀ p q) =
      Module.finrank ℂ (TrackD.jacKer (Eqs.image commonPairEquation)
        (fun kk => TrackD.labelPt i₀ p q (finSumFinEquiv.symm kk))) := by
  unfold outerLabelTangent
  let S := TrackD.jacKer (Eqs.image commonPairEquation)
    (fun kk => TrackD.labelPt i₀ p q (finSumFinEquiv.symm kk))
  let e := TrackD.productLinearEquiv (d := d)
  have hbase : (@outerPairLinear d) = e.toLinearMap :=
    outerPairLinear_eq_productLinearEquiv
  have hcomap : S.comap (e.toLinearMap) =
      S.map e.symm.toLinearMap := by
    ext x
    constructor
    · intro hx
      have hxS : e x ∈ S := hx
      refine ⟨e x, hxS, ?_⟩
      simp
    · rintro ⟨y, hy, hxy⟩
      show e x ∈ S
      have hxy' : e.symm y = x := hxy
      have heq : e x = y := by
        conv_lhs => rw [← hxy']
        exact e.apply_symm_apply y
      rw [heq]; exact hy
  rw [hbase, hcomap]
  exact LinearEquiv.finrank_map_eq _ _

/-- Label-differential image lies in the outer label tangent (G2 core, helper
for 191): from `hvanish` on the complete product image, via the all-point
chain rule `rational_image_tangent_all`, the product-tangent identification
`product_tangent_space`, the differential identification
`rational_secant_label_differential`, and `tangent_le_jacKer`. No genericity
needed. -/
theorem label_image_le_outerTangent (i₀ : Fin d) (X Y : AffineVariety d)
    (p q : Point d) (hx : p ∈ X) (hy : q ∈ Y)
    (hchart : (q - p) i₀ ≠ 0)
    (Eqs : Finset (TrackD.PairPoly d))
    (hvanish : ∀ G ∈ Eqs,
      commonPairEquation G ∈ (commonProductImage i₀ X Y).ideal) :
    ((X.tangentSpace p).prod (Y.tangentSpace q)).map
      (TrackD.labelDeriv (LinearMap.proj i₀) p q) ≤
      outerLabelTangent Eqs i₀ p q := by
  classical
  -- the product point and denominator nonvanishing
  have hprod_mem : TrackD.productPoint p q ∈ (TrackD.productVariety X Y) := by
    have hpts : TrackD.productPoint p q ∈
        (TrackD.productVariety X Y).points := by
      rw [TrackD.productVariety_points]
      constructor
      · have hL : TrackD.productLeft (TrackD.productPoint p q) = p := by
          funext i
          simp only [TrackD.productPoint, TrackD.productLeft, TrackD.pairPt,
            Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl]
        rw [hL]; exact hx
      · have hR : TrackD.productRight (TrackD.productPoint p q) = q := by
          funext i
          simp only [TrackD.productPoint, TrackD.productRight, TrackD.pairPt,
            Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr]
        rw [hR]; exact hy
    exact hpts
  have hg : MvPolynomial.eval (TrackD.productPoint p q)
      (TrackD.secantChartDenominator i₀) ≠ 0 := by
    rw [TrackD.eval_secantChartDenominator]
    exact hchart
  -- all-point chain rule into the complete image tangent
  have h_all := TrackD.rational_image_tangent_all (TrackD.productVariety X Y)
    (TrackD.secantChartNumerator i₀) (TrackD.secantChartDenominator i₀)
    (TrackD.productPoint p q) hprod_mem hg
  -- identify the left side with the labelDeriv image
  have h_map := TrackD.rational_secant_tangent_map X Y i₀ p q hx hy hchart
  -- the rational label point equals the outer label point
  have hpt_eq : TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
      (TrackD.secantChartDenominator i₀) (TrackD.productPoint p q) =
      (fun kk => TrackD.labelPt i₀ p q (finSumFinEquiv.symm kk)) := by
    have hlab := TrackD.rational_secant_label i₀ p q hchart
    rw [hlab]
    funext kk
    simp only [TrackD.productPoint, Function.comp_apply, TrackD.labelPt,
      TrackD.pairPt, TrackD.dirChart, LinearMap.proj_apply]
  -- image tangent lies in the Jacobian kernel via `hvanish`
  have h_jac : (commonProductImage i₀ X Y).tangentSpace
      (TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
        (TrackD.secantChartDenominator i₀) (TrackD.productPoint p q)) ≤
      TrackD.jacKer (Eqs.image commonPairEquation)
        (fun kk => TrackD.labelPt i₀ p q (finSumFinEquiv.symm kk)) := by
    rw [← hpt_eq]
    apply TrackD.tangent_le_jacKer
    intro f hf
    obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp hf
    exact hvanish G hG
  -- chain the three inclusions and transport across `outerPairLinear`
  have h_chain : (((X.tangentSpace p).prod (Y.tangentSpace q)).map
      (TrackD.labelDeriv (LinearMap.proj i₀) p q)).map
      TrackD.productLinearEquiv.toLinearMap ≤
      TrackD.jacKer (Eqs.image commonPairEquation)
        (fun kk => TrackD.labelPt i₀ p q (finSumFinEquiv.symm kk)) := by
    calc (((X.tangentSpace p).prod (Y.tangentSpace q)).map
          (TrackD.labelDeriv (LinearMap.proj i₀) p q)).map
          TrackD.productLinearEquiv.toLinearMap
        = ((TrackD.productVariety X Y).tangentSpace
            (TrackD.productPoint p q)).map
            (TrackD.rationalDifferential (TrackD.secantChartNumerator i₀)
              (TrackD.secantChartDenominator i₀) (TrackD.productPoint p q)) := by
          rw [h_map]
      _ ≤ (commonProductImage i₀ X Y).tangentSpace
            (TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
              (TrackD.secantChartDenominator i₀) (TrackD.productPoint p q)) := h_all
      _ ≤ _ := h_jac
  unfold outerLabelTangent
  rw [outerPairLinear_eq_productLinearEquiv]
  rwa [Submodule.map_le_iff_le_comap] at h_chain

/-- Assemble the tangent bundle once the physical and label rank tests pass. -/
theorem outer_tangent_data_from_kernels (i₀ : Fin d) (E : Finset (Poly d))
    (Eqs : Finset (TrackD.PairPoly d)) (X Y : AffineVariety d) (k : ℕ)
    (hX : X.IsIrreducible) (hY : Y.IsIrreducible)
    (hXk : X.dimension = k) (hYk : Y.dimension = k)
    (hEX : ∀ f ∈ E, f ∈ X.ideal) (hEY : ∀ f ∈ E, f ∈ Y.ideal)
    (p q : Point d) (hp : p ∈ X.points) (hq : q ∈ Y.points)
    (hchart : (q - p) i₀ ≠ 0)
    (hprank : Module.finrank ℂ (TrackD.jacKer E p) ≤ k)
    (hqrank : Module.finrank ℂ (TrackD.jacKer E q) ≤ k)
    (hsrc : q - p ∉ TrackD.jacKer E p) (htgt : q - p ∉ TrackD.jacKer E q)
    (hneq : 2 ≤ k → TrackD.jacKer E p ⊔ (ℂ ∙ (q - p)) ≠
      TrackD.jacKer E q ⊔ (ℂ ∙ (q - p)))
    (hlab : Module.finrank ℂ (TrackD.jacKer (Eqs.image commonPairEquation)
      (fun kk => TrackD.labelPt i₀ p q (finSumFinEquiv.symm kk))) = 2 * k)
    (hvanish : ∀ G ∈ Eqs, commonPairEquation G ∈ (commonProductImage i₀ X Y).ideal) :
    Nonempty (OuterTangentData i₀ p q X Y k (outerLabelTangent Eqs i₀ p q)) := by
  obtain ⟨hTX, hdimX⟩ := physical_tangent_eq_of_rank X hX E k hXk hEX p hp hprank
  obtain ⟨hTY, hdimY⟩ := physical_tangent_eq_of_rank Y hY E k hYk hEY q hq hqrank
  have hrank := label_image_rank_of_transverse p q i₀ hchart
    (TrackD.jacKer E p) (TrackD.jacKer E q) htgt
  rw [hdimX, hdimY] at hrank
  refine ⟨{
    TX := TrackD.jacKer E p, TY := TrackD.jacKer E q,
    hchart := hchart, hsrc := hsrc, htgt := htgt,
    hdimX := hdimX, hdimY := hdimY, hrank := hrank,
    hdimW := ?_, hW := ?_, hneq := hneq,
    hTX := hTX.symm, hTY := hTY.symm }⟩
  · rw [outerLabelTangent_finrank', hlab]
    omega
  · rw [← hTX, ← hTY]
    exact label_image_le_outerTangent i₀ X Y p q hp hq hchart Eqs hvanish

/-- A chart carrying pairs has identical original source and target roles. -/
theorem outer_chart_equal_roles_or_empty {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} {M : CommonPoolProfile T}
    {k i j : ℕ} {i₀ : Fin d} {ρ ε ρ' τ : ℝ}
    (chart : OuterChartCert T M k i j i₀ ρ ε ρ' τ) :
    T.sources i = T.targets i ∨ chart.G = ∅ := by
  rcases common_pool_roles_equal_or_disjoint T M i with heq | hdis
  · exact Or.inl heq
  · right
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro pq hpq
    have hqS := chart.pool.hSsub (chart.hGmem pq hpq).2
    have hqT : pq.2 ∈ TrackD.poolPts (T.targets i) :=
      (Finset.mem_filter.mp (chart.hGpoolsList pq hpq).2.1).1
    exact Finset.disjoint_left.mp hdis hqS hqT

/-- A common label-rank guard loses none of the finitely many good labels. -/
theorem outer_label_rank_guard {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} {M : CommonPoolProfile T}
    {k i j : ℕ} {i₀ : Fin d} {ρ ε ρ' Bdeg τ : ℝ}
    (cert : OuterRegularityCert T M k i j i₀ ρ ε ρ' Bdeg τ) (hkd : k ≤ d) :
    ∃ H : TrackD.PairPoly d,
      (∀ pq ∈ cert.chart.G, cert.good pq →
        MvPolynomial.eval (TrackD.pairPt (TrackD.toC pq.1) (TrackD.toC pq.2)) H ≠ 0) ∧
      ∀ p q : Point d, (q - p) i₀ ≠ 0 →
        MvPolynomial.eval (TrackD.pairPt p q) H ≠ 0 →
        Module.finrank ℂ (TrackD.jacKer (cert.Eqs.image commonPairEquation)
          (fun kk => TrackD.labelPt i₀ p q (finSumFinEquiv.symm kk))) ≤ 2 * k := by
  let E := (cert.Eqs.image commonPairEquation).toList
  have hEfin : E.toFinset = cert.Eqs.image commonPairEquation := by
    exact Finset.toList_toFinset _
  let Z := (cert.chart.G.filter cert.good).image (outerLabelPt i₀)
  have hZ : ∀ z ∈ Z, Module.finrank ℂ (TrackD.jacKer E.toFinset z) = 2 * k := by
    intro z hz
    obtain ⟨pq, hpq, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hpq, hgood⟩ := Finset.mem_filter.mp hpq
    rw [hEfin]
    exact cert.hsmooth pq hpq hgood
  obtain ⟨g, hgn, hgrank⟩ := finite_jacobian_rank_test E (2 * k) (by omega) Z hZ
  let G : TrackD.PairPoly d := MvPolynomial.rename finSumFinEquiv.symm g
  have hG (p q : Point d) : MvPolynomial.eval (TrackD.labelPt i₀ p q) G =
      MvPolynomial.eval (fun kk => TrackD.labelPt i₀ p q (finSumFinEquiv.symm kk)) g := by
    simp [G, MvPolynomial.eval_rename, Function.comp_def]
  obtain ⟨N, H, hH⟩ := label_clear_exists i₀ G
  refine ⟨H, ?_, ?_⟩
  · intro pq hpq hgood
    rw [hH _ _ (cert.chart.hchart pq hpq), hG]
    apply mul_ne_zero (pow_ne_zero _ (cert.chart.hchart pq hpq))
    exact hgn _ (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hpq, hgood⟩))
  · intro p q hc hn
    have hgne : MvPolynomial.eval
        (fun kk => TrackD.labelPt i₀ p q (finSumFinEquiv.symm kk)) g ≠ 0 := by
      intro hz
      apply hn
      rw [hH p q hc, hG, hz, mul_zero]
    have hh := hgrank _ hgne
    rw [hEfin] at hh
    exact hh

/-- At one index the three physical pair tests suffice; the label guard is
chosen to lose none of the old good pairs. -/
theorem outer_tangent_tests_on_good {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} {M : CommonPoolProfile T}
    {k i j : ℕ} {i₀ : Fin d} {ρ ε ρ' Bdeg τ : ℝ}
    (cert : OuterRegularityCert T M k i j i₀ ρ ε ρ' Bdeg τ)
    (hkj : k + j + 1 = d) (hkd : k ≤ d)
    (hE : ∀ Z, TrackD.PoolCarrier (T.sources i ∪ T.targets i) (j + 1) Z →
      ∀ f ∈ cert.chart.W.equations i, f ∈ Z.ideal)
    (hminor : ∀ y : Point d, MvPolynomial.eval y (cert.chart.W.minor i) ≠ 0 →
      Module.finrank ℂ (TrackD.jacKer (cert.chart.W.equations i) y) + (j + 1) ≤ d)
    (fs ft fm : TrackD.PairPoly d)
    (hfs : fs ∈ Submodule.span ℂ
      ((cert.chart.W.equations i).image secantSourceTest : Set _))
    (hft : ft ∈ Submodule.span ℂ
      ((cert.chart.W.equations i).image secantTargetTest : Set _))
    (hfm : 2 ≤ k → fm ∈ Submodule.span ℂ
      (combinedSecantMinors (cert.chart.W.equations i) (d - k) : Set _)) :
    ∃ sys : @OuterTestSystem d,
      (∀ pq ∈ cert.chart.G, cert.good pq →
        MvPolynomial.eval (TrackD.pairPt (TrackD.toC pq.1) (TrackD.toC pq.2))
          (fs * ft * fm) ≠ 0 → ∀ X Y : AffineVariety d,
        cert.chart.W.owner i pq.1 = X → cert.chart.W.owner i pq.2 = Y →
        OuterTestsNonvanishing sys (TrackD.toC pq.1) (TrackD.toC pq.2) ∧
        Nonempty (OuterTangentData i₀ (TrackD.toC pq.1) (TrackD.toC pq.2) X Y k
          (outerLabelTangent cert.Eqs i₀ (TrackD.toC pq.1) (TrackD.toC pq.2)))) ∧
      (∀ pq ∈ cert.chart.G, cert.good pq → ∀ X Y : AffineVariety d, ∀ q' : Point d,
        cert.chart.W.owner i pq.1 = X → cert.chart.W.owner i pq.2 = Y →
        q' ∈ Y.points → (q' - TrackD.toC pq.1) i₀ ≠ 0 →
        (fun kk => TrackD.labelPt i₀ (TrackD.toC pq.1) q'
          (finSumFinEquiv.symm kk)) ∈ (commonProductImage i₀ X Y).points →
        OuterTestsNonvanishing sys (TrackD.toC pq.1) q' →
        Nonempty (OuterTangentData i₀ (TrackD.toC pq.1) q' X Y k
          (outerLabelTangent cert.Eqs i₀ (TrackD.toC pq.1) q'))) := by
  obtain ⟨H, hHgood, hHrank⟩ := outer_label_rank_guard cert hkd
  let sys : @OuterTestSystem d := {
    gph := cert.chart.W.minor i
    srcTests := {fs, fm, H}
    tgtTests := {ft} }
  have hsource (pq : RPoint d × RPoint d) (hpq : pq ∈ cert.chart.G) :=
    common_retained_owner_regular (T.sources i) (T.sources i ∪ T.targets i)
      Finset.subset_union_left (j + 1) (cert.chart.W.equations i) (cert.chart.W.minor i)
      (cert.chart.W.owner i) (cert.chart.W.supported i) pq.1
      (cert.chart.hGpoolsList pq hpq).1
  have htarget (pq : RPoint d × RPoint d) (hpq : pq ∈ cert.chart.G) :=
    common_retained_owner_regular (T.targets i) (T.sources i ∪ T.targets i)
      Finset.subset_union_right (j + 1) (cert.chart.W.equations i) (cert.chart.W.minor i)
      (cert.chart.W.owner i) (cert.chart.W.supported i) pq.2
      (cert.chart.hGpoolsList pq hpq).2.1
  have hsecond : ∀ pq ∈ cert.chart.G, cert.good pq →
      ∀ X Y : AffineVariety d, ∀ q' : Point d,
        cert.chart.W.owner i pq.1 = X → cert.chart.W.owner i pq.2 = Y →
        q' ∈ Y.points → (q' - TrackD.toC pq.1) i₀ ≠ 0 →
        (fun kk => TrackD.labelPt i₀ (TrackD.toC pq.1) q'
          (finSumFinEquiv.symm kk)) ∈ (commonProductImage i₀ X Y).points →
        OuterTestsNonvanishing sys (TrackD.toC pq.1) q' →
        Nonempty (OuterTangentData i₀ (TrackD.toC pq.1) q' X Y k
          (outerLabelTangent cert.Eqs i₀ (TrackD.toC pq.1) q')) := by
    intro pq hpq hgood X Y q' hX hY hq' hc hlabel hn
    obtain ⟨r, hr, hrX, hrY⟩ := cert.chart.hown pq hpq
    have hXr : X = r.1 := by rw [← hX, cert.chart.hWownF]; exact hrX
    have hYr : Y = r.2 := by rw [← hY, cert.chart.hWownF]; exact hrY
    have hirr := cert.chart.pool.hRirr r hr
    have hdim := cert.chart.pool.hRdim r hr
    rw [← hXr, ← hYr] at hirr hdim
    have hpdata := hsource pq hpq
    have hqdata := htarget pq hpq
    rw [hX] at hpdata
    rw [hY] at hqdata
    have hprank : Module.finrank ℂ
        (TrackD.jacKer (cert.chart.W.equations i) (TrackD.toC pq.1)) ≤ k := by
      have hh := hminor _ hpdata.2.2.2.2.2.1
      omega
    have hqrank : Module.finrank ℂ
        (TrackD.jacKer (cert.chart.W.equations i) q') ≤ k := by
      have hh := hminor _ hn.1
      omega
    have hs : q' - TrackD.toC pq.1 ∉
        TrackD.jacKer (cert.chart.W.equations i) (TrackD.toC pq.1) :=
      secantSource_combination_transverse _ _ _ hfs
        (hn.2.1 fs (by simp [sys]))
    have ht : q' - TrackD.toC pq.1 ∉ TrackD.jacKer (cert.chart.W.equations i) q' :=
      secantTarget_combination_transverse _ _ _ hft
        (hn.2.2 ft (by simp [sys]))
    have hpk := (physical_tangent_eq_of_rank X hirr.1 (cert.chart.W.equations i)
      k hdim.1 (hE X hpdata.1) _ hpdata.2.1 hprank).2
    have hneq : 2 ≤ k →
        TrackD.jacKer (cert.chart.W.equations i) (TrackD.toC pq.1) ⊔ (ℂ ∙ (q' - TrackD.toC pq.1)) ≠
        TrackD.jacKer (cert.chart.W.equations i) q' ⊔ (ℂ ∙ (q' - TrackD.toC pq.1)) := by
      intro hk2
      exact combinedSecant_combination_unequal _ _ _ k hkd hs ht hpk (hfm hk2)
        (hn.2.1 fm (by simp [sys]))
    have hvanish : ∀ G ∈ cert.Eqs,
        commonPairEquation G ∈ (commonProductImage i₀ X Y).ideal := by
      simpa only [hX, hY] using cert.hvanish pq hpq hgood
    have hU := cert.chart.hU _ (cert.chart.hUmem pq hpq)
    rw [hX, hY] at hU
    have hlo := TrackD.tangent_finrank_ge_dimension _ hU.1 _ hlabel
    rw [hU.2] at hlo
    have hle := Submodule.finrank_mono
      (TrackD.tangent_le_jacKer (commonProductImage i₀ X Y)
        (cert.Eqs.image commonPairEquation) (by
          intro f hf
          obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp hf
          exact hvanish G hG)
        (fun kk => TrackD.labelPt i₀ (TrackD.toC pq.1) q' (finSumFinEquiv.symm kk)))
    have hhi := hHrank _ _ hc (hn.2.1 H (by simp [sys]))
    have heq : Module.finrank ℂ (TrackD.jacKer (cert.Eqs.image commonPairEquation)
        (fun kk => TrackD.labelPt i₀ (TrackD.toC pq.1) q' (finSumFinEquiv.symm kk))) = 2 * k := by
      omega
    exact outer_tangent_data_from_kernels i₀ (cert.chart.W.equations i) cert.Eqs
      X Y k hirr.1 hirr.2 hdim.1 hdim.2 (hE X hpdata.1) (hE Y hqdata.1)
      _ q' hpdata.2.1 hq' hc hprank hqrank hs ht hneq heq hvanish
  refine ⟨sys, ?_, hsecond⟩
  intro pq hpq hgood hn X Y hX hY
  simp only [map_mul, ne_eq, mul_eq_zero, not_or] at hn
  have hnon : OuterTestsNonvanishing sys (TrackD.toC pq.1) (TrackD.toC pq.2) := by
    refine ⟨(htarget pq hpq).2.2.2.2.2.1, ?_, ?_⟩
    · intro G hG
      simp only [sys, Finset.mem_insert, Finset.mem_singleton] at hG
      rcases hG with rfl | rfl | rfl
      · exact hn.1.1
      · exact hn.2
      · exact hHgood pq hpq hgood
    · intro G hG
      have hGft : G = ft := by simpa only [sys, Finset.mem_singleton] using hG
      subst G
      exact hn.1.2
  refine ⟨hnon, hsecond pq hpq hgood X Y _ hX hY ?_ (cert.chart.hchart pq hpq) ?_ hnon⟩
  · have hh := (htarget pq hpq).2.1
    rw [hY] at hh
    exact hh
  · simpa only [hX, hY] using cert.chart.hlabel pq hpq

/-- Spend a separately bounded pair loss while retaining the equations and
the fixed physical sequence. -/
def outer_regularity_restrict {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} {M : CommonPoolProfile T}
    {k i j : ℕ} {i₀ : Fin d} {ρ ε ρ₀ ρ₁ η Bdeg τ : ℝ}
    (cert : OuterRegularityCert T M k i j i₀ ρ ε ρ₀ Bdeg τ)
    (keep : RPoint d × RPoint d → Prop) (hη : 0 ≤ η) (hbudget : ρ₀ + η ≤ ρ₁)
    (hloss : ((cert.chart.G.filter (fun pq => ¬ keep pq)).card : ℝ) ≤
      η * (cert.chart.pool.S.card : ℝ) ^ 2) :
    OuterRegularityCert T M k i j i₀ ρ ε ρ₁ Bdeg τ where
  chart := cert.chart.mono (by linarith)
  Eqs := cert.Eqs
  good := fun pq => cert.good pq ∧ keep pq
  hEqdeg := cert.hEqdeg
  hbad := by
    have hsub : cert.chart.G.filter (fun pq => ¬ (cert.good pq ∧ keep pq)) ⊆
        cert.chart.G.filter (fun pq => ¬ cert.good pq) ∪
          cert.chart.G.filter (fun pq => ¬ keep pq) := by
      intro pq hpq
      obtain ⟨hpq, hn⟩ := Finset.mem_filter.mp hpq
      by_cases hg : cert.good pq
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hpq, fun hk => hn ⟨hg, hk⟩⟩)
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hpq, hg⟩)
    have hcard : ((cert.chart.G.filter (fun pq => ¬ (cert.good pq ∧ keep pq))).card : ℝ) ≤
        ((cert.chart.G.filter (fun pq => ¬ cert.good pq)).card : ℝ) +
          ((cert.chart.G.filter (fun pq => ¬ keep pq)).card : ℝ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hh := hcard.trans (add_le_add cert.hbad hloss)
    have hmul := mul_le_mul_of_nonneg_right hbudget (sq_nonneg (cert.chart.pool.S.card : ℝ))
    have htotal : ((cert.chart.G.filter (fun pq => ¬ (cert.good pq ∧ keep pq))).card : ℝ) ≤
        ρ₁ * (cert.chart.pool.S.card : ℝ) ^ 2 := by
      nlinarith
    convert htotal using 1 <;> dsimp only [OuterChartCert.mono]
    congr 2
    ext pq
    simp only [Finset.mem_filter]
  hvanish := fun pq hpq hg => cert.hvanish pq hpq hg.1
  hsmooth := fun pq hpq hg => cert.hsmooth pq hpq hg.1

/-- The physical tests are chosen on precisely the carrier products used by
the chart and the new fixed target lists. -/
theorem outer_chart_physical_tests {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} {M : CommonPoolProfile T}
    {k i j : ℕ} {i₀ : Fin d} {ρ ε ρ' τ η : ℝ}
    (chart : OuterChartCert T M k i j i₀ ρ ε ρ' τ)
    (hkj : k + j + 1 = d) (hk : 1 ≤ k) (D : ℕ)
    (hdeg : ∀ f ∈ chart.W.equations i, f.totalDegree ≤ D)
    (hE : ∀ Z, TrackD.PoolCarrier (T.sources i ∪ T.targets i) (j + 1) Z →
      ∀ f ∈ chart.W.equations i, f ∈ Z.ideal)
    (hminor : ∀ y : Point d, MvPolynomial.eval y (chart.W.minor i) ≠ 0 →
      Module.finrank ℂ (TrackD.jacKer (chart.W.equations i) y) + (j + 1) ≤ d)
    (L : CommonProductLists chart.W η)
    (hgeometry : ∀ X ∈ chart.W.sourceCarriers i, ∀ Y ∈ L.lists i X,
      TrackD.GenericallyTransverse X Y) :
    ∃ fs ft fm : TrackD.PairPoly d,
      fs ∈ Submodule.span ℂ ((chart.W.equations i).image secantSourceTest : Set _) ∧
      ft ∈ Submodule.span ℂ ((chart.W.equations i).image secantTargetTest : Set _) ∧
      (2 ≤ k → fm ∈ Submodule.span ℂ
        (combinedSecantMinors (chart.W.equations i) (d - k) : Set _)) ∧
      (fs * ft * fm).totalDegree ≤ (2 * d + 2) * D ∧
      ∀ pq ∈ chart.G, chart.W.owner i pq.2 ∈ L.lists i (chart.W.owner i pq.1) →
        ¬ TrackD.VanishesOnProduct (fs * ft * fm)
          (chart.W.owner i pq.1) (chart.W.owner i pq.2) := by
  let R := (chart.G.filter (fun pq => chart.W.owner i pq.2 ∈
    L.lists i (chart.W.owner i pq.1))).image
      (fun pq => (chart.W.owner i pq.1, chart.W.owner i pq.2))
  have hwitness (r : AffineVariety d × AffineVariety d) (hr : r ∈ R) :
      ∃ pq ∈ chart.G, chart.W.owner i pq.2 ∈ L.lists i (chart.W.owner i pq.1) ∧
        chart.W.owner i pq.1 = r.1 ∧ chart.W.owner i pq.2 = r.2 := by
    obtain ⟨pq, hpq, heq⟩ := Finset.mem_image.mp hr
    obtain ⟨hpq, hlist⟩ := Finset.mem_filter.mp hpq
    exact ⟨pq, hpq, hlist, congrArg Prod.fst heq, congrArg Prod.snd heq⟩
  have hR (r : AffineVariety d × AffineVariety d) (hr : r ∈ R) :
      r.1.IsIrreducible ∧ r.2.IsIrreducible ∧ r.1.dimension = k ∧ r.2.dimension = k := by
    obtain ⟨pq, hpq, _, hX, hY⟩ := hwitness r hr
    obtain ⟨r₀, hr₀, hrX, hrY⟩ := chart.hown pq hpq
    have hXr : r.1 = r₀.1 := by rw [← hX, chart.hWownF]; exact hrX
    have hYr : r.2 = r₀.2 := by rw [← hY, chart.hWownF]; exact hrY
    have hirr := chart.pool.hRirr r₀ hr₀
    have hdim := chart.pool.hRdim r₀ hr₀
    rw [← hXr, ← hYr] at hirr hdim
    exact ⟨hirr.1, hirr.2, hdim.1, hdim.2⟩
  have hgeneric (X : AffineVariety d) (hX : X.IsIrreducible) (hdim : X.dimension = k)
      (hcarrier : TrackD.PoolCarrier (T.sources i ∪ T.targets i) (j + 1) X)
      (x : Point d) (hx : x ∈ X.points) (hn : MvPolynomial.eval x (chart.W.minor i) ≠ 0) :
      TrackD.ForGeneralPoint X (fun p => X.tangentSpace p =
        TrackD.jacKer (chart.W.equations i) p ∧
        Module.finrank ℂ (TrackD.jacKer (chart.W.equations i) p) = k) := by
    apply physical_tangent_generic X hX (chart.W.equations i) (chart.W.minor i) k hdim
      (hE X hcarrier) ⟨x, hx, hn⟩
    intro y hy
    have hh := hminor y hy
    omega
  have htr (r : AffineVariety d × AffineVariety d) (hr : r ∈ R) :
      TrackD.GenericallyTransverse r.1 r.2 := by
    obtain ⟨pq, hpq, hlist, hX, hY⟩ := hwitness r hr
    have hsource : chart.W.owner i pq.1 ∈ chart.W.sourceCarriers i :=
      Finset.mem_image_of_mem _ (chart.hGpoolsList pq hpq).1
    rw [← hX, ← hY]
    exact hgeometry _ hsource _ hlist
  have hpeq (r : AffineVariety d × AffineVariety d) (hr : r ∈ R) :
      TrackD.ForGeneralPoint r.1 (fun p => r.1.tangentSpace p =
        TrackD.jacKer (chart.W.equations i) p ∧
        Module.finrank ℂ (TrackD.jacKer (chart.W.equations i) p) = k) := by
    obtain ⟨pq, hpq, _, hX, _⟩ := hwitness r hr
    have hh := common_retained_owner_regular (T.sources i) (T.sources i ∪ T.targets i)
      Finset.subset_union_left (j + 1) (chart.W.equations i) (chart.W.minor i)
      (chart.W.owner i) (chart.W.supported i) pq.1 (chart.hGpoolsList pq hpq).1
    rw [hX] at hh
    exact hgeneric r.1 (hR r hr).1 (hR r hr).2.2.1 hh.1 _ hh.2.1 hh.2.2.2.2.2.1
  have hqeq (r : AffineVariety d × AffineVariety d) (hr : r ∈ R) :
      TrackD.ForGeneralPoint r.2 (fun q => r.2.tangentSpace q =
        TrackD.jacKer (chart.W.equations i) q ∧
        Module.finrank ℂ (TrackD.jacKer (chart.W.equations i) q) = k) := by
    obtain ⟨pq, hpq, _, _, hY⟩ := hwitness r hr
    have hh := common_retained_owner_regular (T.targets i) (T.sources i ∪ T.targets i)
      Finset.subset_union_right (j + 1) (chart.W.equations i) (chart.W.minor i)
      (chart.W.owner i) (chart.W.supported i) pq.2 (chart.hGpoolsList pq hpq).2.1
    rw [hY] at hh
    exact hgeneric r.2 (hR r hr).2.1 (hR r hr).2.2.2 hh.1 _ hh.2.1 hh.2.2.2.2.2.1
  have hspan : 2 ≤ k → ∀ r ∈ R, ¬ ∃ Ff : AffineSubspace ℂ (Point d),
      Module.finrank ℂ Ff.direction ≤ k + 1 ∧ r.1.points ⊆ ↑Ff := by
    intro hk2 r hr
    obtain ⟨pq, hpq, _, hX, _⟩ := hwitness r hr
    have hh := chart.pool.hspan hk2 pq.1 (chart.hGmem pq hpq).1
    rw [← chart.hWownF pq.1, hX] at hh
    exact hh
  obtain ⟨fs, ft, fm, hfs, hft, hfm, hdegree, hnonvan⟩ :=
    exists_physical_pair_tests (chart.W.equations i) D k R hk hdeg hR htr hpeq hqeq hspan
  refine ⟨fs, ft, fm, hfs, hft, hfm, hdegree, ?_⟩
  intro pq hpq hlist
  exact hnonvan _ (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hpq, hlist⟩))

/-- Uniform tangent tests with the plateau and retained-mass premises
explicit. The caller in `OuterRows` already has these premises. -/
theorem outer_tangent_tests_of_plateau {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (M : CommonPoolProfile T)
    (k j : ℕ) (hkj : k + j + 1 = d) (hk : 1 ≤ k ∧ k + 1 < d)
    (i₀ : Fin d) (ρ ε : ℝ) (Bdeg : ℕ → ℝ) (τ : ℝ)
    (hρ1 : ρ < 1) (ξ : ℝ) (hξ : 0 < ξ)
    (hplateau : TrackD.OnPlateau M.b (j + 1) ξ τ)
    (W : CommonPhysicalSequence T M (j + 1) τ)
    (hreg : ∀ ρ'' : ℝ, 0 < ρ'' → ∀ᶠ i in atTop,
      ∃ cert : OuterRegularityCert T M k i j i₀ ρ ε ρ'' (Bdeg i) τ,
        cert.chart.W = W) :
    ∀ ρ' : ℝ, 0 < ρ' → ∀ᶠ i in atTop,
      ∃ (cert : OuterRegularityCert T M k i j i₀ ρ ε ρ' (Bdeg i) τ)
        (_ : cert.chart.W = W) (sys : @OuterTestSystem d),
      (∀ pq ∈ cert.chart.G, cert.good pq → ∀ X Y : AffineVariety d,
        cert.chart.W.owner i pq.1 = X → cert.chart.W.owner i pq.2 = Y →
        OuterTestsNonvanishing sys (TrackD.toC pq.1) (TrackD.toC pq.2) ∧
        Nonempty (OuterTangentData i₀ (TrackD.toC pq.1) (TrackD.toC pq.2) X Y k
          (outerLabelTangent cert.Eqs i₀ (TrackD.toC pq.1) (TrackD.toC pq.2)))) ∧
      (∀ pq ∈ cert.chart.G, cert.good pq → ∀ X Y : AffineVariety d, ∀ q' : Point d,
        cert.chart.W.owner i pq.1 = X → cert.chart.W.owner i pq.2 = Y →
        q' ∈ Y.points → (q' - TrackD.toC pq.1) i₀ ≠ 0 →
        (fun kk => TrackD.labelPt i₀ (TrackD.toC pq.1) q'
          (finSumFinEquiv.symm kk)) ∈ (commonProductImage i₀ X Y).points →
        OuterTestsNonvanishing sys (TrackD.toC pq.1) q' →
        Nonempty (OuterTangentData i₀ (TrackD.toC pq.1) q' X Y k
          (outerLabelTangent cert.Eqs i₀ (TrackD.toC pq.1) q'))) := by
  intro ρ' hρ'
  have hj : j + 1 < d := by omega
  have hτ : -1 < τ := by
    have hb := common_profile_time_lower M ⟨0, by omega⟩
    have hh := (hplateau ⟨0, by omega⟩).1 (by change (0 : ℕ) < j + 1; omega)
    linarith
  obtain ⟨L⟩ := selected_common_product_lists W hj (by omega) 1 (by norm_num)
  have h1ρ : 0 < 1 - ρ := by linarith
  let θ : ℝ := (ρ' / 3) * (1 - ρ) ^ 2
  let K : ℝ := 2 * d + 2
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hK : 1 ≤ K := by dsimp [K]; have := Nat.cast_nonneg (α := ℝ) d; linarith
  filter_upwards [hreg (ρ' / 3) (by positivity), W.tests, L.geometry,
    common_list_pair_loss W L θ hθ,
    common_source_product_testing T M (j + 1) hj τ ξ W hτ hξ hplateau θ K hθ hK]
    with i hci htests hgeo hlists hprod
  obtain ⟨cert, hpin⟩ := hci
  subst W
  rcases outer_chart_equal_roles_or_empty cert.chart with hroles | hGempty
  · let D : ℕ := ⌊TrackD.testDeg (TrackD.cfgB (regime.P i)) (M.s i) τ⌋₊
    have hT0 : 0 ≤ TrackD.testDeg (TrackD.cfgB (regime.P i)) (M.s i) τ := by
      unfold TrackD.testDeg
      exact (mul_pos (regime.B_pos i) (Real.exp_pos _)).le
    have hdegree : ∀ f ∈ cert.chart.W.equations i, f.totalDegree ≤ D := by
      intro f hf
      exact Nat.le_floor (htests.1 f hf)
    have hgeometry : ∀ X ∈ cert.chart.W.sourceCarriers i,
        ∀ Y ∈ L.lists i X, TrackD.GenericallyTransverse X Y := by
      intro X hX Y hY
      exact (hgeo X hX Y hY).mono (fun _ _ _ _ hh => ⟨hh.1, hh.2.1⟩)
    obtain ⟨fs, ft, fm, hfs, hft, hfm, hFdeg, hFn⟩ := outer_chart_physical_tests
      cert.chart hkj hk.1 D hdegree htests.2.2.1 htests.2.2.2 L hgeometry
    let Ftest := fs * ft * fm
    have hFreal : (Ftest.totalDegree : ℝ) ≤ K * (D : ℝ) := by
      dsimp [Ftest, K]
      exact_mod_cast hFdeg
    have hDbound : (D : ℝ) ≤ TrackD.testDeg (TrackD.cfgB (regime.P i)) (M.s i) τ :=
      Nat.floor_le hT0
    have hFbound := hFreal.trans
      (mul_le_mul_of_nonneg_left hDbound (by dsimp [K]; positivity))
    let n : ℝ := (TrackD.poolPts (T.sources i)).card
    let s : ℝ := cert.chart.pool.S.card
    have hn0 : 0 ≤ n := Nat.cast_nonneg _
    have hscale : θ * n ^ 2 ≤ (ρ' / 3) * s ^ 2 := by
      have hh := pow_le_pow_left₀ (mul_nonneg (by linarith : 0 ≤ 1 - ρ) hn0)
        cert.chart.pool.hScard 2
      calc θ * n ^ 2 = (ρ' / 3) * ((1 - ρ) * n) ^ 2 := by dsimp [θ]; ring
        _ ≤ (ρ' / 3) * s ^ 2 := mul_le_mul_of_nonneg_left hh (by positivity)
    let badL := cert.chart.G.filter (fun pq =>
      cert.chart.W.owner i pq.2 ∉ L.lists i (cert.chart.W.owner i pq.1))
    let badF := cert.chart.G.filter (fun pq =>
      cert.chart.W.owner i pq.2 ∈ L.lists i (cert.chart.W.owner i pq.1) ∧
      MvPolynomial.eval (TrackD.pairPt (TrackD.toC pq.1) (TrackD.toC pq.2)) Ftest = 0)
    have hbadL : (badL.card : ℝ) ≤ θ * n ^ 2 := by
      have hsub : badL ⊆ (cert.chart.W.sources i ×ˢ cert.chart.W.targets i).filter (fun pq =>
          cert.chart.W.owner i pq.2 ∉ L.lists i (cert.chart.W.owner i pq.1)) := by
        intro pq hpq
        obtain ⟨hpq, hnot⟩ := Finset.mem_filter.mp hpq
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨(cert.chart.hGpoolsList pq hpq).1, (cert.chart.hGpoolsList pq hpq).2.1⟩, hnot⟩
      have hcard : (badL.card : ℝ) ≤
          (((cert.chart.W.sources i ×ˢ cert.chart.W.targets i).filter (fun pq =>
            cert.chart.W.owner i pq.2 ∉ L.lists i (cert.chart.W.owner i pq.1))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      have hh := hcard.trans hlists
      rw [← common_physical_same_pool cert.chart.W i hroles] at hh
      have hret : (cert.chart.W.sources i).card ≤ (TrackD.poolPts (T.sources i)).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      have hretR : ((cert.chart.W.sources i).card : ℝ) ≤ n := by
        dsimp [n]
        exact_mod_cast hret
      calc (badL.card : ℝ) ≤ θ * (cert.chart.W.sources i).card * (cert.chart.W.sources i).card := hh
        _ = θ * ((cert.chart.W.sources i).card : ℝ) ^ 2 := by ring
        _ ≤ θ * n ^ 2 := mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (Nat.cast_nonneg _) hretR 2) hθ.le
    have hbadF : (badF.card : ℝ) ≤ θ * n ^ 2 := by
      have hsub : badF ⊆
          (TrackD.poolPts (T.sources i) ×ˢ TrackD.poolPts (T.sources i)).filter (fun pq =>
            MvPolynomial.eval (TrackD.pairPt (TrackD.toC pq.1) (TrackD.toC pq.2)) Ftest = 0 ∧
            ¬ TrackD.VanishesOnProduct Ftest (cert.chart.W.owner i pq.1)
              (cert.chart.W.owner i pq.2)) := by
        intro pq hpq
        obtain ⟨hpq, hlist, hz⟩ := Finset.mem_filter.mp hpq
        have hmem := cert.chart.hGmem pq hpq
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨cert.chart.pool.hSsub hmem.1, cert.chart.pool.hSsub hmem.2⟩, hz, hFn pq hpq hlist⟩
      have hcard : (badF.card : ℝ) ≤
          (((TrackD.poolPts (T.sources i) ×ˢ TrackD.poolPts (T.sources i)).filter (fun pq =>
            MvPolynomial.eval (TrackD.pairPt (TrackD.toC pq.1) (TrackD.toC pq.2)) Ftest = 0 ∧
            ¬ TrackD.VanishesOnProduct Ftest (cert.chart.W.owner i pq.1)
              (cert.chart.W.owner i pq.2))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      exact hcard.trans (hprod Ftest hFbound)
    let keep : RPoint d × RPoint d → Prop := fun pq =>
      cert.chart.W.owner i pq.2 ∈ L.lists i (cert.chart.W.owner i pq.1) ∧
      MvPolynomial.eval (TrackD.pairPt (TrackD.toC pq.1) (TrackD.toC pq.2)) Ftest ≠ 0
    have hloss : ((cert.chart.G.filter (fun pq => ¬ keep pq)).card : ℝ) ≤
        (2 * ρ' / 3) * (cert.chart.pool.S.card : ℝ) ^ 2 := by
      have hsub : cert.chart.G.filter (fun pq => ¬ keep pq) ⊆ badL ∪ badF := by
        intro pq hpq
        obtain ⟨hpq, hn⟩ := Finset.mem_filter.mp hpq
        by_cases hlist : cert.chart.W.owner i pq.2 ∈ L.lists i (cert.chart.W.owner i pq.1)
        · have hz : MvPolynomial.eval (TrackD.pairPt (TrackD.toC pq.1) (TrackD.toC pq.2)) Ftest = 0 := by
            by_contra hne
            exact hn ⟨hlist, hne⟩
          exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hpq, hlist, hz⟩)
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hpq, hlist⟩)
      have hcard : ((cert.chart.G.filter (fun pq => ¬ keep pq)).card : ℝ) ≤
          (badL.card : ℝ) + (badF.card : ℝ) := by
        exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      calc _ ≤ (badL.card : ℝ) + (badF.card : ℝ) := hcard
        _ ≤ θ * n ^ 2 + θ * n ^ 2 := add_le_add hbadL hbadF
        _ ≤ (ρ' / 3) * s ^ 2 + (ρ' / 3) * s ^ 2 := add_le_add hscale hscale
        _ = (2 * ρ' / 3) * (cert.chart.pool.S.card : ℝ) ^ 2 := by dsimp [s]; ring
    obtain ⟨sys, hfirst, hsecond⟩ := outer_tangent_tests_on_good cert hkj (by omega)
      htests.2.2.1 htests.2.2.2 fs ft fm hfs hft hfm
    let cert' := outer_regularity_restrict (ρ₁ := ρ') (η := 2 * ρ' / 3)
      cert keep (by positivity) (by linarith) (by
        convert hloss using 1 <;> congr 2 <;> ext pq <;> simp only [Finset.mem_filter])
    refine ⟨cert', rfl, sys, ?_, ?_⟩
    · intro pq hpq hgood
      change cert.good pq ∧ keep pq at hgood
      exact hfirst pq hpq hgood.1 hgood.2.2
    · intro pq hpq hgood
      change cert.good pq ∧ keep pq at hgood
      exact hsecond pq hpq hgood.1
  · let cert' := outer_regularity_restrict (ρ₁ := ρ') (η := 0)
      cert (fun _ => True) (by norm_num) (by linarith) (by simp)
    refine ⟨cert', rfl, { gph := 0, srcTests := ∅, tgtTests := ∅ }, ?_, ?_⟩
    · intro pq hpq
      have hh : pq ∈ cert.chart.G := hpq
      exfalso
      simpa [hGempty] using hh
    · intro pq hpq
      have hh : pq ∈ cert.chart.G := hpq
      exfalso
      simpa [hGempty] using hh

/-- sc:outer-regularity.tangent-tests (sparse-cones.tex:526–561).
Input: regularity certificates at every budget (190). Output at budget `ρ'`:
a certificate (from the input at `ρ'/2`, chart weakened by
`OuterChartCert.mono`, good pairs further restricted at cost `ρ'/2`) and one
global test system `sys`. Tests: source/target injectivity
`∇f_a(r)·(q-p) ≠ 0` from the common physical equations of `chart.W` (at
`r ∈ S` their Jacobian kernel is the tangent space of the unique carrier,
`TrackD.JacRegularAt`), the physical minor `chart.W.minor i`, a generic
combination of the `(2d-2k)`-minors of the label Jacobian of `Eqs` at
`labelPt i₀ p q` (cleared of the chart denominator; nonzero at every good
label by `hsmooth`), and for `k ≥ 2` the combined-row-span `c'×c'` minors
(`c' = d-k`; carriers span `≥ k+2` by `pool.hspan`; equal projected tangents
would force a common `(k+1)`-flat, `TrackD.geo_secants_equal_tangents`).
Choose generic constant combinations and product-test their actual zeros
away (`o(|S|²)`). Part 1: tangent data with `TW = outerLabelTangent` at every
good pair. Part 2: the same at any `q'` on the target carrier whose label lies
in the complete product image and where `sys` is nonzero (consumed by the
lift pooling 195): at such `q'` the minor gives `Y` smooth with tangent space
the physical Jacobian kernel, and the label Jacobian has corank `2k` because
`Eqs` vanish on the `2k`-dimensional image through the label (`hvanish`).
The physical sequence `W` is fixed globally: every consumed and produced cert
satisfies `cert.chart.W = W`, so the source/target test degrees come from the
single `W.tests` and the product-testing deletion is uniform in `i`. Without
the pin the statement is unprovable as stated (each cert could carry its own
`W` with its own `tests` threshold). The retained-pool
bound also needs `ρ < 1` and a positive plateau margin `ξ` at `τ`; the body is `outer_tangent_tests_of_plateau`. -/
theorem outer_tangent_tests {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (M : CommonPoolProfile T)
    (k j : ℕ) (hkj : k + j + 1 = d) (hk : 1 ≤ k ∧ k + 1 < d)
    (i₀ : Fin d) (ρ ε : ℝ) (Bdeg : ℕ → ℝ) (τ : ℝ)
    (hρ1 : ρ < 1) (ξ : ℝ) (hξ : 0 < ξ)
    (hplateau : TrackD.OnPlateau M.b (j + 1) ξ τ)
    (W : CommonPhysicalSequence T M (j + 1) τ)
    (hreg : ∀ ρ'' : ℝ, 0 < ρ'' → ∀ᶠ i in atTop,
      ∃ cert : OuterRegularityCert T M k i j i₀ ρ ε ρ'' (Bdeg i) τ,
        cert.chart.W = W) :
    ∀ ρ' : ℝ, 0 < ρ' → ∀ᶠ i in atTop,
      ∃ (cert : OuterRegularityCert T M k i j i₀ ρ ε ρ' (Bdeg i) τ)
        (_ : cert.chart.W = W)
        (sys : @OuterTestSystem d),
      (∀ pq ∈ cert.chart.G, cert.good pq → ∀ X Y : AffineVariety d,
        cert.chart.W.owner i pq.1 = X → cert.chart.W.owner i pq.2 = Y →
        OuterTestsNonvanishing sys (TrackD.toC pq.1) (TrackD.toC pq.2) ∧
        Nonempty (OuterTangentData i₀ (TrackD.toC pq.1) (TrackD.toC pq.2) X Y k
          (outerLabelTangent cert.Eqs i₀ (TrackD.toC pq.1) (TrackD.toC pq.2)))) ∧
      (∀ pq ∈ cert.chart.G, cert.good pq → ∀ X Y : AffineVariety d, ∀ q' : Point d,
        cert.chart.W.owner i pq.1 = X → cert.chart.W.owner i pq.2 = Y →
        q' ∈ Y.points →
        (q' - TrackD.toC pq.1) i₀ ≠ 0 →
        (fun kk => TrackD.labelPt i₀ (TrackD.toC pq.1) q'
          (finSumFinEquiv.symm kk)) ∈ (commonProductImage i₀ X Y).points →
        OuterTestsNonvanishing sys (TrackD.toC pq.1) q' →
        Nonempty (OuterTangentData i₀ (TrackD.toC pq.1) q' X Y k
          (outerLabelTangent cert.Eqs i₀ (TrackD.toC pq.1) q'))) :=
  outer_tangent_tests_of_plateau T M k j hkj hk i₀ ρ ε Bdeg τ hρ1 ξ hξ hplateau W hreg

end
end DistinctDistances.SparseCones
