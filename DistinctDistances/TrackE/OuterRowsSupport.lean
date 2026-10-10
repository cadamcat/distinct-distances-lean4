import DistinctDistances.TrackE.OuterChartRows
import DistinctDistances.TrackE.OuterAssembly
import DistinctDistances.TrackE.CommonPhysical
import DistinctDistances.TrackE.CommonLabelGroup
import DistinctDistances.Bridges.CurveSamples

/-! Support for the assembly of `outer_rows_sparse` (sparse-cones.tex:340–651):
pool points are sample points, the globally unassigned targets are few, every
selected pair lies in some direction chart, and the three numeric comparisons
(discard, rows, unassigned targets). -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- Pool points are sample points. -/
theorem outer_poolPts_subset_P {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (i : ℕ) :
    TrackD.poolPts (T.sources i) ⊆ regime.P i ∧
      TrackD.poolPts (T.targets i) ⊆ regime.P i := by
  have hgood := (T.certificate i).good
  constructor
  · intro q hq
    obtain ⟨X, hX, hqX⟩ := Finset.mem_biUnion.mp hq
    exact (hgood.pieces_good X ((T.certificate i).sources_subset hX)).1.subset hqX
  · intro q hq
    obtain ⟨X, hX, hqX⟩ := Finset.mem_biUnion.mp hq
    exact (hgood.pieces_good X ((T.certificate i).targets_subset hX)).1.subset hqX

/-- The targets without a global terminal curve are a `θ`-fraction of the
target pool (`TerminalAssignment.unassigned`, pieces disjoint). -/
theorem outer_unassigned_targets_card {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (i : ℕ) :
    (((TrackD.poolPts (T.targets i)).filter (fun q => T.terminal i q = none)).card : ℝ) ≤
      selectionTolerance (T.precision i) * (TrackD.poolPts (T.targets i)).card := by
  have hcert := T.certificate i
  have hdisj : ((T.targets i : Set (TrackD.Piece d))).PairwiseDisjoint TrackD.Piece.pts :=
    hcert.good.pieces_disjoint.subset (Finset.coe_subset.mpr hcert.targets_subset)
  have hcard : ((TrackD.poolPts (T.targets i)).card : ℝ) =
      ∑ X ∈ T.targets i, (X.pts.card : ℝ) := by
    unfold TrackD.poolPts
    rw [Finset.card_biUnion hdisj]
    push_cast
    rfl
  have hfil : (TrackD.poolPts (T.targets i)).filter (fun q => T.terminal i q = none) =
      (T.targets i).biUnion (fun X => X.pts.filter (fun q => T.terminal i q = none)) := by
    unfold TrackD.poolPts
    rw [Finset.filter_biUnion]
  rw [hfil, hcard, Finset.mul_sum]
  calc (((T.targets i).biUnion
        (fun X => X.pts.filter (fun q => T.terminal i q = none))).card : ℝ)
      ≤ ∑ X ∈ T.targets i, ((X.pts.filter (fun q => T.terminal i q = none)).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ X ∈ T.targets i, selectionTolerance (T.precision i) * (X.pts.card : ℝ) :=
        Finset.sum_le_sum fun X hX =>
          hcert.terminal.unassigned X (hcert.targets_subset hX)

/-- Every selected pair has a nonzero secant coordinate (a direction chart). -/
theorem outer_exists_chart {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} {i : ℕ} {pq : RPoint d × RPoint d}
    (h : pq ∈ outerSelectedGraph T i) :
    ∃ i₀ : Fin d, (TrackD.toC pq.2 - TrackD.toC pq.1) i₀ ≠ 0 := by
  have hsel := (Finset.mem_filter.mp h).2
  have hne : pq.1 ≠ pq.2 := hsel.1
  by_contra hcon
  push_neg at hcon
  apply hne
  apply profile_toC_injective
  funext a
  have h' := hcon a
  rw [Pi.sub_apply, sub_eq_zero] at h'
  exact h'.symm

/-- The discard comparison: `B^{2-c} · B^{tol} ≤ ρ' A` eventually, since the
selection tolerance tends to zero and `A = B²`. -/
theorem outer_discard_numeric {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (c ρ' : ℝ) (hc : 0 < c) (hρ' : 0 < ρ') :
    ∀ᶠ i in atTop, regime.B i ^ (2 - c) * regime.B i ^ selectionTolerance (T.precision i) ≤
      ρ' * regime.A i := by
  have htol := (selection_tolerance_tendsto_zero T.precision T.precision_grows).eventually
    (Iic_mem_nhds (half_pos hc))
  have hB1 := regime.B_tendsto.eventually (eventually_ge_atTop (1 : ℝ))
  have hsmall : Tendsto (fun i => regime.B i ^ (-(c / 2))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (half_pos hc)).comp regime.B_tendsto
  have hs2 := hsmall.eventually (Iic_mem_nhds hρ')
  filter_upwards [htol, hB1, hs2] with i hti hBi hsi
  have hBpos : 0 < regime.B i := by linarith
  rw [← Real.rpow_add hBpos, regime.A_eq_B_sq]
  calc regime.B i ^ (2 - c + selectionTolerance (T.precision i))
      ≤ regime.B i ^ ((2 : ℝ) + -(c / 2)) :=
        Real.rpow_le_rpow_of_exponent_le hBi (by linarith)
    _ = regime.B i ^ (2 : ℕ) * regime.B i ^ (-(c / 2)) := by
        rw [Real.rpow_add hBpos]
        norm_cast
    _ ≤ regime.B i ^ 2 * ρ' := mul_le_mul_of_nonneg_left hsi (by positivity)
    _ = ρ' * regime.B i ^ 2 := mul_comm _ _

/-- Pure arithmetic of the discard: with `E = δN/A`, `n ≥ N√δ`, `|S| ≥ n/2`
and `X ≤ (ρ'/2) A`, one has `E·X ≤ ρ'|S|`. -/
theorem outer_discard_arith (δ N A n S X ρ' : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hA : 0 < A) (hN : 0 < N) (hn : N * Real.sqrt δ ≤ n) (hS : (1 - 1 / 2) * n ≤ S)
    (hX : X ≤ ρ' / 2 * A) (hρ' : 0 < ρ') :
    δ * N / A * X ≤ ρ' * S := by
  have hsq := Real.sq_sqrt hδ0.le
  have hs1 : Real.sqrt δ ≤ 1 := by
    have := Real.sqrt_le_sqrt hδ1
    rwa [Real.sqrt_one] at this
  have hs0 := Real.sqrt_nonneg δ
  have hδs : δ ≤ Real.sqrt δ := by nlinarith
  have hE0 : 0 ≤ δ * N / A := by positivity
  have h1 : δ * N / A * X ≤ δ * N / A * (ρ' / 2 * A) := mul_le_mul_of_nonneg_left hX hE0
  have h2 : δ * N / A * (ρ' / 2 * A) = δ * N * ρ' / 2 := by
    field_simp
  have h3 : δ * N * ρ' / 2 ≤ Real.sqrt δ * N * ρ' / 2 := by
    have := mul_le_mul_of_nonneg_right hδs (le_of_lt (mul_pos hN hρ'))
    nlinarith
  nlinarith

/-- The row comparison: `d · C₀ M (2E) ≤ ρ n` eventually, from `M/A → 0`,
`δ → 0` and the outer mass `n ≥ N√δ`. -/
theorem outer_row_numeric {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (houter : ∀ i, T.IsOuter i)
    (C0 ρ : ℝ) (hC0 : 0 ≤ C0) (hρ : 0 < ρ) :
    ∀ᶠ i in atTop, (d : ℝ) * (C0 * regime.M i * (2 * (F.delta i * regime.N i / regime.A i))) ≤
      ρ * (TrackD.poolPts (T.sources i)).card := by
  set K : ℝ := 2 * d * C0 + 1 with hK
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hKpos : 0 < K := by positivity
  have hMA := regime.M_div_A_tendsto.eventually (Iic_mem_nhds (div_pos hρ hKpos))
  have hδ1 := F.delta_tendsto.eventually (Iic_mem_nhds (zero_lt_one' ℝ))
  filter_upwards [hMA, hδ1] with i hMAi hδi
  have hA := regime.A_pos i
  have hN := regime.N_pos i
  have hM : 0 ≤ regime.M i := le_trans (by norm_num) (regime.M_ge_two i)
  have hδ0 := F.delta_pos i
  have hn := (houter i).2.2
  have hsq := Real.sq_sqrt hδ0.le
  have hs1 : Real.sqrt (F.delta i) ≤ 1 := by
    have := Real.sqrt_le_sqrt hδi
    rwa [Real.sqrt_one] at this
  have hs0 := Real.sqrt_nonneg (F.delta i)
  have hδs : F.delta i ≤ Real.sqrt (F.delta i) := by nlinarith
  set x : ℝ := regime.M i / regime.A i with hx
  have hx0 : 0 ≤ x := by positivity
  have hLHS : (d : ℝ) * (C0 * regime.M i * (2 * (F.delta i * regime.N i / regime.A i))) =
      (2 * d * C0) * x * (F.delta i * regime.N i) := by
    rw [hx, div_eq_mul_inv, div_eq_mul_inv]; ring
  rw [hLHS]
  have hKx : (2 * d * C0) * x ≤ ρ := by
    have h1 : K * x ≤ ρ := by
      have := mul_le_mul_of_nonneg_left hMAi hKpos.le
      rwa [mul_div_cancel₀ _ hKpos.ne'] at this
    have h2 : (2 * d * C0) * x ≤ K * x := mul_le_mul_of_nonneg_right (by linarith) hx0
    linarith
  have hδN : F.delta i * regime.N i ≤ (TrackD.poolPts (T.sources i)).card := by
    have := mul_le_mul_of_nonneg_right hδs hN.le
    linarith
  have h2dC : 0 ≤ (2 * d * C0) * x := by positivity
  calc (2 * d * C0) * x * (F.delta i * regime.N i)
      ≤ (2 * d * C0) * x * (TrackD.poolPts (T.sources i)).card :=
        mul_le_mul_of_nonneg_left hδN h2dC
    _ ≤ ρ * (TrackD.poolPts (T.sources i)).card :=
        mul_le_mul_of_nonneg_right hKx (Nat.cast_nonneg _)

/-- The outer rows at one index (sparse-cones.tex:340–651, combination of the
`d` direction charts). Given, in every chart, the regular certificate with its
test system (191) and the discard numerics, the retained graph is the union over
the charts of the good, undiscarded pairs whose target has a global terminal
curve. Its deletion is at most `3ρ'|S|²` per chart plus the unassigned targets
(`θ n²`), and every row has at most `C₀ M (2E)` partners per chart (`k ≥ 2`:
`outer_chart_row_bound`; `k = 1`: empty, `outer_chart_terminal_false`). -/
theorem outer_rows_at_index {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (M : CommonPoolProfile T)
    (k i j : ℕ) (hk : 1 ≤ k) {ρp ε ρ' τ : ℝ} (hρ' : 0 ≤ ρ')
    (houter : T.IsOuter i)
    (Bdeg : Fin d → ℝ)
    (cert : ∀ i₀ : Fin d, OuterRegularityCert T M k i j i₀ ρp ε ρ' (Bdeg i₀) τ)
    (sys : Fin d → @OuterTestSystem d)
    (hP1 : ∀ i₀ : Fin d, ∀ pq ∈ (cert i₀).chart.G, (cert i₀).good pq →
      ∀ X Y : AffineVariety d,
      (cert i₀).chart.W.owner i pq.1 = X → (cert i₀).chart.W.owner i pq.2 = Y →
      OuterTestsNonvanishing (sys i₀) (TrackD.toC pq.1) (TrackD.toC pq.2) ∧
      Nonempty (OuterTangentData i₀ (TrackD.toC pq.1) (TrackD.toC pq.2) X Y k
        (outerLabelTangent (cert i₀).Eqs i₀ (TrackD.toC pq.1) (TrackD.toC pq.2))))
    (hP2 : ∀ i₀ : Fin d, ∀ pq ∈ (cert i₀).chart.G, (cert i₀).good pq →
      ∀ X Y : AffineVariety d, ∀ q' : Point d,
      (cert i₀).chart.W.owner i pq.1 = X → (cert i₀).chart.W.owner i pq.2 = Y →
      q' ∈ Y.points →
      (q' - TrackD.toC pq.1) i₀ ≠ 0 →
      (fun kk => TrackD.labelPt i₀ (TrackD.toC pq.1) q'
        (finSumFinEquiv.symm kk)) ∈ (commonProductImage i₀ X Y).points →
      OuterTestsNonvanishing (sys i₀) (TrackD.toC pq.1) q' →
      Nonempty (OuterTangentData i₀ (TrackD.toC pq.1) q' X Y k
        (outerLabelTangent (cert i₀).Eqs i₀ (TrackD.toC pq.1) q')))
    (E : ℝ) (hE0 : 0 ≤ E)
    (hE : ∀ p ∈ TrackD.poolPts (T.sources i),
      ((ProjectiveFamily.degree (F.family i p) : ℚ) : ℝ) ≤ E)
    (hsmall : ∀ i₀ : Fin d,
      E * Bdeg i₀ * outerLineCap T i ≤ ρ' * ((cert i₀).chart.pool.S.card : ℝ))
    (C0 : ℝ) (hC0 : 0 ≤ C0)
    (hcurve : ∀ Y : AffineVariety d, TrackD.IsCurve Y →
      (TrackD.massOn (regime.P i) Y.points : ℝ) ≤
        C0 * ((Y.degree : ℚ) : ℝ) * TrackD.cfgM (regime.P i)) :
    ∃ Γ : Finset (RPoint d × RPoint d), Γ ⊆ outerSelectedGraph T i ∧
      ((outerSelectedGraph T i \ Γ).card : ℝ) ≤
        (d : ℝ) * (3 * ρ' * ((TrackD.poolPts (T.sources i)).card : ℝ) ^ 2) +
        ((TrackD.poolPts (T.sources i)).card : ℝ) *
          (selectionTolerance (T.precision i) * (TrackD.poolPts (T.sources i)).card) ∧
      ∀ p : RPoint d, ((Γ.filter (fun pq => pq.1 = p)).card : ℝ) ≤
        (d : ℝ) * (C0 * TrackD.cfgM (regime.P i) * (2 * E)) := by
  set n : ℝ := ((TrackD.poolPts (T.sources i)).card : ℝ) with hn
  have hPsub := outer_poolPts_subset_P T i
  have htgt : T.targets i = T.sources i := houter.1.symm
  -- the discard in each chart
  have h192 : ∀ i₀ : Fin d, ∃ D : Finset (RPoint d × RPoint d), D ⊆ (cert i₀).chart.G ∧
      ((D.card : ℝ)) ≤ ρ' * ((cert i₀).chart.pool.S.card : ℝ) ^ 2 ∧
      ∀ pq ∈ (cert i₀).chart.G \ D, (cert i₀).good pq → ∀ γ ∈ F.family i pq.1,
        γ.IsIrreducible → γ.dimension = 1 →
        (∃ h : TrackD.toC pq.2 ≠ TrackD.toC pq.1,
          radialProjection (TrackD.toC pq.1) (TrackD.toC pq.2) h ∈ γ.points) →
        outerGammaInEqs i₀ (cert i₀).Eqs (TrackD.toC pq.1) γ := by
    intro i₀
    exact outer_discard_uncontained T M k i j i₀ ρp ε ρ' (Bdeg i₀) (cert i₀) (F.family i)
      (fun pq hpq _ => ((cert i₀).chart.selected hpq).2.1) E
      (fun p hp => hE p ((cert i₀).chart.pool.hSsub hp)) (hsmall i₀)
  choose D hDsub hDcard hDisc using h192
  -- the retained pieces
  let Γc : Fin d → Finset (RPoint d × RPoint d) := fun i₀ =>
    ((cert i₀).chart.G \ D i₀).filter (fun pq => (cert i₀).good pq ∧ T.terminal i pq.2 ≠ none)
  refine ⟨Finset.univ.biUnion Γc, ?_, ?_, ?_⟩
  · intro pq hpq
    obtain ⟨i₀, _, h⟩ := Finset.mem_biUnion.mp hpq
    exact (cert i₀).chart.hGsub (Finset.mem_sdiff.mp (Finset.mem_filter.mp h).1).1
  · -- deletions
    let Del : Fin d → Finset (RPoint d × RPoint d) := fun i₀ =>
      (((outerSelectedGraph T i).filter (fun pq =>
        (TrackD.toC pq.2 - TrackD.toC pq.1) i₀ ≠ 0)) \ (cert i₀).chart.G) ∪
      ((cert i₀).chart.G.filter (fun pq => ¬ (cert i₀).good pq)) ∪ D i₀
    let Un := (outerSelectedGraph T i).filter (fun pq => T.terminal i pq.2 = none)
    have hsub : outerSelectedGraph T i \ Finset.univ.biUnion Γc ⊆
        Finset.univ.biUnion Del ∪ Un := by
      intro pq hpq
      obtain ⟨hG, hnot⟩ := Finset.mem_sdiff.mp hpq
      obtain ⟨i₀, hi₀⟩ := outer_exists_chart hG
      by_cases hterm : T.terminal i pq.2 = none
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hG, hterm⟩)
      apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      refine ⟨i₀, Finset.mem_univ _, ?_⟩
      by_cases hGc : pq ∈ (cert i₀).chart.G
      · by_cases hgood : (cert i₀).good pq
        · by_cases hD : pq ∈ D i₀
          · exact Finset.mem_union_right _ hD
          · exfalso
            apply hnot
            exact Finset.mem_biUnion.mpr ⟨i₀, Finset.mem_univ _,
              Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hGc, hD⟩, hgood, hterm⟩⟩
        · exact Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨hGc, hgood⟩))
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨hG, hi₀⟩, hGc⟩))
    have hScard : ∀ i₀ : Fin d, ((cert i₀).chart.pool.S.card : ℝ) ≤ n := fun i₀ => by
      rw [hn]
      exact_mod_cast Finset.card_le_card (cert i₀).chart.pool.hSsub
    have hSsq : ∀ i₀ : Fin d,
        ρ' * ((cert i₀).chart.pool.S.card : ℝ) ^ 2 ≤ ρ' * n ^ 2 := fun i₀ =>
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) (hScard i₀) 2) hρ'
    have hDelcard : ∀ i₀ : Fin d, ((Del i₀).card : ℝ) ≤ 3 * ρ' * n ^ 2 := by
      intro i₀
      have h1 := (cert i₀).chart.hGdel
      have h2 := (cert i₀).hbad
      have h3 := hDcard i₀
      have hc : ((Del i₀).card : ℝ) ≤
          ((((outerSelectedGraph T i).filter (fun pq =>
            (TrackD.toC pq.2 - TrackD.toC pq.1) i₀ ≠ 0)) \ (cert i₀).chart.G).card : ℝ) +
          (((cert i₀).chart.G.filter (fun pq => ¬ (cert i₀).good pq)).card : ℝ) +
          ((D i₀).card : ℝ) := by
        exact_mod_cast (Finset.card_union_le _ _).trans
          (Nat.add_le_add_right (Finset.card_union_le _ _) _)
      linarith [hSsq i₀]
    have hUncard : (Un.card : ℝ) ≤ n * (selectionTolerance (T.precision i) * n) := by
      have hsub' : Un ⊆ TrackD.poolPts (T.sources i) ×ˢ
          (TrackD.poolPts (T.sources i)).filter (fun q => T.terminal i q = none) := by
        intro pq hpq
        obtain ⟨hG, hnone⟩ := Finset.mem_filter.mp hpq
        have hG' := (Finset.mem_filter.mp hG).1
        obtain ⟨h1, h2⟩ := Finset.mem_product.mp hG'
        rw [htgt] at h2
        exact Finset.mem_product.mpr ⟨h1, Finset.mem_filter.mpr ⟨h2, hnone⟩⟩
      have hc := Finset.card_le_card hsub'
      rw [Finset.card_product] at hc
      have hu := outer_unassigned_targets_card T i
      rw [htgt] at hu
      have hc' : (Un.card : ℝ) ≤ n * (((TrackD.poolPts (T.sources i)).filter
          (fun q => T.terminal i q = none)).card : ℝ) := by
        rw [hn]
        exact_mod_cast hc
      exact hc'.trans (mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg _))
    calc ((outerSelectedGraph T i \ Finset.univ.biUnion Γc).card : ℝ)
        ≤ ((Finset.univ.biUnion Del ∪ Un).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ ((Finset.univ.biUnion Del).card : ℝ) + Un.card := by
          exact_mod_cast Finset.card_union_le _ _
      _ ≤ ∑ i₀ : Fin d, ((Del i₀).card : ℝ) + Un.card := by
          gcongr
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _i₀ : Fin d, 3 * ρ' * n ^ 2 + n * (selectionTolerance (T.precision i) * n) := by
          gcongr with i₀ _
          exact hDelcard i₀
      _ = (d : ℝ) * (3 * ρ' * n ^ 2) + n * (selectionTolerance (T.precision i) * n) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  · -- rows
    intro p
    have hdirfam : ∀ i₀ : Fin d, ∀ p ∈ (cert i₀).chart.pool.S,
        TrackD.IsDirectionalFamily (F.family i p) :=
      fun i₀ p hp => F.directional i p (hPsub.1 ((cert i₀).chart.pool.hSsub hp))
    have hGP : ∀ i₀ : Fin d, ∀ pq ∈ (cert i₀).chart.G, pq.2 ∈ regime.P i := by
      intro i₀ pq hpq
      have h := (cert i₀).chart.hGsub hpq
      exact hPsub.2 (Finset.mem_product.mp (Finset.mem_filter.mp h).1).2
    have hM0 : 0 ≤ TrackD.cfgM (regime.P i) := by unfold TrackD.cfgM; positivity
    have hrow : ∀ i₀ : Fin d, (((Γc i₀).filter (fun pq => pq.1 = p)).card : ℝ) ≤
        C0 * TrackD.cfgM (regime.P i) * (2 * E) := by
      intro i₀
      rcases Nat.lt_or_ge k 2 with hk1 | hk2
      · have hk0 : k = 1 := by omega
        have hemp : (Γc i₀).filter (fun pq => pq.1 = p) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro pq hpq _
          obtain ⟨hGD, hgood, hterm⟩ := Finset.mem_filter.mp hpq
          obtain ⟨Y, hY⟩ := Option.ne_none_iff_exists'.mp hterm
          exact outer_chart_terminal_false hk0 (cert i₀) (sys i₀) (hP1 i₀) (D i₀) (hDisc i₀)
            (hdirfam i₀) hGD hgood hY
        rw [hemp, Finset.card_empty, Nat.cast_zero]
        positivity
      · have hsub : (Γc i₀).filter (fun pq => pq.1 = p) ⊆
            ((cert i₀).chart.G \ D i₀).filter (fun pq => (cert i₀).good pq ∧ pq.1 = p) := by
          intro pq hpq
          obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hpq
          obtain ⟨h3, h4, _⟩ := Finset.mem_filter.mp h1
          exact Finset.mem_filter.mpr ⟨h3, h4, h2⟩
        have hc : (((Γc i₀).filter (fun pq => pq.1 = p)).card : ℝ) ≤
            ((((cert i₀).chart.G \ D i₀).filter
              (fun pq => (cert i₀).good pq ∧ pq.1 = p)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
        refine hc.trans ?_
        exact outer_chart_row_bound hk2 (cert i₀) (sys i₀) (hP1 i₀) (hP2 i₀) (D i₀) (hDisc i₀)
          (hdirfam i₀) E hE0 (fun p hp => hE p ((cert i₀).chart.pool.hSsub hp)) C0 hC0 hcurve
          (hGP i₀) p
    have hfil : (Finset.univ.biUnion Γc).filter (fun pq => pq.1 = p) =
        Finset.univ.biUnion (fun i₀ => (Γc i₀).filter (fun pq => pq.1 = p)) :=
      Finset.filter_biUnion _ _ _
    rw [hfil]
    calc (((Finset.univ.biUnion (fun i₀ => (Γc i₀).filter (fun pq => pq.1 = p))).card : ℝ))
        ≤ ∑ i₀ : Fin d, (((Γc i₀).filter (fun pq => pq.1 = p)).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _i₀ : Fin d, C0 * TrackD.cfgM (regime.P i) * (2 * E) :=
          Finset.sum_le_sum fun i₀ _ => hrow i₀
      _ = (d : ℝ) * (C0 * TrackD.cfgM (regime.P i) * (2 * E)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end
end DistinctDistances.SparseCones
