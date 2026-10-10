import DistinctDistances.TrackE.CommonCertificateSupport

/-! Dense dimension groups of the label envelope on a common plateau,
sparse-cones.tex:239–306. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- Limiting cut times are at least `-1` (piece times lie in `[-1, 1+θ]`). -/
theorem common_profile_time_lower {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} (M : CommonPoolProfile T) (a : Fin d) :
    -1 ≤ M.b a := by
  by_contra hnot
  have hlt : M.b a < -1 := lt_of_not_ge hnot
  have hρ : 0 < (-1 - M.b a) / 2 := by linarith
  obtain ⟨i, hi⟩ := (M.limit _ hρ).exists
  obtain ⟨X, hX⟩ := (T.certificate i).sources_nonempty
  have hgood := ((T.certificate i).good.pieces_good X
    ((T.certificate i).sources_subset hX)).1
  have hrange := (hgood.time_range a).1
  have hclose := hi X (Finset.mem_union_left _ hX) a
  have := (abs_le.mp hclose).2
  linarith

/-- After the first cut the testing degree is at least one at every index. -/
theorem common_plateau_test_degree_ge_one {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} (M : CommonPoolProfile T) (a : Fin d) (τ : ℝ)
    (hτ : M.b a < τ) (i : ℕ) :
    1 ≤ TrackD.testDeg (regime.B i) (M.s i) τ := by
  have hb := common_profile_time_lower M a
  have hs := common_pool_width_le_logB M i
  have hspos := M.width_pos i
  have hB := regime.B_pos i
  unfold TrackD.testDeg
  rw [← Real.exp_log hB, ← Real.exp_add]
  apply Real.one_le_exp
  nlinarith

/-- sc:retained-products applied on a plateau after at least two cuts
(`k < d-1`, sparse-cones.tex:56–213, 239–261, 297–306): physical retention at
a regularity time in `(b_j, τ)` (`selected_common_physical_retention`), the
fixed generic-depth lists and chart graph mass
(`selected_common_chart_graph_mass`, giving the `e_{j+1}^2` mass bound),
product testing of the degree-`L` label equations of `Γ` into the complete
images (`common_graph_complete_images`), and their geometry
(`common_product_image_geometry`, `common_product_label_mem`). -/
theorem common_label_image_certificate_retained {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (M : CommonPoolProfile T)
    (j : ℕ) (hj : j + 1 < d) (hj1 : 1 ≤ j) (τ : ℝ)
    (hτ : M.b ⟨j, by omega⟩ < τ ∧ τ < M.b ⟨j + 1, hj⟩) :
    ∀ θ : ℝ, 0 < θ → ∀ ρ : ℝ, 0 < ρ → ∀ᶠ i in atTop,
      ∀ (i₀ : Fin d) (Γ : Finset (RPoint d × RPoint d)),
        Γ ⊆ TrackD.poolPts (T.sources i) ×ˢ TrackD.poolPts (T.targets i) →
        (∀ pq ∈ Γ, (TrackD.toC pq.2 - TrackD.toC pq.1) i₀ ≠ 0) →
        ρ * ((TrackD.poolPts (T.sources i)).card : ℝ) *
          (TrackD.poolPts (T.targets i)).card ≤ Γ.card →
        ∃ (Γr : Finset (RPoint d × RPoint d)) (Z : RPoint d × RPoint d → AffineVariety (d + d)),
          CommonImageCertificate M j θ ρ i i₀
            ⌊TrackD.testDeg (regime.B i) (M.s i) τ⌋₊ Γ Γr Z := by
  intro θ hθ ρ hρ
  have hd3 := regime.dimension_ge_three
  set β := M.b ⟨j, by omega⟩ with hβdef
  set γ := M.b ⟨j + 1, hj⟩ with hγdef
  have hβ1 : -1 ≤ β := common_profile_time_lower M _
  -- plateau margins at the regularity time and at the testing time
  have hplat : ∀ t : ℝ, β < t → t < γ →
      TrackD.OnPlateau M.b (j + 1) (min (t - β) (γ - t)) t := by
    intro t ht1 ht2 a
    constructor
    · intro ha
      have hab : M.b a ≤ β := M.sorted (show a ≤ (⟨j, by omega⟩ : Fin d) from
        Nat.lt_succ_iff.mp ha)
      have := min_le_left (t - β) (γ - t)
      linarith
    · intro ha
      have hab : γ ≤ M.b a := M.sorted (show (⟨j + 1, hj⟩ : Fin d) ≤ a from ha)
      have := min_le_right (t - β) (γ - t)
      linarith
  set τph := (β + τ) / 2 with hτphdef
  have hτph1 : β < τph := by rw [hτphdef]; linarith [hτ.1]
  have hτph2 : τph < γ := by rw [hτphdef]; linarith [hτ.1, hτ.2]
  obtain ⟨W⟩ := selected_common_physical_retention T M (j + 1) hj τph
    (min (τph - β) (γ - τph)) (by linarith) (lt_min (by linarith) (by linarith))
    (hplat τph hτph1 hτph2)
  obtain ⟨L, hLmass⟩ := selected_common_chart_graph_mass W hj (by omega) θ hθ
  have hρ6 : 0 < ρ / 6 := by positivity
  have htest := common_graph_complete_images T M (j + 1) hj τph W τ
    (min (τ - β) (γ - τ)) (by linarith [hτ.1]) (lt_min (by linarith [hτ.1]) (by linarith [hτ.2]))
    (hplat τ hτ.1 hτ.2) (ρ / 6) hρ6 1 le_rfl
  filter_upwards [hLmass, htest, common_retained_pair_omissions W (ρ / 6) hρ6,
    common_list_pair_loss W L (ρ / 6) hρ6] with i hmass hpt homit hlist
  intro i₀ Γ hΓ hchart hdense
  have hB : TrackD.cfgB (regime.P i) = regime.B i := by
    simp [TrackD.cfgB, Regime.B, Regime.N]
  set Lg := ⌊TrackD.testDeg (regime.B i) (M.s i) τ⌋₊ with hLgdef
  let 𝒢 : Set (TrackD.PairPoly d) := {G | G.totalDegree ≤ Lg ∧ ∀ pq ∈ Γ,
    MvPolynomial.eval (TrackD.labelPt i₀ (TrackD.toC pq.1) (TrackD.toC pq.2)) G = 0}
  have htd0 : 0 ≤ TrackD.testDeg (regime.B i) (M.s i) τ := by
    unfold TrackD.testDeg; exact (mul_pos (regime.B_pos i) (Real.exp_pos _)).le
  obtain ⟨hgsub, hgloss, hgimg⟩ := hpt i₀ 𝒢 (by
      intro G hG
      rw [hB, one_mul]
      exact (Nat.cast_le.mpr hG.1).trans (Nat.floor_le htd0))
    Γ hΓ (fun pq hpq => ⟨hchart pq hpq, fun G hG => hG.2 pq hpq⟩)
  set good := commonImageGoodGraph i₀ Γ 𝒢 (W.owner i) with hgooddef
  let Γr := good.filter (fun pq => pq.1 ∈ W.sources i ∧ pq.2 ∈ W.targets i ∧
    W.owner i pq.2 ∈ L.lists i (W.owner i pq.1))
  let Z : RPoint d × RPoint d → AffineVariety (d + d) :=
    fun pq => commonProductImage i₀ (W.owner i pq.1) (W.owner i pq.2)
  set Sx := TrackD.poolPts (T.sources i) with hSxdef
  set Sy := TrackD.poolPts (T.targets i) with hSydef
  have hWx : W.sources i ⊆ Sx := Finset.filter_subset _ _
  have hWy : W.targets i ⊆ Sy := Finset.filter_subset _ _
  have hWcard : ((W.sources i).card : ℝ) * (W.targets i).card ≤ (Sx.card : ℝ) * Sy.card := by
    have h1 : ((W.sources i).card : ℝ) ≤ Sx.card := by exact_mod_cast Finset.card_le_card hWx
    have h2 : ((W.targets i).card : ℝ) ≤ Sy.card := by exact_mod_cast Finset.card_le_card hWy
    exact mul_le_mul h1 h2 (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  -- the actual owners contain the physical points
  have hown : ∀ x, x ∈ Sx ∨ x ∈ Sy → TrackD.toC x ∈ W.owner i x := by
    intro x hx
    have hx' : ∃ X ∈ T.sources i ∪ T.targets i, x ∈ X.pts := by
      rcases hx with hx | hx
      · rw [hSxdef, TrackD.poolPts, Finset.mem_biUnion] at hx
        obtain ⟨X, hX, h⟩ := hx
        exact ⟨X, Finset.mem_union_left _ hX, h⟩
      · rw [hSydef, TrackD.poolPts, Finset.mem_biUnion] at hx
        obtain ⟨X, hX, h⟩ := hx
        exact ⟨X, Finset.mem_union_right _ hX, h⟩
    obtain ⟨X, hX, hxX⟩ := hx'
    exact (W.supported i X hX x hxX).2
  have hΓr : ∀ pq ∈ Γr, pq ∈ Γ ∧ pq.1 ∈ W.sources i ∧ pq.2 ∈ W.targets i ∧
      W.owner i pq.2 ∈ L.lists i (W.owner i pq.1) ∧ pq ∈ good := by
    intro pq hpq
    obtain ⟨hg, h1, h2, h3⟩ := Finset.mem_filter.mp hpq
    exact ⟨hgsub hg, h1, h2, h3, hg⟩
  have hchartImg : ∀ pq ∈ Γr, Z pq ∈ commonChartImages W L i i₀ := by
    intro pq hpq
    obtain ⟨hpΓ, h1, h2, h3, _⟩ := hΓr pq hpq
    simp only [commonChartImages, Finset.mem_biUnion, Finset.mem_image]
    refine ⟨W.owner i pq.1, Finset.mem_image_of_mem _ h1, W.owner i pq.2, ?_, rfl⟩
    rw [mem_common_chart_targets]
    refine ⟨h3, TrackD.toC pq.1, hown _ (Or.inl (hWx h1)),
      TrackD.toC pq.2, hown _ (Or.inr (hWy h2)), hchart pq hpΓ⟩
  refine ⟨Γr, Z, fun pq hpq => (hΓr pq hpq).1, ?_, ?_, ?_⟩
  · -- the three deletions
    have hsub : Γ \ Γr ⊆ (Γ \ good) ∪
        (((Sx ×ˢ Sy) \ (W.sources i ×ˢ W.targets i)) ∪
          ((W.sources i ×ˢ W.targets i).filter (fun pq =>
            W.owner i pq.2 ∉ L.lists i (W.owner i pq.1)))) := by
      intro pq hpq
      obtain ⟨hpΓ, hnot⟩ := Finset.mem_sdiff.mp hpq
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_product, Finset.mem_filter]
      by_cases hg : pq ∈ good
      · by_cases hw : pq.1 ∈ W.sources i ∧ pq.2 ∈ W.targets i
        · right; right
          refine ⟨hw, fun hl => hnot ?_⟩
          exact Finset.mem_filter.mpr ⟨hg, hw.1, hw.2, hl⟩
        · right; left
          have hpS := Finset.mem_product.mp (hΓ hpΓ)
          exact ⟨hpS, hw⟩
      · left; exact ⟨hpΓ, hg⟩
    have hc := (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_left (Finset.card_union_le _ _) _))
    have hc' := (Nat.cast_le (α := ℝ)).mpr hc
    push_cast at hc'
    have hW6 := mul_le_mul_of_nonneg_left hWcard (by positivity : (0 : ℝ) ≤ ρ / 6)
    have e1 : ρ / 6 * (((W.sources i).card : ℝ) * (W.targets i).card) =
        ρ / 6 * ((W.sources i).card : ℝ) * (W.targets i).card := by ring
    have e2 : ρ / 6 * ((Sx.card : ℝ) * Sy.card) = ρ / 6 * (Sx.card : ℝ) * Sy.card := by ring
    have e3 : ρ / 2 * (Sx.card : ℝ) * Sy.card =
        ρ / 6 * (Sx.card : ℝ) * Sy.card + ρ / 6 * (Sx.card : ℝ) * Sy.card +
          ρ / 6 * (Sx.card : ℝ) * Sy.card := by ring
    rw [e3]
    linarith [hgloss, homit, hlist]
  · intro pq hpq
    obtain ⟨hpΓ, h1, h2, h3, hg⟩ := hΓr pq hpq
    obtain ⟨hirr, hdim⟩ := (hmass i₀).1 (Z pq) (hchartImg pq hpq)
    refine ⟨hirr, hdim, ?_, ?_⟩
    · apply common_image_subvariety_envelope i₀ Γ Lg (Z pq)
      intro G hG hv
      exact hgimg pq hg G ⟨hG, hv⟩
    · exact common_label_mem_product_image i₀ _ _ pq.1 pq.2
        (hown _ (Or.inl (hWx h1)))
        (hown _ (Or.inr (hWy h2))) (hchart pq hpΓ)
  · intro Γ'' hΓ''
    have hsubW : Γ'' ⊆ W.sources i ×ˢ W.targets i := by
      intro pq hpq
      obtain ⟨_, h1, h2, _, _⟩ := hΓr pq (hΓ'' hpq)
      exact Finset.mem_product.mpr ⟨h1, h2⟩
    have hb := (hmass i₀).2 Γ'' hsubW (fun pq hpq => (hΓr pq (hΓ'' hpq)).2.2.2.1)
      (fun pq hpq => hchart pq (hΓr pq (hΓ'' hpq)).1) (Γ''.image Z)
    have hfilt : Γ''.filter (fun pq =>
        commonProductImage i₀ (W.owner i pq.1) (W.owner i pq.2) ∈ Γ''.image Z) = Γ'' := by
      apply Finset.filter_true_of_mem
      intro pq hpq
      exact Finset.mem_image_of_mem Z hpq
    rw [hfilt] at hb
    have hdegJ : (∑ Z' ∈ (commonChartImages W L i i₀).filter (fun Z' => Z' ∈ Γ''.image Z),
        (Z'.degree : ℝ)) ≤ ((AffineFamily.degree (Γ''.image Z) : ℚ) : ℝ) := by
      rw [AffineFamily.degree, Rat.cast_sum]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro Z' hZ'
        exact (Finset.mem_filter.mp hZ').2
      · intro Z' hZ' _
        obtain ⟨pq, hpq, rfl⟩ := Finset.mem_image.mp hZ'
        have hirr := ((hmass i₀).1 (Z pq) (hchartImg pq (hΓ'' hpq))).1
        have := AffineVariety.one_le_degree (Z pq) hirr.ne_top
        exact_mod_cast (show (0 : ℚ) ≤ (Z pq).degree by linarith)
    have hdeg0 : (0 : ℝ) ≤ ((AffineFamily.degree (Γ''.image Z) : ℚ) : ℝ) := by
      rw [AffineFamily.degree, Rat.cast_sum]
      apply Finset.sum_nonneg
      intro Z' hZ'
      obtain ⟨pq, hpq, rfl⟩ := Finset.mem_image.mp hZ'
      have hirr := ((hmass i₀).1 (Z pq) (hchartImg pq (hΓ'' hpq))).1
      have := AffineVariety.one_le_degree (Z pq) hirr.ne_top
      exact_mod_cast (show (0 : ℚ) ≤ (Z pq).degree by linarith)
    have hlower : commonEqualDimLower M i j = (commonCarrierScale M (j + 1) i) ^ 2 := by
      unfold commonEqualDimLower commonCarrierScale
      rw [if_neg (show ¬ j = 0 by omega)]
    have he : 0 < commonCarrierScale M (j + 1) i := by
      unfold commonCarrierScale TrackD.eScale
      apply Finset.prod_pos
      intro a _
      unfold TrackD.cutScale TrackD.testDeg
      exact mul_pos (regime.B_pos i) (Real.exp_pos _)
    rw [hlower]
    set e := commonCarrierScale M (j + 1) i
    have hexp : Real.exp (-θ * M.s i) * Real.exp (θ * M.s i) = 1 := by
      rw [← Real.exp_add, show -θ * M.s i + θ * M.s i = 0 by ring, Real.exp_zero]
    have hstep : (Γ''.card : ℝ) ≤ Real.exp (θ * M.s i) *
        (((W.sources i).card : ℝ) * (W.targets i).card / e ^ 2) *
        ((AffineFamily.degree (Γ''.image Z) : ℚ) : ℝ) := by
      refine hb.trans (mul_le_mul_of_nonneg_left hdegJ ?_)
      exact mul_nonneg (Real.exp_pos _).le
        (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (sq_nonneg _))
    have he2 : 0 < e ^ 2 := pow_pos he 2
    set w : ℝ := ((W.sources i).card : ℝ) * (W.targets i).card with hwdef
    set D : ℝ := ((AffineFamily.degree (Γ''.image Z) : ℚ) : ℝ) with hDdef
    calc e ^ 2 * Real.exp (-θ * M.s i) * (Γ''.card : ℝ)
        ≤ e ^ 2 * Real.exp (-θ * M.s i) * (Real.exp (θ * M.s i) * (w / e ^ 2) * D) :=
          mul_le_mul_of_nonneg_left hstep (mul_nonneg (sq_nonneg e) (Real.exp_pos _).le)
      _ = (Real.exp (-θ * M.s i) * Real.exp (θ * M.s i)) * w * D * (e ^ 2 / e ^ 2) := by
          ring
      _ = w * D := by rw [hexp, div_self he2.ne']; ring
      _ ≤ (Sx.card : ℝ) * Sy.card * D := mul_le_mul_of_nonneg_right hWcard hdeg0

/-- The first plateau (`k = d-1`, sparse-cones.tex:276–295): union regularity,
deletion of nonreal-flat points, of pairs on one common hyperplane carrier
(generically tangent; proper-flat cap) and product testing. The complete image
of a retained hypersurface pair is `X ×` (the direction chart), of degree
`deg X`, and the source carrier mass budget `n_X ≤ deg X (N/D_1) e^{o(s)}`
gives the `D_1` mass bound. -/
theorem common_label_image_certificate_hypersurface {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (M : CommonPoolProfile T) (hd : 1 < d) (τ : ℝ)
    (hτ : M.b ⟨0, by omega⟩ < τ ∧ τ < M.b ⟨1, hd⟩) :
    ∀ θ : ℝ, 0 < θ → ∀ ρ : ℝ, 0 < ρ → ∀ᶠ i in atTop,
      ∀ (i₀ : Fin d) (Γ : Finset (RPoint d × RPoint d)),
        Γ ⊆ TrackD.poolPts (T.sources i) ×ˢ TrackD.poolPts (T.targets i) →
        (∀ pq ∈ Γ, (TrackD.toC pq.2 - TrackD.toC pq.1) i₀ ≠ 0) →
        ρ * ((TrackD.poolPts (T.sources i)).card : ℝ) *
          (TrackD.poolPts (T.targets i)).card ≤ Γ.card →
        ∃ (Γr : Finset (RPoint d × RPoint d)) (Z : RPoint d × RPoint d → AffineVariety (d + d)),
          CommonImageCertificate M 0 θ ρ i i₀
            ⌊TrackD.testDeg (regime.B i) (M.s i) τ⌋₊ Γ Γr Z := by
  intro θ hθ ρ hρ
  have hd3 := regime.dimension_ge_three
  set β := M.b ⟨0, by omega⟩ with hβdef
  set γ := M.b ⟨1, hd⟩ with hγdef
  have hβ1 : -1 ≤ β := common_profile_time_lower M _
  have hplat : ∀ t : ℝ, β < t → t < γ →
      TrackD.OnPlateau M.b 1 (min (t - β) (γ - t)) t := by
    intro t ht1 ht2 a
    constructor
    · intro ha
      have hab : M.b a ≤ β := M.sorted (show a ≤ (⟨0, by omega⟩ : Fin d) from
        Nat.lt_succ_iff.mp ha)
      have := min_le_left (t - β) (γ - t)
      linarith
    · intro ha
      have hab : γ ≤ M.b a := M.sorted (show (⟨1, hd⟩ : Fin d) ≤ a from ha)
      have := min_le_right (t - β) (γ - t)
      linarith
  set τph := (β + τ) / 2 with hτphdef
  have hτph1 : β < τph := by rw [hτphdef]; linarith [hτ.1]
  have hτph2 : τph < γ := by rw [hτphdef]; linarith [hτ.1, hτ.2]
  obtain ⟨W⟩ := selected_common_physical_retention T M 1 hd τph
    (min (τph - β) (γ - τph)) (by linarith) (lt_min (by linarith) (by linarith))
    (hplat τph hτph1 hτph2)
  have hρ6 : 0 < ρ / 6 := by positivity
  have htest := common_graph_complete_images T M 1 hd τph W τ
    (min (τ - β) (γ - τ)) (by linarith [hτ.1]) (lt_min (by linarith [hτ.1]) (by linarith [hτ.2]))
    (hplat τ hτ.1 hτ.2) (ρ / 6) hρ6 1 le_rfl
  have hBlarge : ∀ᶠ i in atTop, (12 / ρ) ^ 4 ≤ regime.B i :=
    regime.B_tendsto.eventually_ge_atTop _
  filter_upwards [htest, common_retained_pair_omissions W (ρ / 6) hρ6,
    wide_regime_flat_cap regime, common_retained_mass_lower W (1 / 12) (by norm_num),
    selected_common_carrier_budgets W (by omega) θ hθ, hBlarge]
    with i hpt homit hcap hmassLow hbud hBi
  intro i₀ Γ hΓ hchart hdense
  have hB : TrackD.cfgB (regime.P i) = regime.B i := by
    simp [TrackD.cfgB, Regime.B, Regime.N]
  have hN : TrackD.cfgN (regime.P i) = regime.N i := by
    simp [TrackD.cfgN, Regime.N]
  obtain ⟨hpureX, hpureY, hSX, hTY, _⟩ := common_retained_carrier_structure W (by omega) i
  obtain ⟨Lp, _, hLloss, hLtr⟩ := TrackD.generic_depth_transverse_pruning (regime.P i)
    (1 / 3) hcap (d - 1) (d - 1) (by omega) (by omega) (W.sourceCarriers i)
    (W.targetCarriers i) (W.sourceAssigned i) (W.targetAssigned i)
    (fun X hX => hpureX X hX) (fun Y hY => hpureY Y hY) hSX hTY
  set Lg := ⌊TrackD.testDeg (regime.B i) (M.s i) τ⌋₊ with hLgdef
  let 𝒢 : Set (TrackD.PairPoly d) := {G | G.totalDegree ≤ Lg ∧ ∀ pq ∈ Γ,
    MvPolynomial.eval (TrackD.labelPt i₀ (TrackD.toC pq.1) (TrackD.toC pq.2)) G = 0}
  have htd0 : 0 ≤ TrackD.testDeg (regime.B i) (M.s i) τ := by
    unfold TrackD.testDeg; exact (mul_pos (regime.B_pos i) (Real.exp_pos _)).le
  obtain ⟨hgsub, hgloss, hgimg⟩ := hpt i₀ 𝒢 (by
      intro G hG
      rw [hB, one_mul]
      exact (Nat.cast_le.mpr hG.1).trans (Nat.floor_le htd0))
    Γ hΓ (fun pq hpq => ⟨hchart pq hpq, fun G hG => hG.2 pq hpq⟩)
  set good := commonImageGoodGraph i₀ Γ 𝒢 (W.owner i) with hgooddef
  let Γr := good.filter (fun pq => pq.1 ∈ W.sources i ∧ pq.2 ∈ W.targets i ∧
    W.owner i pq.2 ∈ Lp (W.owner i pq.1))
  let Z : RPoint d × RPoint d → AffineVariety (d + d) :=
    fun pq => commonLabelCylinder i₀ (W.owner i pq.1)
  set Sx := TrackD.poolPts (T.sources i) with hSxdef
  set Sy := TrackD.poolPts (T.targets i) with hSydef
  have hWx : W.sources i ⊆ Sx := Finset.filter_subset _ _
  have hWy : W.targets i ⊆ Sy := Finset.filter_subset _ _
  have hWxS : ((W.sources i).card : ℝ) ≤ Sx.card := by
    exact_mod_cast Finset.card_le_card hWx
  have hWyS : ((W.targets i).card : ℝ) ≤ Sy.card := by
    exact_mod_cast Finset.card_le_card hWy
  have hWcard : ((W.sources i).card : ℝ) * (W.targets i).card ≤ (Sx.card : ℝ) * Sy.card :=
    mul_le_mul hWxS hWyS (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hown : ∀ x, x ∈ Sx ∨ x ∈ Sy → TrackD.toC x ∈ W.owner i x := by
    intro x hx
    have hx' : ∃ X ∈ T.sources i ∪ T.targets i, x ∈ X.pts := by
      rcases hx with hx | hx
      · rw [hSxdef, TrackD.poolPts, Finset.mem_biUnion] at hx
        obtain ⟨X, hX, h⟩ := hx
        exact ⟨X, Finset.mem_union_left _ hX, h⟩
      · rw [hSydef, TrackD.poolPts, Finset.mem_biUnion] at hx
        obtain ⟨X, hX, h⟩ := hx
        exact ⟨X, Finset.mem_union_right _ hX, h⟩
    obtain ⟨X, hX, hxX⟩ := hx'
    exact (W.supported i X hX x hxX).2
  have hΓr : ∀ pq ∈ Γr, pq ∈ Γ ∧ pq.1 ∈ W.sources i ∧ pq.2 ∈ W.targets i ∧
      W.owner i pq.2 ∈ Lp (W.owner i pq.1) ∧ pq ∈ good := by
    intro pq hpq
    obtain ⟨hg, h1, h2, h3⟩ := Finset.mem_filter.mp hpq
    exact ⟨hgsub hg, h1, h2, h3, hg⟩
  -- the complete image of a retained pair is the label cylinder of its source owner
  have himage : ∀ pq ∈ Γr,
      commonProductImage i₀ (W.owner i pq.1) (W.owner i pq.2) = Z pq ∧
      (W.owner i pq.1).IsIrreducible ∧ (W.owner i pq.1).dimension = d - 1 ∧
      W.owner i pq.1 ∈ W.sourceCarriers i := by
    intro pq hpq
    obtain ⟨hpΓ, h1, h2, h3, _⟩ := hΓr pq hpq
    set X := W.owner i pq.1 with hXdef
    set Y := W.owner i pq.2 with hYdef
    have hXmem : X ∈ W.sourceCarriers i := Finset.mem_image_of_mem _ h1
    have hYmem : Y ∈ W.targetCarriers i := Finset.mem_image_of_mem _ h2
    obtain ⟨hXirr, hXdim⟩ := hpureX X hXmem
    obtain ⟨hYirr, hYdim⟩ := hpureY Y hYmem
    have hp : TrackD.toC pq.1 ∈ X := hown _ (Or.inl (hWx h1))
    have hq : TrackD.toC pq.2 ∈ Y := hown _ (Or.inr (hWy h2))
    have htr := (hLtr X hXmem Y h3).mono (fun x _ y _ h => h.2)
    obtain ⟨hZirr, hZdim⟩ := common_product_image_geometry i₀ X Y hXirr hYirr
      ⟨_, hp, _, hq, hchart pq hpΓ⟩ htr
    obtain ⟨hCirr, hCdim, _, hCpts, _⟩ := common_label_cylinder i₀ X hXirr
    have hsub : (commonProductImage i₀ X Y).Subvariety (commonLabelCylinder i₀ X) := by
      intro f hf
      let G : TrackD.PairPoly d := MvPolynomial.rename finSumFinEquiv.symm f
      have hG : commonPairEquation G = f := by
        simp only [commonPairEquation, G, MvPolynomial.rename_rename]
        simp
      rw [← hG]
      apply (common_product_image_equation_iff i₀ X Y G).mpr
      intro x hx y hy hi
      have hpt : TrackD.productPoint x (TrackD.dirChart (LinearMap.proj i₀) (y - x)) ∈
          commonLabelCylinder i₀ X := by
        rw [hCpts]
        refine ⟨hx, ?_⟩
        simp only [TrackD.dirChart, LinearMap.proj_apply, Pi.smul_apply, smul_eq_mul]
        exact inv_mul_cancel₀ hi
      have h0 : MvPolynomial.eval
          (TrackD.productPoint x (TrackD.dirChart (LinearMap.proj i₀) (y - x))) f = 0 := hpt f hf
      have heq : TrackD.labelPt i₀ x y ∘ finSumFinEquiv.symm =
          TrackD.productPoint x (TrackD.dirChart (LinearMap.proj i₀) (y - x)) := by
        funext k
        simp only [TrackD.productPoint, TrackD.labelPt, TrackD.dirChart, LinearMap.proj_apply,
          Function.comp_apply]
      simp only [G, MvPolynomial.eval_rename, heq]
      exact h0
    refine ⟨TrackD.irreducible_subvariety_eq_of_pos_dimension_eq _ _ hZirr hCirr hsub
      (by rw [hCdim]; omega) (by rw [hZdim, hCdim, hXdim, hYdim]), hXirr, hXdim, hXmem⟩
  refine ⟨Γr, Z, fun pq hpq => (hΓr pq hpq).1, ?_, ?_, ?_⟩
  · -- the three deletions
    have hsubd : Γ \ Γr ⊆ (Γ \ good) ∪
        (((Sx ×ˢ Sy) \ (W.sources i ×ˢ W.targets i)) ∪
          ((W.sources i ×ˢ W.targets i).filter (fun pq =>
            W.owner i pq.2 ∉ Lp (W.owner i pq.1)))) := by
      intro pq hpq
      obtain ⟨hpΓ, hnot⟩ := Finset.mem_sdiff.mp hpq
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_product, Finset.mem_filter]
      by_cases hg : pq ∈ good
      · by_cases hw : pq.1 ∈ W.sources i ∧ pq.2 ∈ W.targets i
        · right; right
          refine ⟨hw, fun hl => hnot ?_⟩
          exact Finset.mem_filter.mpr ⟨hg, hw.1, hw.2, hl⟩
        · right; left
          exact ⟨Finset.mem_product.mp (hΓ hpΓ), hw⟩
      · left; exact ⟨hpΓ, hg⟩
    have hc := (Finset.card_le_card hsubd).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_left (Finset.card_union_le _ _) _))
    have hc' := (Nat.cast_le (α := ℝ)).mpr hc
    push_cast at hc'
    -- the transverse pruning loss
    have hout := common_pairs_outside_lists_card W Lp i
    have hmassX := common_owner_family_mass (W.sources i) (W.owner i)
    have hmassY := common_owner_family_mass (W.targets i) (W.owner i)
    have hLloss' : commonDiscardedProductMass W Lp i ≤
        regime.N i * regime.B i ^ (-(1 / 3 : ℝ)) *
          (((W.sources i).card : ℝ) + (W.targets i).card) := by
      have h := hLloss
      rw [hB, hN] at h
      unfold commonDiscardedProductMass
      have e1 : TrackD.famMass (W.sourceCarriers i) (W.sourceAssigned i) =
          ((W.sources i).card : ℝ) := hmassX
      have e2 : TrackD.famMass (W.targetCarriers i) (W.targetAssigned i) =
          ((W.targets i).card : ℝ) := hmassY
      rw [e1, e2] at h
      exact h
    -- scalar comparison: N B^{-1/3} ≤ (ρ/12) N B^{-1/12} ≤ (ρ/12) |S|
    have hNpos := regime.N_pos i
    have hBpos := regime.B_pos i
    have hs := common_pool_width_le_logB M i
    have hlogB : 4 * Real.log (12 / ρ) ≤ Real.log (regime.B i) := by
      have := Real.log_le_log (by positivity) hBi
      rwa [Real.log_pow] at this
    have hrp : regime.B i ^ (-(1 / 3 : ℝ)) = Real.exp (-(1 / 3) * Real.log (regime.B i)) := by
      rw [Real.rpow_def_of_pos hBpos]; ring_nf
    have hkey : regime.N i * regime.B i ^ (-(1 / 3 : ℝ)) ≤
        (ρ / 12) * (regime.N i * Real.exp (-(1 / 12) * M.s i)) := by
      rw [hrp]
      have h1 : Real.exp (-(1 / 3) * Real.log (regime.B i)) ≤
          (ρ / 12) * Real.exp (-(1 / 12) * Real.log (regime.B i)) := by
        have h12 : Real.exp (-(1 / 4) * Real.log (regime.B i)) ≤ ρ / 12 := by
          calc Real.exp (-(1 / 4) * Real.log (regime.B i))
              ≤ Real.exp (-(1 / 4) * (4 * Real.log (12 / ρ))) :=
                Real.exp_le_exp.mpr (by nlinarith)
            _ = ρ / 12 := by
                rw [show -(1 / 4) * (4 * Real.log (12 / ρ)) = -Real.log (12 / ρ) by ring,
                  Real.exp_neg, Real.exp_log (by positivity)]
                field_simp
        calc Real.exp (-(1 / 3) * Real.log (regime.B i))
            = Real.exp (-(1 / 4) * Real.log (regime.B i)) *
                Real.exp (-(1 / 12) * Real.log (regime.B i)) := by
              rw [← Real.exp_add]; ring_nf
          _ ≤ (ρ / 12) * Real.exp (-(1 / 12) * Real.log (regime.B i)) :=
              mul_le_mul_of_nonneg_right h12 (Real.exp_pos _).le
      have h2 : Real.exp (-(1 / 12) * Real.log (regime.B i)) ≤
          Real.exp (-(1 / 12) * M.s i) := Real.exp_le_exp.mpr (by nlinarith)
      calc regime.N i * Real.exp (-(1 / 3) * Real.log (regime.B i))
          ≤ regime.N i * ((ρ / 12) * Real.exp (-(1 / 12) * Real.log (regime.B i))) :=
            mul_le_mul_of_nonneg_left h1 hNpos.le
        _ ≤ regime.N i * ((ρ / 12) * Real.exp (-(1 / 12) * M.s i)) := by gcongr
        _ = _ := by ring
    obtain ⟨hlowX, hlowY⟩ := hmassLow
    have hSxl : regime.N i * Real.exp (-(1 / 12) * M.s i) ≤ Sx.card := hlowX.trans hWxS
    have hSyl : regime.N i * Real.exp (-(1 / 12) * M.s i) ≤ Sy.card := hlowY.trans hWyS
    have hfin : regime.N i * regime.B i ^ (-(1 / 3 : ℝ)) *
        (((W.sources i).card : ℝ) + (W.targets i).card) ≤
        ρ / 6 * (Sx.card : ℝ) * Sy.card := by
      have hρ12 : (0 : ℝ) ≤ ρ / 12 := by linarith
      have a1 : regime.N i * regime.B i ^ (-(1 / 3 : ℝ)) ≤ (ρ / 12) * Sy.card :=
        hkey.trans (mul_le_mul_of_nonneg_left hSyl hρ12)
      have a2 : regime.N i * regime.B i ^ (-(1 / 3 : ℝ)) ≤ (ρ / 12) * Sx.card :=
        hkey.trans (mul_le_mul_of_nonneg_left hSxl hρ12)
      have b1 := mul_le_mul a1 hWxS (Nat.cast_nonneg _)
        (mul_nonneg hρ12 (Nat.cast_nonneg _))
      have b2 := mul_le_mul a2 hWyS (Nat.cast_nonneg _)
        (mul_nonneg hρ12 (Nat.cast_nonneg _))
      calc regime.N i * regime.B i ^ (-(1 / 3 : ℝ)) *
            (((W.sources i).card : ℝ) + (W.targets i).card)
          = regime.N i * regime.B i ^ (-(1 / 3 : ℝ)) * ((W.sources i).card : ℝ) +
            regime.N i * regime.B i ^ (-(1 / 3 : ℝ)) * (W.targets i).card := by ring
        _ ≤ (ρ / 12) * Sy.card * Sx.card + (ρ / 12) * Sx.card * Sy.card := add_le_add b1 b2
        _ = ρ / 6 * (Sx.card : ℝ) * Sy.card := by ring
    have e3 : ρ / 2 * (Sx.card : ℝ) * Sy.card =
        ρ / 6 * (Sx.card : ℝ) * Sy.card + ρ / 6 * (Sx.card : ℝ) * Sy.card +
          ρ / 6 * (Sx.card : ℝ) * Sy.card := by ring
    rw [e3]
    linarith [hgloss, homit, hout, hLloss', hfin]
  · intro pq hpq
    obtain ⟨hpΓ, h1, h2, h3, hg⟩ := hΓr pq hpq
    obtain ⟨hZeq, hXirr, hXdim, _⟩ := himage pq hpq
    obtain ⟨hCirr, hCdim, _, _, _⟩ := common_label_cylinder i₀ (W.owner i pq.1) hXirr
    refine ⟨hCirr, by rw [hCdim, hXdim]; omega, ?_, ?_⟩
    · apply common_image_subvariety_envelope i₀ Γ Lg (Z pq)
      intro G hG hv
      rw [← hZeq]
      exact hgimg pq hg G ⟨hG, hv⟩
    · rw [← hZeq]
      exact common_label_mem_product_image i₀ _ _ pq.1 pq.2
        (hown _ (Or.inl (hWx h1))) (hown _ (Or.inr (hWy h2))) (hchart pq hpΓ)
  · intro Γ'' hΓ''
    set Xs := Γ''.image (fun pq => W.owner i pq.1) with hXsdef
    have hXsC : ∀ X ∈ Xs, X ∈ W.sourceCarriers i ∧ X.IsIrreducible := by
      intro X hX
      obtain ⟨pq, hpq, rfl⟩ := Finset.mem_image.mp hX
      obtain ⟨_, hXirr, _, hXmem⟩ := himage pq (hΓ'' hpq)
      exact ⟨hXmem, hXirr⟩
    have himgZ : Γ''.image Z = Xs.image (commonLabelCylinder i₀) := by
      rw [hXsdef, Finset.image_image]
      rfl
    have hinj : Set.InjOn (commonLabelCylinder i₀) (Xs : Set (AffineVariety d)) := by
      intro X hX X' _ hEq
      exact ((common_label_cylinder i₀ X (hXsC X hX).2).2.2.2.2 X' hEq.symm).symm
    have hdegimg : (∑ X ∈ Xs, (X.degree : ℝ)) ≤
        ((AffineFamily.degree (Γ''.image Z) : ℚ) : ℝ) := by
      rw [himgZ, AffineFamily.degree, Finset.sum_image hinj, Rat.cast_sum]
      apply Finset.sum_le_sum
      intro X hX
      exact_mod_cast (common_label_cylinder i₀ X (hXsC X hX).2).2.2.1
    have hdeg0 : (0 : ℝ) ≤ ∑ X ∈ Xs, (X.degree : ℝ) := by
      apply Finset.sum_nonneg
      intro X hX
      have := AffineVariety.one_le_degree X (hXsC X hX).2.ne_top
      exact_mod_cast (show (0 : ℚ) ≤ X.degree by linarith)
    -- each source fiber of Γ'' lies in the owner fiber times the retained targets
    have hfib : ∀ X ∈ Xs, ((Γ''.filter (fun pq => W.owner i pq.1 = X)).card : ℝ) ≤
        ((W.sourceAssigned i X).card : ℝ) * (W.targets i).card := by
      intro X _
      have hsub : Γ''.filter (fun pq => W.owner i pq.1 = X) ⊆
          W.sourceAssigned i X ×ˢ W.targets i := by
        intro pq hpq
        obtain ⟨hpq, hX⟩ := Finset.mem_filter.mp hpq
        obtain ⟨_, h1, h2, _, _⟩ := hΓr pq (hΓ'' hpq)
        exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨h1, hX⟩, h2⟩
      have := Finset.card_le_card hsub
      rw [Finset.card_product] at this
      exact_mod_cast this
    have hsplit : (Γ''.card : ℝ) = ∑ X ∈ Xs,
        ((Γ''.filter (fun pq => W.owner i pq.1 = X)).card : ℝ) := by
      rw [Finset.card_eq_sum_card_fiberwise (f := fun pq => W.owner i pq.1) (t := Xs)
        (fun pq hpq => Finset.mem_image_of_mem _ hpq)]
      push_cast
      rfl
    set e := commonCarrierScale M 1 i with hedef
    have he : 0 < e := by
      rw [hedef]
      unfold commonCarrierScale TrackD.eScale
      apply Finset.prod_pos
      intro a _
      unfold TrackD.cutScale TrackD.testDeg
      exact mul_pos (regime.B_pos i) (Real.exp_pos _)
    have hlower : commonEqualDimLower M i 0 = e := by
      rw [hedef]
      unfold commonEqualDimLower commonCarrierScale TrackD.eScale
      rw [if_pos (rfl : (0 : ℕ) = 0)]
      have hfilt : (Finset.univ.filter (fun a : Fin d => a.val < 1)) =
          {(⟨0, by omega⟩ : Fin d)} := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro ha; exact Fin.ext (by show a.val = 0; omega)
        · intro ha; rw [ha]; show (0 : ℕ) < 1; omega
      rw [hfilt, Finset.prod_singleton]
    have hbudX := hbud.2.2.1
    have hsum : (Γ''.card : ℝ) ≤ ((W.sources i).card : ℝ) * (W.targets i).card / e *
        Real.exp (θ * M.s i) * ∑ X ∈ Xs, (X.degree : ℝ) := by
      rw [hsplit, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro X hX
      have h1 := hfib X hX
      have h2 := hbudX X (hXsC X hX).1
      calc ((Γ''.filter (fun pq => W.owner i pq.1 = X)).card : ℝ)
          ≤ ((W.sourceAssigned i X).card : ℝ) * (W.targets i).card := h1
        _ ≤ (((W.sources i).card : ℝ) * (X.degree : ℝ) / e * Real.exp (θ * M.s i)) *
              (W.targets i).card := mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg _)
        _ = ((W.sources i).card : ℝ) * (W.targets i).card / e *
              Real.exp (θ * M.s i) * (X.degree : ℝ) := by ring
    rw [hlower]
    have hexp : Real.exp (-θ * M.s i) * Real.exp (θ * M.s i) = 1 := by
      rw [← Real.exp_add, show -θ * M.s i + θ * M.s i = 0 by ring, Real.exp_zero]
    set w : ℝ := ((W.sources i).card : ℝ) * (W.targets i).card with hwdef
    set Dg : ℝ := ∑ X ∈ Xs, (X.degree : ℝ) with hDgdef
    calc e * Real.exp (-θ * M.s i) * (Γ''.card : ℝ)
        ≤ e * Real.exp (-θ * M.s i) * (w / e * Real.exp (θ * M.s i) * Dg) :=
          mul_le_mul_of_nonneg_left hsum (mul_nonneg he.le (Real.exp_pos _).le)
      _ = (Real.exp (-θ * M.s i) * Real.exp (θ * M.s i)) * w * Dg * (e / e) := by ring
      _ = w * Dg := by rw [hexp, div_self he.ne']; ring
      _ ≤ (Sx.card : ℝ) * Sy.card * Dg := mul_le_mul_of_nonneg_right hWcard hdeg0
      _ ≤ (Sx.card : ℝ) * Sy.card * ((AffineFamily.degree (Γ''.image Z) : ℚ) : ℝ) :=
          mul_le_mul_of_nonneg_left hdegimg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

/-- sc:common-rank.group: some envelope dimension group carries a dense
portion of every later dense graph, with the equal-dimension degree bound. -/
theorem common_label_dense_group {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (M : CommonPoolProfile T)
    (j : ℕ) (hj : j + 1 < d) (τ : ℝ)
    (hτ : M.b ⟨j, by omega⟩ < τ ∧ τ < M.b ⟨j + 1, hj⟩) :
    ∀ θ : ℝ, 0 < θ → ∀ ρ : ℝ, 0 < ρ → ∀ᶠ i in atTop,
      ∀ (i₀ : Fin d) (Γ : Finset (RPoint d × RPoint d)),
        Γ ⊆ TrackD.poolPts (T.sources i) ×ˢ TrackD.poolPts (T.targets i) →
        (∀ pq ∈ Γ, (TrackD.toC pq.2 - TrackD.toC pq.1) i₀ ≠ 0) →
        ρ * ((TrackD.poolPts (T.sources i)).card : ℝ) *
          (TrackD.poolPts (T.targets i)).card ≤ Γ.card →
        ∃ h : ℕ, 2 * (d - (j + 1)) ≤ h ∧ h ≤ 2 * d ∧
          ∃ Γ' : Finset (RPoint d × RPoint d), Γ' ⊆ Γ ∧
            (ρ / (2 * (2 * d + 1 : ℝ))) * ((TrackD.poolPts (T.sources i)).card : ℝ) *
              (TrackD.poolPts (T.targets i)).card ≤ Γ'.card ∧
            commonLabelPoints i₀ Γ' ⊆
              (AffineFamily.locus (commonLabelGroup i₀ Γ
                ⌊TrackD.testDeg (regime.B i) (M.s i) τ⌋₊ h)).points ∧
            (h = 2 * (d - (j + 1)) →
              commonEqualDimLower M i j * Real.exp (-θ * M.s i) ≤
                ((AffineFamily.degree (commonLabelGroup i₀ Γ
                  ⌊TrackD.testDeg (regime.B i) (M.s i) τ⌋₊ h) : ℚ) : ℝ)) := by
  intro θ hθ ρ hρ
  have hcert : ∀ᶠ i in atTop,
      ∀ (i₀ : Fin d) (Γ : Finset (RPoint d × RPoint d)),
        Γ ⊆ TrackD.poolPts (T.sources i) ×ˢ TrackD.poolPts (T.targets i) →
        (∀ pq ∈ Γ, (TrackD.toC pq.2 - TrackD.toC pq.1) i₀ ≠ 0) →
        ρ * ((TrackD.poolPts (T.sources i)).card : ℝ) *
          (TrackD.poolPts (T.targets i)).card ≤ Γ.card →
        ∃ (Γr : Finset (RPoint d × RPoint d)) (Z : RPoint d × RPoint d → AffineVariety (d + d)),
          CommonImageCertificate M j (θ / 2) ρ i i₀
            ⌊TrackD.testDeg (regime.B i) (M.s i) τ⌋₊ Γ Γr Z := by
    rcases Nat.eq_zero_or_pos j with hj0 | hj1
    · subst hj0
      exact common_label_image_certificate_hypersurface T M hj τ hτ (θ / 2) (by positivity) ρ hρ
    · exact common_label_image_certificate_retained T M j hj hj1 τ hτ (θ / 2)
        (by positivity) ρ hρ
  set ρ' : ℝ := ρ / (2 * (2 * d + 1 : ℝ)) with hρ'def
  have hρ' : 0 < ρ' := by positivity
  filter_upwards [hcert, M.width_grows.eventually_ge_atTop ((2 / θ) * Real.log (1 / ρ'))]
    with i hi hs
  intro i₀ Γ hΓ hchart hdense
  obtain ⟨Γr, Z, hZ⟩ := hi i₀ Γ hΓ hchart hdense
  obtain ⟨h, hh1, hh2, Γ', hΓ', hdense', hlabels, hdeg⟩ :=
    common_label_dense_group_of_certificate M j hj (θ / 2) ρ hρ i i₀ _ Γ Γr Z hZ hdense
  refine ⟨h, hh1, hh2, Γ', hΓ', hdense', hlabels, fun heq => ?_⟩
  have hdeg' := hdeg heq
  have hexp : Real.exp (-(θ / 2) * M.s i) ≤ ρ' := by
    calc Real.exp (-(θ / 2) * M.s i)
        ≤ Real.exp (-(θ / 2) * ((2 / θ) * Real.log (1 / ρ'))) := by
          apply Real.exp_le_exp.mpr
          have : 0 < θ / 2 := by positivity
          nlinarith
      _ = ρ' := by
          rw [show -(θ / 2) * ((2 / θ) * Real.log (1 / ρ')) = -Real.log (1 / ρ') by
            field_simp]
          rw [Real.exp_neg, Real.exp_log (by positivity)]
          simp
  have hlower : 0 ≤ commonEqualDimLower M i j := by
    unfold commonEqualDimLower
    split_ifs
    · unfold TrackD.cutScale TrackD.testDeg
      exact (mul_pos (regime.B_pos i) (Real.exp_pos _)).le
    · exact sq_nonneg _
  calc commonEqualDimLower M i j * Real.exp (-θ * M.s i)
      = commonEqualDimLower M i j * Real.exp (-(θ / 2) * M.s i) *
          Real.exp (-(θ / 2) * M.s i) := by
        rw [mul_assoc, ← Real.exp_add]; ring_nf
    _ ≤ commonEqualDimLower M i j * Real.exp (-(θ / 2) * M.s i) * ρ' := by
        apply mul_le_mul_of_nonneg_left hexp
        exact mul_nonneg hlower (Real.exp_pos _).le
    _ ≤ _ := hdeg'

end
end DistinctDistances.SparseCones
