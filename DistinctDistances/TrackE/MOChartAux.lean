import DistinctDistances.TrackE.CommonImageData
import DistinctDistances.TrackE.CommonImageMassData
import DistinctDistances.TrackE.CommonCarrierData
import DistinctDistances.TrackE.MODegAux
import DistinctDistances.TrackA.PoolingSupport

/-! Helpers for `outer_chart_restriction` degree bound.

`mo_chart_family_degree_le` is the elementary assembly: per-pair bound +
`pooling_degree_biUnion` + `selected_common_carrier_budgets` counting. It takes the
per-pair bound as an explicit hypothesis. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- Sum over distinct images is bounded by the sum with multiplicity
(nonnegative degrees, each distinct value occurs at least once). -/
theorem mo_chart_image_sum_le {n m : ℕ} (F : AffineFamily.Family n)
    (f : AffineVariety n → AffineVariety m)
    (hdeg : ∀ Z ∈ F.image f, (0 : ℝ) ≤ (Z.degree : ℝ)) :
    (∑ Z ∈ F.image f, (Z.degree : ℝ)) ≤ ∑ Y ∈ F, ((f Y).degree : ℝ) := by
  classical
  by_cases hF : F.Nonempty
  · -- choose one preimage per distinct value via a total choice function
    have hchoice : ∀ Z ∈ F.image f, ∃ Y ∈ F, f Y = Z := by
      intro Z hZ
      exact Finset.mem_image.mp hZ
    choose g hgmem hgimg using hchoice
    -- totalize to a plain function (junk outside the image)
    let g0 : AffineVariety m → AffineVariety n := fun Z =>
      if h : Z ∈ F.image f then g Z h else AffineVariety.empty
    have hg0mem : ∀ Z ∈ F.image f, g0 Z ∈ F := by
      intro Z hZ
      simp only [g0, dif_pos hZ]
      exact hgmem _ hZ
    have hg0img : ∀ Z ∈ F.image f, f (g0 Z) = Z := by
      intro Z hZ
      simp only [g0, dif_pos hZ]
      exact hgimg _ hZ
    have hg0_inj : Set.InjOn g0 (↑(F.image f) : Set (AffineVariety m)) := by
      intro a ha b hb hab
      have ha' : a ∈ F.image f := ha
      have hb' : b ∈ F.image f := hb
      have heq : a = b := by
        calc a = f (g0 a) := (hg0img a ha').symm
          _ = f (g0 b) := by rw [hab]
          _ = b := hg0img b hb'
      exact heq
    have hnn : ∀ Y ∈ F, (0 : ℝ) ≤ ((f Y).degree : ℝ) := by
      intro Y hY
      exact hdeg _ (Finset.mem_image.mpr ⟨Y, hY, rfl⟩)
    have h1 : ∑ Z ∈ F.image f, (Z.degree : ℝ)
        = ∑ Z ∈ F.image f, ((f (g0 Z)).degree : ℝ) := by
      apply Finset.sum_congr rfl
      intro Z hZ
      rw [hg0img Z hZ]
    have h2 : ∑ Z ∈ F.image f, ((f (g0 Z)).degree : ℝ)
        = ∑ Y ∈ (F.image f).image g0, ((f Y).degree : ℝ) := by
      rw [Finset.sum_image (fun a ha b hb hab => hg0_inj ha hb hab)]
    have h3 : (F.image f).image g0 ⊆ F := by
      intro Y hY
      obtain ⟨Z, hZ, rfl⟩ := Finset.mem_image.mp hY
      exact hg0mem Z hZ
    rw [h1, h2]
    exact Finset.sum_le_sum_of_subset_of_nonneg h3 (fun Y _ _ => hnn Y ‹_›)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hF]
    simp only [Finset.image_empty, Finset.sum_empty, le_refl]

/-- Family degree bound from a per-pair bound (the per-pair bound is
an explicit hypothesis, supplied by `mo_chart_product_image_degree_const_full`).

`W` lives at index `jW` with `d - jW = k`; `L` has tolerance `ε/2`; budgets are
consumed at `ε/4`; the fixed constant `C` is absorbed by `hCabsorb`
(`C <= exp(ε s/2)`, from `s -> oo`); the `(1+ρ)` slack is trivial since `ρ > 0`. -/
theorem mo_chart_family_degree_le
    {F : ConeCoverageSequence regime} {T : SelectedProfileSequence F}
    {M : CommonPoolProfile T} {jW : ℕ} {τ ε : ℝ}
    (W : CommonPhysicalSequence T M jW τ) (L : CommonProductLists W (ε / 2))
    (k : ℕ) (hk : 1 ≤ k) (hkdim : d - jW = k) (hjW : jW ≤ d)
    (i : ℕ) (i₀ : Fin d) (ρ : ℝ) (hρ : 0 < ρ) (hε : 0 < ε)
    (C : ℝ) (hC : 0 < C)
    (hpair : ∀ X ∈ W.sourceCarriers i, ∀ Y ∈ L.lists i X,
      X.IsIrreducible → X.dimension = k → Y.IsIrreducible → Y.dimension = k →
      (∃ x ∈ X, ∃ y ∈ Y, (y - x) i₀ ≠ 0) →
      ((commonProductImage i₀ X Y).degree : ℝ) ≤
        C * (X.degree : ℝ) * (Y.degree : ℝ))
    (hbudgets : CommonCarrierBudgets W i (ε / 4))
    (hpure : AffineFamily.IsPure (commonChartImages W L i i₀) (2 * k))
    (hCabsorb : C ≤ Real.exp ((ε / 2) * M.s i)) :
    ((AffineFamily.degree (commonChartImages W L i i₀) : ℚ) : ℝ) ≤
      (1 + ρ) * (commonCarrierScale M jW i) ^ 2 * Real.exp (ε * M.s i) := by
  classical
  have hstruct := common_retained_carrier_structure W hjW i
  have hdim_eq : d - jW = k := hkdim
  -- carrier purity rewritten at k
  have hsrc_pure : ∀ X ∈ W.sourceCarriers i, X.IsIrreducible ∧ X.dimension = k := by
    intro X hX
    have h := hstruct.1 X hX
    exact ⟨h.1, by omega⟩
  have htgt_pure : ∀ Y ∈ W.targetCarriers i, Y.IsIrreducible ∧ Y.dimension = k := by
    intro Y hY
    have h := hstruct.2.1 Y hY
    exact ⟨h.1, by omega⟩
  -- per-image families are subfamilies of U, hence pure
  have hsub_img : ∀ X ∈ W.sourceCarriers i,
      (commonChartTargets W L i i₀ X).image (commonProductImage i₀ X) ⊆
        commonChartImages W L i i₀ := by
    intro X hX
    intro Z hZ
    simp only [commonChartImages, Finset.mem_biUnion]
    obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hZ
    exact ⟨X, hX, Finset.mem_image.mpr ⟨Y, hY, rfl⟩⟩
  have hpure_img : ∀ X ∈ W.sourceCarriers i,
      AffineFamily.IsPure ((commonChartTargets W L i i₀ X).image (commonProductImage i₀ X)) (2 * k) := by
    intro X hX Z hZ
    exact hpure Z (hsub_img X hX hZ)
  -- step 1: degree(U) <= sum_X degree(image_X)
  have hstep1 : ((AffineFamily.degree (commonChartImages W L i i₀) : ℚ) : ℝ) ≤
      ∑ X ∈ W.sourceCarriers i,
        ((AffineFamily.degree ((commonChartTargets W L i i₀ X).image (commonProductImage i₀ X)) : ℚ) : ℝ) := by
    have hle : AffineFamily.degree (commonChartImages W L i i₀) ≤
        ∑ X ∈ W.sourceCarriers i,
          AffineFamily.degree ((commonChartTargets W L i i₀ X).image (commonProductImage i₀ X)) := by
      have hunfold : commonChartImages W L i i₀ =
          (W.sourceCarriers i).biUnion (fun X => (commonChartTargets W L i i₀ X).image (commonProductImage i₀ X)) := rfl
      rw [hunfold]
      exact TrackA.pooling_degree_biUnion _ _ _ hpure_img
    have hcast : (((AffineFamily.degree (commonChartImages W L i i₀) : ℚ)) : ℝ) ≤
        (((∑ X ∈ W.sourceCarriers i,
          AffineFamily.degree ((commonChartTargets W L i i₀ X).image (commonProductImage i₀ X)) : ℚ)) : ℝ) := by
      exact_mod_cast hle
    rwa [Rat.cast_sum] at hcast
  -- nonnegativity of image degrees
  have himg_nn : ∀ X ∈ W.sourceCarriers i, ∀ Z ∈
      (commonChartTargets W L i i₀ X).image (commonProductImage i₀ X),
      (0 : ℝ) ≤ (Z.degree : ℝ) := by
    intro X hX Z hZ
    have h := hpure_img X hX Z hZ
    have h1 : (1 : ℚ) ≤ Z.degree := AffineVariety.one_le_degree Z h.1.ne_top
    exact_mod_cast le_trans (by norm_num : (0 : ℚ) ≤ 1) h1
  -- step 2: per-source image degree <= C * degX * sum_{chartTargets} degY
  have hstep2 : ∀ X ∈ W.sourceCarriers i,
      ((AffineFamily.degree ((commonChartTargets W L i i₀ X).image (commonProductImage i₀ X)) : ℚ) : ℝ) ≤
        C * (X.degree : ℝ) * ∑ Y ∈ commonChartTargets W L i i₀ X, (Y.degree : ℝ) := by
    intro X hX
    have hXpure := hsrc_pure X hX
    -- chart targets sit in lists and in target carriers
    have hCTsub : commonChartTargets W L i i₀ X ⊆ L.lists i X := Finset.filter_subset _ _
    have hCTtgt : ∀ Y ∈ commonChartTargets W L i i₀ X, Y ∈ W.targetCarriers i := by
      intro Y hY
      exact L.subset i X hX (hCTsub hY)
    -- per-pair bounds at each Y
    have hYle : ∀ Y ∈ commonChartTargets W L i i₀ X,
        ((commonProductImage i₀ X Y).degree : ℝ) ≤ C * (X.degree : ℝ) * (Y.degree : ℝ) := by
      intro Y hY
      have hYlist : Y ∈ L.lists i X := hCTsub hY
      have hYpure := htgt_pure Y (hCTtgt Y hY)
      have hchart : ∃ x ∈ X, ∃ y ∈ Y, (y - x) i₀ ≠ 0 := by
        have hmem : Y ∈ commonChartTargets W L i i₀ X := hY
        simp only [commonChartTargets, Finset.mem_filter] at hmem
        exact hmem.2
      exact hpair X hX Y hYlist hXpure.1 hXpure.2 hYpure.1 hYpure.2 hchart
    calc ((AffineFamily.degree ((commonChartTargets W L i i₀ X).image (commonProductImage i₀ X)) : ℚ) : ℝ)
        = ∑ Z ∈ (commonChartTargets W L i i₀ X).image (commonProductImage i₀ X), (Z.degree : ℝ) := by
          rw [AffineFamily.degree, Rat.cast_sum]
      _ ≤ ∑ Y ∈ commonChartTargets W L i i₀ X, ((commonProductImage i₀ X Y).degree : ℝ) :=
          mo_chart_image_sum_le _ _ (fun Z hZ => himg_nn X hX Z hZ)
      _ ≤ ∑ Y ∈ commonChartTargets W L i i₀ X, C * (X.degree : ℝ) * (Y.degree : ℝ) :=
          Finset.sum_le_sum hYle
      _ = C * (X.degree : ℝ) * ∑ Y ∈ commonChartTargets W L i i₀ X, (Y.degree : ℝ) := by
          rw [Finset.mul_sum]
  -- step 3: chart-target degree sums <= target-carrier sum (subset + nonneg)
  have htgt_nn : ∀ Y ∈ W.targetCarriers i, (0 : ℝ) ≤ (Y.degree : ℝ) := by
    intro Y hY
    have h := htgt_pure Y hY
    have h1 : (1 : ℚ) ≤ Y.degree := AffineVariety.one_le_degree Y h.1.ne_top
    exact_mod_cast le_trans (by norm_num : (0 : ℚ) ≤ 1) h1
  have hsrc_nn : ∀ X ∈ W.sourceCarriers i, (0 : ℝ) ≤ (X.degree : ℝ) := by
    intro X hX
    have h := hsrc_pure X hX
    have h1 : (1 : ℚ) ≤ X.degree := AffineVariety.one_le_degree X h.1.ne_top
    exact_mod_cast le_trans (by norm_num : (0 : ℚ) ≤ 1) h1
  have hCT_sum_le : ∀ X ∈ W.sourceCarriers i,
      ∑ Y ∈ commonChartTargets W L i i₀ X, (Y.degree : ℝ) ≤
        ∑ Y ∈ W.targetCarriers i, (Y.degree : ℝ) := by
    intro X hX
    have hsub : commonChartTargets W L i i₀ X ⊆ W.targetCarriers i := by
      intro Y hY
      exact L.subset i X hX (Finset.filter_subset _ _ hY)
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun Y _ _ => htgt_nn Y ‹_›)
  -- combine over X
  have hcomb : ∑ X ∈ W.sourceCarriers i,
        ((AffineFamily.degree ((commonChartTargets W L i i₀ X).image (commonProductImage i₀ X)) : ℚ) : ℝ) ≤
      C * (∑ X ∈ W.sourceCarriers i, (X.degree : ℝ)) *
        (∑ Y ∈ W.targetCarriers i, (Y.degree : ℝ)) := by
    calc ∑ X ∈ W.sourceCarriers i,
          ((AffineFamily.degree ((commonChartTargets W L i i₀ X).image (commonProductImage i₀ X)) : ℚ) : ℝ)
        ≤ ∑ X ∈ W.sourceCarriers i,
            C * (X.degree : ℝ) * ∑ Y ∈ W.targetCarriers i, (Y.degree : ℝ) := by
          apply Finset.sum_le_sum
          intro X hX
          exact (hstep2 X hX).trans (by
            apply mul_le_mul_of_nonneg_left (hCT_sum_le X hX)
            apply mul_nonneg hC.le (hsrc_nn X hX))
      _ = C * (∑ X ∈ W.sourceCarriers i, (X.degree : ℝ)) *
          (∑ Y ∈ W.targetCarriers i, (Y.degree : ℝ)) := by
          have heq : ∀ X : AffineVariety d, C * (X.degree : ℝ) *
              (∑ Y ∈ W.targetCarriers i, (Y.degree : ℝ))
              = (C * (∑ Y ∈ W.targetCarriers i, (Y.degree : ℝ))) * (X.degree : ℝ) := by
            intro X; ring
          simp_rw [heq, ← Finset.mul_sum]
          ring
  -- carrier budgets at ε/4
  have hSbud := hbudgets.1
  have hTbud := hbudgets.2.1
  have he_pos : 0 < commonCarrierScale M jW i := by
    unfold commonCarrierScale TrackD.eScale TrackD.cutScale TrackD.testDeg
    exact Finset.prod_pos fun _ _ => mul_pos (regime.B_pos i) (Real.exp_pos _)
  -- C * budgets <= (1+ρ) eScale^2 exp(ε s)
  have hexp2 : Real.exp ((ε / 4) * M.s i) * Real.exp ((ε / 4) * M.s i) =
      Real.exp ((ε / 2) * M.s i) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hprod_le : C * (∑ X ∈ W.sourceCarriers i, (X.degree : ℝ)) *
        (∑ Y ∈ W.targetCarriers i, (Y.degree : ℝ)) ≤
      (1 + ρ) * (commonCarrierScale M jW i) ^ 2 * Real.exp (ε * M.s i) := by
    have h1 : (∑ X ∈ W.sourceCarriers i, (X.degree : ℝ)) ≤
        commonCarrierScale M jW i * Real.exp ((ε / 4) * M.s i) := hSbud
    have h2 : (∑ Y ∈ W.targetCarriers i, (Y.degree : ℝ)) ≤
        commonCarrierScale M jW i * Real.exp ((ε / 4) * M.s i) := hTbud
    have hnn1 : 0 ≤ (∑ X ∈ W.sourceCarriers i, (X.degree : ℝ)) :=
      Finset.sum_nonneg fun X hX => hsrc_nn X hX
    have hnn2 : 0 ≤ (∑ Y ∈ W.targetCarriers i, (Y.degree : ℝ)) :=
      Finset.sum_nonneg fun Y hY => htgt_nn Y hY
    have hbase : C * (∑ X ∈ W.sourceCarriers i, (X.degree : ℝ)) *
        (∑ Y ∈ W.targetCarriers i, (Y.degree : ℝ)) ≤
        C * (commonCarrierScale M jW i * Real.exp ((ε / 4) * M.s i)) *
          (commonCarrierScale M jW i * Real.exp ((ε / 4) * M.s i)) := by
      have hCS : C * (∑ X ∈ W.sourceCarriers i, (X.degree : ℝ)) ≤
          C * (commonCarrierScale M jW i * Real.exp ((ε / 4) * M.s i)) :=
        mul_le_mul_of_nonneg_left h1 hC.le
      have hS'nn : 0 ≤ C * (commonCarrierScale M jW i * Real.exp ((ε / 4) * M.s i)) :=
        mul_nonneg hC.le (mul_nonneg he_pos.le (Real.exp_pos _).le)
      exact mul_le_mul hCS h2 hnn2 hS'nn
    have hexp_rw : C * (commonCarrierScale M jW i * Real.exp ((ε / 4) * M.s i)) *
        (commonCarrierScale M jW i * Real.exp ((ε / 4) * M.s i)) =
        (commonCarrierScale M jW i) ^ 2 * (C * Real.exp ((ε / 2) * M.s i)) := by
      rw [← hexp2]
      ring
    have hCexp : C * Real.exp ((ε / 2) * M.s i) ≤
        (1 + ρ) * Real.exp (ε * M.s i) := by
      have hexp_le : Real.exp ((ε / 2) * M.s i) ≤ Real.exp (ε * M.s i) := by
        apply Real.exp_le_exp.mpr
        have hs : 0 ≤ M.s i := (M.width_pos i).le
        have hε2 : ε / 2 ≤ ε := by linarith [hε]
        exact mul_le_mul_of_nonneg_right hε2 hs
      calc C * Real.exp ((ε / 2) * M.s i)
          ≤ Real.exp ((ε / 2) * M.s i) * Real.exp ((ε / 2) * M.s i) := by
            -- C <= exp(ε s/2), multiply by exp(ε s/2) >= 0
            exact mul_le_mul_of_nonneg_right hCabsorb (Real.exp_pos _).le
        _ = Real.exp (ε * M.s i) := by
            rw [← Real.exp_add]
            congr 1
            ring
        _ ≤ (1 + ρ) * Real.exp (ε * M.s i) := by
            apply le_mul_of_one_le_left (Real.exp_pos _).le
            linarith [hρ]
    calc C * (∑ X ∈ W.sourceCarriers i, (X.degree : ℝ)) *
          (∑ Y ∈ W.targetCarriers i, (Y.degree : ℝ))
        ≤ C * (commonCarrierScale M jW i * Real.exp ((ε / 4) * M.s i)) *
            (commonCarrierScale M jW i * Real.exp ((ε / 4) * M.s i)) := hbase
      _ = (commonCarrierScale M jW i) ^ 2 * (C * Real.exp ((ε / 2) * M.s i)) := hexp_rw
      _ ≤ (commonCarrierScale M jW i) ^ 2 * ((1 + ρ) * Real.exp (ε * M.s i)) :=
          mul_le_mul_of_nonneg_left hCexp (sq_nonneg _)
      _ = (1 + ρ) * (commonCarrierScale M jW i) ^ 2 * Real.exp (ε * M.s i) := by ring
  exact hstep1.trans (hcomb.trans hprod_le)

end
end DistinctDistances.SparseCones
