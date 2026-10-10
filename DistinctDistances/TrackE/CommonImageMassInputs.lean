import DistinctDistances.TrackE.CommonImageMassData

/-! Finite owner-fiber and chart inputs to the uniform image-mass bound,
`sc:retained-products.mass`, sparse-cones.tex:143–148, 201–213. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}
variable {F : ConeCoverageSequence regime} {T : SelectedProfileSequence F}
    {M : CommonPoolProfile T} {j : ℕ} {τ ε : ℝ}

theorem mem_common_chart_targets (W : CommonPhysicalSequence T M j τ)
    (L : CommonProductLists W ε) (i : ℕ) (i₀ : Fin d) (X Y : AffineVariety d) :
    Y ∈ commonChartTargets W L i i₀ X ↔
      Y ∈ L.lists i X ∧ ∃ x ∈ X, ∃ y ∈ Y, (y - x) i₀ ≠ 0 := by
  unfold commonChartTargets
  exact Finset.mem_filter

/-- Purity uses every original image and the full original transversality list. -/
theorem common_chart_images_pure (W : CommonPhysicalSequence T M j τ)
    (hj : j ≤ d) (L : CommonProductLists W ε) (i : ℕ) (i₀ : Fin d)
    (htrans : ∀ X ∈ W.sourceCarriers i, ∀ Y ∈ L.lists i X,
      TrackD.ForGeneralPair X Y (fun x y => y - x ∉ Y.tangentSpace y)) :
    AffineFamily.IsPure (commonChartImages W L i i₀) (2 * (d - j)) := by
  classical
  intro V hV
  have hstructure := common_retained_carrier_structure W hj i
  obtain ⟨hsource, htarget, _, _, _⟩ := hstructure
  simp only [commonChartImages, Finset.mem_biUnion] at hV
  obtain ⟨X, hXS, hXV⟩ := hV
  obtain ⟨Y, hYX, hYXV⟩ := Finset.mem_image.mp hXV
  have hYmem := (mem_common_chart_targets W L i i₀ X Y).mp hYX
  obtain ⟨hYlist, x, hxX, y, hyY, hne⟩ := hYmem
  have hXpure := hsource X hXS
  have hYcarrier : Y ∈ W.targetCarriers i := L.subset i X hXS hYlist
  have hYpure := htarget Y hYcarrier
  have htransXY := htrans X hXS Y hYlist
  obtain ⟨hVirr, hVdim⟩ :=
    common_product_image_geometry i₀ X Y hXpure.1 hYpure.1 ⟨x, hxX, y, hyY, hne⟩ htransXY
  subst hYXV
  refine ⟨hVirr, ?_⟩
  rw [hVdim, hXpure.2, hYpure.2]
  omega

/-- Multiply and pool the two original owner-card caps at their actual degrees. -/
theorem common_chart_mass_from_carrier_caps (W : CommonPhysicalSequence T M j τ)
    (L : CommonProductLists W ε) (i : ℕ) (i₀ : Fin d) (η : ℝ)
    (he : 0 < commonCarrierScale M j i) (hbudgets : CommonCarrierBudgets W i η)
    (J : AffineFamily.Family (d + d)) :
    commonChartImageMass W L i i₀ J ≤
      (((W.sources i).card : ℝ) * (W.targets i).card /
        (commonCarrierScale M j i) ^ 2) * Real.exp ((2 * η) * M.s i) *
      (∑ X ∈ W.sourceCarriers i, (X.degree : ℝ) *
        (∑ Y ∈ (commonChartTargets W L i i₀ X).filter
          (fun Y => commonProductImage i₀ X Y ∈ J), (Y.degree : ℝ))) := by
  classical
  have hene : commonCarrierScale M j i ≠ 0 := ne_of_gt he
  have hexp : Real.exp (η * M.s i) * Real.exp (η * M.s i) =
      Real.exp ((2 * η) * M.s i) := by
    rw [← Real.exp_add]
    congr 1
    ring
  -- pointwise fiber-product bound
  have hXY : ∀ X ∈ W.sourceCarriers i,
      ∀ Y ∈ (commonChartTargets W L i i₀ X).filter
        (fun Y => commonProductImage i₀ X Y ∈ J),
      ((W.sourceAssigned i X).card : ℝ) * ((W.targetAssigned i Y).card : ℝ) ≤
        ((((W.sources i).card : ℝ) * (W.targets i).card /
          (commonCarrierScale M j i) ^ 2) * Real.exp ((2 * η) * M.s i)) *
        (X.degree : ℝ) * (Y.degree : ℝ) := by
    intro X hX Y hY
    have hYCT : Y ∈ commonChartTargets W L i i₀ X :=
      (Finset.mem_filter.mp hY).1
    have hYlist : Y ∈ L.lists i X :=
      ((mem_common_chart_targets W L i i₀ X Y).mp hYCT).1
    have hYcarrier : Y ∈ W.targetCarriers i := L.subset i X hX hYlist
    have hSX := hbudgets.2.2.1 X hX
    have hTY := hbudgets.2.2.2 Y hYcarrier
    have ha0 : (0 : ℝ) ≤ ((W.sourceAssigned i X).card : ℝ) := Nat.cast_nonneg _
    have hb0 : (0 : ℝ) ≤ ((W.targetAssigned i Y).card : ℝ) := Nat.cast_nonneg _
    have haR0 : (0 : ℝ) ≤ ((W.sources i).card : ℝ) * (X.degree : ℝ) /
        commonCarrierScale M j i * Real.exp (η * M.s i) :=
      le_trans ha0 hSX
    have hmul := mul_le_mul hSX hTY hb0 haR0
    refine hmul.trans ?_
    -- cap product equals the claimed coefficient times degrees
    have heq : (((W.sources i).card : ℝ) * (X.degree : ℝ) /
          commonCarrierScale M j i * Real.exp (η * M.s i)) *
        (((W.targets i).card : ℝ) * (Y.degree : ℝ) /
          commonCarrierScale M j i * Real.exp (η * M.s i)) =
        ((((W.sources i).card : ℝ) * (W.targets i).card /
          (commonCarrierScale M j i) ^ 2) * Real.exp ((2 * η) * M.s i)) *
        (X.degree : ℝ) * (Y.degree : ℝ) := by
      have h1 : (((W.sources i).card : ℝ) * (X.degree : ℝ) /
            commonCarrierScale M j i * Real.exp (η * M.s i)) *
          (((W.targets i).card : ℝ) * (Y.degree : ℝ) /
            commonCarrierScale M j i * Real.exp (η * M.s i)) =
          (((W.sources i).card : ℝ) * (W.targets i).card /
            (commonCarrierScale M j i) ^ 2) *
          ((X.degree : ℝ) * (Y.degree : ℝ)) *
          (Real.exp (η * M.s i) * Real.exp (η * M.s i)) := by
        field_simp
      rw [h1, hexp]
      ring
    exact heq.le
  -- sum the pointwise bound
  have hle : (∑ X ∈ W.sourceCarriers i, ∑ Y ∈ (commonChartTargets W L i i₀ X).filter
        (fun Y => commonProductImage i₀ X Y ∈ J),
        ((W.sourceAssigned i X).card : ℝ) * ((W.targetAssigned i Y).card : ℝ)) ≤
      (∑ X ∈ W.sourceCarriers i, ∑ Y ∈ (commonChartTargets W L i i₀ X).filter
        (fun Y => commonProductImage i₀ X Y ∈ J),
        ((((W.sources i).card : ℝ) * (W.targets i).card /
          (commonCarrierScale M j i) ^ 2) * Real.exp ((2 * η) * M.s i)) *
        (X.degree : ℝ) * (Y.degree : ℝ)) := by
    apply Finset.sum_le_sum
    intro X hX
    apply Finset.sum_le_sum
    intro Y hY
    exact hXY X hX Y hY
  -- factor the coefficient out of the double sum
  have heq : (∑ X ∈ W.sourceCarriers i, ∑ Y ∈ (commonChartTargets W L i i₀ X).filter
        (fun Y => commonProductImage i₀ X Y ∈ J),
        ((((W.sources i).card : ℝ) * (W.targets i).card /
          (commonCarrierScale M j i) ^ 2) * Real.exp ((2 * η) * M.s i)) *
        (X.degree : ℝ) * (Y.degree : ℝ)) =
      ((((W.sources i).card : ℝ) * (W.targets i).card /
        (commonCarrierScale M j i) ^ 2) * Real.exp ((2 * η) * M.s i)) *
      (∑ X ∈ W.sourceCarriers i, (X.degree : ℝ) *
        (∑ Y ∈ (commonChartTargets W L i i₀ X).filter
          (fun Y => commonProductImage i₀ X Y ∈ J), (Y.degree : ℝ))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro X _
    have hXeq : ((((W.sources i).card : ℝ) * (W.targets i).card /
          (commonCarrierScale M j i) ^ 2) * Real.exp ((2 * η) * M.s i)) *
        ((X.degree : ℝ) *
        (∑ Y ∈ (commonChartTargets W L i i₀ X).filter
          (fun Y => commonProductImage i₀ X Y ∈ J), (Y.degree : ℝ))) =
        ∑ Y ∈ (commonChartTargets W L i i₀ X).filter
          (fun Y => commonProductImage i₀ X Y ∈ J),
        ((((W.sources i).card : ℝ) * (W.targets i).card /
          (commonCarrierScale M j i) ^ 2) * Real.exp ((2 * η) * M.s i)) *
        (X.degree : ℝ) * (Y.degree : ℝ) := by
      have hfactor : ((((W.sources i).card : ℝ) * (W.targets i).card /
            (commonCarrierScale M j i) ^ 2) * Real.exp ((2 * η) * M.s i)) *
          ((X.degree : ℝ) *
          (∑ Y ∈ (commonChartTargets W L i i₀ X).filter
            (fun Y => commonProductImage i₀ X Y ∈ J), (Y.degree : ℝ))) =
          ((((W.sources i).card : ℝ) * (W.targets i).card /
            (commonCarrierScale M j i) ^ 2) * Real.exp ((2 * η) * M.s i) *
          (X.degree : ℝ)) *
          (∑ Y ∈ (commonChartTargets W L i i₀ X).filter
            (fun Y => commonProductImage i₀ X Y ∈ J), (Y.degree : ℝ)) := by
        ring
      rw [hfactor, Finset.mul_sum]
    rw [hXeq]
  simpa only [commonChartImageMass] using hle.trans heq.le

theorem common_two_exp_absorb (ε s : ℝ) (hε : 0 < ε)
    (hs : 4 * Real.log 2 / ε ≤ s) :
    2 * Real.exp ((3 * ε / 4) * s) ≤ Real.exp (ε * s) := by
  have hε4 : (0 : ℝ) < ε / 4 := by positivity
  have hlog : Real.log 2 ≤ (ε / 4) * s := by
    have hmul := mul_le_mul_of_nonneg_right hs hε4.le
    have heq : (4 * Real.log 2 / ε) * (ε / 4) = Real.log 2 := by
      field_simp
    have heq2 : s * (ε / 4) = (ε / 4) * s := by ring
    rw [heq, heq2] at hmul
    exact hmul
  have h2le : (2 : ℝ) ≤ Real.exp ((ε / 4) * s) := by
    have h := Real.exp_le_exp.mpr hlog
    rwa [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
  calc 2 * Real.exp ((3 * ε / 4) * s)
      ≤ Real.exp ((ε / 4) * s) * Real.exp ((3 * ε / 4) * s) :=
        mul_le_mul_of_nonneg_right h2le (Real.exp_pos _).le
    _ = Real.exp (ε * s) := by
        rw [← Real.exp_add]
        congr 1
        ring

/-- An actual retained chart graph is charged to the full original owner fibers. -/
theorem common_chart_graph_card_le_image_mass (W : CommonPhysicalSequence T M j τ)
    (hj : j ≤ d) (L : CommonProductLists W ε) (i : ℕ) (i₀ : Fin d)
    (Γ : Finset (RPoint d × RPoint d)) (hΓ : Γ ⊆ W.sources i ×ˢ W.targets i)
    (hlist : ∀ pq ∈ Γ, W.owner i pq.2 ∈ L.lists i (W.owner i pq.1))
    (hchart : ∀ pq ∈ Γ, (TrackD.toC pq.2 - TrackD.toC pq.1) i₀ ≠ 0)
    (J : AffineFamily.Family (d + d)) :
    ((Γ.filter (fun pq =>
      commonProductImage i₀ (W.owner i pq.1) (W.owner i pq.2) ∈ J)).card : ℝ) ≤
      commonChartImageMass W L i i₀ J := by
  classical
  -- membership in the two retained point sets
  have hmem : ∀ pq ∈ Γ, pq.1 ∈ W.sources i ∧ pq.2 ∈ W.targets i := by
    intro pq hpq
    have h := hΓ hpq
    rwa [Finset.mem_product] at h
  -- complex points lie in their owners
  have htoC_source : ∀ q ∈ W.sources i, TrackD.toC q ∈ W.owner i q := by
    intro q hq
    have hpool : q ∈ TrackD.poolPts (T.sources i) := (Finset.mem_filter.mp hq).1
    obtain ⟨P, hP, hqP⟩ := Finset.mem_biUnion.mp hpool
    have hPunion : P ∈ T.sources i ∪ T.targets i :=
      Finset.mem_union.mpr (Or.inl hP)
    exact ((W.supported i P hPunion q hqP).2)
  have htoC_target : ∀ q ∈ W.targets i, TrackD.toC q ∈ W.owner i q := by
    intro q hq
    have hpool : q ∈ TrackD.poolPts (T.targets i) := (Finset.mem_filter.mp hq).1
    obtain ⟨P, hP, hqP⟩ := Finset.mem_biUnion.mp hpool
    have hPunion : P ∈ T.sources i ∪ T.targets i :=
      Finset.mem_union.mpr (Or.inr hP)
    exact ((W.supported i P hPunion q hqP).2)
  have howner_source : ∀ pq ∈ Γ, W.owner i pq.1 ∈ W.sourceCarriers i := by
    intro pq hpq
    show W.owner i pq.1 ∈ commonOwnerFamily (W.sources i) (W.owner i)
    exact Finset.mem_image.mpr ⟨pq.1, (hmem pq hpq).1, rfl⟩
  have hYchart : ∀ pq ∈ Γ,
      W.owner i pq.2 ∈ commonChartTargets W L i i₀ (W.owner i pq.1) := by
    intro pq hpq
    rw [mem_common_chart_targets]
    refine ⟨hlist pq hpq, TrackD.toC pq.1, htoC_source _ (hmem pq hpq).1,
      TrackD.toC pq.2, htoC_target _ (hmem pq hpq).2, hchart pq hpq⟩
  -- filtered graph and owner fibers
  set Γ' : Finset (RPoint d × RPoint d) :=
    Γ.filter (fun pq => commonProductImage i₀ (W.owner i pq.1) (W.owner i pq.2) ∈ J)
    with hΓ'def
  have hΓ'sub : Γ' ⊆ Γ := Finset.filter_subset _ _
  have hmem' : ∀ pq ∈ Γ', pq.1 ∈ W.sources i ∧ pq.2 ∈ W.targets i := by
    intro pq hpq
    exact hmem pq (hΓ'sub hpq)
  have hJmem : ∀ pq ∈ Γ',
      commonProductImage i₀ (W.owner i pq.1) (W.owner i pq.2) ∈ J := by
    intro pq hpq
    exact (Finset.mem_filter.mp hpq).2
  -- first level: partition by source owner
  set HX : AffineVariety d → Finset (RPoint d × RPoint d) :=
    fun X => Γ'.filter (fun pq => W.owner i pq.1 = X) with hHXdef
  have hXmem : ∀ pq ∈ Γ', W.owner i pq.1 ∈ W.sourceCarriers i := by
    intro pq hpq
    exact howner_source pq (hΓ'sub hpq)
  have hΓ'eq : Γ' = (W.sourceCarriers i).biUnion (fun X => HX X) := by
    ext pq
    constructor
    · intro hpq
      have hpqΓ : pq ∈ Γ := hΓ'sub hpq
      have hXS : W.owner i pq.1 ∈ W.sourceCarriers i := howner_source pq hpqΓ
      rw [Finset.mem_biUnion]
      exact ⟨W.owner i pq.1, hXS, Finset.mem_filter.mpr ⟨hpq, rfl⟩⟩
    · intro hpq
      rw [Finset.mem_biUnion] at hpq
      obtain ⟨X, _, hpqHX⟩ := hpq
      exact (Finset.mem_filter.mp hpqHX).1
  have hdisjX : Set.PairwiseDisjoint (↑(W.sourceCarriers i) : Set (AffineVariety d))
      (fun X => HX X) := by
    intro X _ X' _ hne
    show Disjoint (HX X) (HX X')
    rw [Finset.disjoint_left]
    intro pq hpq hpq'
    have h1 : W.owner i pq.1 = X := (Finset.mem_filter.mp hpq).2
    have h2 : W.owner i pq.1 = X' := (Finset.mem_filter.mp hpq').2
    exact hne (h1.symm.trans h2)
  -- second level: for fixed X, partition by target owner
  have hYmemTX : ∀ X : AffineVariety d, ∀ pq ∈ HX X,
      W.owner i pq.2 ∈ (commonChartTargets W L i i₀ X).filter
        (fun Y => commonProductImage i₀ X Y ∈ J) := by
    intro X pq hpq
    have hpqΓ' : pq ∈ Γ' := (Finset.mem_filter.mp hpq).1
    have hpqΓ : pq ∈ Γ := hΓ'sub hpqΓ'
    have hXeq : W.owner i pq.1 = X := (Finset.mem_filter.mp hpq).2
    have hchartmem : W.owner i pq.2 ∈ commonChartTargets W L i i₀ (W.owner i pq.1) :=
      hYchart pq hpqΓ
    rw [hXeq] at hchartmem
    have hJX : commonProductImage i₀ X (W.owner i pq.2) ∈ J := by
      have hJ := hJmem pq hpqΓ'
      rw [hXeq] at hJ
      exact hJ
    exact Finset.mem_filter.mpr ⟨hchartmem, hJX⟩
  set HXY : AffineVariety d → AffineVariety d → Finset (RPoint d × RPoint d) :=
    fun X Y => (HX X).filter (fun pq => W.owner i pq.2 = Y) with hHXYdef
  have hHXeq : ∀ X ∈ W.sourceCarriers i,
      HX X = ((commonChartTargets W L i i₀ X).filter
        (fun Y => commonProductImage i₀ X Y ∈ J)).biUnion (fun Y => HXY X Y) := by
    intro X _
    ext pq
    constructor
    · intro hpq
      have hpqΓ' : pq ∈ Γ' := (Finset.mem_filter.mp hpq).1
      have hXeq : W.owner i pq.1 = X := (Finset.mem_filter.mp hpq).2
      have hY : W.owner i pq.2 ∈ (commonChartTargets W L i i₀ X).filter
          (fun Y => commonProductImage i₀ X Y ∈ J) :=
        hYmemTX X pq (Finset.mem_filter.mpr ⟨hpqΓ', hXeq⟩)
      rw [Finset.mem_biUnion]
      exact ⟨W.owner i pq.2, hY, Finset.mem_filter.mpr ⟨hpq, rfl⟩⟩
    · intro hpq
      rw [Finset.mem_biUnion] at hpq
      obtain ⟨Y, _, hpqH⟩ := hpq
      exact (Finset.mem_filter.mp hpqH).1
  have hdisjY : ∀ X ∈ W.sourceCarriers i,
      Set.PairwiseDisjoint
        (↑((commonChartTargets W L i i₀ X).filter
          (fun Y => commonProductImage i₀ X Y ∈ J)) : Set (AffineVariety d))
        (fun Y => HXY X Y) := by
    intro X _
    intro Y _ Y' _ hne
    show Disjoint (HXY X Y) (HXY X Y')
    rw [Finset.disjoint_left]
    intro pq hpq hpq'
    have h1 : W.owner i pq.2 = Y := (Finset.mem_filter.mp hpq).2
    have h2 : W.owner i pq.2 = Y' := (Finset.mem_filter.mp hpq').2
    exact hne (h1.symm.trans h2)
  -- each (X,Y) fiber sits in the owner product
  have hsub : ∀ X ∈ W.sourceCarriers i,
      ∀ Y ∈ (commonChartTargets W L i i₀ X).filter
        (fun Y => commonProductImage i₀ X Y ∈ J),
      HXY X Y ⊆ (W.sourceAssigned i X) ×ˢ (W.targetAssigned i Y) := by
    intro X _ Y _ pq hpq
    have hpqHX : pq ∈ HX X := (Finset.mem_filter.mp hpq).1
    have hpqΓ' : pq ∈ Γ' := (Finset.mem_filter.mp hpqHX).1
    have hXeq : W.owner i pq.1 = X := (Finset.mem_filter.mp hpqHX).2
    have hYeq : W.owner i pq.2 = Y := (Finset.mem_filter.mp hpq).2
    have hsrc : pq.1 ∈ W.sources i := (hmem' pq hpqΓ').1
    have htgt : pq.2 ∈ W.targets i := (hmem' pq hpqΓ').2
    rw [Finset.mem_product]
    constructor
    · show pq.1 ∈ commonOwnerFiber (W.sources i) (W.owner i) X
      unfold commonOwnerFiber
      rw [Finset.mem_filter]
      exact ⟨hsrc, hXeq⟩
    · show pq.2 ∈ commonOwnerFiber (W.targets i) (W.owner i) Y
      unfold commonOwnerFiber
      rw [Finset.mem_filter]
      exact ⟨htgt, hYeq⟩
  -- card identities and bounds
  have hcardX : Γ'.card =
      ∑ X ∈ W.sourceCarriers i, (HX X).card := by
    rw [hΓ'eq, Finset.card_biUnion hdisjX]
  have hcardXY : ∀ X ∈ W.sourceCarriers i,
      (HX X).card =
        ∑ Y ∈ (commonChartTargets W L i i₀ X).filter
          (fun Y => commonProductImage i₀ X Y ∈ J), (HXY X Y).card := by
    intro X hX
    rw [hHXeq X hX, Finset.card_biUnion (hdisjY X hX)]
  have hbound : ∀ X ∈ W.sourceCarriers i,
      ∀ Y ∈ (commonChartTargets W L i i₀ X).filter
        (fun Y => commonProductImage i₀ X Y ∈ J),
      ((HXY X Y).card : ℝ) ≤
        ((W.sourceAssigned i X).card : ℝ) * ((W.targetAssigned i Y).card : ℝ) := by
    intro X hX Y hY
    have hle : (HXY X Y).card ≤
        ((W.sourceAssigned i X) ×ˢ (W.targetAssigned i Y)).card :=
      Finset.card_le_card (hsub X hX Y hY)
    have hprod : ((W.sourceAssigned i X) ×ˢ (W.targetAssigned i Y)).card =
        (W.sourceAssigned i X).card * (W.targetAssigned i Y).card :=
      Finset.card_product _ _
    have hcast : (((HXY X Y).card : ℕ) : ℝ) ≤
        ((((W.sourceAssigned i X).card * (W.targetAssigned i Y).card : ℕ)) : ℝ) := by
      exact_mod_cast hle.trans (hprod.le)
    rwa [Nat.cast_mul] at hcast
  -- assemble in ℝ
  have hcard_eq : (Γ'.card : ℝ) =
      ∑ X ∈ W.sourceCarriers i, ∑ Y ∈ (commonChartTargets W L i i₀ X).filter
        (fun Y => commonProductImage i₀ X Y ∈ J), ((HXY X Y).card : ℝ) := by
    have h1 : (Γ'.card : ℝ) =
        ((∑ X ∈ W.sourceCarriers i, (HX X).card : ℕ) : ℝ) := by
      rw [hcardX]
    rw [h1, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro X hX
    rw [hcardXY X hX, Nat.cast_sum]
  have hle : (Γ'.card : ℝ) ≤
      ∑ X ∈ W.sourceCarriers i, ∑ Y ∈ (commonChartTargets W L i i₀ X).filter
        (fun Y => commonProductImage i₀ X Y ∈ J),
        ((W.sourceAssigned i X).card : ℝ) * ((W.targetAssigned i Y).card : ℝ) := by
    rw [hcard_eq]
    apply Finset.sum_le_sum
    intro X hX
    apply Finset.sum_le_sum
    intro Y hY
    exact hbound X hX Y hY
  simpa only [hΓ'def, commonChartImageMass,
    CommonPhysicalSequence.sourceAssigned, CommonPhysicalSequence.targetAssigned]
    using hle

end
end DistinctDistances.SparseCones
