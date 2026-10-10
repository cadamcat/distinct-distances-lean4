import DistinctDistances.TrackE.CommonCarrierBudgets

/-! Fixed common target lists from generic depth,
`sc:retained-products.depth`, sparse-cones.tex:139–150, 177–182. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

def commonDiscardedProductMass {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} {M : CommonPoolProfile T} {j : ℕ} {τ : ℝ}
    (W : CommonPhysicalSequence T M j τ)
    (L : AffineVariety d → AffineFamily.Family d) (i : ℕ) : ℝ :=
  ∑ X ∈ W.sourceCarriers i, ∑ Y ∈ W.targetCarriers i \ L X,
    ((W.sourceAssigned i X).card : ℝ) * (W.targetAssigned i Y).card

/-- A certificate uses the actual carrier fibers and makes no chart, later
image subfamily, equation system or graph choice. -/
def CommonDepthCertificate {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} {M : CommonPoolProfile T} {j : ℕ} {τ : ℝ}
    (W : CommonPhysicalSequence T M j τ) (ε : ℝ) (i : ℕ) (δ : ℝ)
    (L : AffineVariety d → AffineFamily.Family d) : Prop :=
  (∀ X ∈ W.sourceCarriers i, L X ⊆ W.targetCarriers i) ∧
  commonDiscardedProductMass W L i ≤
    δ * ((W.sources i).card : ℝ) * (W.targets i).card ∧
  ∀ X ∈ W.sourceCarriers i, ∀ Y ∈ L X,
    TrackD.ForGeneralPair X Y (fun x y =>
      y - x ∉ X.tangentSpace x ∧ y - x ∉ Y.tangentSpace y ∧
      (TrackD.movingRoots (L X) x y).Finite ∧
      ((TrackD.movingRoots (L X) x y).ncard : ℝ) ≤ Real.exp (ε * M.s i))

/-- Lists are fixed on the original sequence before every later density
quantifier and image subfamily; no reindexing of physical roles occurs. -/
structure CommonProductLists {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} {M : CommonPoolProfile T} {j : ℕ} {τ : ℝ}
    (W : CommonPhysicalSequence T M j τ) (ε : ℝ) where
  lists : ℕ → AffineVariety d → AffineFamily.Family d
  subset : ∀ i, ∀ X ∈ W.sourceCarriers i, lists i X ⊆ W.targetCarriers i
  loss : Framework.LittleO (fun i => commonDiscardedProductMass W (lists i) i)
    (fun i => ((W.sources i).card : ℝ) * (W.targets i).card)
  geometry : ∀ᶠ i in atTop, ∀ X ∈ W.sourceCarriers i, ∀ Y ∈ lists i X,
    TrackD.ForGeneralPair X Y (fun x y =>
      y - x ∉ X.tangentSpace x ∧ y - x ∉ Y.tangentSpace y ∧
      (TrackD.movingRoots (lists i X) x y).Finite ∧
      ((TrackD.movingRoots (lists i X) x y).ncard : ℝ) ≤ Real.exp (ε * M.s i))

/-- Fixed-error lists apply generic depth to the literal pooled physical data. -/
theorem common_fixed_error_lists {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} {M : CommonPoolProfile T} {j : ℕ} {τ : ℝ}
    (W : CommonPhysicalSequence T M j τ) (hj : j < d) (hk : d - j + 1 < d)
    (ε : ℝ) (hε : 0 < ε) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ i in atTop, ∃ L : AffineVariety d → AffineFamily.Family d,
      CommonDepthCertificate W ε i δ L := by
  have hdim : 1 ≤ d - j := by omega
  have hkd : d - j < d := by omega
  obtain ⟨η, hη, w₀, hgeo⟩ := TrackD.geo_generic_depth d regime.dimension_ge_three
    (1 / 3) (by norm_num) ε hε δ hδ
  filter_upwards [selected_common_carrier_budgets W hj.le η hη,
    common_retained_mass_lower W η hη, wide_regime_flat_cap regime,
    M.width_grows.eventually_ge_atTop w₀] with i hbudgets hmass hcap hwidth
  have hstructure := common_retained_carrier_structure W hj.le i
  rcases hstructure with ⟨hsource, htarget, hsourceAssign, htargetAssign, hreal⟩
  have he : 0 < commonCarrierScale M j i := by
    unfold commonCarrierScale TrackD.eScale TrackD.cutScale TrackD.testDeg
    exact Finset.prod_pos fun _ _ => mul_pos (regime.B_pos i) (Real.exp_pos _)
  have hsourceMass : TrackD.famMass (W.sourceCarriers i) (W.sourceAssigned i) =
      ((W.sources i).card : ℝ) := common_owner_family_mass _ _
  have htargetMass : TrackD.famMass (W.targetCarriers i) (W.targetAssigned i) =
      ((W.targets i).card : ℝ) := common_owner_family_mass _ _
  have hflatS := common_flat_budget (W.sourceCarriers i) (W.sourceAssigned i)
    (fun X hX => (hsource X hX).1) (commonCarrierScale M j i)
    ((W.sources i).card : ℝ) (Real.exp (η * M.s i)) he (Nat.cast_nonneg _)
    (Real.exp_pos _).le hbudgets.1 hbudgets.2.2.1
  have hflatT := common_flat_budget (W.targetCarriers i) (W.targetAssigned i)
    (fun Y hY => (htarget Y hY).1) (commonCarrierScale M j i)
    ((W.targets i).card : ℝ) (Real.exp (η * M.s i)) he (Nat.cast_nonneg _)
    (Real.exp_pos _).le hbudgets.2.1 hbudgets.2.2.2
  have hB : TrackD.cfgB (regime.P i) = regime.B i := rfl
  have hN : TrackD.cfgN (regime.P i) = regime.N i := rfl
  obtain ⟨L, hsub, hloss, hgeometry⟩ := hgeo (regime.P i) (M.s i)
    (commonCarrierScale M j i) hwidth (by rw [hB]; exact common_pool_width_le_logB M i)
    he hcap (d - j) (d - j) le_rfl hdim hkd hk
    (W.sourceCarriers i) (W.targetCarriers i) (W.sourceAssigned i) (W.targetAssigned i)
    hsource htarget hsourceAssign htargetAssign hreal
    (by simpa only [hN, hsourceMass] using hmass.1)
    (by simpa only [hN, htargetMass] using hmass.2)
    (by
      intro _
      rw [hsourceMass, htargetMass]
      exact ⟨hflatS.1, hflatT.1, hflatS.2, hflatT.2⟩)
  refine ⟨L, hsub, ?_, hgeometry⟩
  simpa only [commonDiscardedProductMass, hsourceMass, htargetMass] using hloss

/-- One slow error choice gives fixed lists with negligible actual product
mass loss; later chart and subfamily choices do not enter this diagonal. -/
theorem selected_common_product_lists {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} {M : CommonPoolProfile T} {j : ℕ} {τ : ℝ}
    (W : CommonPhysicalSequence T M j τ) (hj : j < d) (hk : d - j + 1 < d)
    (ε : ℝ) (hε : 0 < ε) : Nonempty (CommonProductLists W ε) := by
  let Q : ℕ → ℕ → Prop := fun n i =>
    ∃ L : AffineVariety d → AffineFamily.Family d,
      CommonDepthCertificate W ε i (selectionTolerance n) L
  have hQ (n : ℕ) : ∀ᶠ i in atTop, Q n i :=
    common_fixed_error_lists W hj hk ε hε (selectionTolerance n)
      (by unfold selectionTolerance; positivity)
  obtain ⟨a, _, hagrows, hdiag⟩ := Framework.exists_slow_diagonal Q hQ
  have hchosen : ∀ᶠ i in atTop, Q (a i) i := hdiag.mono fun i hi => hi (a i) le_rfl
  let L : ℕ → AffineVariety d → AffineFamily.Family d := fun i =>
    if hi : Q (a i) i then Classical.choose hi else fun _ => ∅
  have hcertificate : ∀ᶠ i in atTop,
      CommonDepthCertificate W ε i (selectionTolerance (a i)) (L i) := by
    filter_upwards [hchosen] with i hi
    simpa only [L, dif_pos hi] using Classical.choose_spec hi
  have hsub : ∀ i, ∀ X ∈ W.sourceCarriers i, L i X ⊆ W.targetCarriers i := by
    intro i X hX
    by_cases hi : Q (a i) i
    · simpa only [L, dif_pos hi] using (Classical.choose_spec hi).1 X hX
    · simp only [L, dif_neg hi]
      exact Finset.empty_subset _
  have htolerance := selection_tolerance_tendsto_zero a hagrows
  have hloss : Framework.LittleO (fun i => commonDiscardedProductMass W (L i) i)
      (fun i => ((W.sources i).card : ℝ) * (W.targets i).card) := by
    apply Asymptotics.IsLittleO.of_bound
    intro c hc
    filter_upwards [hcertificate, htolerance.eventually (Iio_mem_nhds hc)] with i hi hci
    have hnonneg : 0 ≤ commonDiscardedProductMass W (L i) i := by
      unfold commonDiscardedProductMass
      exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnonneg,
      abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
    exact hi.2.1.trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hci.le
        (mul_nonneg (Nat.cast_nonneg (W.sources i).card)
          (Nat.cast_nonneg (W.targets i).card)))
  exact ⟨{
    lists := L
    subset := hsub
    loss := hloss
    geometry := hcertificate.mono fun i hi => hi.2.2 }⟩

end
end DistinctDistances.SparseCones
