import DistinctDistances.TrackE.CommonImageMassInputs

/-! Uniform image mass for the unchanged physical owner sequence,
`sc:retained-products.mass`, sparse-cones.tex:146–148, 201–213. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}
variable {F : ConeCoverageSequence regime} {T : SelectedProfileSequence F}
    {M : CommonPoolProfile T} {j : ℕ} {τ ε : ℝ}

/-- One index condition handles every chart and every later image subfamily. -/
theorem common_chart_image_mass_bound (W : CommonPhysicalSequence T M j τ)
    (hj : j < d) (L : CommonProductLists W ε) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ i in atTop, ∀ i₀ : Fin d, ∀ J : AffineFamily.Family (d + d),
      commonChartImageMass W L i i₀ J ≤
        2 * Real.exp ((ε + 2 * η) * M.s i) *
          (((W.sources i).card : ℝ) * (W.targets i).card /
            (commonCarrierScale M j i) ^ 2) *
          (∑ Z ∈ (commonChartImages W L i i₀).filter (fun Z => Z ∈ J),
            (Z.degree : ℝ)) := by
  filter_upwards [L.geometry, selected_common_carrier_budgets W hj.le η hη]
    with i hgeometry hbudgets
  intro i₀ J
  have hstructure := common_retained_carrier_structure W hj.le i
  have hdim : 1 ≤ d - j := by omega
  have he : 0 < commonCarrierScale M j i := by
    unfold commonCarrierScale TrackD.eScale TrackD.cutScale TrackD.testDeg
    exact Finset.prod_pos fun _ _ => mul_pos (regime.B_pos i) (Real.exp_pos _)
  have hFL : ∀ X ∈ W.sourceCarriers i,
      commonChartTargets W L i i₀ X ⊆ L.lists i X := by
    intro X hX Y hY
    exact ((mem_common_chart_targets W L i i₀ X Y).mp hY).1
  have hF : ∀ X ∈ W.sourceCarriers i,
      AffineFamily.IsPure (commonChartTargets W L i i₀ X) (d - j) := by
    intro X hX Y hY
    exact hstructure.2.1 Y (L.subset i X hX (hFL X hX hY))
  have hchart : ∀ X ∈ W.sourceCarriers i,
      ∀ Y ∈ commonChartTargets W L i i₀ X,
        ∃ x ∈ X, ∃ y ∈ Y, (y - x) i₀ ≠ 0 := by
    intro X hX Y hY
    exact ((mem_common_chart_targets W L i i₀ X Y).mp hY).2
  have hfamily := common_original_image_family_degree_bound i₀
    (W.sourceCarriers i) hstructure.1 (commonChartTargets W L i i₀)
    (L.lists i) hFL hdim hF (Real.exp (ε * M.s i)) hchart
    (fun X hX Y hY => hgeometry X hX Y (hFL X hX hY)) J
  have hfamily' :
      (∑ X ∈ W.sourceCarriers i, (X.degree : ℝ) *
        (∑ Y ∈ (commonChartTargets W L i i₀ X).filter
          (fun Y => commonProductImage i₀ X Y ∈ J), (Y.degree : ℝ))) ≤
      2 * Real.exp (ε * M.s i) *
        (∑ Z ∈ (commonChartImages W L i i₀).filter (fun Z => Z ∈ J),
          (Z.degree : ℝ)) := by
    simpa only [commonChartImages] using hfamily
  have hscalar : 0 ≤
      (((W.sources i).card : ℝ) * (W.targets i).card /
        (commonCarrierScale M j i) ^ 2) * Real.exp ((2 * η) * M.s i) := by
    positivity
  calc
    _ ≤ (((W.sources i).card : ℝ) * (W.targets i).card /
        (commonCarrierScale M j i) ^ 2) * Real.exp ((2 * η) * M.s i) *
        (∑ X ∈ W.sourceCarriers i, (X.degree : ℝ) *
          (∑ Y ∈ (commonChartTargets W L i i₀ X).filter
            (fun Y => commonProductImage i₀ X Y ∈ J), (Y.degree : ℝ))) :=
      common_chart_mass_from_carrier_caps W L i i₀ η he hbudgets J
    _ ≤ (((W.sources i).card : ℝ) * (W.targets i).card /
        (commonCarrierScale M j i) ^ 2) * Real.exp ((2 * η) * M.s i) *
        (2 * Real.exp (ε * M.s i) *
          (∑ Z ∈ (commonChartImages W L i i₀).filter (fun Z => Z ∈ J),
            (Z.degree : ℝ))) := mul_le_mul_of_nonneg_left hfamily' hscalar
    _ = _ := by
      have hexp : Real.exp ((2 * η) * M.s i) * Real.exp (ε * M.s i) =
          Real.exp ((ε + 2 * η) * M.s i) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [← hexp]
      ring

/-- Lists and owner assignments are fixed before all later choices. -/
theorem selected_common_chart_image_mass (W : CommonPhysicalSequence T M j τ)
    (hj : j < d) (hk : d - j + 1 < d) (ε₀ : ℝ) (hε₀ : 0 < ε₀) :
    ∃ L : CommonProductLists W (ε₀ / 2), ∀ᶠ i in atTop, ∀ i₀ : Fin d,
      AffineFamily.IsPure (commonChartImages W L i i₀) (2 * (d - j)) ∧
      ∀ J : AffineFamily.Family (d + d),
        commonChartImageMass W L i i₀ J ≤
          Real.exp (ε₀ * M.s i) *
            (((W.sources i).card : ℝ) * (W.targets i).card /
              (commonCarrierScale M j i) ^ 2) *
            (∑ Z ∈ (commonChartImages W L i i₀).filter (fun Z => Z ∈ J),
              (Z.degree : ℝ)) := by
  obtain ⟨L⟩ := selected_common_product_lists W hj hk (ε₀ / 2) (by positivity)
  refine ⟨L, ?_⟩
  filter_upwards [common_chart_image_mass_bound W hj L (ε₀ / 8) (by positivity),
    L.geometry, M.width_grows.eventually_ge_atTop (4 * Real.log 2 / ε₀)]
    with i hmass hgeometry hwidth
  intro i₀
  have htrans : ∀ X ∈ W.sourceCarriers i, ∀ Y ∈ L.lists i X,
      TrackD.ForGeneralPair X Y (fun x y => y - x ∉ Y.tangentSpace y) := by
    intro X hX Y hY
    exact (hgeometry X hX Y hY).mono (fun x hx y hy hh => hh.2.1)
  have hpure := common_chart_images_pure W hj.le L i i₀ htrans
  refine ⟨hpure, ?_⟩
  intro J
  have hsum : 0 ≤ ∑ Z ∈ (commonChartImages W L i i₀).filter (fun Z => Z ∈ J),
      (Z.degree : ℝ) := by
    apply Finset.sum_nonneg
    intro Z hZ
    have hZirr := (hpure Z (Finset.mem_filter.mp hZ).1).1
    exact_mod_cast (le_trans (by norm_num : (0 : ℚ) ≤ 1)
      (AffineVariety.one_le_degree Z hZirr.ne_top))
  have hnormal : 0 ≤ ((W.sources i).card : ℝ) * (W.targets i).card /
      (commonCarrierScale M j i) ^ 2 := by positivity
  have hcoef : 2 * Real.exp ((ε₀ / 2 + 2 * (ε₀ / 8)) * M.s i) ≤
      Real.exp (ε₀ * M.s i) := by
    have heq : ε₀ / 2 + 2 * (ε₀ / 8) = 3 * ε₀ / 4 := by ring
    simpa only [heq] using common_two_exp_absorb ε₀ (M.s i) hε₀ hwidth
  exact (hmass i₀ J).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoef hnormal) hsum)

end
end DistinctDistances.SparseCones
