import DistinctDistances.TrackD.SecantsLabelAlgebra

namespace DistinctDistances.TrackD

noncomputable section
variable {d : ℕ}

theorem further_root_scalar_ne (x y z : Point d) (c : ℂ)
    (hzx : z ≠ x) (hzy : z ≠ y) (hz : z - x = c • (y - x)) : c ≠ 0 ∧ c ≠ 1 := by
  constructor
  · intro hc
    have h : z - x = 0 := by simpa only [hc, zero_smul] using hz
    exact hzx (sub_eq_zero.mp h)
  · intro hc
    have h : z - x = y - x := by simpa only [hc, one_smul] using hz
    exact hzy (sub_left_inj.mp h)

theorem further_root_chart_ne_zero (i : Fin d) (x y z : Point d) (c : ℂ)
    (hc : c ≠ 0) (hi : (y - x) i ≠ 0) (hz : z - x = c • (y - x)) :
    (z - x) i ≠ 0 := by
  have h : (z - x) i = c * (y - x) i := by
    simpa only [Pi.smul_apply, smul_eq_mul] using congrFun hz i
  rw [h]
  exact mul_ne_zero hc hi

theorem further_root_labels_eq (i : Fin d) (x y z : Point d) (c : ℂ)
    (hc : c ≠ 0) (hi : (y - x) i ≠ 0) (hz : z - x = c • (y - x)) :
    rationalPoint (secantChartNumerator i) (secantChartDenominator i) (productPoint x y) =
      rationalPoint (secantChartNumerator i) (secantChartDenominator i) (productPoint x z) := by
  rw [rational_secant_label i x y hi,
    rational_secant_label i x z (further_root_chart_ne_zero i x y z c hc hi hz), hz,
    dirChart_smul (LinearMap.proj i) (y - x) c hc hi]

set_option maxHeartbeats 1000000 in
/-- `secants.tex:63–81`: compare the two actual label-image closures. The
three rational-map requests are the explicit supplying-track frontier; the
product model, rank argument, and equal-dimension step are proved in track D. -/
theorem further_root_label_tangents (X Y Y' : AffineVariety d)
    (hX : X.IsIrreducible) (hY : Y.IsIrreducible) (hY' : Y'.IsIrreducible)
    (hdim : Y'.dimension = Y.dimension) (hlpos : 0 < Y.dimension)
    (htr : ForGeneralPair X Y (fun x y =>
      y - x ∉ X.tangentSpace x ∧ y - x ∉ Y.tangentSpace y))
    (hroot : ForGeneralPair X Y (fun x y =>
      ∃ z ∈ Y', z ≠ x ∧ z ≠ y ∧ ∃ c : ℂ, z - x = c • (y - x))) :
    ∃ i : Fin d, ForGeneralPair X Y (fun x y =>
      ∃ z ∈ Y', ∃ c : ℂ, c ≠ 0 ∧ c ≠ 1 ∧ z - x = c • (y - x) ∧ (y - x) i ≠ 0 ∧
        ((X.tangentSpace x).prod (⊥ : Submodule ℂ (Point d))).map
          (labelDeriv (LinearMap.proj i) x z) ≤
            ((X.tangentSpace x).prod (Y.tangentSpace y)).map
              (labelDeriv (LinearMap.proj i) x y)) := by
  obtain ⟨x₀, hx₀, y₀, hy₀, htrans₀⟩ := htr.exists
  have hu₀ : y₀ - x₀ ≠ 0 := by
    intro h
    apply htrans₀.1
    rw [h]
    exact Submodule.zero_mem _
  have hex : ∃ i : Fin d, (y₀ - x₀) i ≠ 0 := by
    by_contra h
    push Not at h
    apply hu₀
    funext i
    exact h i
  obtain ⟨i, hi₀⟩ := hex
  let f := secantChartNumerator i
  let g := secantChartDenominator i
  let S := productVariety X Y
  let S' := productVariety X Y'
  let W := rationalImage S f g
  let W' := rationalImage S' f g
  have hS : S.IsIrreducible := productVariety_irreducible X Y hX hY
  have hS' : S'.IsIrreducible := productVariety_irreducible X Y' hX hY'
  have hchart : ForGeneralPair X Y (fun x y => (y - x) i ≠ 0) := by
    refine ⟨MvPolynomial.rename finSumFinEquiv.symm g, ⟨x₀, hx₀, y₀, hy₀, ?_⟩, ?_⟩
    · simpa only [eval_product_rename, g, eval_secantChartDenominator] using hi₀
    · intro x hx y hy hn
      simpa only [eval_product_rename, g, eval_secantChartDenominator] using hn
  have hg : g ∉ S.ideal := by
    intro hg
    have hp : productPoint x₀ y₀ ∈ S := AffineVariety.subset_closure _ ⟨x₀, hx₀, y₀, hy₀, rfl⟩
    have hzero := hp g hg
    change MvPolynomial.eval (productPoint x₀ y₀) g = 0 at hzero
    exact hi₀ (by simpa only [g, eval_secantChartDenominator] using hzero)
  have hrootchart := hroot.and hX hY hchart
  have hg' : g ∉ S'.ideal := by
    obtain ⟨x, hx, y, hy, ⟨z, hz, hzx, hzy, c, hline⟩, hi⟩ := hrootchart.exists
    have hc := (further_root_scalar_ne x y z c hzx hzy hline).1
    have hzgi := further_root_chart_ne_zero i x y z c hc hi hline
    intro hg'
    have hp : productPoint x z ∈ S' := AffineVariety.subset_closure _ ⟨x, hx, z, hz, rfl⟩
    have hzero := hp g hg'
    change MvPolynomial.eval (productPoint x z) g = 0 at hzero
    exact hzgi (by simpa only [g, eval_secantChartDenominator] using hzero)
  obtain ⟨hW, hgenW⟩ := request_rational_image_generic_tangent S hS f g hg
  obtain ⟨hW', hgenW'⟩ := request_rational_image_generic_tangent S' hS' f g hg'
  have hsubsetPair : ForGeneralPair X Y (fun x y =>
      MvPolynomial.eval (productPoint x y) g ≠ 0 ∧ rationalPoint f g (productPoint x y) ∈ W') := by
    apply hrootchart.mono
    intro x hx y hy hh
    rcases hh with ⟨⟨z, hz, hzx, hzy, c, hline⟩, hi⟩
    have hc := (further_root_scalar_ne x y z c hzx hzy hline).1
    have hzgi := further_root_chart_ne_zero i x y z c hc hi hline
    refine ⟨by simpa only [g, eval_secantChartDenominator] using hi, ?_⟩
    have heq := further_root_labels_eq i x y z c hc hi hline
    change rationalPoint (secantChartNumerator i) (secantChartDenominator i) (productPoint x y) ∈ W'
    rw [heq]
    exact rationalPoint_mem_image S' f g (productPoint x z)
      (AffineVariety.subset_closure _ ⟨x, hx, z, hz, rfl⟩)
      (by simpa only [g, eval_secantChartDenominator] using hzgi)
  have hsubsetSource : ForGeneralPoint S (fun p => MvPolynomial.eval p g ≠ 0 ∧ rationalPoint f g p ∈ W') := by
    simpa only [productPoint_left_right] using hsubsetPair.on_product
  have hsub : W.Subvariety W' := request_rational_image_generic_subset S hS f g W' hsubsetSource
  have hdx := (general_tangent_finrank X hX).on_left ⟨y₀, hy₀⟩
  have hdy := (general_tangent_finrank Y hY).on_right ⟨x₀, hx₀⟩
  have hrankPair : ForGeneralPair X Y (fun x y => Module.finrank ℂ
      ((S.tangentSpace (productPoint x y)).map (rationalDifferential f g (productPoint x y))) = S.dimension) := by
    apply (((htr.and hX hY hchart).and hX hY hdx).and hX hY hdy).mono
    intro x hx y hy hh
    rcases hh with ⟨⟨⟨htrans, hi⟩, hdx⟩, hdy⟩
    have hr := rational_secant_tangent_finrank X Y i x y hx hy hi htrans.2
    simpa only [S, f, g, product_dimension X Y hX hY, hdx, hdy] using hr
  have hrankSource : ForGeneralPoint S (fun p => Module.finrank ℂ
      ((S.tangentSpace p).map (rationalDifferential f g p)) = S.dimension) := by
    apply hrankPair.on_product.mono
    intro p hp hh
    have heq := productPoint_left_right p
    rw [heq] at hh
    exact hh
  have hdimW : W.dimension = S.dimension :=
    rational_image_dimension_eq_of_generic_rank S hS f g hgenW hrankSource
  have hdimW' : W'.dimension ≤ S'.dimension :=
    rational_image_dimension_le_of_generic_rank S' hS' f g hgenW'
  have hsourceEq : S'.dimension = S.dimension := by
    simp only [S, S', product_dimension X Y hX hY, product_dimension X Y' hX hY', hdim]
  have hdimEq : W.dimension = W'.dimension := by
    have hlo := irreducible_dimension_mono W W' hW hW' hsub
    rw [hsourceEq, ← hdimW] at hdimW'
    exact Nat.le_antisymm hlo hdimW'
  have hpos : 0 < W'.dimension := by
    rw [← hdimEq, hdimW]
    have hsdim := product_dimension X Y hX hY
    change 0 < (productVariety X Y).dimension
    rw [hsdim]
    omega
  have hWW' : W = W' := irreducible_subvariety_eq_of_pos_dimension_eq W W' hW hW' hsub hpos hdimEq
  refine ⟨i, ?_⟩
  apply (hroot.and hX hY hgenW.on_product).mono
  intro x hx y hy hh
  rcases hh with ⟨⟨z, hz, hzx, hzy, c, hline⟩, hgi, hmap, hdim⟩
  have hi : (y - x) i ≠ 0 := by simpa only [g, eval_secantChartDenominator] using hgi
  obtain ⟨hc0, hc1⟩ := further_root_scalar_ne x y z c hzx hzy hline
  have hzgi := further_root_chart_ne_zero i x y z c hc0 hi hline
  have hlabels := further_root_labels_eq i x y z c hc0 hi hline
  have hchain := request_rational_image_tangent_all S' f g (productPoint x z)
    (AffineVariety.subset_closure _ ⟨x, hx, z, hz, rfl⟩)
    (by simpa only [g, eval_secantChartDenominator] using hzgi)
  rw [rational_secant_tangent_map X Y' i x z hx hz hzgi] at hchain
  have hsmall : (X.tangentSpace x).prod (⊥ : Submodule ℂ (Point d)) ≤
      (X.tangentSpace x).prod (Y'.tangentSpace z) := by
    intro p hp
    refine ⟨hp.1, ?_⟩
    have hp0 : p.2 = 0 := by
      have hbot : p.2 ∈ (⊥ : Submodule ℂ (Point d)) := hp.2
      simpa using hbot
    rw [hp0]
    exact Submodule.zero_mem _
  have hsmallMap := (Submodule.map_mono (f := productLinearEquiv.toLinearMap)
    (Submodule.map_mono (f := labelDeriv (LinearMap.proj i) x z) hsmall)).trans hchain
  change (((X.tangentSpace x).prod (⊥ : Submodule ℂ (Point d))).map
    (labelDeriv (LinearMap.proj i) x z)).map productLinearEquiv.toLinearMap ≤
      W'.tangentSpace (rationalPoint f g (productPoint x z)) at hsmallMap
  rw [← hWW', ← hlabels] at hsmallMap
  have hfull : (((X.tangentSpace x).prod (Y.tangentSpace y)).map
      (labelDeriv (LinearMap.proj i) x y)).map productLinearEquiv.toLinearMap =
        W.tangentSpace (rationalPoint f g (productPoint x y)) := by
    rw [← rational_secant_tangent_map X Y i x y hx hy hi]
    exact hmap
  rw [← hfull] at hsmallMap
  refine ⟨z, hz, c, hc0, hc1, hline, hi, ?_⟩
  exact (Submodule.map_le_map_iff_of_injective productLinearEquiv.injective _ _).mp hsmallMap

end
end DistinctDistances.TrackD
