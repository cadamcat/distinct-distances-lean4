import DistinctDistances.TrackE.CommonImageGroupInputs

/-! Actual varying radial degrees bound whole original complete-image groups,
`sc:retained-products.family`, sparse-cones.tex:172–207. -/
namespace DistinctDistances.SparseCones
open scoped BigOperators Classical
noncomputable section

theorem common_original_image_group_degree_bound {d k : ℕ} (i₀ : Fin d)
    (X : AffineVariety d) (hX : X.IsIrreducible) (hXd : X.dimension = k)
    (F L : AffineFamily.Family d) (hFL : F ⊆ L)
    (hk : 1 ≤ k) (hF : AffineFamily.IsPure F k) (R : ℝ)
    (hchart : ∀ Y ∈ F, ∃ x ∈ X, ∃ y ∈ Y, (y - x) i₀ ≠ 0)
    (hdepth : ∀ Y ∈ F, TrackD.ForGeneralPair X Y (fun x y =>
      y - x ∉ X.tangentSpace x ∧ y - x ∉ Y.tangentSpace y ∧
      (TrackD.movingRoots L x y).Finite ∧
        ((TrackD.movingRoots L x y).ncard : ℝ) ≤ R))
    (Y₀ : AffineVariety d) (hY₀ : Y₀ ∈ F) :
    (X.degree : ℝ) *
      (∑ Y ∈ F.filter (fun Y => commonProductImage i₀ X Y =
        commonProductImage i₀ X Y₀), (Y.degree : ℝ)) ≤
      2 * R * ((commonProductImage i₀ X Y₀).degree : ℝ) := by
  have hbudgets := common_original_list_projection_budgets i₀ X hX hXd
    F L hFL hk hF R hchart hdepth
  have htrans : TrackD.ForGeneralPair X Y₀
      (fun p y => y - p ∉ Y₀.tangentSpace y) :=
    (hdepth Y₀ hY₀).mono (fun p hp y hy hh => hh.2.1)
  obtain ⟨S, hcard, hS, hsection⟩ := common_image_mixed_section_bound i₀ X Y₀
    hX (hF Y₀ hY₀).1 hk hXd (hF Y₀ hY₀).2 (hchart Y₀ hY₀)
    htrans _ hbudgets
  obtain ⟨x, hx, y, hy, _, _, _, hcount⟩ := (hdepth Y₀ hY₀).exists
  have hR : 0 ≤ R := (Nat.cast_nonneg (TrackD.movingRoots L x y).ncard).trans hcount
  refine mixed_fiber_degree_bound X (commonProductImage i₀ X Y₀) S
    (F.filter (fun Y => commonProductImage i₀ X Y = commonProductImage i₀ X Y₀))
    (fun p => ((radialImage p Y₀).degree : ℝ)) TrackA.radialMapDegree R hR
    ?_ ?_ ?_ ?_ ?_
  · exact_mod_cast hcard
  · intro p hp
    have hdeg := ((hS p hp).2.1.1 Y₀ hY₀).2.2.2.1
    exact_mod_cast (le_trans (by norm_num : (0 : ℚ) ≤ 1) hdeg)
  · intro p hp Y hY
    rcases Finset.mem_filter.mp hY with ⟨hYF, himage⟩
    have hQ := (hS p hp).2.1
    have heq := hQ.2.1 Y hYF Y₀ hY₀ himage
    simpa only [heq] using (hQ.1 Y hYF).2.2.2.2.2
  · intro p hp
    exact_mod_cast (hS p hp).2.1.2.2 Y₀ hY₀
  · exact_mod_cast hsection

/-- A later subfamily retains complete original groups, including all targets
mapping to a selected image. -/
theorem common_original_image_subfamily_degree_bound {d k : ℕ} (i₀ : Fin d)
    (X : AffineVariety d) (hX : X.IsIrreducible) (hXd : X.dimension = k)
    (F L : AffineFamily.Family d) (hFL : F ⊆ L)
    (hk : 1 ≤ k) (hF : AffineFamily.IsPure F k) (R : ℝ)
    (hchart : ∀ Y ∈ F, ∃ x ∈ X, ∃ y ∈ Y, (y - x) i₀ ≠ 0)
    (hdepth : ∀ Y ∈ F, TrackD.ForGeneralPair X Y (fun x y =>
      y - x ∉ X.tangentSpace x ∧ y - x ∉ Y.tangentSpace y ∧
      (TrackD.movingRoots L x y).Finite ∧
        ((TrackD.movingRoots L x y).ncard : ℝ) ≤ R))
    (J : AffineFamily.Family (d + d)) :
    (X.degree : ℝ) *
      (∑ Y ∈ F.filter (fun Y => commonProductImage i₀ X Y ∈ J),
        (Y.degree : ℝ)) ≤
      2 * R * (∑ Z ∈ (F.image (commonProductImage i₀ X)).filter
        (fun Z => Z ∈ J), (Z.degree : ℝ)) := by
  rw [common_image_group_degree_partition i₀ X F J, Finset.mul_sum]
  calc
    _ ≤ ∑ Z ∈ (F.image (commonProductImage i₀ X)).filter (fun Z => Z ∈ J),
        2 * R * (Z.degree : ℝ) := by
      apply Finset.sum_le_sum
      intro Z hZ
      obtain ⟨Y₀, hY₀, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hZ).1
      exact common_original_image_group_degree_bound i₀ X hX hXd F L hFL
        hk hF R hchart hdepth Y₀ hY₀
    _ = _ := by rw [Finset.mul_sum]

end
end DistinctDistances.SparseCones
