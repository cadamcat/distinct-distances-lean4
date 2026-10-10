import DistinctDistances.TrackE.MOChartAux

/-! The retained chart lists have product images of dimension `2k`.
The degree argument in sparse-cones.tex:143–156 therefore uses only the
full-dimensional good-section package. -/

namespace DistinctDistances.SparseCones
noncomputable section
variable {d : ℕ}

/-- The secant image degree bound for the full-dimensional images in the
retained chart family. -/
theorem mo_chart_product_image_degree_const_full (i₀ : Fin d) (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X Y : AffineVariety d),
      X.IsIrreducible → X.dimension = k → Y.IsIrreducible → Y.dimension = k →
      (∃ x ∈ X, ∃ y ∈ Y, (y - x) i₀ ≠ 0) →
      (commonProductImage i₀ X Y).dimension = 2 * k →
      ((commonProductImage i₀ X Y).degree : ℝ) ≤
        C * (X.degree : ℝ) * (Y.degree : ℝ) := by
  refine ⟨((2 ^ (2 * k) : ℕ) : ℝ), by positivity,
    fun X Y hX hXd hY hYd hchart hZdim => ?_⟩
  have hSirr := TrackD.productVariety_irreducible X Y hX hY
  have hSdim : (TrackD.productVariety X Y).dimension = 2 * k := by
    rw [TrackD.product_dimension X Y hX hY, hXd, hYd]
    ring
  have hSpure := irreducible_isPure _ hSirr hSdim
  have hZirr := mo_product_image_irreducible i₀ X Y hX hY hchart
  obtain ⟨Q, P, E, hQ, hcard, hE, hP⟩ :=
    fulldim_package i₀ k X Y hX hY hXd hYd hchart hk hZirr hZdim
  have hcount := mo_counting_bound k
    (TrackD.productVariety X Y) (commonProductImage i₀ X Y) hSpure Q P E hQ hcard hE hP
  have hprod := mo_product_degree_upper k X Y hX hY hXd hYd
  have hcountR : ((commonProductImage i₀ X Y).degree : ℝ) ≤
      ((TrackD.productVariety X Y).degree : ℝ) * ((2 ^ (2 * k) : ℕ) : ℝ) := by
    exact_mod_cast hcount
  calc ((commonProductImage i₀ X Y).degree : ℝ)
      ≤ ((TrackD.productVariety X Y).degree : ℝ) * ((2 ^ (2 * k) : ℕ) : ℝ) := hcountR
    _ = ((2 ^ (2 * k) : ℕ) : ℝ) * ((TrackD.productVariety X Y).degree : ℝ) := by ring
    _ ≤ ((2 ^ (2 * k) : ℕ) : ℝ) * ((X.degree : ℝ) * (Y.degree : ℝ)) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = ((2 ^ (2 * k) : ℕ) : ℝ) * (X.degree : ℝ) * (Y.degree : ℝ) := by ring

end
end DistinctDistances.SparseCones
