import DistinctDistances.TrackE.CommonImageInputs
import DistinctDistances.TrackD.RationalContainment
import DistinctDistances.TrackD.RationalImageGeometry
import DistinctDistances.TrackD.Requests
import DistinctDistances.TrackD.ProductTangents
import DistinctDistances.TrackA.Intersections
import DistinctDistances.TrackA.Hilbert
import DistinctDistances.TrackA.NormalizationRankSupport
import DistinctDistances.TrackE.MOProdAux
import DistinctDistances.TrackE.MOSecAux

/-! Degree upper bound for secant product images (`sc:retained-products.depth`,
sparse-cones.tex:143-156): helpers for
`SparseCones.mo_chart_product_image_degree_const_full`.

Roadmap (paper: preimages of a general `2k`-fold linear section of the image
are isolated away from the base locus; isolated-intersection Bezout gives
`deg Z <= C_d deg X deg Y`):
- `secantDenominator_degree_le`, `secantNumerator_degree_le`: the fixed secant
  map has bounded degree (numerators `<= 2`, denominator `<= 1`), so cleared
  pullbacks of target linear equations have degree `<= 2`.
- `mo_product_image_irreducible`, `mo_product_image_dim_le`: the image is
  irreducible of dimension `<= 2k` from only the chart hypothesis (no
  transversality needed).
- `irreducible_isPure`: singleton purity from irreducibility (the private
  version in `TrackA.Intersections` is not accessible here).
- `mo_product_degree_upper`: `deg(X x Y) <= deg X * deg Y`, by finite-module Hilbert
  comparison for the product projection.
- `mo_counting_bound`: from a good linear-section package,
  `Z.degree <= S.degree * 2 ^ (2k)` via `TrackA.fa_bezout_relative_points`.
-/

namespace DistinctDistances.SparseCones
open scoped BigOperators Classical
noncomputable section
variable {d : ℕ}

/-- The secant denominator is affine linear. -/
theorem secantDenominator_degree_le (i₀ : Fin d) :
    (TrackD.secantChartDenominator (d := d) i₀).totalDegree ≤ 1 := by
  unfold TrackD.secantChartDenominator
  calc (MvPolynomial.X (finSumFinEquiv (Sum.inr i₀)) -
        MvPolynomial.X (finSumFinEquiv (Sum.inl i₀)) : Poly (d + d)).totalDegree
      ≤ max (MvPolynomial.X (finSumFinEquiv (Sum.inr i₀)) : Poly (d + d)).totalDegree
        (MvPolynomial.X (finSumFinEquiv (Sum.inl i₀)) : Poly (d + d)).totalDegree :=
        MvPolynomial.totalDegree_sub _ _
    _ ≤ 1 := by
        apply max_le <;> simp [MvPolynomial.totalDegree_X]

/-- Every secant numerator has degree at most two (left block `x * g`,
right block a difference). -/
theorem secantNumerator_degree_le (i₀ : Fin d) (j : Fin (d + d)) :
    (TrackD.secantChartNumerator (d := d) i₀ j).totalDegree ≤ 2 := by
  obtain ⟨q, rfl⟩ := finSumFinEquiv.surjective j
  unfold TrackD.secantChartNumerator
  rw [Equiv.symm_apply_apply]
  cases q with
  | inl k =>
    simp only [Sum.elim_inl]
    calc (MvPolynomial.X (finSumFinEquiv (Sum.inl k)) *
          TrackD.secantChartDenominator i₀ : Poly (d + d)).totalDegree
        ≤ (MvPolynomial.X (finSumFinEquiv (Sum.inl k)) : Poly (d + d)).totalDegree +
          (TrackD.secantChartDenominator i₀).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
      _ ≤ 1 + 1 := by
          apply Nat.add_le_add _ (secantDenominator_degree_le i₀)
          simp [MvPolynomial.totalDegree_X]
      _ = 2 := rfl
  | inr k =>
    simp only [Sum.elim_inr]
    calc (MvPolynomial.X (finSumFinEquiv (Sum.inr k)) -
        MvPolynomial.X (finSumFinEquiv (Sum.inl k)) : Poly (d + d)).totalDegree
        ≤ max (MvPolynomial.X (finSumFinEquiv (Sum.inr k)) : Poly (d + d)).totalDegree
          (MvPolynomial.X (finSumFinEquiv (Sum.inl k)) : Poly (d + d)).totalDegree :=
          MvPolynomial.totalDegree_sub _ _
      _ ≤ 2 := by
          apply max_le <;> (calc _ ≤ (1 : ℕ) := by simp [MvPolynomial.totalDegree_X]
            _ ≤ 2 := by omega)

/-- An irreducible variety is pure in its own dimension. -/
theorem irreducible_isPure {n u : ℕ} (V : AffineVariety n)
    (hV : V.IsIrreducible) (hdim : V.dimension = u) : V.IsPure u := by
  intro c
  letI : V.ideal.IsPrime := hV
  have hc : c.val = V.ideal := by
    simpa only [Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff] using
      c.property
  have hvar : c.variety = V := AffineVariety.ext hc
  simpa [hvar] using hdim

/-- The secant product image is irreducible from only the chart hypothesis. -/
theorem mo_product_image_irreducible (i₀ : Fin d) (X Y : AffineVariety d)
    (hX : X.IsIrreducible) (hY : Y.IsIrreducible)
    (hchart : ∃ x ∈ X, ∃ y ∈ Y, (y - x) i₀ ≠ 0) :
    (commonProductImage i₀ X Y).IsIrreducible := by
  have hS := TrackD.productVariety_irreducible X Y hX hY
  have hg := common_image_domain_not_mem i₀ X Y hchart
  unfold commonProductImage
  exact TrackD.rational_image_irreducible _ hS _ _ hg

/-- The secant product image has dimension at most `2k`. -/
theorem mo_product_image_dim_le (i₀ : Fin d) (k : ℕ)
    (X Y : AffineVariety d)
    (hX : X.IsIrreducible) (hY : Y.IsIrreducible)
    (hXd : X.dimension = k) (hYd : Y.dimension = k)
    (hchart : ∃ x ∈ X, ∃ y ∈ Y, (y - x) i₀ ≠ 0) :
    (commonProductImage i₀ X Y).dimension ≤ 2 * k := by
  have hS := TrackD.productVariety_irreducible X Y hX hY
  have hg := common_image_domain_not_mem i₀ X Y hchart
  obtain ⟨_, hgen⟩ := TrackD.request_rational_image_generic_tangent
    (TrackD.productVariety X Y) hS
    (TrackD.secantChartNumerator i₀) (TrackD.secantChartDenominator i₀) hg
  have hle := TrackD.rational_image_dimension_le_of_generic_rank
    (TrackD.productVariety X Y) hS
    (TrackD.secantChartNumerator i₀) (TrackD.secantChartDenominator i₀) hgen
  have hSdim := TrackD.product_dimension X Y hX hY
  rw [hSdim, hXd, hYd] at hle
  calc (commonProductImage i₀ X Y).dimension
      = (TrackD.rationalImage (TrackD.productVariety X Y)
        (TrackD.secantChartNumerator i₀)
        (TrackD.secantChartDenominator i₀)).dimension := rfl
    _ ≤ k + k := hle
    _ = 2 * k := by ring

/-- An irreducible affine variety has dimension at most the ambient dimension. -/
theorem dim_le_ambient {n : ℕ} (V : AffineVariety n)
    (hV : V.IsIrreducible) : V.dimension ≤ n := by
  letI : V.ideal.IsPrime := hV
  have htrdeg : Algebra.trdeg ℂ (Poly n ⧸ V.ideal) ≤ (n : Cardinal) := by
    have hsurj := Ideal.Quotient.mk_surjective (I := V.ideal)
    have h := trdeg_le_of_surjective (Ideal.Quotient.mkₐ ℂ V.ideal) hsurj
    simpa only [MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fin,
      Cardinal.lift_natCast] using h
  have hdim := OAI.QuarticPowerFree.hilbert_natDegree_eq_trdeg V.ideal
    (OAI.QuarticPowerFree.coordinateHilbert V.ideal)
    (OAI.QuarticPowerFree.coordinateHilbert_eventually V.ideal)
  have hle : (V.dimension : Cardinal) ≤ (n : Cardinal) := by
    change ((OAI.QuarticPowerFree.coordinateHilbert V.ideal).natDegree : Cardinal) ≤ _
    rw [hdim]
    exact htrdeg
  exact_mod_cast hle

/-- The degree of the secant image is computed by a general finite linear
section (Noether normalization for `{Z}` plus a general fiber). This gives
the `|Q| = deg Z` half of the good-section package. -/
theorem mo_image_section_exists (i₀ : Fin d) (k : ℕ) (X Y : AffineVariety d)
    (hX : X.IsIrreducible) (hY : Y.IsIrreducible)
    (hXd : X.dimension = k) (hYd : Y.dimension = k)
    (hchart : ∃ x ∈ X, ∃ y ∈ Y, (y - x) i₀ ≠ 0) :
    ∃ (Q : Finset (Point (d + d))),
      ((Q.card : ℚ) = (commonProductImage i₀ X Y).degree) ∧
      (∀ z ∈ Q, z ∈ (commonProductImage i₀ X Y).points) := by
  classical
  have hZirr := mo_product_image_irreducible i₀ X Y hX hY hchart
  set Z := commonProductImage i₀ X Y with hZdef
  have hZd_le : Z.dimension ≤ d + d := dim_le_ambient Z hZirr
  have hZpure : AffineFamily.IsPure ({Z} : AffineFamily.Family (d + d)) Z.dimension :=
    fun W hW => by
      rw [Finset.mem_singleton.mp hW]
      exact ⟨hZirr, rfl⟩
  obtain ⟨φ, _, hφ⟩ := TrackA.poly_hilbert_normalization
    ({Z} : AffineFamily.Family (d + d)) Z.dimension hZd_le hZpure
  obtain ⟨hfin, r, hr, hgen⟩ := hφ Z (Finset.mem_singleton_self Z)
  obtain ⟨_, c, hc, hfib⟩ := hgen
  obtain ⟨t, ht, htc⟩ := GenericFiber.exists_point_of_not_mem (φ.image Z) c hc
  obtain ⟨hffin, hcard⟩ := hfib t ht htc
  refine ⟨hffin.toFinset, ?_, ?_⟩
  · have hn : hffin.toFinset.card = r := by
      rw [← Set.ncard_eq_toFinset_card (φ.fiber Z t) hffin]
      exact hcard
    rw [hn]
    exact hr
  · intro z hz
    exact (hffin.mem_toFinset.mp hz).1

/-- Affine product degree upper bound, from Noether normalization for `{X}`, `{Y}`
(`TrackA.poly_hilbert_normalization`) and finite-module Hilbert comparison for the product
projection. -/
theorem mo_product_degree_upper (k : ℕ) (X Y : AffineVariety d)
    (hX : X.IsIrreducible) (hY : Y.IsIrreducible)
    (hXd : X.dimension = k) (hYd : Y.dimension = k) :
    ((TrackD.productVariety X Y).degree : ℝ) ≤
      (X.degree : ℝ) * (Y.degree : ℝ) := by
  have hQ := prodDegreeEq (d := d) (k := k) (X := X) (Y := Y) hX hY hXd hYd
  have hR : ((TrackD.productVariety X Y).degree : ℝ) =
      (X.degree : ℝ) * (Y.degree : ℝ) := by
    exact_mod_cast hQ
  exact le_of_eq hR

/-- Counting step (proved): a good section package gives
`Z.degree <= S.degree * 2 ^ (2k)` via isolated-intersection Bezout. -/
theorem mo_counting_bound (k : ℕ) (S Z : AffineVariety (d + d))
    (hS : S.IsPure (2 * k))
    (Q : Finset (Point (d + d))) (P : Finset (Point (d + d)))
    (E : Finset (Poly (d + d)))
    (hQ : (Q.card : ℚ) = Z.degree)
    (hcard : Q.card ≤ P.card)
    (hE : ∀ f ∈ E, f.totalDegree ≤ 2)
    (hP : ∀ p ∈ P, pointIdeal p ∈
      (S.ideal ⊔ Ideal.span (↑E : Set (Poly (d + d)))).minimalPrimes) :
    Z.degree ≤ S.degree * (2 : ℚ) ^ (2 * k) := by
  have hbez := TrackA.fa_bezout_relative_points S (2 * k) hS (↑E : Set (Poly (d + d)))
    2 (show 1 ≤ 2 by norm_num) (by simpa using hE) P hP
  have hQP : (Q.card : ℚ) ≤ (P.card : ℚ) := by exact_mod_cast hcard
  calc Z.degree = (Q.card : ℚ) := hQ.symm
    _ ≤ (P.card : ℚ) := hQP
    _ ≤ S.degree * (2 : ℚ) ^ (2 * k) := hbez

end
end DistinctDistances.SparseCones
