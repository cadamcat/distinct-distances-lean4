import DistinctDistances.Foundations

/-!
# A nonconstant-fiber route for retained-product degree bounds

`sc:retained-products.family`, sparse-cones.tex:158–213. Once a mixed section and
common complete projected fibers have been supplied, their fiber degrees need not be
constant. Summing the point-projection estimate over all source section points gives
the required product-degree bound directly.
-/

namespace DistinctDistances.SparseCones

open scoped BigOperators

noncomputable section

open Classical in
/-- Mixed-section degree estimate without Hilbert-polynomial constancy of the fibers.
`S` is a source linear section, `fiberDegree x` is the complete projected-image degree
at that point, and `mapDegree x Y` is the actual generic projection degree of a target.
The geometric inputs are explicit; no new variety model is introduced. -/
theorem mixed_fiber_degree_bound {d n : ℕ} (X : AffineVariety d) (Z : AffineVariety n)
    (S : Finset (Point d)) (F : AffineFamily.Family d)
    (fiberDegree : Point d → ℝ) (mapDegree : Point d → AffineVariety d → ℕ) (R : ℝ)
    (hR : 0 ≤ R) (hsource : (S.card : ℝ) = (X.degree : ℝ))
    (hfiber : ∀ x ∈ S, 0 ≤ fiberDegree x)
    (hprojection : ∀ x ∈ S, ∀ Y ∈ F,
      (Y.degree : ℝ) ≤ 2 * (mapDegree x Y : ℝ) * fiberDegree x)
    (hdepth : ∀ x ∈ S, (∑ Y ∈ F, (mapDegree x Y : ℝ)) ≤ R)
    (hsection : (∑ x ∈ S, fiberDegree x) ≤ (Z.degree : ℝ)) :
    (X.degree : ℝ) * (∑ Y ∈ F, (Y.degree : ℝ)) ≤ 2 * R * (Z.degree : ℝ) := by
  classical
  have hpoint : ∀ x ∈ S, (∑ Y ∈ F, (Y.degree : ℝ)) ≤ 2 * R * fiberDegree x := by
    intro x hx
    calc
      _ ≤ ∑ Y ∈ F, 2 * (mapDegree x Y : ℝ) * fiberDegree x :=
        Finset.sum_le_sum (hprojection x hx)
      _ = 2 * (∑ Y ∈ F, (mapDegree x Y : ℝ)) * fiberDegree x := by
        rw [Finset.mul_sum, Finset.sum_mul]
      _ ≤ 2 * R * fiberDegree x := by
        apply mul_le_mul_of_nonneg_right _ (hfiber x hx)
        exact mul_le_mul_of_nonneg_left (hdepth x hx) (by norm_num)
  calc
    _ = ∑ _ ∈ S, (∑ Y ∈ F, (Y.degree : ℝ)) := by rw [← hsource]; simp
    _ ≤ ∑ x ∈ S, 2 * R * fiberDegree x := Finset.sum_le_sum hpoint
    _ = 2 * R * (∑ x ∈ S, fiberDegree x) := by rw [Finset.mul_sum]
    _ ≤ 2 * R * (Z.degree : ℝ) := mul_le_mul_of_nonneg_left hsection (by positivity)

end

end DistinctDistances.SparseCones
