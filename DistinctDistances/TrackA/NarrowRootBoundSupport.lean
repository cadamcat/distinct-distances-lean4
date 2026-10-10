import DistinctDistances.TrackA.NarrowBezoutCountSupport
import DistinctDistances.TrackA.PoolingSupport

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical BigOperators

/-- The finite narrow-root count with a constant depending only on the
original ambient dimension. -/
theorem narrow_root_count_bound {n l : ℕ} (J : AffineFamily.Family n)
    (hl : 1 ≤ l) (hJ : AffineFamily.IsPure J l) (Y : AffineVariety n) (hY : Y ∈ J)
    (S : Finset (Point n)) (E : Set (Poly n)) (L : ℕ) (hL : 1 ≤ L)
    (hE : ∀ f ∈ E, f.totalDegree ≤ L) (hS : IsolatedPoints E S)
    (himage : ∀ p ∈ S, (radialImage p Y).dimension = l) :
    (∑ p ∈ S, ((groupDepth p J Y - 1 : ℕ) : ℚ)) ≤
      ((n+1 : ℕ) * (2 : ℚ)^(n+1)) * AffineFamily.degree J * (L : ℚ)^(l+1) := by
  have hdim : l ≤ n := by
    rw [← (hJ Y hY).2]
    exact pooling_dimension_le_ambient Y (hJ Y hY).1
  have hdegree : (0 : ℚ) ≤ AffineFamily.degree J := by
    apply Finset.sum_nonneg
    intro V hV
    exact zero_le_one.trans (V.one_le_degree (hJ V hV).1.ne_top)
  have hfactor : (l+1 : ℕ) * (2 : ℚ)^(l+1) ≤ (n+1 : ℕ) * (2 : ℚ)^(n+1) := by
    apply mul_le_mul
    · exact_mod_cast Nat.add_le_add_right hdim 1
    · exact pow_le_pow_right₀ (by norm_num) (by omega)
    · exact pow_nonneg (by norm_num) _
    · exact Nat.cast_nonneg _
  calc
    _ ≤ (l+1 : ℕ) * AffineFamily.degree J * (2*L : ℕ)^(l+1) :=
      narrow_root_count_dimensional J hl hJ Y hY S E L hL hE hS himage
    _ = ((l+1 : ℕ) * (2 : ℚ)^(l+1)) * AffineFamily.degree J * (L : ℚ)^(l+1) := by
      push_cast
      rw [mul_pow]
      ring
    _ ≤ ((n+1 : ℕ) * (2 : ℚ)^(n+1)) * AffineFamily.degree J * (L : ℚ)^(l+1) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hfactor hdegree)
        (pow_nonneg (Nat.cast_nonneg _) _)

end
end DistinctDistances.TrackA
