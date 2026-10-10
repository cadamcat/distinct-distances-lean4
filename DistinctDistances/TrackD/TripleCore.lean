import DistinctDistances.TrackD.Basic

/-! Quantitative core of `geo:terminal.triple`, `secants.tex:464–485`.
The branches and intersection budgets are explicit inputs. In particular,
the bound has no dependence on the finite list of original centres. -/

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section

/-- Removing at most half the fibre leaves at least half its cardinality.
Subtraction is in `ℕ`, with its necessary lower bound supplied explicitly. -/
theorem residual_map_degree_half (t δ : ℕ) (ht : 2 * δ ≤ t) :
    (t : ℝ) / 2 ≤ ((t - δ : ℕ) : ℝ) := by
  have hnat : t ≤ 2 * (t - δ) := by omega
  have hreal : (t : ℝ) ≤ 2 * ((t - δ : ℕ) : ℝ) := by exact_mod_cast hnat
  linarith

/-- The singular-centre projection comparison and the surviving branches give
the lower bound on image multiplicity used in the final Bézout/polar sum. -/
theorem residual_branch_degree_lower (D e μ : ℝ) (t δ : ℕ) (he : 0 ≤ e)
    (ht : 2 * δ ≤ t) (hdegree : D / 2 ≤ (t : ℝ) * e)
    (hbranches : ((t - δ : ℕ) : ℝ) ≤ μ) :
    D ≤ 4 * e * μ := by
  have hhalf : (t : ℝ) / 2 ≤ μ := (residual_map_degree_half t δ ht).trans hbranches
  have hmul := mul_le_mul_of_nonneg_right hhalf he
  nlinarith

/-- Abstract centre sum: multiplicities at distinct plane-image points have
product budget `C A B`, while each is at least its source degree over `4e`.
The distinct-image Bézout case has `C=1`; the coincident-image polar case
has `C=2`. All constants precede the arbitrary finite set of centres. -/
theorem inverse_square_sum_of_multiplicity_budget {α : Type*}
    (Pc : Finset α) (e μ ν : α → ℝ) (A B C : ℝ) (hA : 0 < A) (hB : 0 < B)
    (he : ∀ p ∈ Pc, 0 < e p)
    (hμ : ∀ p ∈ Pc, 0 ≤ μ p) (hν : ∀ p ∈ Pc, 0 ≤ ν p)
    (hlowerμ : ∀ p ∈ Pc, A ≤ 4 * e p * μ p)
    (hlowerν : ∀ p ∈ Pc, B ≤ 4 * e p * ν p)
    (hbudget : ∑ p ∈ Pc, μ p * ν p ≤ C * A * B) :
    ∑ p ∈ Pc, (e p)⁻¹ ^ 2 ≤ 16 * C := by
  have hterm : ∀ p ∈ Pc, (e p)⁻¹ ^ 2 * (A * B) ≤ 16 * (μ p * ν p) := by
    intro p hp
    have hpμ := hμ p hp
    have hpν := hν p hp
    have hpe := he p hp
    have hprod : A * B ≤ (4 * e p * μ p) * (4 * e p * ν p) :=
      mul_le_mul (hlowerμ p hp) (hlowerν p hp) hB.le (by positivity)
    have hinv : (e p)⁻¹ ^ 2 * (e p) ^ 2 = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hpe.ne']
      norm_num
    calc
      (e p)⁻¹ ^ 2 * (A * B) ≤
          (e p)⁻¹ ^ 2 * ((4 * e p * μ p) * (4 * e p * ν p)) :=
        mul_le_mul_of_nonneg_left hprod (sq_nonneg _)
      _ = 16 * ((e p)⁻¹ ^ 2 * (e p) ^ 2) * (μ p * ν p) := by ring
      _ = 16 * (μ p * ν p) := by rw [hinv]; ring
  have hsum : (∑ p ∈ Pc, (e p)⁻¹ ^ 2) * (A * B) ≤ (16 * C) * (A * B) := by
    calc
      (∑ p ∈ Pc, (e p)⁻¹ ^ 2) * (A * B) =
          ∑ p ∈ Pc, (e p)⁻¹ ^ 2 * (A * B) := Finset.sum_mul _ _ _
      _ ≤ ∑ p ∈ Pc, 16 * (μ p * ν p) := Finset.sum_le_sum hterm
      _ = 16 * ∑ p ∈ Pc, μ p * ν p := (Finset.mul_sum _ _ _).symm
      _ ≤ 16 * (C * A * B) := mul_le_mul_of_nonneg_left hbudget (by norm_num)
      _ = (16 * C) * (A * B) := by ring
  exact (mul_le_mul_iff_of_pos_right (mul_pos hA hB)).mp hsum

end
end DistinctDistances.TrackD
