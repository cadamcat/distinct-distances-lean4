import DistinctDistances.TrackC.Basic

open scoped BigOperators

namespace DistinctDistances.TrackC

/-- Exact full-block sum for the integer bisection degree schedule. -/
theorem bisection_degree_block_sum (d q : ℕ) (hd : 1 ≤ d) :
    (∑ j ∈ Finset.range (d*q), d * 2^(j/d+1)) + 2*d^2 = 2*d^2 * 2^q := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hblock : (∑ j ∈ Finset.range d, d * 2^((d*q+j)/d+1)) = d^2 * 2^(q+1) := by
      have hterm (j : ℕ) (hj : j ∈ Finset.range d) :
          d * 2^((d*q+j)/d+1) = d * 2^(q+1) := by
        have hjd : j / d = 0 := Nat.div_eq_of_lt (Finset.mem_range.mp hj)
        rw [Nat.add_div (by omega : 0 < d), Nat.mul_div_right q (by omega : 0 < d), hjd] <;>
          simp [Nat.mod_lt j (by omega : 0 < d)]
      rw [Finset.sum_congr rfl hterm]
      simp [pow_two, Nat.mul_assoc]
    rw [Nat.mul_succ, Finset.sum_range_add, hblock, pow_succ (2 : ℕ) q]
    nlinarith [ih]

/-- Truncating a full block costs only a dimension-dependent constant. -/
theorem bisection_degree_sum_bound (d J : ℕ) (hd : 1 ≤ d) :
    (∑ j ∈ Finset.range J, d * 2^(j/d+1)) ≤ 4*d^2 * 2^(J/d) := by
  have hJ : J ≤ d * (J/d+1) := by
    have hmod := Nat.mod_lt J (by omega : 0 < d)
    have hsum := Nat.mod_add_div J d
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hle : (∑ j ∈ Finset.range J, d * 2^(j/d+1)) ≤
      ∑ j ∈ Finset.range (d*(J/d+1)), d * 2^(j/d+1) :=
    Finset.sum_le_sum_of_subset (Finset.range_mono hJ)
  have hfull := bisection_degree_block_sum d (J/d+1) hd
  rw [pow_succ (2 : ℕ) (J/d)] at hfull
  nlinarith

end DistinctDistances.TrackC
