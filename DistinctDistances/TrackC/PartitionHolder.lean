import DistinctDistances.TrackC.FiniteIncidence

open scoped BigOperators
open Classical

namespace DistinctDistances.TrackC

/-- Summing cell counts at the three-point incidence exponent. -/
theorem partition_two_thirds_sum {α : Type*} (I : Finset α) (a b : α → ℝ)
    (p D n m r : ℝ) (hp : 0 ≤ p) (hD : 0 ≤ D) (hn : 0 ≤ n) (hm : 0 ≤ m) (hr : 0 < r)
    (ha : ∀ i ∈ I, 0 ≤ a i ∧ a i ≤ p*n/r^2)
    (hb : ∀ i ∈ I, 0 ≤ b i)
    (hI : (I.card:ℝ) ≤ p*r^2) (hsum : (∑ i ∈ I, b i) ≤ D*m*r) :
    (∑ i ∈ I, a i*(b i)^((2:ℝ)/3)) ≤
      (p*D^((2:ℝ)/3)*p^((1:ℝ)/3))*n*m^((2:ℝ)/3)/r^((2:ℝ)/3) := by
  have hs : (∑ i ∈ I, (b i)^((2:ℝ)/3)) ≤ (D*m*r)^((2:ℝ)/3)*(p*r^2)^((1:ℝ)/3) := by
    calc
      _ ≤ (∑ i ∈ I, b i)^((2:ℝ)/3)*(I.card:ℝ)^((1:ℝ)/3) := sum_two_thirds_le I b hb
      _ ≤ _ := by
        apply mul_le_mul
        · exact Real.rpow_le_rpow (Finset.sum_nonneg hb) hsum (by norm_num)
        · exact Real.rpow_le_rpow (Nat.cast_nonneg _) hI (by norm_num)
        · positivity
        · positivity
  have hrcube : (r^((2:ℝ)/3))^3 = r^2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    norm_num
  have hrroot : 0 < r^((2:ℝ)/3) := Real.rpow_pos_of_pos hr _
  calc
    _ ≤ ∑ i ∈ I, (p*n/r^2)*(b i)^((2:ℝ)/3) :=
      Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_right (ha i hi).2 (Real.rpow_nonneg (hb i hi) _))
    _ = (p*n/r^2)*(∑ i ∈ I, (b i)^((2:ℝ)/3)) := (Finset.mul_sum _ _ _).symm
    _ ≤ (p*n/r^2)*((D*m*r)^((2:ℝ)/3)*(p*r^2)^((1:ℝ)/3)) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by
      rw [Real.mul_rpow (mul_nonneg hD hm) hr.le, Real.mul_rpow hD hm,
        Real.mul_rpow hp (sq_nonneg r)]
      have hsquare : (r^2)^((1:ℝ)/3) = r^((2:ℝ)/3) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
        norm_num
      rw [hsquare, ← hrcube]
      field_simp [hrroot.ne']
      <;> ring

end DistinctDistances.TrackC
