import DistinctDistances.TrackC.FiniteIncidence

open scoped BigOperators

namespace DistinctDistances.TrackC

/-- Cauchy--Schwarz in the form used by point-line cells. -/
theorem sum_sqrt_le {α : Type*} (I : Finset α) (a : α → ℝ) (ha : ∀ i ∈ I,0 ≤ a i) :
    (∑ i ∈ I,Real.sqrt (a i)) ≤ Real.sqrt (∑ i ∈ I,a i)*Real.sqrt (I.card:ℝ) := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt I (fun i => Real.sqrt (a i)) (fun _ => 1)
  have heq : (∑ i ∈ I,(Real.sqrt (a i))^2) = ∑ i ∈ I,a i :=
    Finset.sum_congr rfl (fun i hi => Real.sq_sqrt (ha i hi))
  simpa only [mul_one,heq,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] using h

/-- Sum the square-root cell estimates with uniform occupancy and crossing budgets. -/
theorem partition_sqrt_sum {α : Type*} (I : Finset α) (a b : α → ℝ)
    (p D n m r : ℝ) (hp : 0 ≤ p) (hD : 0 ≤ D) (hn : 0 ≤ n) (hm : 0 ≤ m) (hr : 0 < r)
    (ha : ∀ i ∈ I,0 ≤ a i ∧ a i ≤ p*n/r^2) (hb : ∀ i ∈ I,0 ≤ b i)
    (hI : (I.card:ℝ) ≤ p*r^2) (hsum : (∑ i ∈ I,b i) ≤ D*m*r) :
    (∑ i ∈ I,a i*Real.sqrt (b i)) ≤ (p*Real.sqrt D*Real.sqrt p)*n*Real.sqrt m/Real.sqrt r := by
  have hs : (∑ i ∈ I,Real.sqrt (b i)) ≤ Real.sqrt (D*m*r)*Real.sqrt (p*r^2) := by
    calc
      _ ≤ Real.sqrt (∑ i ∈ I,b i)*Real.sqrt (I.card:ℝ) := sum_sqrt_le I b hb
      _ ≤ _ := by gcongr
  let R := Real.sqrt r
  have hR : 0 < R := Real.sqrt_pos.mpr hr
  have hR2 : R^2 = r := Real.sq_sqrt hr.le
  calc
    _ ≤ ∑ i ∈ I,(p*n/r^2)*Real.sqrt (b i) :=
      Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_right (ha i hi).2 (Real.sqrt_nonneg _))
    _ = (p*n/r^2)*(∑ i ∈ I,Real.sqrt (b i)) := (Finset.mul_sum _ _ _).symm
    _ ≤ (p*n/r^2)*(Real.sqrt (D*m*r)*Real.sqrt (p*r^2)) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by
      rw [Real.sqrt_mul (mul_nonneg hD hm),Real.sqrt_mul hD,Real.sqrt_mul hp,Real.sqrt_sq hr.le]
      change (p*n/r^2)*(Real.sqrt D*Real.sqrt m*R*(Real.sqrt p*r)) =
        (p*Real.sqrt D*Real.sqrt p)*n*Real.sqrt m/R
      rw [← hR2]
      field_simp [hR.ne']
      <;> ring

end DistinctDistances.TrackC
