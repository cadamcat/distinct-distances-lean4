import DistinctDistances.TrackB.SegreCoefficients
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.RingTheory.PowerSeries.WellKnown
/-!
Arithmetic support for B13.4, the finite coefficient calculation for
concentration.tex:704–748. The triangular moments, boundary cancellation and scalar slice transforms are proved.
The frozen `koszulIncidenceHilbert_point_coefficient` is proved in IncidenceHilbert.lean.
The geometric Hilbert identity remains open.
-/

namespace DistinctDistances.TrackB.IncidenceMoments

set_option autoImplicit false

open scoped BigOperators

theorem alternating_choose_sum (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ k * (n.choose k : ℚ)) =
      if n = 0 then 1 else 0 := by
  exact_mod_cast (Int.alternating_sum_range_choose (n := n))

/-- Finite binomial cancellation used in B13.4's boundary and triangular sums. -/
theorem alternating_choose_moment (e a : ℕ) (ha : a ≤ e) :
    (∑ k ∈ Finset.range (e + 1),
      (-1 : ℚ) ^ k * (e.choose k : ℚ) * (k.choose a : ℚ)) =
      if a = e then (-1 : ℚ) ^ e else 0 := by
  have heq : e + 1 = a + (e - a + 1) := by omega
  have hlow : (∑ k ∈ Finset.range a,
      (-1 : ℚ) ^ k * (e.choose k : ℚ) * (k.choose a : ℚ)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    simp [Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hk)]
  have hchoose : ∀ r : ℕ,
      (e.choose (a + r) : ℚ) * ((a + r).choose a : ℚ) =
        (e.choose a : ℚ) * ((e - a).choose r : ℚ) := by
    intro r
    have hNat : e.choose (a + r) * (a + r).choose a =
        e.choose a * (e - a).choose r := by
      simpa using (Nat.choose_mul (n := e) (k := a + r) (s := a) (by omega))
    exact_mod_cast hNat
  calc
    (∑ k ∈ Finset.range (e + 1),
        (-1 : ℚ) ^ k * (e.choose k : ℚ) * (k.choose a : ℚ)) =
        (∑ k ∈ Finset.range a,
          (-1 : ℚ) ^ k * (e.choose k : ℚ) * (k.choose a : ℚ)) +
        ∑ r ∈ Finset.range (e - a + 1),
          (-1 : ℚ) ^ (a + r) * (e.choose (a + r) : ℚ) * ((a + r).choose a : ℚ) := by
      rw [heq, Finset.sum_range_add]
    _ = (-1 : ℚ) ^ a * (e.choose a : ℚ) *
        ∑ r ∈ Finset.range (e - a + 1), (-1 : ℚ) ^ r * ((e - a).choose r : ℚ) := by
      rw [hlow, zero_add, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      rw [pow_add]
      calc
        ((-1 : ℚ) ^ a * (-1 : ℚ) ^ r) * (e.choose (a + r) : ℚ) *
            ((a + r).choose a : ℚ) =
            (-1 : ℚ) ^ a * (-1 : ℚ) ^ r *
              ((e.choose (a + r) : ℚ) * ((a + r).choose a : ℚ)) := by ring
        _ = (-1 : ℚ) ^ a * (-1 : ℚ) ^ r *
            ((e.choose a : ℚ) * ((e - a).choose r : ℚ)) := by rw [hchoose]
        _ = _ := by ring
    _ = if a = e then (-1 : ℚ) ^ e else 0 := by
      rw [alternating_choose_sum]
      by_cases h : a = e
      · subst a
        simp
      · have hn : e - a ≠ 0 := by omega
        simp [h, hn]

theorem alternating_descFactorial_moment (e a : ℕ) (ha : a ≤ e) :
    (∑ k ∈ Finset.range (e + 1),
      (-1 : ℚ) ^ k * (e.choose k : ℚ) * (k.descFactorial a : ℚ)) =
      if a = e then (-1 : ℚ) ^ e * (e.factorial : ℚ) else 0 := by
  have heq : (∑ k ∈ Finset.range (e + 1),
      (-1 : ℚ) ^ k * (e.choose k : ℚ) * (k.descFactorial a : ℚ)) =
      (a.factorial : ℚ) * ∑ k ∈ Finset.range (e + 1),
        (-1 : ℚ) ^ k * (e.choose k : ℚ) * (k.choose a : ℚ) := by
    simp_rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intros
    ring
  rw [heq, alternating_choose_moment e a ha]
  by_cases h : a = e
  · simp [h, mul_comm]
  · simp [h]

theorem alternating_power_expansion (e a : ℕ) :
    (∑ k ∈ Finset.range (e + 1),
      (-1 : ℚ) ^ k * (e.choose k : ℚ) * (k : ℚ) ^ a) =
      ∑ r ∈ Finset.range (a + 1), (Nat.stirlingSecond a r : ℚ) *
        ∑ k ∈ Finset.range (e + 1),
          (-1 : ℚ) ^ k * (e.choose k : ℚ) * (k.descFactorial r : ℚ) := by
  have hexp : ∀ k : ℕ, (k : ℚ) ^ a =
      ∑ r ∈ Finset.range (a + 1), (Nat.stirlingSecond a r : ℚ) * (k.descFactorial r : ℚ) := by
    intro k
    exact_mod_cast Nat.pow_eq_sum_stirlingSecond_mul_descFactorial k a

  simp_rw [hexp, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intros
  apply Finset.sum_congr rfl
  intros
  ring

theorem alternating_power_moment_zero (e a : ℕ) (ha : a < e) :
    (∑ k ∈ Finset.range (e + 1),
      (-1 : ℚ) ^ k * (e.choose k : ℚ) * (k : ℚ) ^ a) = 0 := by
  rw [alternating_power_expansion]
  apply Finset.sum_eq_zero
  intro r hr
  have hre : r < e := by have := Finset.mem_range.mp hr; omega
  rw [alternating_descFactorial_moment e r hre.le]
  simp [ne_of_lt hre]

#print axioms alternating_power_moment_zero

theorem alternating_power_moment_top (e : ℕ) :
    (∑ k ∈ Finset.range (e + 1),
      (-1 : ℚ) ^ k * (e.choose k : ℚ) * (k : ℚ) ^ e) =
      (-1 : ℚ) ^ e * (e.factorial : ℚ) := by
  rw [alternating_power_expansion, Finset.sum_range_succ]
  have hzero : (∑ r ∈ Finset.range e, (Nat.stirlingSecond e r : ℚ) *
      ∑ k ∈ Finset.range (e + 1),
        (-1 : ℚ) ^ k * (e.choose k : ℚ) * (k.descFactorial r : ℚ)) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    have hre : r < e := Finset.mem_range.mp hr
    rw [alternating_descFactorial_moment e r hre.le]
    simp [ne_of_lt hre]
  rw [hzero, zero_add, alternating_descFactorial_moment e e le_rfl]
  simp [Nat.stirlingSecond_self]

theorem alternating_polynomial_moment_zero (e : ℕ) (F : Polynomial ℚ)
    (hF : F.natDegree < e) :
    (∑ k ∈ Finset.range (e + 1), (-1 : ℚ) ^ k * (e.choose k : ℚ) * F.eval (k : ℚ)) = 0 := by
  have heval : ∀ k : ℕ, F.eval (k : ℚ) =
      ∑ a ∈ F.support, F.coeff a * (k : ℚ) ^ a := by
    intro k
    exact Polynomial.eval_eq_sum
  rw [show (∑ k ∈ Finset.range (e + 1),
      (-1 : ℚ) ^ k * (e.choose k : ℚ) * F.eval (k : ℚ)) =
      ∑ a ∈ F.support, F.coeff a * ∑ k ∈ Finset.range (e + 1),
        (-1 : ℚ) ^ k * (e.choose k : ℚ) * (k : ℚ) ^ a by
    simp_rw [heval, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intros
    apply Finset.sum_congr rfl
    intros
    ring]
  apply Finset.sum_eq_zero
  intro a ha
  have hae : a < e := lt_of_le_of_lt (Polynomial.le_natDegree_of_mem_supp a ha) hF
  rw [alternating_power_moment_zero e a hae, mul_zero]

#print axioms alternating_power_moment_top
#print axioms alternating_polynomial_moment_zero

/-- An order-e binomial difference extracts the degree-e coefficient. -/
theorem alternating_polynomial_moment (e : ℕ) (F : Polynomial ℚ)
    (hF : F.natDegree ≤ e) :
    (∑ k ∈ Finset.range (e + 1), (-1 : ℚ) ^ k * (e.choose k : ℚ) * F.eval (k : ℚ)) =
      (-1 : ℚ) ^ e * (e.factorial : ℚ) * F.coeff e := by
  have heval : ∀ k : ℕ, F.eval (k : ℚ) =
      ∑ a ∈ F.support, F.coeff a * (k : ℚ) ^ a := by
    intro k
    exact Polynomial.eval_eq_sum
  rw [show (∑ k ∈ Finset.range (e + 1),
      (-1 : ℚ) ^ k * (e.choose k : ℚ) * F.eval (k : ℚ)) =
      ∑ a ∈ F.support, F.coeff a * ∑ k ∈ Finset.range (e + 1),
        (-1 : ℚ) ^ k * (e.choose k : ℚ) * (k : ℚ) ^ a by
    simp_rw [heval, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intros
    apply Finset.sum_congr rfl
    intros
    ring]
  rw [Finset.sum_eq_single e]
  · rw [alternating_power_moment_top]
    ring
  · intro a ha hne
    have hae : a < e := by
      have := (Polynomial.le_natDegree_of_mem_supp a ha).trans hF
      omega
    rw [alternating_power_moment_zero e a hae, mul_zero]
  · intro hnot
    have hce : F.coeff e = 0 := by
      simpa only [Polynomial.mem_support_iff, not_not] using hnot
    simp [hce]

#print axioms alternating_polynomial_moment



/-- Coefficient moment of the univariate generating polynomial for B13.4. -/
noncomputable def polynomialMoment (b : ℕ) : Polynomial ℚ →ₗ[ℚ] ℚ :=
  Polynomial.lsum fun m => DistribSMul.toLinearMap ℚ ℚ ((-(m : ℚ)) ^ b)

theorem polynomialMoment_apply (b : ℕ) (F : Polynomial ℚ) :
    polynomialMoment b F = ∑ m ∈ F.support, F.coeff m * (-(m : ℚ)) ^ b := by
  simp [polynomialMoment, Polynomial.lsum, Polynomial.sum_def, smul_eq_mul, mul_comm]

theorem taylor_one_coeff_choose (r : ℕ) (F : Polynomial ℚ) :
    (Polynomial.taylor 1 F).coeff r =
      ∑ m ∈ F.support, (m.choose r : ℚ) * F.coeff m := by
  rw [Polynomial.taylor_coeff, Polynomial.hasseDeriv_apply, Polynomial.sum_def]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial, one_pow, mul_one]

theorem descFactorial_coeff_taylor (r : ℕ) (F : Polynomial ℚ) :
    (∑ m ∈ F.support, F.coeff m * (m.descFactorial r : ℚ)) =
      (r.factorial : ℚ) * (Polynomial.taylor 1 F).coeff r := by
  rw [taylor_one_coeff_choose, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  ring

theorem polynomialMoment_taylor (b : ℕ) (F : Polynomial ℚ) :
    polynomialMoment b F = (-1 : ℚ) ^ b *
      ∑ r ∈ Finset.range (b + 1),
        (Nat.stirlingSecond b r : ℚ) * (r.factorial : ℚ) *
          (Polynomial.taylor 1 F).coeff r := by
  have hexp : ∀ m : ℕ, (-(m : ℚ)) ^ b = (-1 : ℚ) ^ b *
      ∑ r ∈ Finset.range (b + 1),
        (Nat.stirlingSecond b r : ℚ) * (m.descFactorial r : ℚ) := by
    intro m
    rw [neg_pow]
    congr 1
    exact_mod_cast Nat.pow_eq_sum_stirlingSecond_mul_descFactorial m b
  rw [polynomialMoment_apply]
  calc
    (∑ m ∈ F.support, F.coeff m * (-(m : ℚ)) ^ b) =
        (-1 : ℚ) ^ b * ∑ r ∈ Finset.range (b + 1), (Nat.stirlingSecond b r : ℚ) *
          ∑ m ∈ F.support, F.coeff m * (m.descFactorial r : ℚ) := by
      simp_rw [hexp, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intros
      apply Finset.sum_congr rfl
      intros
      ring
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro r _
      rw [descFactorial_coeff_taylor]
      ring

theorem taylor_root_factor (d : ℕ) (Q : Polynomial ℚ) :
    Polynomial.taylor 1 ((1 - Polynomial.X) ^ d * Q) =
      Polynomial.C ((-1 : ℚ) ^ d) *
        (Polynomial.X ^ d * Polynomial.taylor 1 Q) := by
  have hlin : Polynomial.taylor (1 : ℚ) (1 - Polynomial.X) = -Polynomial.X := by
    simp [Polynomial.taylor_apply]
  have hpow : (-Polynomial.X : Polynomial ℚ) ^ d =
      Polynomial.C ((-1 : ℚ) ^ d) * Polynomial.X ^ d := by
    rw [neg_pow]
    congr 1
    simpa using (map_pow (Polynomial.C : ℚ →+* Polynomial ℚ) (-1 : ℚ) d).symm
  rw [Polynomial.taylor_mul, Polynomial.taylor_pow, hlin, hpow, mul_assoc]

theorem taylor_root_coeff_lt (d r : ℕ) (hr : r < d) (Q : Polynomial ℚ) :
    (Polynomial.taylor 1 ((1 - Polynomial.X) ^ d * Q)).coeff r = 0 := by
  rw [taylor_root_factor, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
  simp [not_le_of_gt hr]

theorem taylor_root_coeff_self (d : ℕ) (Q : Polynomial ℚ) :
    (Polynomial.taylor 1 ((1 - Polynomial.X) ^ d * Q)).coeff d =
      (-1 : ℚ) ^ d * Q.eval 1 := by
  rw [taylor_root_factor, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
  simp

/-- A root at 1 kills all coefficient moments below its multiplicity. -/
theorem polynomialMoment_root_zero (d b : ℕ) (hb : b < d) (Q : Polynomial ℚ) :
    polynomialMoment b ((1 - Polynomial.X) ^ d * Q) = 0 := by
  rw [polynomialMoment_taylor]
  have hzero : (∑ r ∈ Finset.range (b + 1),
      (Nat.stirlingSecond b r : ℚ) * (r.factorial : ℚ) *
        (Polynomial.taylor 1 ((1 - Polynomial.X) ^ d * Q)).coeff r) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    have hrd : r < d := by have := Finset.mem_range.mp hr; omega
    rw [taylor_root_coeff_lt d r hrd Q, mul_zero]
  rw [hzero, mul_zero]

/-- The first surviving coefficient moment is the factorial times the residual value at 1. -/
theorem polynomialMoment_root_top (d : ℕ) (Q : Polynomial ℚ) :
    polynomialMoment d ((1 - Polynomial.X) ^ d * Q) =
      (d.factorial : ℚ) * Q.eval 1 := by
  rw [polynomialMoment_taylor, Finset.sum_range_succ]
  have hzero : (∑ r ∈ Finset.range d,
      (Nat.stirlingSecond d r : ℚ) * (r.factorial : ℚ) *
        (Polynomial.taylor 1 ((1 - Polynomial.X) ^ d * Q)).coeff r) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    rw [taylor_root_coeff_lt d r (Finset.mem_range.mp hr) Q, mul_zero]
  rw [hzero, zero_add, taylor_root_coeff_self]
  simp only [Nat.stirlingSecond_self, Nat.cast_one, one_mul]
  have hsign : (-1 : ℚ) ^ d * (-1 : ℚ) ^ d = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    (-1 : ℚ) ^ d * ((d.factorial : ℚ) * ((-1 : ℚ) ^ d * Q.eval 1)) =
        ((-1 : ℚ) ^ d * (-1 : ℚ) ^ d) * ((d.factorial : ℚ) * Q.eval 1) := by ring
    _ = _ := by rw [hsign, one_mul]

#print axioms polynomialMoment_root_zero
#print axioms polynomialMoment_root_top




noncomputable def powerMomentSeries (a : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun m => (m : ℚ) ^ a

theorem shifted_geometric_choose (r m : ℕ) :
    PowerSeries.coeff m
      (PowerSeries.X ^ r * (PowerSeries.invOneSubPow ℚ (r + 1) : PowerSeries ℚ)) =
        (m.choose r : ℚ) := by
  rw [PowerSeries.coeff_X_pow_mul']
  split_ifs with hr
  · simp only [PowerSeries.invOneSubPow, PowerSeries.coeff_mk]
    rw [Nat.add_sub_of_le hr]
  · simp [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hr)]

theorem powerMomentSeries_stirling (a : ℕ) :
    powerMomentSeries a = ∑ r ∈ Finset.range (a + 1),
      PowerSeries.C ((Nat.stirlingSecond a r : ℚ) * (r.factorial : ℚ)) *
        (PowerSeries.X ^ r * (PowerSeries.invOneSubPow ℚ (r + 1) : PowerSeries ℚ)) := by
  ext m
  simp only [powerMomentSeries, PowerSeries.coeff_mk, map_sum, PowerSeries.coeff_C_mul,
    shifted_geometric_choose]
  calc
    (m : ℚ) ^ a = ∑ r ∈ Finset.range (a + 1),
        (Nat.stirlingSecond a r : ℚ) * (m.descFactorial r : ℚ) := by
      exact_mod_cast Nat.pow_eq_sum_stirlingSecond_mul_descFactorial m a
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
      ring

theorem one_sub_pow_mul_invOneSubPow (e d : ℕ) (hd : d ≤ e) :
    (1 - PowerSeries.X : PowerSeries ℚ) ^ e * PowerSeries.invOneSubPow ℚ d =
      (1 - PowerSeries.X : PowerSeries ℚ) ^ (e - d) := by
  have hunit : (1 - PowerSeries.X : PowerSeries ℚ) ^ d *
      PowerSeries.invOneSubPow ℚ d = 1 := by
    rw [← PowerSeries.invOneSubPow_inv_eq_one_sub_pow]
    exact (PowerSeries.invOneSubPow ℚ d).inv_val
  have heq : e = (e - d) + d := by omega
  rw [heq, pow_add, mul_assoc, hunit, mul_one]
  congr 1
  omega

noncomputable def triangleMomentPolynomial (e a t : ℕ) : Polynomial ℚ :=
  ∑ r ∈ Finset.range (a + 1), ∑ s ∈ Finset.range (t + 1),
    Polynomial.C ((Nat.stirlingSecond a r : ℚ) * (Nat.stirlingSecond t s : ℚ) *
      (r.factorial : ℚ) * (s.factorial : ℚ)) *
        (Polynomial.X ^ (r + s) * (1 - Polynomial.X) ^ (e - r - s - 2))

theorem triangleMomentPolynomial_series (e a t : ℕ) (hbound : a + t + 2 ≤ e) :
    (triangleMomentPolynomial e a t : PowerSeries ℚ) =
      (1 - PowerSeries.X) ^ e * powerMomentSeries a * powerMomentSeries t := by
  change Polynomial.coeToPowerSeries.ringHom (triangleMomentPolynomial e a t) = _
  rw [powerMomentSeries_stirling, powerMomentSeries_stirling]
  simp only [triangleMomentPolynomial, map_sum, map_mul, map_pow, map_sub, map_one]
  simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C, Polynomial.coe_X]
  conv_rhs =>
    rw [mul_assoc, Finset.sum_mul, Finset.mul_sum]
    simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  have hd : (r + 1) + (s + 1) ≤ e := by
    have := Finset.mem_range.mp hr
    have := Finset.mem_range.mp hs
    omega
  have hinv : (PowerSeries.invOneSubPow ℚ (r + 1) : PowerSeries ℚ) *
      PowerSeries.invOneSubPow ℚ (s + 1) =
        PowerSeries.invOneSubPow ℚ ((r + 1) + (s + 1)) := by
    exact_mod_cast (PowerSeries.invOneSubPow_add (S := ℚ) (d := r + 1) (s + 1)).symm
  have hexp : e - r - s - 2 = e - ((r + 1) + (s + 1)) := by omega
  rw [hexp]
  simp only [← map_mul]
  calc
    PowerSeries.C ((Nat.stirlingSecond a r : ℚ) * (Nat.stirlingSecond t s : ℚ) *
        (r.factorial : ℚ) * (s.factorial : ℚ)) *
        (PowerSeries.X ^ (r + s) * (1 - PowerSeries.X) ^ (e - ((r + 1) + (s + 1)))) =
        PowerSeries.C ((Nat.stirlingSecond a r : ℚ) * (Nat.stirlingSecond t s : ℚ) *
          (r.factorial : ℚ) * (s.factorial : ℚ)) * PowerSeries.X ^ (r + s) *
          ((1 - PowerSeries.X : PowerSeries ℚ) ^ e *
            (PowerSeries.invOneSubPow ℚ ((r + 1) + (s + 1)) : PowerSeries ℚ)) := by
      rw [one_sub_pow_mul_invOneSubPow e ((r + 1) + (s + 1)) hd]
      ring
    _ = _ := by
      rw [← hinv, pow_add]
      simp only [map_mul]
      ring

#print axioms triangleMomentPolynomial_series

theorem one_sub_X_pow_coeff (e m : ℕ) :
    PowerSeries.coeff m ((1 - PowerSeries.X : PowerSeries ℚ) ^ e) =
      (-1 : ℚ) ^ m * (e.choose m : ℚ) := by
  have hc : PowerSeries.coeff m ((1 + PowerSeries.X : PowerSeries ℚ) ^ e) =
      (e.choose m : ℚ) := by
    simpa only [← Polynomial.coe_pow, ← Polynomial.coe_one, ← Polynomial.coe_X,
      ← Polynomial.coe_add, Polynomial.coeff_coe] using Polynomial.coeff_one_add_X_pow ℚ e m
  have hrescale : PowerSeries.rescale (-1 : ℚ) ((1 + PowerSeries.X : PowerSeries ℚ) ^ e) =
      (1 - PowerSeries.X : PowerSeries ℚ) ^ e := by
    simp [map_pow, map_add, sub_eq_add_neg]
  rw [← hrescale, PowerSeries.coeff_rescale, hc]

theorem triangle_series_coefficient (e a t m : ℕ) :
    PowerSeries.coeff m ((1 - PowerSeries.X : PowerSeries ℚ) ^ e *
      powerMomentSeries a * powerMomentSeries t) =
      ∑ k ∈ Finset.range (m + 1), ∑ l ∈ Finset.range (m - k + 1),
        (-1 : ℚ) ^ k * (e.choose k : ℚ) * (l : ℚ) ^ a * ((m - k - l : ℕ) : ℚ) ^ t := by
  rw [mul_assoc, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp_rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    powerMomentSeries, PowerSeries.coeff_mk, one_sub_X_pow_coeff, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intros
  ring

theorem polynomialMoment_range (b N : ℕ) (F : Polynomial ℚ) (hF : F.natDegree < N) :
    polynomialMoment b F = ∑ m ∈ Finset.range N, F.coeff m * (-(m : ℚ)) ^ b := by
  rw [polynomialMoment_apply]
  have hsub : F.support ⊆ Finset.range N := by
    intro m hm
    exact Finset.mem_range.mpr ((Polynomial.le_natDegree_of_mem_supp m hm).trans_lt hF)
  apply Finset.sum_subset hsub
  intro m _ hnot
  have hc : F.coeff m = 0 := by
    simpa only [Polynomial.mem_support_iff, not_not] using hnot
  rw [hc, zero_mul]

#print axioms triangle_series_coefficient
#print axioms polynomialMoment_range

theorem polynomialMoment_C_mul (b : ℕ) (c : ℚ) (F : Polynomial ℚ) :
    polynomialMoment b (Polynomial.C c * F) = c * polynomialMoment b F := by
  rw [Polynomial.C_mul', map_smul, smul_eq_mul]

theorem triangle_term_moment_zero (e a t b r s : ℕ)
    (hr : r ≤ a) (hs : s ≤ t) (hbound : a + t + b + 2 < e) :
    polynomialMoment b
      (Polynomial.C ((Nat.stirlingSecond a r : ℚ) * (Nat.stirlingSecond t s : ℚ) *
        (r.factorial : ℚ) * (s.factorial : ℚ)) *
          (Polynomial.X ^ (r + s) * (1 - Polynomial.X) ^ (e - r - s - 2))) = 0 := by
  have hd : b < e - r - s - 2 := by omega
  rw [polynomialMoment_C_mul, mul_comm (Polynomial.X ^ (r + s))]
  rw [polynomialMoment_root_zero (e - r - s - 2) b hd, mul_zero]

theorem triangleMomentPolynomial_moment_zero (e a t b : ℕ)
    (hbound : a + t + b + 2 < e) :
    polynomialMoment b (triangleMomentPolynomial e a t) = 0 := by
  simp only [triangleMomentPolynomial, map_sum]
  apply Finset.sum_eq_zero
  intro r hr
  apply Finset.sum_eq_zero
  intro s hs
  exact triangle_term_moment_zero e a t b r s
    (Nat.le_of_lt_succ (Finset.mem_range.mp hr))
    (Nat.le_of_lt_succ (Finset.mem_range.mp hs)) hbound

theorem triangleMomentPolynomial_moment_top (e a t b : ℕ)
    (hbound : a + t + b + 2 = e) :
    polynomialMoment b (triangleMomentPolynomial e a t) =
      (a.factorial : ℚ) * (t.factorial : ℚ) * (b.factorial : ℚ) := by
  simp only [triangleMomentPolynomial, map_sum]
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single t]
    · have hd : e - a - t - 2 = b := by omega
      rw [polynomialMoment_C_mul, hd, mul_comm (Polynomial.X ^ (a + t)),
        polynomialMoment_root_top]
      simp [Nat.stirlingSecond_self]
    · intro s hs hne
      have hs' : s ≤ t := Nat.le_of_lt_succ (Finset.mem_range.mp hs)
      have hd : b < e - a - s - 2 := by omega
      rw [polynomialMoment_C_mul, mul_comm (Polynomial.X ^ (a + s)),
        polynomialMoment_root_zero (e - a - s - 2) b hd, mul_zero]
    · simp
  · intro r hr hne
    apply Finset.sum_eq_zero
    intro s hs
    have hr' : r ≤ a := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
    have hs' : s ≤ t := Nat.le_of_lt_succ (Finset.mem_range.mp hs)
    have hd : b < e - r - s - 2 := by omega
    rw [polynomialMoment_C_mul, mul_comm (Polynomial.X ^ (r + s)),
      polynomialMoment_root_zero (e - r - s - 2) b hd, mul_zero]
  · simp

#print axioms triangleMomentPolynomial_moment_zero
#print axioms triangleMomentPolynomial_moment_top

theorem triangleMomentPolynomial_degree (e a t : ℕ) (hbound : a + t + 2 ≤ e) :
    (triangleMomentPolynomial e a t).natDegree ≤ e - 2 := by
  unfold triangleMomentPolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro r hr
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro s hs
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  apply Polynomial.natDegree_mul_le.trans
  have hsub : (1 - Polynomial.X : Polynomial ℚ).natDegree ≤ 1 := by
    simpa using Polynomial.natDegree_sub_le (1 : Polynomial ℚ) Polynomial.X
  have hpow := Polynomial.natDegree_pow_le_of_le (e - r - s - 2) hsub
  simp only [Polynomial.natDegree_X_pow, mul_one] at hpow ⊢
  have := Finset.mem_range.mp hr
  have := Finset.mem_range.mp hs
  omega

#print axioms triangleMomentPolynomial_degree

/-- The actual finite triangular sum after eliminating the Koszul delta index. -/
noncomputable def triangleMoment (e a t b : ℕ) : ℚ :=
  ∑ m ∈ Finset.range (e - 1), ∑ k ∈ Finset.range (m + 1),
    ∑ l ∈ Finset.range (m - k + 1),
      (-1 : ℚ) ^ k * (e.choose k : ℚ) * (l : ℚ) ^ a *
        ((m - k - l : ℕ) : ℚ) ^ t * (-(m : ℚ)) ^ b

theorem triangleMoment_eq_polynomialMoment (e a t b : ℕ) (hbound : a + t + 2 ≤ e) :
    triangleMoment e a t b = polynomialMoment b (triangleMomentPolynomial e a t) := by
  have hdegree : (triangleMomentPolynomial e a t).natDegree < e - 1 := by
    have hd := triangleMomentPolynomial_degree e a t hbound
    omega
  rw [polynomialMoment_range b (e - 1) (triangleMomentPolynomial e a t) hdegree]
  unfold triangleMoment
  apply Finset.sum_congr rfl
  intro m _
  rw [← Polynomial.coeff_coe, triangleMomentPolynomial_series e a t hbound,
    triangle_series_coefficient]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_mul]

/-- Lower-degree triangular moments cancel. -/
theorem triangleMoment_zero (e a t b : ℕ) (hbound : a + t + b + 2 < e) :
    triangleMoment e a t b = 0 := by
  rw [triangleMoment_eq_polynomialMoment e a t b (by omega)]
  exact triangleMomentPolynomial_moment_zero e a t b hbound

/-- The first nonzero triangular moment is the product of the three factorials. -/
theorem triangleMoment_top (e a t b : ℕ) (hbound : a + t + b + 2 = e) :
    triangleMoment e a t b =
      (a.factorial : ℚ) * (t.factorial : ℚ) * (b.factorial : ℚ) := by
  rw [triangleMoment_eq_polynomialMoment e a t b (by omega)]
  exact triangleMomentPolynomial_moment_top e a t b hbound

#print axioms triangleMoment_zero
#print axioms triangleMoment_top



theorem triangleMomentPolynomial_coefficient (e a t m : ℕ) (hbound : a + t + 2 ≤ e) :
    (triangleMomentPolynomial e a t).coeff m =
      ∑ k ∈ Finset.range (m + 1), ∑ l ∈ Finset.range (m - k + 1),
        (-1 : ℚ) ^ k * (e.choose k : ℚ) * (l : ℚ) ^ a * ((m - k - l : ℕ) : ℚ) ^ t := by
  rw [← Polynomial.coeff_coe, triangleMomentPolynomial_series e a t hbound]
  exact triangle_series_coefficient e a t m

theorem shifted_power_expansion (p m l : ℕ) :
    (-(m : ℚ) - (l : ℚ)) ^ p =
      ∑ a ∈ Finset.range (p + 1), (p.choose a : ℚ) * (-1 : ℚ) ^ a *
        (-(m : ℚ)) ^ (p - a) * (l : ℚ) ^ a := by
  rw [show -(m : ℚ) - (l : ℚ) = -(l : ℚ) + -(m : ℚ) by ring, add_pow]
  apply Finset.sum_congr rfl
  intro a _
  rw [neg_pow]
  ring

noncomputable def shiftedSliceMoment (e p t m : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (m + 1), ∑ l ∈ Finset.range (m - k + 1),
    (-1 : ℚ) ^ k * (e.choose k : ℚ) * (-(m : ℚ) - (l : ℚ)) ^ p *
      ((m - k - l : ℕ) : ℚ) ^ t

theorem shiftedSliceMoment_expansion (e p t m : ℕ) (hbound : p + t + 2 ≤ e) :
    shiftedSliceMoment e p t m = ∑ a ∈ Finset.range (p + 1),
      (p.choose a : ℚ) * (-1 : ℚ) ^ a * (-(m : ℚ)) ^ (p - a) *
        (triangleMomentPolynomial e a t).coeff m := by
  calc
    shiftedSliceMoment e p t m =
        ∑ k ∈ Finset.range (m + 1), ∑ l ∈ Finset.range (m - k + 1),
          ∑ a ∈ Finset.range (p + 1),
            ((p.choose a : ℚ) * (-1 : ℚ) ^ a * (-(m : ℚ)) ^ (p - a)) *
              ((-1 : ℚ) ^ k * (e.choose k : ℚ) * (l : ℚ) ^ a *
                ((m - k - l : ℕ) : ℚ) ^ t) := by
      unfold shiftedSliceMoment
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      rw [shifted_power_expansion, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intros
      ring
    _ = ∑ k ∈ Finset.range (m + 1), ∑ a ∈ Finset.range (p + 1),
          ∑ l ∈ Finset.range (m - k + 1),
            ((p.choose a : ℚ) * (-1 : ℚ) ^ a * (-(m : ℚ)) ^ (p - a)) *
              ((-1 : ℚ) ^ k * (e.choose k : ℚ) * (l : ℚ) ^ a *
                ((m - k - l : ℕ) : ℚ) ^ t) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      have hab : a + t + 2 ≤ e := by have := Finset.mem_range.mp ha; omega
      rw [triangleMomentPolynomial_coefficient e a t m hab, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]

theorem shiftedSliceMoment_boundary_zero (e p t m : ℕ) (hbound : p + t + 2 ≤ e)
    (hm : e - 1 ≤ m) : shiftedSliceMoment e p t m = 0 := by
  rw [shiftedSliceMoment_expansion e p t m hbound]
  apply Finset.sum_eq_zero
  intro a ha
  have hab : a + t + 2 ≤ e := by have := Finset.mem_range.mp ha; omega
  have hd : (triangleMomentPolynomial e a t).natDegree < m := by
    have hd := triangleMomentPolynomial_degree e a t hab
    omega
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt hd, mul_zero]

#print axioms shiftedSliceMoment_boundary_zero



theorem segreCoeff_succ (P n : ℕ) :
    segreCoeff P (n + 1) = (P.choose (n + 1) : ℤ) - 2 * segreCoeff P n := by
  unfold segreCoeff
  rw [Finset.sum_range_succ]
  simp only [Nat.sub_self, pow_zero, mul_one]
  have hsum : (∑ k ∈ Finset.range (n + 1),
      (P.choose k : ℤ) * (-2 : ℤ) ^ (n + 1 - k)) =
      -2 * ∑ k ∈ Finset.range (n + 1), (P.choose k : ℤ) * (-2 : ℤ) ^ (n - k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have heq : n + 1 - k = (n - k) + 1 := by have := Finset.mem_range.mp hk; omega
    rw [heq, pow_succ]
    ring
  rw [hsum]
  ring

def alternatingSegreCoeff (P u : ℕ) : ℤ :=
  ∑ a ∈ Finset.range (u + 1), (-1 : ℤ) ^ a * ((P - 1 - a).choose (u - a) : ℤ)

theorem alternatingSegreCoeff_succ (P n : ℕ) (hP : n + 2 ≤ P) :
    alternatingSegreCoeff P (n + 1) =
      (P.choose (n + 1) : ℤ) - 2 * alternatingSegreCoeff P n := by
  let G : ℤ := ∑ a ∈ Finset.range (n + 2),
    (-1 : ℤ) ^ a * ((P - a).choose (n + 1 - a) : ℤ)
  have hpascal : ∀ a ≤ n,
      ((P - 1 - a).choose (n + 1 - a) : ℤ) +
        ((P - 1 - a).choose (n - a) : ℤ) = ((P - a).choose (n + 1 - a) : ℤ) := by
    intro a ha
    have hPa : P - a = (P - 1 - a) + 1 := by omega
    have hna : n + 1 - a = (n - a) + 1 := by omega
    rw [hPa, hna, Nat.choose_succ_succ, Nat.cast_add]
    ring
  have hFG : alternatingSegreCoeff P (n + 1) + alternatingSegreCoeff P n = G := by
    unfold alternatingSegreCoeff G
    rw [Finset.sum_range_succ]
    conv_rhs => rw [Finset.sum_range_succ]
    simp only [Nat.sub_self, Nat.choose_zero_right, Nat.cast_one, mul_one]
    rw [show (∑ a ∈ Finset.range (n + 1),
        (-1 : ℤ) ^ a * ((P - 1 - a).choose (n + 1 - a) : ℤ)) + (-1 : ℤ) ^ (n + 1) +
        (∑ a ∈ Finset.range (n + 1),
          (-1 : ℤ) ^ a * ((P - 1 - a).choose (n - a) : ℤ)) =
        (∑ a ∈ Finset.range (n + 1),
          (-1 : ℤ) ^ a * (((P - 1 - a).choose (n + 1 - a) : ℤ) +
            ((P - 1 - a).choose (n - a) : ℤ))) + (-1 : ℤ) ^ (n + 1) by
      simp only [mul_add, Finset.sum_add_distrib]
      ring]
    congr 1
    apply Finset.sum_congr rfl
    intro a ha
    rw [hpascal a (Nat.le_of_lt_succ (Finset.mem_range.mp ha))]
  have hG : G = (P.choose (n + 1) : ℤ) - alternatingSegreCoeff P n := by
    unfold G alternatingSegreCoeff
    rw [Finset.sum_range_succ']
    simp only [pow_zero, Nat.sub_zero, one_mul]
    have hshift : (∑ a ∈ Finset.range (n + 1),
        (-1 : ℤ) ^ (a + 1) * ((P - (a + 1)).choose (n + 1 - (a + 1)) : ℤ)) =
        -(∑ a ∈ Finset.range (n + 1),
          (-1 : ℤ) ^ a * ((P - 1 - a).choose (n - a) : ℤ)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro a _
      have hPa : P - (a + 1) = P - 1 - a := by omega
      have hna : n + 1 - (a + 1) = n - a := by omega
      rw [hPa, hna, pow_succ]
      ring
    rw [hshift]
    ring
  omega

theorem segreCoeff_alternating_choose (P u : ℕ) (hP : u + 1 ≤ P) :
    segreCoeff P u = ∑ a ∈ Finset.range (u + 1),
      (-1 : ℤ) ^ a * ((P - 1 - a).choose (u - a) : ℤ) := by
  change segreCoeff P u = alternatingSegreCoeff P u
  induction u with
  | zero => simp [segreCoeff, alternatingSegreCoeff]
  | succ u ih =>
    have hbound : u + 2 ≤ P := by omega
    rw [segreCoeff_succ, alternatingSegreCoeff_succ P u hbound,
      ih (by omega)]

#print axioms segreCoeff_alternating_choose

noncomputable def shiftedSlicePower (e p t b : ℕ) : ℚ :=
  ∑ m ∈ Finset.range (e - 1), shiftedSliceMoment e p t m * (-(m : ℚ)) ^ b

theorem shiftedSlicePower_expansion (e p t b : ℕ) (hbound : p + t + 2 ≤ e) :
    shiftedSlicePower e p t b = ∑ a ∈ Finset.range (p + 1),
      (p.choose a : ℚ) * (-1 : ℚ) ^ a * triangleMoment e a t (p - a + b) := by
  unfold shiftedSlicePower
  simp_rw [shiftedSliceMoment_expansion e p t _ hbound, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  have hab : a + t + 2 ≤ e := by have := Finset.mem_range.mp ha; omega
  have hdegree : (triangleMomentPolynomial e a t).natDegree < e - 1 := by
    have hd := triangleMomentPolynomial_degree e a t hab
    omega
  rw [triangleMoment_eq_polynomialMoment e a t (p - a + b) hab,
    polynomialMoment_range (p - a + b) (e - 1) _ hdegree, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [pow_add]
  ring

theorem shiftedSlicePower_zero (e p t b : ℕ) (hbound : p + t + b + 2 < e) :
    shiftedSlicePower e p t b = 0 := by
  rw [shiftedSlicePower_expansion e p t b (by omega)]
  apply Finset.sum_eq_zero
  intro a ha
  have ha' : a ≤ p := by have := Finset.mem_range.mp ha; omega
  rw [triangleMoment_zero e a t (p - a + b) (by omega), mul_zero]

theorem shiftedSlicePower_top (e p t b : ℕ) (hbound : p + t + b + 2 = e) :
    shiftedSlicePower e p t b = ∑ a ∈ Finset.range (p + 1),
      (p.choose a : ℚ) * (-1 : ℚ) ^ a *
        ((a.factorial : ℚ) * (t.factorial : ℚ) * ((p - a + b).factorial : ℚ)) := by
  rw [shiftedSlicePower_expansion e p t b (by omega)]
  apply Finset.sum_congr rfl
  intro a ha
  have ha' : a ≤ p := by have := Finset.mem_range.mp ha; omega
  rw [triangleMoment_top e a t (p - a + b) (by omega)]

noncomputable def shiftedSlicePolynomial (e p t : ℕ) (F : Polynomial ℚ) : ℚ :=
  ∑ m ∈ Finset.range (e - 1), shiftedSliceMoment e p t m * F.eval (m : ℚ)

theorem shiftedSlicePolynomial_expansion (e p t : ℕ) (F : Polynomial ℚ) :
    shiftedSlicePolynomial e p t F = ∑ b ∈ F.support,
      F.coeff b * (-1 : ℚ) ^ b * shiftedSlicePower e p t b := by
  have hexp : ∀ m : ℕ, F.eval (m : ℚ) =
      ∑ b ∈ F.support, F.coeff b * ((-1 : ℚ) ^ b * (-(m : ℚ)) ^ b) := by
    intro m
    rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
    apply Finset.sum_congr rfl
    intro b _
    rw [← mul_pow]
    congr 2
    ring
  unfold shiftedSlicePolynomial shiftedSlicePower
  simp_rw [hexp, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intros
  ring

theorem shiftedSlicePolynomial_top (e p t d : ℕ) (F : Polynomial ℚ)
    (hbound : p + t + d + 2 = e) (hF : F.natDegree ≤ d) :
    shiftedSlicePolynomial e p t F = F.coeff d * (-1 : ℚ) ^ d *
      ∑ a ∈ Finset.range (p + 1), (p.choose a : ℚ) * (-1 : ℚ) ^ a *
        ((a.factorial : ℚ) * (t.factorial : ℚ) * ((p - a + d).factorial : ℚ)) := by
  rw [shiftedSlicePolynomial_expansion, Finset.sum_eq_single d]
  · rw [shiftedSlicePower_top e p t d hbound]
  · intro b hb hbd
    have hb' : b < d := by
      have := (Polynomial.le_natDegree_of_mem_supp b hb).trans hF
      omega
    rw [shiftedSlicePower_zero e p t b (by omega), mul_zero]
  · intro hd
    have hc : F.coeff d = 0 := by simpa only [Polynomial.mem_support_iff, not_not] using hd
    rw [hc, zero_mul, zero_mul]

theorem shiftedSlicePolynomial_zero (e p t d : ℕ) (F : Polynomial ℚ)
    (hbound : p + t + d + 2 < e) (hF : F.natDegree ≤ d) :
    shiftedSlicePolynomial e p t F = 0 := by
  rw [shiftedSlicePolynomial_expansion]
  apply Finset.sum_eq_zero
  intro b hb
  have hb' := (Polynomial.le_natDegree_of_mem_supp b hb).trans hF
  rw [shiftedSlicePower_zero e p t b (by omega), mul_zero]

#print axioms shiftedSlicePower_top
#print axioms shiftedSlicePolynomial_top
#print axioms shiftedSlicePolynomial_zero


theorem factorial_segre_term (p d a : ℕ) (ha : a ≤ p) :
    (p.choose a : ℚ) * (a.factorial : ℚ) * ((p - a + d).factorial : ℚ) / (d.factorial : ℚ) =
      (p.factorial : ℚ) * ((d + p - a).choose (p - a) : ℚ) := by
  have h1 : (p.choose a : ℚ) * (a.factorial : ℚ) * ((p - a).factorial : ℚ) = (p.factorial : ℚ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial ha
  have h2 : ((p - a + d).choose (p - a) : ℚ) * ((p - a).factorial : ℚ) *
      (d.factorial : ℚ) = ((p - a + d).factorial : ℚ) := by
    have hh := Nat.choose_mul_factorial_mul_factorial (n := p - a + d) (k := p - a) (by omega)
    simpa only [Nat.add_sub_cancel_left, Nat.cast_mul] using (show
      ((p - a + d).choose (p - a) : ℚ) * ((p - a).factorial : ℚ) *
        ((p - a + d - (p - a)).factorial : ℚ) = ((p - a + d).factorial : ℚ) by exact_mod_cast hh)
  have hd : (d.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
  rw [show d + p - a = p - a + d by omega]
  apply (div_eq_iff hd).mpr
  rw [← h2]
  linear_combination (((p - a + d).choose (p - a) : ℚ) * (d.factorial : ℚ)) * h1

/-- Factorial-normalized top slice equals the scalar Segre coefficient. -/
theorem normalized_shiftedSlicePolynomial_top (e p t d K j : ℕ) (F : Polynomial ℚ)
    (hbound : p + t + d + 2 = e) (hF : F.natDegree ≤ d)
    (hcoeff : F.coeff d = (-1 : ℚ) ^ d / ((K.factorial : ℚ) * (d.factorial : ℚ))) :
    (K.factorial : ℚ) * (j.factorial : ℚ) * ((t + j).choose j : ℚ) *
        shiftedSlicePolynomial e p t F =
      (p.factorial : ℚ) * ((t + j).factorial : ℚ) * (segreCoeff (d + p + 1) p : ℚ) := by
  rw [shiftedSlicePolynomial_top e p t d F hbound hF]
  have hK : (K.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero K
  have hd : (d.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
  have hlead : (K.factorial : ℚ) * F.coeff d * (-1 : ℚ) ^ d = 1 / (d.factorial : ℚ) := by
    rw [hcoeff]
    field_simp
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  have hq : (j.factorial : ℚ) * ((t + j).choose j : ℚ) * (t.factorial : ℚ) = ((t + j).factorial : ℚ) := by
    have hh := Nat.choose_mul_factorial_mul_factorial (n := t + j) (k := j) (by omega)
    have hhQ : ((t + j).choose j : ℚ) * (j.factorial : ℚ) * (t.factorial : ℚ) = ((t + j).factorial : ℚ) := by
      exact_mod_cast (show (t + j).choose j * j.factorial * t.factorial = (t + j).factorial by
        simpa only [Nat.add_sub_cancel_right] using hh)
    nlinarith [hhQ]
  have hsegre : (segreCoeff (d + p + 1) p : ℚ) =
      ∑ a ∈ Finset.range (p + 1), (-1 : ℚ) ^ a * ((d + p - a).choose (p - a) : ℚ) := by
    have hh := segreCoeff_alternating_choose (d + p + 1) p (by omega)
    simpa only [Nat.add_sub_cancel_right] using (show (segreCoeff (d + p + 1) p : ℚ) =
      ∑ a ∈ Finset.range (p + 1), (-1 : ℚ) ^ a * ((d + p + 1 - 1 - a).choose (p - a) : ℚ) by exact_mod_cast hh)
  rw [hsegre]
  calc
    _ = ((j.factorial : ℚ) * ((t + j).choose j : ℚ)) *
        ((K.factorial : ℚ) * F.coeff d * (-1 : ℚ) ^ d) *
          ∑ a ∈ Finset.range (p + 1), (p.choose a : ℚ) * (-1 : ℚ) ^ a *
            ((a.factorial : ℚ) * (t.factorial : ℚ) * ((p - a + d).factorial : ℚ)) := by ring
    _ = _ := by
      rw [hlead, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      have ha' : a ≤ p := by have := Finset.mem_range.mp ha; omega
      calc
        _ = ((j.factorial : ℚ) * ((t + j).choose j : ℚ) * (t.factorial : ℚ)) *
            (-1 : ℚ) ^ a * ((p.choose a : ℚ) * (a.factorial : ℚ) *
              ((p - a + d).factorial : ℚ) / (d.factorial : ℚ)) := by ring
        _ = _ := by rw [hq, factorial_segre_term p d a ha']; ring

#print axioms factorial_segre_term
#print axioms normalized_shiftedSlicePolynomial_top

theorem triangle_slice_sum (E m delta : ℕ) (hdelta : delta ≤ m) (hm : m ≤ E)
    (f : ℕ → ℕ → ℕ → ℚ) :
    (∑ k ∈ Finset.range (E + 1), ∑ l ∈ Finset.range (m + 1),
      ∑ beta ∈ Finset.range (m + 1),
        if delta + k + l + beta = m then f k l beta else 0) =
      ∑ k ∈ Finset.range (m - delta + 1), ∑ l ∈ Finset.range (m - delta - k + 1),
        f k l (m - delta - k - l) := by
  have hksub : Finset.range (m - delta + 1) ⊆ Finset.range (E + 1) := by
    apply Finset.range_mono
    omega
  calc
    _ = ∑ k ∈ Finset.range (m - delta + 1), ∑ l ∈ Finset.range (m + 1),
        ∑ beta ∈ Finset.range (m + 1),
          if delta + k + l + beta = m then f k l beta else 0 := by
      symm
      apply Finset.sum_subset hksub
      intro k _ hk
      have hk' : m - delta < k := by have := hk; simp only [Finset.mem_range, not_lt] at this; omega
      apply Finset.sum_eq_zero
      intro l _
      apply Finset.sum_eq_zero
      intro beta _
      simp only [if_neg (by omega : delta + k + l + beta ≠ m)]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k ≤ m - delta := by have := Finset.mem_range.mp hk; omega
      have hlsub : Finset.range (m - delta - k + 1) ⊆ Finset.range (m + 1) := by
        apply Finset.range_mono
        omega
      calc
        _ = ∑ l ∈ Finset.range (m - delta - k + 1),
            ∑ beta ∈ Finset.range (m + 1),
              if delta + k + l + beta = m then f k l beta else 0 := by
          symm
          apply Finset.sum_subset hlsub
          intro l _ hl
          have hl' : m - delta - k < l := by have := hl; simp only [Finset.mem_range, not_lt] at this; omega
          apply Finset.sum_eq_zero
          intro beta _
          simp only [if_neg (by omega : delta + k + l + beta ≠ m)]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro l hl
          have hl' : l ≤ m - delta - k := by have := Finset.mem_range.mp hl; omega
          rw [Finset.sum_eq_single (m - delta - k - l)]
          · simp only [if_pos (by omega : delta + k + l + (m - delta - k - l) = m)]
          · intro beta _ hb
            simp only [if_neg (by omega : delta + k + l + beta ≠ m)]
          · intro hnot
            exfalso
            apply hnot
            apply Finset.mem_range.mpr
            omega

#print axioms triangle_slice_sum

theorem slice_summation_parts (e : ℕ) (he : 1 ≤ e) (A B : ℕ → ℚ) :
    (∑ m ∈ Finset.range e, (A m - if m = 0 then 0 else A (m - 1)) * B m) =
      (∑ m ∈ Finset.range (e - 1), A m * (B m - B (m + 1))) +
        A (e - 1) * B (e - 1) := by
  have heq : e = (e - 1) + 1 := by omega
  have hleft : (∑ m ∈ Finset.range e, A m * B m) =
      (∑ m ∈ Finset.range (e - 1), A m * B m) + A (e - 1) * B (e - 1) := by
    conv_lhs => rw [heq, Finset.sum_range_succ]
  have hright : (∑ m ∈ Finset.range e, (if m = 0 then 0 else A (m - 1)) * B m) =
      ∑ m ∈ Finset.range (e - 1), A m * B (m + 1) := by
    conv_lhs => rw [heq, Finset.sum_range_succ']
    simp only [ite_true, zero_mul, Nat.add_sub_cancel, Nat.add_one_ne_zero, ite_false, add_zero]
  calc
    _ = (∑ m ∈ Finset.range e, A m * B m) -
        (∑ m ∈ Finset.range e, (if m = 0 then 0 else A (m - 1)) * B m) := by
      simp only [sub_mul, Finset.sum_sub_distrib]
    _ = _ := by
      rw [hleft, hright]
      simp only [mul_sub, Finset.sum_sub_distrib]
      ring

#print axioms slice_summation_parts

noncomputable def signedExteriorSlice (e m delta p t : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (e + 1), ∑ l ∈ Finset.range (m + 1),
    ∑ beta ∈ Finset.range (m + 1),
      if delta + k + l + beta = m then
        (-1 : ℚ) ^ (delta + k) * (e.choose k : ℚ) *
          (-((k : ℚ) + 2 * (l : ℚ) + (beta : ℚ))) ^ p * (beta : ℚ) ^ t
      else 0

theorem signedExteriorSlice_eq (e m delta p t : ℕ) (hdelta : delta ≤ m) (hm : m ≤ e) :
    signedExteriorSlice e m delta p t = (-1 : ℚ) ^ delta *
      shiftedSliceMoment e p t (m - delta) := by
  unfold signedExteriorSlice
  rw [triangle_slice_sum e m delta hdelta hm]
  unfold shiftedSliceMoment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  have hk' : k ≤ m - delta := by have := Finset.mem_range.mp hk; omega
  have hl' : l ≤ m - delta - k := by have := Finset.mem_range.mp hl; omega
  have hsum : (k : ℚ) + (l : ℚ) + ((m - delta - k - l : ℕ) : ℚ) = (m - delta : ℕ) := by
    exact_mod_cast (show k + l + (m - delta - k - l) = m - delta by omega)
  have hshift : -((k : ℚ) + 2 * (l : ℚ) + ((m - delta - k - l : ℕ) : ℚ)) =
      -((m - delta : ℕ) : ℚ) - (l : ℚ) := by linarith
  rw [hshift, pow_add]
  ring

theorem signedExteriorSlice_zero (e p t : ℕ) : signedExteriorSlice e 0 1 p t = 0 := by
  unfold signedExteriorSlice
  apply Finset.sum_eq_zero
  intro k _
  apply Finset.sum_eq_zero
  intro l _
  apply Finset.sum_eq_zero
  intro beta _
  simp only [if_neg (by omega : 1 + k + l + beta ≠ 0)]

theorem signedExteriorSlice_pair (e m p t : ℕ) (hm : m ≤ e) :
    signedExteriorSlice e m 0 p t + signedExteriorSlice e m 1 p t =
      shiftedSliceMoment e p t m - if m = 0 then 0 else shiftedSliceMoment e p t (m - 1) := by
  rw [signedExteriorSlice_eq e m 0 p t (by omega) hm]
  simp only [pow_zero, Nat.sub_zero, one_mul]
  by_cases hm0 : m = 0
  · subst m
    rw [signedExteriorSlice_zero]
    simp
  · rw [signedExteriorSlice_eq e m 1 p t (by omega) hm, if_neg hm0]
    simp only [pow_one, neg_one_mul]
    ring

#print axioms signedExteriorSlice_pair

end DistinctDistances.TrackB.IncidenceMoments
