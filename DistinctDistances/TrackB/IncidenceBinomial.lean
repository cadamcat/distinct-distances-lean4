import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! The rational point-binomial and its shift coefficients for the explicit B13.4
Koszul transform (concentration.tex:704–748). The actual multivariate-product bridge
lives in IncidenceHilbert.lean. -/

namespace DistinctDistances.TrackB.IncidenceBinomial
open scoped BigOperators
noncomputable section
set_option autoImplicit false

def pointBinomial (n : ℕ) (s : ℚ) : Polynomial ℚ :=
  Polynomial.C ((n.factorial : ℚ)⁻¹) *
    ∏ k ∈ Finset.range n, (Polynomial.X + Polynomial.C ((n : ℚ) - s - (k : ℚ)))

theorem pointBinomial_pascal (n : ℕ) (s : ℚ) :
    pointBinomial (n + 1) s - pointBinomial (n + 1) (s + 1) = pointBinomial n s := by
  let F : Polynomial ℚ := ∏ k ∈ Finset.range n,
    (Polynomial.X + Polynomial.C ((n : ℚ) - s - (k : ℚ)))
  have hleft : (∏ k ∈ Finset.range (n + 1),
      (Polynomial.X + Polynomial.C (((n + 1 : ℕ) : ℚ) - s - (k : ℚ)))) =
      (Polynomial.X + Polynomial.C ((n : ℚ) + 1 - s)) * F := by
    rw [Finset.prod_range_succ']
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, sub_zero]
    rw [mul_comm]
    congr 1
    apply Finset.prod_congr rfl
    intro k _
    congr 2
    ring
  have hright : (∏ k ∈ Finset.range (n + 1),
      (Polynomial.X + Polynomial.C (((n + 1 : ℕ) : ℚ) - (s + 1) - (k : ℚ)))) =
      F * (Polynomial.X + Polynomial.C (-s)) := by
    rw [Finset.prod_range_succ]
    simp only [Nat.cast_add, Nat.cast_one]
    congr 1
    · apply Finset.prod_congr rfl
      intro k _
      congr 2
      ring
    · congr 2
      ring
  unfold pointBinomial
  rw [hleft, hright]
  change Polynomial.C _ * ((Polynomial.X + Polynomial.C _) * F) -
      Polynomial.C _ * (F * (Polynomial.X + Polynomial.C _)) = Polynomial.C _ * F
  have hn : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hs : (n : ℚ) + 1 ≠ 0 := by positivity
  have hscalar : (((n + 1).factorial : ℚ)⁻¹) * ((n : ℚ) + 1) = (n.factorial : ℚ)⁻¹ := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp
  calc
    _ = Polynomial.C ((((n + 1).factorial : ℚ)⁻¹) * ((n : ℚ) + 1)) * F := by
      simp only [map_add, map_sub, map_mul, map_one, map_neg]
      ring
    _ = _ := by rw [hscalar]


theorem pointBinomial_taylor (n : ℕ) (s : ℚ) :
    pointBinomial n s = Polynomial.taylor (-s) (pointBinomial n 0) := by
  unfold pointBinomial
  rw [Polynomial.taylor_apply, Polynomial.mul_comp, Polynomial.C_comp,
    Polynomial.prod_comp]
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  simp only [Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp, sub_zero]
  simp only [map_sub, map_neg]
  ring

theorem pointBinomial_degree (n : ℕ) (s : ℚ) : (pointBinomial n s).natDegree = n := by
  have hfac : ((n.factorial : ℚ)⁻¹) ≠ 0 := inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero n)
  unfold pointBinomial
  rw [Polynomial.natDegree_C_mul hfac]
  rw [Polynomial.natDegree_prod_of_monic]
  · simp only [Polynomial.natDegree_X_add_C, Finset.sum_const, Finset.card_range,
      smul_eq_mul, mul_one]
  · intro k _
    exact Polynomial.monic_X_add_C _

theorem pointBinomial_leadingCoeff (n : ℕ) (s : ℚ) :
    (pointBinomial n s).leadingCoeff = (n.factorial : ℚ)⁻¹ := by
  unfold pointBinomial
  simp only [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
    Polynomial.leadingCoeff_prod, Polynomial.leadingCoeff_X_add_C,
    Finset.prod_const_one, mul_one]

/-- Polynomial in the shift s giving the coefficient of the point variable. -/
def pointCoefficientPolynomial (n K : ℕ) : Polynomial ℚ :=
  (Polynomial.hasseDeriv K (pointBinomial n 0)).comp (-Polynomial.X)

theorem pointCoefficientPolynomial_eval (n K : ℕ) (s : ℚ) :
    (pointCoefficientPolynomial n K).eval s = (pointBinomial n s).coeff K := by
  rw [pointBinomial_taylor, Polynomial.taylor_coeff]
  simp [pointCoefficientPolynomial, Polynomial.eval_comp]

theorem pointCoefficientPolynomial_degree (n K : ℕ) :
    (pointCoefficientPolynomial n K).natDegree = n - K := by
  unfold pointCoefficientPolynomial
  rw [Polynomial.natDegree_comp, Polynomial.natDegree_neg, Polynomial.natDegree_X,
    mul_one, Polynomial.natDegree_hasseDeriv, pointBinomial_degree]

theorem pointCoefficientPolynomial_top (n K : ℕ) (hK : K ≤ n) :
    (pointCoefficientPolynomial n K).coeff (n - K) =
      (-1 : ℚ) ^ (n - K) / ((K.factorial : ℚ) * ((n - K).factorial : ℚ)) := by
  have hd : (Polynomial.hasseDeriv K (pointBinomial n 0)).natDegree = n - K := by
    rw [Polynomial.natDegree_hasseDeriv, pointBinomial_degree]
  have hcomp := Polynomial.coeff_comp_degree_mul_degree
    (p := Polynomial.hasseDeriv K (pointBinomial n 0))
    (q := (-Polynomial.X : Polynomial ℚ)) (by simp)
  simp only [Polynomial.natDegree_neg, Polynomial.natDegree_X, mul_one, hd,
    Polynomial.leadingCoeff_neg, Polynomial.leadingCoeff_X] at hcomp
  rw [pointCoefficientPolynomial, hcomp, Polynomial.leadingCoeff, hd,
    Polynomial.hasseDeriv_coeff]
  have hadd : n - K + K = n := by omega
  rw [hadd]
  have hb : (pointBinomial n 0).coeff n = (n.factorial : ℚ)⁻¹ := by
    have hb0 := Polynomial.coeff_natDegree (p := pointBinomial n 0)
    rw [pointBinomial_degree, pointBinomial_leadingCoeff] at hb0
    exact hb0
  rw [hb]
  have hchoose := Nat.choose_mul_factorial_mul_factorial hK
  have hchooseQ : (n.choose K : ℚ) * (K.factorial : ℚ) * ((n - K).factorial : ℚ) = (n.factorial : ℚ) := by
    exact_mod_cast hchoose
  have hn : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hKfac : (K.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero K
  have hdfac : ((n - K).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n - K)
  field_simp
  exact hchooseQ

#print axioms pointBinomial_pascal
#print axioms pointCoefficientPolynomial_eval
#print axioms pointCoefficientPolynomial_degree
#print axioms pointCoefficientPolynomial_top

end
end DistinctDistances.TrackB.IncidenceBinomial
