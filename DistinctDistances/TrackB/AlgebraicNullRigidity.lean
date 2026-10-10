import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.LinearCombination

/-!
An algebraic specialization of conc:degree's local null rigidity
(concentration.tex:970–985). On the function field, extend the coordinate partial
derivations through the generically finite separable coordinate projection.
The geometric chart, extension/commutation, and constant-field assertions are
separate inputs; no function-field or degree model is defined in this file.
-/

namespace DistinctDistances.TrackB

set_option autoImplicit false

open scoped BigOperators

variable {K : Type*} [Field K] [Algebra ℂ K] [CharZero K]

/-- B26's Hessian argument in a field with commuting coordinate derivations. -/
theorem commuting_derivation_gram_hessian_zero (r : ℕ)
    (δ : Fin r → Derivation ℂ K K) (w : Fin r → K)
    (hcomm : ∀ i j x, δ i (δ j x) = δ j (δ i x))
    (hgram : ∀ i j, (∑ l, δ i (w l) * δ j (w l)) = if i = j then 1 else 0) :
    ∀ i j l, δ i (δ j (w l)) = 0 := by
  classical
  let S : Fin r → Fin r → Fin r → K :=
    fun i j k => ∑ l, δ i (δ j (w l)) * δ k (w l)
  have hS : ∀ i j k, S i j k = S j i k := by
    intro i j k
    exact Finset.sum_congr rfl fun l _ => congrArg (fun x => x * δ k (w l)) (hcomm i j (w l))
  have hdiff : ∀ i j k, S i j k + S i k j = 0 := by
    intro i j k
    have hd := congrArg (δ i) (hgram j k)
    have hrhs : δ i (if j = k then (1 : K) else 0) = 0 := by
      split_ifs <;> simp
    rw [hrhs] at hd
    simp only [map_sum, Derivation.leibniz, smul_eq_mul] at hd
    simpa only [S, Finset.sum_add_distrib, mul_comm, add_comm] using hd
  have hzero : ∀ i j k, S i j k = 0 := by
    intro i j k
    have e1 := hdiff i j k
    have e2 := hdiff j i k
    have e3 := hdiff k i j
    rw [hS j i k] at e2
    rw [hS k i j, hS k j i] at e3
    have htwo : (2 : K) * S i j k = 0 := by
      linear_combination e1 + e2 - e3
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  let M : Matrix (Fin r) (Fin r) K := fun i l => δ i (w l)
  have hM : M * M.transpose = 1 := by
    ext i j
    change (∑ l, δ i (w l) * δ j (w l)) = if i = j then 1 else 0
    exact hgram i j
  have hunit : IsUnit M :=
    (Matrix.isUnit_iff_isUnit_det M).mpr (Matrix.isUnit_det_of_right_inverse hM)
  have hinj : Function.Injective M.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr hunit
  intro i j l
  let H : Fin r → K := fun k => δ i (δ j (w k))
  have hMH : M.mulVec H = 0 := by
    funext k
    simpa only [Matrix.mulVec, dotProduct, M, H, S, mul_comm, Pi.zero_apply] using hzero i j k
  have hH : H = 0 := hinj (hMH.trans (Matrix.mulVec_zero M).symm)
  exact congrFun hH l

/-- B26's affine conclusion in the function field. Common constants must really be
the base field; this condition must be proved for the geometric application. -/
theorem commuting_derivation_gram_affine (r : ℕ)
    (δ : Fin r → Derivation ℂ K K) (u w : Fin r → K)
    (hcomm : ∀ i j x, δ i (δ j x) = δ j (δ i x))
    (hcoords : ∀ i j, δ i (u j) = if i = j then 1 else 0)
    (hgram : ∀ i j, (∑ l, δ i (w l) * δ j (w l)) = if i = j then 1 else 0)
    (hconstants : ∀ x : K, (∀ i, δ i x = 0) → ∃ c : ℂ, algebraMap ℂ K c = x) :
    ∃ a : Fin r → Fin r → ℂ, ∃ b : Fin r → ℂ,
      ∀ l, w l = algebraMap ℂ K (b l) + ∑ i, algebraMap ℂ K (a l i) * u i := by
  classical
  have hH := commuting_derivation_gram_hessian_zero r δ w hcomm hgram
  have hslopes : ∀ l i, ∃ c : ℂ, algebraMap ℂ K c = δ i (w l) :=
    fun l i => hconstants (δ i (w l)) (fun j => hH j i l)
  choose a ha using hslopes
  have hres : ∀ l j, δ j (w l - ∑ i, algebraMap ℂ K (a l i) * u i) = 0 := by
    intro l j
    simp only [map_sub, map_sum, Derivation.leibniz, Derivation.map_algebraMap,
      smul_eq_mul, hcoords, mul_ite, mul_one, mul_zero, add_zero]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [ha l j]
    exact sub_self _
  choose b hb using fun l => hconstants
    (w l - ∑ i, algebraMap ℂ K (a l i) * u i) (hres l)
  refine ⟨a, b, ?_⟩
  intro l
  linear_combination -hb l

#print axioms commuting_derivation_gram_hessian_zero
#print axioms commuting_derivation_gram_affine

end DistinctDistances.TrackB
