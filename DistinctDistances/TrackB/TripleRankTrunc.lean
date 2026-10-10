import DistinctDistances.TrackB.IncidenceMoments
import DistinctDistances.TrackB.IncidenceHilbert
import Mathlib.NumberTheory.Bernoulli

/-!
(P4) Truncation helpers: Faulhaber polynomials and the Koszul vanishing above the rank.
Pure combinatorics; no geometry.
-/

namespace DistinctDistances.TrackB
namespace TripleRankTrunc

set_option autoImplicit false
open scoped BigOperators

/-- Faulhaber polynomial: `S_p(n) = ∑_{β < n} β ^ p`. -/
noncomputable def faulhaberPoly (p : ℕ) : Polynomial ℚ :=
  ∑ i ∈ Finset.range (p + 1),
    Polynomial.C (bernoulli i * ((p + 1).choose i : ℚ) / (p + 1 : ℚ)) *
      Polynomial.X ^ (p + 1 - i)

theorem faulhaber_eval (p n : ℕ) :
    (faulhaberPoly p).eval (n : ℚ) = ∑ β ∈ Finset.range n, (β : ℚ) ^ p := by
  unfold faulhaberPoly
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  rw [sum_range_pow n p]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem faulhaber_natDegree_le (p : ℕ) : (faulhaberPoly p).natDegree ≤ p + 1 := by
  unfold faulhaberPoly
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  calc (Polynomial.C (bernoulli i * ((p + 1).choose i : ℚ) / (p + 1 : ℚ)) *
      Polynomial.X ^ (p + 1 - i)).natDegree
      ≤ (Polynomial.X ^ (p + 1 - i) : Polynomial ℚ).natDegree := by
        apply Polynomial.natDegree_C_mul_le
    _ = p + 1 - i := Polynomial.natDegree_X_pow _
    _ ≤ p + 1 := Nat.sub_le _ _

theorem faulhaber_zero (p : ℕ) : (faulhaberPoly p).eval 0 = 0 := by
  have h := faulhaber_eval p 0
  simpa using h

/-- Degree of `C c - X` is one. -/
theorem degree_C_sub_X (c : ℚ) : (Polynomial.C c - Polynomial.X : Polynomial ℚ).degree = 1 := by
  have h1 : (Polynomial.C c : Polynomial ℚ).degree < (Polynomial.X : Polynomial ℚ).degree := by
    calc (Polynomial.C c : Polynomial ℚ).degree ≤ 0 := Polynomial.degree_C_le
      _ < (Polynomial.X : Polynomial ℚ).degree := by
          rw [Polynomial.degree_X]
          simp
  have heq : Polynomial.C c - Polynomial.X = -(Polynomial.X - Polynomial.C c) := by ring
  rw [heq, Polynomial.degree_neg]
  exact Polynomial.degree_X_sub_C c

theorem degree_X_add_C (c : ℚ) : (Polynomial.X + Polynomial.C c : Polynomial ℚ).degree = 1 := by
  have heq : Polynomial.X + Polynomial.C c = Polynomial.X - Polynomial.C (-c) := by
    simp
  rw [heq]
  exact Polynomial.degree_X_sub_C _

theorem natDegree_X_add_C (c : ℚ) :
    (Polynomial.X + Polynomial.C c : Polynomial ℚ).natDegree = 1 :=
  Polynomial.natDegree_eq_of_degree_eq_some (degree_X_add_C c)

theorem leadingCoeff_X_add_C (c : ℚ) :
    (Polynomial.X + Polynomial.C c : Polynomial ℚ).leadingCoeff = 1 := by
  have h : (Polynomial.X + Polynomial.C c : Polynomial ℚ).coeff 1 = 1 := by
    simp
  rw [Polynomial.leadingCoeff, natDegree_X_add_C]
  exact h

theorem natDegree_comp_X_add_C (P : Polynomial ℚ) (c : ℚ) :
    (P.comp (Polynomial.X + Polynomial.C c)).natDegree = P.natDegree := by
  rw [Polynomial.natDegree_comp, natDegree_X_add_C, mul_one]

theorem leadingCoeff_comp_X_add_C (P : Polynomial ℚ) (c : ℚ) :
    (P.comp (Polynomial.X + Polynomial.C c)).leadingCoeff = P.leadingCoeff := by
  have hq : (Polynomial.X + Polynomial.C c : Polynomial ℚ).natDegree ≠ 0 := by
    rw [natDegree_X_add_C]; omega
  rw [Polynomial.leadingCoeff_comp hq, leadingCoeff_X_add_C, one_pow, mul_one]

/-- Difference of `X + C` comps drops degree (nonconstant case). -/
theorem comp_X_add_C_sub_natDegree_lt {P : Polynomial ℚ} (hP : 1 ≤ P.natDegree)
    (c1 c2 : ℚ) :
    (P.comp (Polynomial.X + Polynomial.C c1) -
      P.comp (Polynomial.X + Polynomial.C c2)).natDegree < P.natDegree := by
  have hP0 : P ≠ 0 := by
    intro h0; rw [h0] at hP; simp at hP
  have h1 : P.comp (Polynomial.X + Polynomial.C c1) ≠ 0 := by
    intro h0
    have hn := congrArg Polynomial.natDegree h0
    rw [Polynomial.natDegree_zero, natDegree_comp_X_add_C] at hn
    omega
  have h2 : P.comp (Polynomial.X + Polynomial.C c2) ≠ 0 := by
    intro h0
    have hn := congrArg Polynomial.natDegree h0
    rw [Polynomial.natDegree_zero, natDegree_comp_X_add_C] at hn
    omega
  have hd : (P.comp (Polynomial.X + Polynomial.C c1)).degree =
      (P.comp (Polynomial.X + Polynomial.C c2)).degree := by
    rw [Polynomial.degree_eq_natDegree h1, Polynomial.degree_eq_natDegree h2,
      natDegree_comp_X_add_C, natDegree_comp_X_add_C]
  have hlc : (P.comp (Polynomial.X + Polynomial.C c1)).leadingCoeff =
      (P.comp (Polynomial.X + Polynomial.C c2)).leadingCoeff := by
    rw [leadingCoeff_comp_X_add_C, leadingCoeff_comp_X_add_C]
  have hdeg := Polynomial.degree_sub_lt_left hd h1 hlc
  by_cases hdiff : P.comp (Polynomial.X + Polynomial.C c1) -
      P.comp (Polynomial.X + Polynomial.C c2) = 0
  · rw [hdiff, Polynomial.natDegree_zero]
    omega
  · rw [Polynomial.natDegree_lt_iff_degree_lt hdiff]
    have hd1 : (P.comp (Polynomial.X + Polynomial.C c1)).degree = P.degree := by
      rw [Polynomial.degree_eq_natDegree h1, natDegree_comp_X_add_C,
        ← Polynomial.degree_eq_natDegree hP0]
    calc (P.comp (Polynomial.X + Polynomial.C c1) -
          P.comp (Polynomial.X + Polynomial.C c2)).degree
        < (P.comp (Polynomial.X + Polynomial.C c1)).degree := hdeg
      _ = P.degree := hd1
      _ = P.natDegree := Polynomial.degree_eq_natDegree hP0

theorem natDegree_C_sub_X (c : ℚ) : (Polynomial.C c - Polynomial.X : Polynomial ℚ).natDegree = 1 := by
  exact Polynomial.natDegree_eq_of_degree_eq_some (degree_C_sub_X c)

theorem leadingCoeff_C_sub_X (c : ℚ) :
    (Polynomial.C c - Polynomial.X : Polynomial ℚ).leadingCoeff = -1 := by
  have h : (Polynomial.C c - Polynomial.X : Polynomial ℚ).coeff 1 = -1 := by
    simp
  rw [Polynomial.leadingCoeff, natDegree_C_sub_X]
  exact h

/-- Comps with `C c - X` preserve degree and leading coefficient up to `(-1)^d`. -/
theorem natDegree_comp_C_sub_X (P : Polynomial ℚ) (c : ℚ) :
    (P.comp (Polynomial.C c - Polynomial.X)).natDegree = P.natDegree := by
  rw [Polynomial.natDegree_comp, natDegree_C_sub_X, mul_one]

theorem leadingCoeff_comp_C_sub_X (P : Polynomial ℚ) (c : ℚ) :
    (P.comp (Polynomial.C c - Polynomial.X)).leadingCoeff =
      P.leadingCoeff * (-1 : ℚ) ^ P.natDegree := by
  have hq : (Polynomial.C c - Polynomial.X : Polynomial ℚ).natDegree ≠ 0 := by
    rw [natDegree_C_sub_X]; omega
  rw [Polynomial.leadingCoeff_comp hq, leadingCoeff_C_sub_X]

/-- Difference of two such comps drops degree (nonconstant case). -/
theorem comp_C_sub_X_sub_natDegree_lt {P : Polynomial ℚ} (hP : 1 ≤ P.natDegree)
    (c1 c2 : ℚ) :
    (P.comp (Polynomial.C c1 - Polynomial.X) -
      P.comp (Polynomial.C c2 - Polynomial.X)).natDegree < P.natDegree := by
  have hP0 : P ≠ 0 := by
    intro h0; rw [h0] at hP; simp at hP
  have h1 : P.comp (Polynomial.C c1 - Polynomial.X) ≠ 0 := by
    intro h0
    have hn := congrArg Polynomial.natDegree h0
    rw [Polynomial.natDegree_zero, natDegree_comp_C_sub_X] at hn
    omega
  have h2 : P.comp (Polynomial.C c2 - Polynomial.X) ≠ 0 := by
    intro h0
    have hn := congrArg Polynomial.natDegree h0
    rw [Polynomial.natDegree_zero, natDegree_comp_C_sub_X] at hn
    omega
  have hd : (P.comp (Polynomial.C c1 - Polynomial.X)).degree =
      (P.comp (Polynomial.C c2 - Polynomial.X)).degree := by
    rw [Polynomial.degree_eq_natDegree h1, Polynomial.degree_eq_natDegree h2,
      natDegree_comp_C_sub_X, natDegree_comp_C_sub_X]
  have hlc : (P.comp (Polynomial.C c1 - Polynomial.X)).leadingCoeff =
      (P.comp (Polynomial.C c2 - Polynomial.X)).leadingCoeff := by
    rw [leadingCoeff_comp_C_sub_X, leadingCoeff_comp_C_sub_X]
  have hdeg := Polynomial.degree_sub_lt_left hd h1 hlc
  by_cases hdiff : P.comp (Polynomial.C c1 - Polynomial.X) -
      P.comp (Polynomial.C c2 - Polynomial.X) = 0
  · rw [hdiff, Polynomial.natDegree_zero]
    omega
  · rw [Polynomial.natDegree_lt_iff_degree_lt hdiff]
    have hd1 : (P.comp (Polynomial.C c1 - Polynomial.X)).degree = P.degree := by
      rw [Polynomial.degree_eq_natDegree h1, natDegree_comp_C_sub_X,
        ← Polynomial.degree_eq_natDegree hP0]
    calc (P.comp (Polynomial.C c1 - Polynomial.X) -
          P.comp (Polynomial.C c2 - Polynomial.X)).degree
        < (P.comp (Polynomial.C c1 - Polynomial.X)).degree := hdeg
      _ = P.degree := hd1
      _ = P.natDegree := Polynomial.degree_eq_natDegree hP0

/-- `(-1)^(m-k) = (-1)^m * (-1)^k` for `k ≤ m`. -/
theorem neg_one_pow_sub (m k : ℕ) (hk : k ≤ m) :
    (-1 : ℚ) ^ (m - k) = (-1 : ℚ) ^ m * (-1 : ℚ) ^ k := by
  have h1 : (-1 : ℚ) ^ k * (-1 : ℚ) ^ (m - k) = (-1 : ℚ) ^ m := by
    rw [← pow_add, Nat.add_sub_cancel' hk]
  have h2 : (-1 : ℚ) ^ k * (-1 : ℚ) ^ k = 1 := by
    rw [← pow_add]
    have : k + k = 2 * k := by omega
    rw [this, pow_mul]
    simp
  calc (-1 : ℚ) ^ (m - k) = 1 * (-1 : ℚ) ^ (m - k) := by rw [one_mul]
    _ = ((-1 : ℚ) ^ k * (-1 : ℚ) ^ k) * (-1 : ℚ) ^ (m - k) := by rw [h2]
    _ = (-1 : ℚ) ^ k * ((-1 : ℚ) ^ k * (-1 : ℚ) ^ (m - k)) := by ring
    _ = (-1 : ℚ) ^ k * (-1 : ℚ) ^ m := by rw [h1]
    _ = (-1 : ℚ) ^ m * (-1 : ℚ) ^ k := by ring

/-- Faulhaber polynomials are nonconstant. -/
theorem faulhaber_one_le_natDegree (p : ℕ) : 1 ≤ (faulhaberPoly p).natDegree := by
  by_contra h
  push_neg at h
  have h0 : (faulhaberPoly p).natDegree = 0 := by omega
  have hC := Polynomial.eq_C_of_natDegree_eq_zero h0
  have he0 := faulhaber_zero p
  have hcoeff : (faulhaberPoly p).coeff 0 = 0 := by
    have := congrArg (fun q : Polynomial ℚ => q.eval 0) hC
    simp only [Polynomial.eval_C] at this
    rw [he0] at this
    exact this.symm
  have hzero : faulhaberPoly p = 0 := by
    rw [hC, hcoeff, Polynomial.C_0]
  have he2 := faulhaber_eval p 2
  rw [hzero] at he2
  simp only [Polynomial.eval_zero] at he2
  have hsum : (∑ β ∈ Finset.range 2, (β : ℚ) ^ p) ≠ 0 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    simp only [Finset.sum_range_zero, zero_add]
    by_cases hp : p = 0
    · subst hp
      simp
    · simp [hp]
  exact hsum he2.symm

/-- The combining polynomial for the monomial vanishing (fixed `a b m s t`).
`R(k) = Σ_{i,j} C(a,i)C(b,j) t^{b-j} [P1_i Q1_{i,j} - P2_i Q2_{i,j}](k)`. -/
noncomputable def truncPoly (a b m : ℕ) (s t : ℚ) : Polynomial ℚ :=
  ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
    Polynomial.C ((a.choose i : ℚ) * (b.choose j : ℚ) * t ^ (b - j)) *
      ((Polynomial.X + Polynomial.C (s - 2 * (m : ℚ))) ^ (a - i) *
        (faulhaberPoly (i + j)).comp (Polynomial.C ((m : ℚ) + 1) - Polynomial.X)
      - (Polynomial.X + Polynomial.C (s - 2 * (m : ℚ) + 2)) ^ (a - i) *
        (faulhaberPoly (i + j)).comp (Polynomial.C (m : ℚ) - Polynomial.X))

/-- Evaluation of `truncPoly` (unfolded form). -/
theorem truncPoly_eval_form (a b m : ℕ) (s t : ℚ) (k : ℕ) :
    (truncPoly a b m s t).eval (k : ℚ) =
    ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
      ((a.choose i : ℚ) * (b.choose j : ℚ) * t ^ (b - j)) *
        (((k : ℚ) + (s - 2 * (m : ℚ))) ^ (a - i) *
          (faulhaberPoly (i + j)).eval (((m : ℚ) + 1) - (k : ℚ))
        - ((k : ℚ) + (s - 2 * (m : ℚ) + 2)) ^ (a - i) *
          (faulhaberPoly (i + j)).eval ((m : ℚ) - (k : ℚ))) := by
  unfold truncPoly
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_comp, Polynomial.eval_sub]

/-- Fiber sum expansion via binomial theorem and Faulhaber. -/
theorem fiber_expand (a b r : ℕ) (s t : ℚ) (k : ℕ) :
    (∑ β ∈ Finset.range (r + 1), (s - (k : ℚ) - 2 * (r : ℚ) + (β : ℚ)) ^ a * (t + (β : ℚ)) ^ b) =
    ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
      ((a.choose i : ℚ) * (b.choose j : ℚ) * (s - (k : ℚ) - 2 * (r : ℚ)) ^ (a - i) * t ^ (b - j)) *
        (faulhaberPoly (i + j)).eval ((r : ℚ) + 1) := by
  classical
  have hexpand_a : ∀ β : ℕ, (s - (k : ℚ) - 2 * (r : ℚ) + (β : ℚ)) ^ a =
      ∑ i ∈ Finset.range (a + 1), (a.choose i : ℚ) * (s - (k : ℚ) - 2 * (r : ℚ)) ^ (a - i) * (β : ℚ) ^ i := by
    intro β
    have hbase : s - (k : ℚ) - 2 * (r : ℚ) + (β : ℚ) = (β : ℚ) + (s - (k : ℚ) - 2 * (r : ℚ)) := by ring
    rw [hbase, add_pow]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hexpand_b : ∀ β : ℕ, (t + (β : ℚ)) ^ b =
      ∑ j ∈ Finset.range (b + 1), (b.choose j : ℚ) * t ^ (b - j) * (β : ℚ) ^ j := by
    intro β
    have hbase : (t : ℚ) + (β : ℚ) = (β : ℚ) + t := by ring
    rw [hbase, add_pow]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  calc (∑ β ∈ Finset.range (r + 1), (s - (k : ℚ) - 2 * (r : ℚ) + (β : ℚ)) ^ a * (t + (β : ℚ)) ^ b)
      = ∑ β ∈ Finset.range (r + 1),
        (∑ i ∈ Finset.range (a + 1), (a.choose i : ℚ) * (s - (k : ℚ) - 2 * (r : ℚ)) ^ (a - i) * (β : ℚ) ^ i) *
        (∑ j ∈ Finset.range (b + 1), (b.choose j : ℚ) * t ^ (b - j) * (β : ℚ) ^ j) := by
        apply Finset.sum_congr rfl
        intro β _
        rw [hexpand_a, hexpand_b]
    _ = ∑ β ∈ Finset.range (r + 1), ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
        ((a.choose i : ℚ) * (b.choose j : ℚ) * (s - (k : ℚ) - 2 * (r : ℚ)) ^ (a - i) * t ^ (b - j)) *
          (β : ℚ) ^ (i + j) := by
        apply Finset.sum_congr rfl
        intro β _
        rw [Finset.sum_mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
    _ = ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
        ((a.choose i : ℚ) * (b.choose j : ℚ) * (s - (k : ℚ) - 2 * (r : ℚ)) ^ (a - i) * t ^ (b - j)) *
          ∑ β ∈ Finset.range (r + 1), (β : ℚ) ^ (i + j) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
    _ = ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
        ((a.choose i : ℚ) * (b.choose j : ℚ) * (s - (k : ℚ) - 2 * (r : ℚ)) ^ (a - i) * t ^ (b - j)) *
          (faulhaberPoly (i + j)).eval ((r : ℚ) + 1) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        congr 1
        have hfaul := faulhaber_eval (i + j) (r + 1)
        have hcast : (((r + 1 : ℕ)) : ℚ) = (r : ℚ) + 1 := by push_cast; ring
        rw [hcast] at hfaul
        rw [hfaul]

/-- Degree bound for `truncPoly`: `natDegree < e` when `a + b + 1 ≤ e`. -/
theorem truncPoly_natDegree_lt (a b m e : ℕ) (hab : a + b + 1 ≤ e) (s t : ℚ) :
    (truncPoly a b m s t).natDegree < e := by
  classical
  -- it suffices to bound each (i,j) summand by `a + b`
  have hterm : ∀ ij ∈ Finset.range (a + 1) ×ˢ Finset.range (b + 1),
      (Polynomial.C ((a.choose ij.1 : ℚ) * (b.choose ij.2 : ℚ) * t ^ (b - ij.2)) *
        ((Polynomial.X + Polynomial.C (s - 2 * (m : ℚ))) ^ (a - ij.1) *
          (faulhaberPoly (ij.1 + ij.2)).comp (Polynomial.C ((m : ℚ) + 1) - Polynomial.X)
        - (Polynomial.X + Polynomial.C (s - 2 * (m : ℚ) + 2)) ^ (a - ij.1) *
          (faulhaberPoly (ij.1 + ij.2)).comp (Polynomial.C (m : ℚ) - Polynomial.X))).natDegree
      ≤ a + b := by
    intro ij hij
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hij
    obtain ⟨hi, hj⟩ := hij
    have hi_le : ij.1 ≤ a := Nat.lt_succ_iff.mp hi
    have hj_le : ij.2 ≤ b := Nat.lt_succ_iff.mp hj
    set i := ij.1 with hi_def
    set j := ij.2 with hj_def
    set p := i + j with hp_def
    set n := a - i with hn_def
    have hn_eq : i + n = a := Nat.add_sub_cancel' hi_le
    have hp_le : p ≤ a + b := by omega
    -- degrees of the four factors
    have hP1_deg : ((Polynomial.X + Polynomial.C (s - 2 * (m : ℚ)) : Polynomial ℚ) ^ n).natDegree = n := by
      rw [Polynomial.natDegree_pow, natDegree_X_add_C, mul_one]
    have hP2_deg : ((Polynomial.X + Polynomial.C (s - 2 * (m : ℚ) + 2) : Polynomial ℚ) ^ n).natDegree = n := by
      rw [Polynomial.natDegree_pow, natDegree_X_add_C, mul_one]
    have hS_le : (faulhaberPoly p).natDegree ≤ p + 1 := faulhaber_natDegree_le p
    have hS_pos : 1 ≤ (faulhaberPoly p).natDegree := faulhaber_one_le_natDegree p
    have hQ1_deg_le : ((faulhaberPoly p).comp (Polynomial.C ((m : ℚ) + 1) - Polynomial.X)).natDegree ≤ p + 1 := by
      rw [Polynomial.natDegree_comp, natDegree_C_sub_X, mul_one]
      exact hS_le
    have hQ2_deg_le : ((faulhaberPoly p).comp (Polynomial.C (m : ℚ) - Polynomial.X)).natDegree ≤ p + 1 := by
      rw [Polynomial.natDegree_comp, natDegree_C_sub_X, mul_one]
      exact hS_le
    have hQdiff_lt : (((faulhaberPoly p).comp (Polynomial.C ((m : ℚ) + 1) - Polynomial.X)) -
        (faulhaberPoly p).comp (Polynomial.C (m : ℚ) - Polynomial.X)).natDegree < (faulhaberPoly p).natDegree :=
      comp_C_sub_X_sub_natDegree_lt hS_pos _ _
    have hQdiff_le : (((faulhaberPoly p).comp (Polynomial.C ((m : ℚ) + 1) - Polynomial.X)) -
        (faulhaberPoly p).comp (Polynomial.C (m : ℚ) - Polynomial.X)).natDegree ≤ p := by
      have h1 := hQdiff_lt
      have h2 := hS_le
      omega
    -- P-difference: (X+C c1)^n - (X+C c2)^n drops degree (or is zero when n = 0)
    have hPdiff : (((Polynomial.X + Polynomial.C (s - 2 * (m : ℚ)) : Polynomial ℚ) ^ n) -
        (Polynomial.X + Polynomial.C (s - 2 * (m : ℚ) + 2)) ^ n).natDegree ≤ n - 1 + 0 := by
      by_cases hn0 : n = 0
      · rw [hn0]
        simp
      · have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn0
        have hPX : ((Polynomial.X : Polynomial ℚ) ^ n).natDegree = n := by
          simp
        have hP1_eq : ((Polynomial.X + Polynomial.C (s - 2 * (m : ℚ)) : Polynomial ℚ) ^ n) =
            ((Polynomial.X : Polynomial ℚ) ^ n).comp (Polynomial.X + Polynomial.C (s - 2 * (m : ℚ))) := by
          rw [Polynomial.X_pow_comp]
        have hP2_eq : ((Polynomial.X + Polynomial.C (s - 2 * (m : ℚ) + 2) : Polynomial ℚ) ^ n) =
            ((Polynomial.X : Polynomial ℚ) ^ n).comp (Polynomial.X + Polynomial.C (s - 2 * (m : ℚ) + 2)) := by
          rw [Polynomial.X_pow_comp]
        rw [hP1_eq, hP2_eq]
        have hlt := comp_X_add_C_sub_natDegree_lt (P := (Polynomial.X : Polynomial ℚ) ^ n)
          (by rw [hPX]; exact hn1) (s - 2 * (m : ℚ)) (s - 2 * (m : ℚ) + 2)
        have hle : (((Polynomial.X : Polynomial ℚ) ^ n).comp (Polynomial.X + Polynomial.C (s - 2 * (m : ℚ))) -
            ((Polynomial.X : Polynomial ℚ) ^ n).comp (Polynomial.X + Polynomial.C (s - 2 * (m : ℚ) + 2))).natDegree ≤ n - 1 := by
          have h1 := hlt
          rw [hPX] at h1
          omega
        omega
    -- A = P1 * (Q1 - Q2) has degree ≤ (a-i) + (i+j) = a+j
    have hA_le : (((Polynomial.X + Polynomial.C (s - 2 * (m : ℚ)) : Polynomial ℚ) ^ n) *
        (((faulhaberPoly p).comp (Polynomial.C ((m : ℚ) + 1) - Polynomial.X)) -
          (faulhaberPoly p).comp (Polynomial.C (m : ℚ) - Polynomial.X))).natDegree
        ≤ a + j := by
      have hle := Polynomial.natDegree_mul_le
        (p := ((Polynomial.X + Polynomial.C (s - 2 * (m : ℚ)) : Polynomial ℚ) ^ n))
        (q := ((faulhaberPoly p).comp (Polynomial.C ((m : ℚ) + 1) - Polynomial.X) -
          (faulhaberPoly p).comp (Polynomial.C (m : ℚ) - Polynomial.X)))
      omega
    -- B = (P1 - P2) * Q2 has degree ≤ a+j (split n = 0 vs n ≥ 1)
    have hB_le : ((((Polynomial.X + Polynomial.C (s - 2 * (m : ℚ)) : Polynomial ℚ) ^ n) -
        (Polynomial.X + Polynomial.C (s - 2 * (m : ℚ) + 2)) ^ n) *
        (faulhaberPoly p).comp (Polynomial.C (m : ℚ) - Polynomial.X)).natDegree
        ≤ a + j := by
      by_cases hn0 : n = 0
      · have hzero : (((Polynomial.X + Polynomial.C (s - 2 * (m : ℚ)) : Polynomial ℚ) ^ n) -
          (Polynomial.X + Polynomial.C (s - 2 * (m : ℚ) + 2)) ^ n) = 0 := by
          rw [hn0]
          simp
        rw [hzero, zero_mul, Polynomial.natDegree_zero]
        omega
      · have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn0
        have hle := Polynomial.natDegree_mul_le
          (p := (((Polynomial.X + Polynomial.C (s - 2 * (m : ℚ)) : Polynomial ℚ) ^ n) -
            (Polynomial.X + Polynomial.C (s - 2 * (m : ℚ) + 2)) ^ n))
          (q := (faulhaberPoly p).comp (Polynomial.C (m : ℚ) - Polynomial.X))
        have h1 := hPdiff
        have h2 := hQ2_deg_le
        omega
    -- T = A + B has degree ≤ a+j ≤ a+b
    have hT_le : (((Polynomial.X + Polynomial.C (s - 2 * (m : ℚ)) : Polynomial ℚ) ^ n) *
        (((faulhaberPoly p).comp (Polynomial.C ((m : ℚ) + 1) - Polynomial.X)) -
          (faulhaberPoly p).comp (Polynomial.C (m : ℚ) - Polynomial.X)) +
        ((((Polynomial.X + Polynomial.C (s - 2 * (m : ℚ)) : Polynomial ℚ) ^ n) -
          (Polynomial.X + Polynomial.C (s - 2 * (m : ℚ) + 2)) ^ n) *
          (faulhaberPoly p).comp (Polynomial.C (m : ℚ) - Polynomial.X))).natDegree
        ≤ a + j := by
      calc (((Polynomial.X + Polynomial.C (s - 2 * (m : ℚ)) : Polynomial ℚ) ^ n) *
          (((faulhaberPoly p).comp (Polynomial.C ((m : ℚ) + 1) - Polynomial.X)) -
            (faulhaberPoly p).comp (Polynomial.C (m : ℚ) - Polynomial.X)) +
          ((((Polynomial.X + Polynomial.C (s - 2 * (m : ℚ)) : Polynomial ℚ) ^ n) -
            (Polynomial.X + Polynomial.C (s - 2 * (m : ℚ) + 2)) ^ n) *
            (faulhaberPoly p).comp (Polynomial.C (m : ℚ) - Polynomial.X))).natDegree
          ≤ max
            ((((Polynomial.X + Polynomial.C (s - 2 * (m : ℚ)) : Polynomial ℚ) ^ n) *
              (((faulhaberPoly p).comp (Polynomial.C ((m : ℚ) + 1) - Polynomial.X)) -
                (faulhaberPoly p).comp (Polynomial.C (m : ℚ) - Polynomial.X))).natDegree)
            (((((Polynomial.X + Polynomial.C (s - 2 * (m : ℚ)) : Polynomial ℚ) ^ n) -
              (Polynomial.X + Polynomial.C (s - 2 * (m : ℚ) + 2)) ^ n) *
              (faulhaberPoly p).comp (Polynomial.C (m : ℚ) - Polynomial.X)).natDegree) :=
            Polynomial.natDegree_add_le _ _
        _ ≤ a + j := Nat.max_le.mpr ⟨hA_le, hB_le⟩
    -- rewrite P1Q1 - P2Q2 as A + B (ring) and add outer C (degree 0)
    have hrewrite : ((Polynomial.X + Polynomial.C (s - 2 * (m : ℚ)) : Polynomial ℚ) ^ n) *
          (faulhaberPoly p).comp (Polynomial.C ((m : ℚ) + 1) - Polynomial.X) -
          (Polynomial.X + Polynomial.C (s - 2 * (m : ℚ) + 2)) ^ n *
          (faulhaberPoly p).comp (Polynomial.C (m : ℚ) - Polynomial.X) =
        (((Polynomial.X + Polynomial.C (s - 2 * (m : ℚ)) : Polynomial ℚ) ^ n) *
          (((faulhaberPoly p).comp (Polynomial.C ((m : ℚ) + 1) - Polynomial.X)) -
            (faulhaberPoly p).comp (Polynomial.C (m : ℚ) - Polynomial.X)) +
        ((((Polynomial.X + Polynomial.C (s - 2 * (m : ℚ)) : Polynomial ℚ) ^ n) -
          (Polynomial.X + Polynomial.C (s - 2 * (m : ℚ) + 2)) ^ n) *
          (faulhaberPoly p).comp (Polynomial.C (m : ℚ) - Polynomial.X))) := by
      ring
    have hC_le : (Polynomial.C ((a.choose i : ℚ) * (b.choose j : ℚ) * t ^ (b - j)) *
        (((Polynomial.X + Polynomial.C (s - 2 * (m : ℚ)) : Polynomial ℚ) ^ n) *
          (faulhaberPoly p).comp (Polynomial.C ((m : ℚ) + 1) - Polynomial.X) -
          (Polynomial.X + Polynomial.C (s - 2 * (m : ℚ) + 2)) ^ n *
          (faulhaberPoly p).comp (Polynomial.C (m : ℚ) - Polynomial.X))).natDegree
        ≤ a + b := by
      rw [hrewrite]
      have hle := Polynomial.natDegree_mul_le
        (p := Polynomial.C ((a.choose i : ℚ) * (b.choose j : ℚ) * t ^ (b - j)))
        (q := (((Polynomial.X + Polynomial.C (s - 2 * (m : ℚ)) : Polynomial ℚ) ^ n) *
          (((faulhaberPoly p).comp (Polynomial.C ((m : ℚ) + 1) - Polynomial.X)) -
            (faulhaberPoly p).comp (Polynomial.C (m : ℚ) - Polynomial.X)) +
          ((((Polynomial.X + Polynomial.C (s - 2 * (m : ℚ)) : Polynomial ℚ) ^ n) -
            (Polynomial.X + Polynomial.C (s - 2 * (m : ℚ) + 2)) ^ n) *
            (faulhaberPoly p).comp (Polynomial.C (m : ℚ) - Polynomial.X))))
      have hC0 : (Polynomial.C ((a.choose i : ℚ) * (b.choose j : ℚ) * t ^ (b - j)) : Polynomial ℚ).natDegree = 0 :=
        Polynomial.natDegree_C _
      rw [hC0] at hle
      -- hle : natDegree (C * T) ≤ 0 + natDegree T; need natDegree T ≤ a+j ≤ a+b
      have hT : (((Polynomial.X + Polynomial.C (s - 2 * (m : ℚ)) : Polynomial ℚ) ^ n) *
          (((faulhaberPoly p).comp (Polynomial.C ((m : ℚ) + 1) - Polynomial.X)) -
            (faulhaberPoly p).comp (Polynomial.C (m : ℚ) - Polynomial.X)) +
          ((((Polynomial.X + Polynomial.C (s - 2 * (m : ℚ)) : Polynomial ℚ) ^ n) -
            (Polynomial.X + Polynomial.C (s - 2 * (m : ℚ) + 2)) ^ n) *
            (faulhaberPoly p).comp (Polynomial.C (m : ℚ) - Polynomial.X))).natDegree ≤ a + j :=
        hT_le
      omega
    exact hC_le
  -- sum of terms each of degree ≤ a+b has degree ≤ a+b < e (or is zero with degree 0 < e)
  have hsum_le : (truncPoly a b m s t).natDegree ≤ a + b := by
    unfold truncPoly
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro j hj
    have hij_mem : (i, j) ∈ Finset.range (a + 1) ×ˢ Finset.range (b + 1) := by
      rw [Finset.mem_product]
      exact ⟨Finset.mem_range.mpr (Finset.mem_range.mp hi),
        Finset.mem_range.mpr (Finset.mem_range.mp hj)⟩
    -- hterm gives bound for (i,j) = (ij.1, ij.2) with ij = (i,j); need to convert
    have h := hterm (i, j) hij_mem
    simpa using h
  have he_pos : 1 ≤ e := by omega
  have hlt : a + b < e := by omega
  calc (truncPoly a b m s t).natDegree ≤ a + b := hsum_le
    _ < e := hlt

/-- Inner `l,β` sum for `δ = 0`, fixed `k ≤ m`. -/
theorem inner_zero_eq (a b m k : ℕ) (hk : k ≤ m) (s t : ℚ) :
    (∑ l ∈ Finset.range (m + 1), ∑ β ∈ Finset.range (m + 1),
      if k + l + β = m then (-1 : ℚ) ^ (l + β) * (s - k - 2 * l - β) ^ a * (t + β) ^ b
      else 0) =
    (-1 : ℚ) ^ (m - k) * ∑ β ∈ Finset.range (m - k + 1),
      (s - (k : ℚ) - 2 * (((m - k : ℕ)) : ℚ) + (β : ℚ)) ^ a * (t + (β : ℚ)) ^ b := by
  classical
  set r := m - k with hr
  have hkr : k + r = m := Nat.add_sub_cancel' hk
  have hr_le : r ≤ m := Nat.sub_le _ _
  -- swap to sum over β outside
  rw [Finset.sum_comm]
  -- each β-slice
  have hslice : ∀ β ∈ Finset.range (m + 1),
      (∑ l ∈ Finset.range (m + 1),
        if k + l + β = m then (-1 : ℚ) ^ (l + β) * (s - k - 2 * l - β) ^ a * (t + β) ^ b
        else 0) =
      if β ≤ r then (-1 : ℚ) ^ r * (s - k - 2 * r + β) ^ a * (t + β) ^ b
      else 0 := by
    intro β hβ
    rw [Finset.mem_range] at hβ
    by_cases hle : β ≤ r
    · rw [if_pos hle]
      have hcond : ∀ l : ℕ, (k + l + β = m) ↔ (l = r - β) := by
        intro l
        omega
      simp_rw [hcond]
      rw [Finset.sum_ite_eq']
      have hmem : r - β ∈ Finset.range (m + 1) := by
        rw [Finset.mem_range]
        omega
      rw [if_pos hmem]
      have hlβ : (r - β) + β = r := Nat.sub_add_cancel hle
      -- rewrite exponent and base using l = r - β
      have hpow : (-1 : ℚ) ^ ((r - β) + β) = (-1 : ℚ) ^ r := by rw [hlβ]
      have hbase : (s - (k : ℚ) - 2 * ((r - β : ℕ) : ℚ) - (β : ℚ)) =
          s - (k : ℚ) - 2 * (r : ℚ) + (β : ℚ) := by
        have hcast : (((r - β : ℕ)) : ℚ) = (r : ℚ) - (β : ℚ) := Nat.cast_sub hle
        rw [hcast]
        ring
      have hterm : (-1 : ℚ) ^ ((r - β) + β) *
          (s - (k : ℚ) - 2 * (((r - β : ℕ)) : ℚ) - (β : ℚ)) ^ a * (t + (β : ℚ)) ^ b =
          (-1 : ℚ) ^ r * (s - k - 2 * r + β) ^ a * (t + β) ^ b := by
        rw [hpow, hbase]
      exact hterm
    · rw [if_neg hle]
      apply Finset.sum_eq_zero
      intro l _
      rw [if_neg]
      omega
  rw [Finset.sum_congr rfl hslice]
  -- factor (-1)^r and reduce to range (r+1)
  have hsub : Finset.range (r + 1) ⊆ Finset.range (m + 1) :=
    Finset.range_subset_range.mpr (by omega)
  have hfactor : ∀ β ∈ Finset.range (m + 1),
      (if β ≤ r then (-1 : ℚ) ^ r * (s - k - 2 * r + β) ^ a * (t + β) ^ b else 0) =
      (-1 : ℚ) ^ r * (if β ≤ r then (s - k - 2 * r + β) ^ a * (t + β) ^ b else 0) := by
    intro β _
    by_cases h : β ≤ r
    · simp [h, mul_assoc]
    · simp [h]
  rw [Finset.sum_congr rfl hfactor, ← Finset.mul_sum]
  congr 1
  -- LHS `if` sum over range(m+1) equals RHS sum over range(r+1) (with `r = m-k`)
  have hgoal : (∑ β ∈ Finset.range (m + 1),
        (if β ≤ r then (s - (k : ℚ) - 2 * (r : ℚ) + (β : ℚ)) ^ a * (t + (β : ℚ)) ^ b else 0)) =
      ∑ β ∈ Finset.range (r + 1),
        (s - (k : ℚ) - 2 * (r : ℚ) + (β : ℚ)) ^ a * (t + (β : ℚ)) ^ b := by
    have hsub2 : ∀ x ∈ Finset.range (m + 1),
        x ∉ Finset.range (r + 1) →
        (if x ≤ r then (s - (k : ℚ) - 2 * (r : ℚ) + ((x : ℕ) : ℚ)) ^ a * (t + ((x : ℕ) : ℚ)) ^ b else 0) = 0 := by
      intro x _ hnot
      rw [if_neg]
      intro hle
      apply hnot
      rw [Finset.mem_range]
      omega
    have hsub_eq := Finset.sum_subset hsub hsub2
    -- `sum_subset` gives small = big; we need big = small
    rw [← hsub_eq]
    apply Finset.sum_congr rfl
    intro β hβ
    rw [Finset.mem_range] at hβ
    rw [if_pos (by omega)]
  exact hgoal

/-- Inner `l,β` sum for `δ = 1`, fixed `k + 1 ≤ m`. -/
theorem inner_one_eq (a b m k : ℕ) (hk1 : k + 1 ≤ m) (s t : ℚ) :
    (∑ l ∈ Finset.range (m + 1), ∑ β ∈ Finset.range (m + 1),
      if 1 + k + l + β = m then (-1 : ℚ) ^ (l + β) * (s - k - 2 * l - β) ^ a * (t + β) ^ b
      else 0) =
    (-1 : ℚ) ^ (m - 1 - k) * ∑ β ∈ Finset.range (m - k),
      (s - (k : ℚ) - 2 * ((((m - 1 - k : ℕ))) : ℚ) + (β : ℚ)) ^ a * (t + (β : ℚ)) ^ b := by
  classical
  have hk : k ≤ m := by omega
  set r := m - 1 - k with hr
  have hkr : 1 + k + r = m := by omega
  have hr_le : r ≤ m := Nat.le_trans (Nat.sub_le _ _) (Nat.sub_le _ _)
  have hrm : r + 1 = m - k := by omega
  rw [Finset.sum_comm]
  have hslice : ∀ β ∈ Finset.range (m + 1),
      (∑ l ∈ Finset.range (m + 1),
        if 1 + k + l + β = m then (-1 : ℚ) ^ (l + β) * (s - k - 2 * l - β) ^ a * (t + β) ^ b
        else 0) =
      if β ≤ r then (-1 : ℚ) ^ r * (s - k - 2 * r + β) ^ a * (t + β) ^ b
      else 0 := by
    intro β hβ
    rw [Finset.mem_range] at hβ
    by_cases hle : β ≤ r
    · rw [if_pos hle]
      have hcond : ∀ l : ℕ, (1 + k + l + β = m) ↔ (l = r - β) := by
        intro l
        omega
      simp_rw [hcond]
      rw [Finset.sum_ite_eq']
      have hmem : r - β ∈ Finset.range (m + 1) := by
        rw [Finset.mem_range]
        omega
      rw [if_pos hmem]
      have hlβ : (r - β) + β = r := Nat.sub_add_cancel hle
      have hpow : (-1 : ℚ) ^ ((r - β) + β) = (-1 : ℚ) ^ r := by rw [hlβ]
      have hbase : (s - (k : ℚ) - 2 * ((r - β : ℕ) : ℚ) - (β : ℚ)) =
          s - (k : ℚ) - 2 * (r : ℚ) + (β : ℚ) := by
        have hcast : (((r - β : ℕ)) : ℚ) = (r : ℚ) - (β : ℚ) := Nat.cast_sub hle
        rw [hcast]
        ring
      have hterm : (-1 : ℚ) ^ ((r - β) + β) *
          (s - (k : ℚ) - 2 * (((r - β : ℕ)) : ℚ) - (β : ℚ)) ^ a * (t + (β : ℚ)) ^ b =
          (-1 : ℚ) ^ r * (s - k - 2 * r + β) ^ a * (t + β) ^ b := by
        rw [hpow, hbase]
      exact hterm
    · rw [if_neg hle]
      apply Finset.sum_eq_zero
      intro l _
      rw [if_neg]
      omega
  rw [Finset.sum_congr rfl hslice]
  have hsub : Finset.range (r + 1) ⊆ Finset.range (m + 1) :=
    Finset.range_subset_range.mpr (by omega)
  have hfactor : ∀ β ∈ Finset.range (m + 1),
      (if β ≤ r then (-1 : ℚ) ^ r * (s - k - 2 * r + β) ^ a * (t + β) ^ b else 0) =
      (-1 : ℚ) ^ r * (if β ≤ r then (s - k - 2 * r + β) ^ a * (t + β) ^ b else 0) := by
    intro β _
    by_cases h : β ≤ r
    · simp [h, mul_assoc]
    · simp [h]
  rw [Finset.sum_congr rfl hfactor, ← Finset.mul_sum]
  congr 1
  have hgoal : (∑ β ∈ Finset.range (m + 1),
        (if β ≤ r then (s - (k : ℚ) - 2 * (r : ℚ) + (β : ℚ)) ^ a * (t + (β : ℚ)) ^ b else 0)) =
      ∑ β ∈ Finset.range (r + 1),
        (s - (k : ℚ) - 2 * (r : ℚ) + (β : ℚ)) ^ a * (t + (β : ℚ)) ^ b := by
    have hsub2 : ∀ x ∈ Finset.range (m + 1),
        x ∉ Finset.range (r + 1) →
        (if x ≤ r then (s - (k : ℚ) - 2 * (r : ℚ) + ((x : ℕ) : ℚ)) ^ a * (t + ((x : ℕ) : ℚ)) ^ b else 0) = 0 := by
      intro x _ hnot
      rw [if_neg]
      intro hle
      apply hnot
      rw [Finset.mem_range]
      omega
    have hsub_eq := Finset.sum_subset hsub hsub2
    rw [← hsub_eq]
    apply Finset.sum_congr rfl
    intro β hβ
    rw [Finset.mem_range] at hβ
    rw [if_pos (by omega)]
  rw [hgoal, hrm]

/-- Monomial case of truncation. -/
theorem monomial_truncation (e a b m : ℕ) (hab : a + b + 1 ≤ e) (hm : e ≤ m)
    (s t : ℚ) :
    (∑ δ ∈ Finset.range 2, ∑ k ∈ Finset.range (e + 1),
      ∑ l ∈ Finset.range (m + 1), ∑ β ∈ Finset.range (m + 1),
        if δ + k + l + β = m then (-1 : ℚ) ^ (l + β) * (e.choose k : ℚ) *
          (s - k - 2 * l - β) ^ a * (t + β) ^ b
        else 0) = 0 := by
  classical
  -- split δ = 0, 1
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  simp only [Finset.sum_range_zero, zero_add]
  -- It suffices to show the combined k-sum vanishes via the polynomial R.
  -- First, rewrite each k-slice using the inner lemmas.
  have hk_le : ∀ k ∈ Finset.range (e + 1), k ≤ m := by
    intro k hk
    rw [Finset.mem_range] at hk
    omega
  -- S0 (δ=0) and S1 (δ=1) as k-sums with C(e,k) factored (see below for full assembly).
  -- The remaining assembly (factoring, R-matching, moments) is routine Finset manipulation
  -- using `inner_zero_eq`, `inner_one_eq`, `fiber_expand`, `truncPoly_eval_form`,
  -- `neg_one_pow_sub` and `alternating_polynomial_moment_zero`; see NOTES for the arithmetic.
  -- Full assembly below (factor C, match R, apply moments).
  have hS0 : (∑ k ∈ Finset.range (e + 1), ∑ l ∈ Finset.range (m + 1), ∑ β ∈ Finset.range (m + 1),
        if k + l + β = m then (-1 : ℚ) ^ (l + β) * (e.choose k : ℚ) *
          (s - k - 2 * l - β) ^ a * (t + β) ^ b else 0) =
      ∑ k ∈ Finset.range (e + 1), (e.choose k : ℚ) *
        (((-1 : ℚ) ^ (m - k)) * ∑ β ∈ Finset.range (m - k + 1),
          (s - (k : ℚ) - 2 * (((m - k : ℕ)) : ℚ) + (β : ℚ)) ^ a * (t + (β : ℚ)) ^ b) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkm := hk_le k hk
    have hinner := inner_zero_eq a b m k hkm s t
    -- factor C(e,k) out of l,β sums
    have hfactor : (∑ l ∈ Finset.range (m + 1), ∑ β ∈ Finset.range (m + 1),
          if k + l + β = m then (-1 : ℚ) ^ (l + β) * (e.choose k : ℚ) *
            (s - k - 2 * l - β) ^ a * (t + β) ^ b else 0) =
        (e.choose k : ℚ) * (∑ l ∈ Finset.range (m + 1), ∑ β ∈ Finset.range (m + 1),
          if k + l + β = m then (-1 : ℚ) ^ (l + β) *
            (s - k - 2 * l - β) ^ a * (t + β) ^ b else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro β _
      by_cases h : k + l + β = m
      · rw [if_pos h, if_pos h]; ring
      · rw [if_neg h, if_neg h]; ring
    rw [hfactor, hinner]
  -- S1 (δ=1): for k+1 ≤ m use inner_one_eq, else (k = m) the sum is empty (0).
  have hS1 : (∑ k ∈ Finset.range (e + 1), ∑ l ∈ Finset.range (m + 1), ∑ β ∈ Finset.range (m + 1),
        if 1 + k + l + β = m then (-1 : ℚ) ^ (l + β) * (e.choose k : ℚ) *
          (s - k - 2 * l - β) ^ a * (t + β) ^ b else 0) =
      ∑ k ∈ Finset.range (e + 1), (e.choose k : ℚ) *
        (if k + 1 ≤ m then ((-1 : ℚ) ^ (m - 1 - k)) * ∑ β ∈ Finset.range (m - k),
          (s - (k : ℚ) - 2 * ((((m - 1 - k : ℕ))) : ℚ) + (β : ℚ)) ^ a * (t + (β : ℚ)) ^ b else 0) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkm : k ≤ m := hk_le k hk
    by_cases hk1 : k + 1 ≤ m
    · have hcond : ∀ l β : ℕ, (1 + k + l + β = m) ↔ (1 + k + l + β = m) := by
        intro l β; rfl
      have hinner1 := inner_one_eq a b m k hk1 s t
      have hfactor1 : (∑ l ∈ Finset.range (m + 1), ∑ β ∈ Finset.range (m + 1),
            if 1 + k + l + β = m then (-1 : ℚ) ^ (l + β) * (e.choose k : ℚ) *
              (s - k - 2 * l - β) ^ a * (t + β) ^ b else 0) =
          (e.choose k : ℚ) * (∑ l ∈ Finset.range (m + 1), ∑ β ∈ Finset.range (m + 1),
            if 1 + k + l + β = m then (-1 : ℚ) ^ (l + β) *
              (s - k - 2 * l - β) ^ a * (t + β) ^ b else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro β _
        by_cases h : 1 + k + l + β = m
        · rw [if_pos h, if_pos h]; ring
        · rw [if_neg h, if_neg h]; ring
      rw [hfactor1, hinner1, if_pos hk1]
    · rw [if_neg hk1]
      -- 1 + k > m so no (l,β) satisfy; each inner sum is 0, whole k-slice is 0 = C * 0
      have hempty : (∑ l ∈ Finset.range (m + 1), ∑ β ∈ Finset.range (m + 1),
            if 1 + k + l + β = m then (-1 : ℚ) ^ (l + β) * (e.choose k : ℚ) *
              (s - k - 2 * l - β) ^ a * (t + β) ^ b else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro l _
        apply Finset.sum_eq_zero
        intro β _
        rw [if_neg]
        omega
      rw [hempty]
      ring
  -- R matches the fiber difference: R(k) = F0(k) - F1(k).
  have hR_eq : ∀ k ∈ Finset.range (e + 1),
      (truncPoly a b m s t).eval (k : ℚ) =
        (∑ β ∈ Finset.range (m - k + 1),
          (s - (k : ℚ) - 2 * (((m - k : ℕ)) : ℚ) + (β : ℚ)) ^ a * (t + (β : ℚ)) ^ b) -
        (∑ β ∈ Finset.range (m - k),
          (s - (k : ℚ) - 2 * ((((m - 1 - k : ℕ))) : ℚ) + (β : ℚ)) ^ a * (t + (β : ℚ)) ^ b) := by
    intro k hk
    have hkm : k ≤ m := hk_le k hk
    have hR_form := truncPoly_eval_form a b m s t k
    have hF0 := fiber_expand a b (m - k) s t k
    by_cases hk1 : k + 1 ≤ m
    · -- k < m: both fiber sums non-empty; match via fiber_expand + cast_sub + ring.
      have hF1 := fiber_expand a b (m - 1 - k) s t k
      have hcast_mk : (((m - k : ℕ)) : ℚ) = (m : ℚ) - (k : ℚ) := Nat.cast_sub hkm
      have hcast_m1k : ((((m - 1 - k : ℕ))) : ℚ) = (m : ℚ) - 1 - (k : ℚ) := by
        have h1 : 1 ≤ m := by omega
        have h2 : k ≤ m - 1 := by omega
        have e1 : (((m - 1 - k : ℕ)) : ℚ) = ((m - 1 : ℕ) : ℚ) - (k : ℚ) := Nat.cast_sub h2
        have e2 : (((m - 1 : ℕ)) : ℚ) = (m : ℚ) - 1 := Nat.cast_sub h1
        rw [e1, e2]
      have hr1_eq : m - 1 - k + 1 = m - k := by omega
      -- Expand F0/F1 via hF0/hF1 and R via eval_form; match termwise via cast_sub + ring.
      have hP1_eq : ∀ i ∈ Finset.range (a + 1),
          (s - (k : ℚ) - 2 * (((m - k : ℕ)) : ℚ)) ^ (a - i) =
          ((k : ℚ) + (s - 2 * (m : ℚ))) ^ (a - i) := by
        intro i _
        rw [hcast_mk]
        ring
      have hQ1_eq : ∀ ij ∈ Finset.range (a + 1) ×ˢ Finset.range (b + 1),
          (faulhaberPoly (ij.1 + ij.2)).eval ((((m - k : ℕ)) : ℚ) + 1) =
          (faulhaberPoly (ij.1 + ij.2)).eval (((m : ℚ) + 1) - (k : ℚ)) := by
        intro ij _
        congr 1
        rw [hcast_mk]
        ring
      have hP2_eq : ∀ i ∈ Finset.range (a + 1),
          (s - (k : ℚ) - 2 * ((((m - 1 - k : ℕ))) : ℚ)) ^ (a - i) =
          ((k : ℚ) + (s - 2 * (m : ℚ) + 2)) ^ (a - i) := by
        intro i _
        rw [hcast_m1k]
        ring
      have hQ2_eq : ∀ ij ∈ Finset.range (a + 1) ×ˢ Finset.range (b + 1),
          (faulhaberPoly (ij.1 + ij.2)).eval ((((m - 1 - k : ℕ)) : ℚ) + 1) =
          (faulhaberPoly (ij.1 + ij.2)).eval ((m : ℚ) - (k : ℚ)) := by
        intro ij _
        congr 1
        rw [← Nat.cast_add_one, hr1_eq, hcast_mk]
      have hR_F : (truncPoly a b m s t).eval (k : ℚ) =
          (∑ β ∈ Finset.range (m - k + 1),
            (s - (k : ℚ) - 2 * (((m - k : ℕ)) : ℚ) + (β : ℚ)) ^ a * (t + (β : ℚ)) ^ b) -
          (∑ β ∈ Finset.range (m - k),
            (s - (k : ℚ) - 2 * ((((m - 1 - k : ℕ))) : ℚ) + (β : ℚ)) ^ a * (t + (β : ℚ)) ^ b) := by
        have hF1_rw : (∑ β ∈ Finset.range (m - k),
            (s - (k : ℚ) - 2 * ((((m - 1 - k : ℕ))) : ℚ) + (β : ℚ)) ^ a * (t + (β : ℚ)) ^ b) =
            ∑ β ∈ Finset.range (m - 1 - k + 1),
              (s - (k : ℚ) - 2 * ((((m - 1 - k : ℕ))) : ℚ) + (β : ℚ)) ^ a * (t + (β : ℚ)) ^ b := by
          rw [hr1_eq]
        rw [hR_form, hF0, hF1_rw, hF1]
        -- Both sides are double sums over i,j; match termwise via hP1_eq/hQ1_eq/hP2_eq/hQ2_eq.
        -- LHS = Σ c*(P1Q1-P2Q2), RHS = Σ c*P1'Q1' - Σ c*P2'Q2' with P1=P1', etc.
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        have hP1 := hP1_eq i (Finset.mem_range.mpr (by have := Finset.mem_range.mp hi; omega))
        have hP2 := hP2_eq i (Finset.mem_range.mpr (by have := Finset.mem_range.mp hi; omega))
        have hij_mem : (i, j) ∈ Finset.range (a + 1) ×ˢ Finset.range (b + 1) := by
          rw [Finset.mem_product]
          exact ⟨Finset.mem_range.mpr (by have := Finset.mem_range.mp hi; omega),
            Finset.mem_range.mpr (by have := Finset.mem_range.mp hj; omega)⟩
        have hQ1 := hQ1_eq (i, j) hij_mem
        have hQ2 := hQ2_eq (i, j) hij_mem
        rw [hP1, hP2, hQ1, hQ2]
        ring
      exact hR_F
    · -- k = m: second fiber sum empty (range 0), R second term vanishes via S(0)=0.
      have hkm_eq : k = m := by omega
      rw [hkm_eq]
      have hF0_0 := fiber_expand a b 0 s t m
      have hR_form_m := truncPoly_eval_form a b m s t m
      -- F1 range (m-m) = range 0 empty, so second fiber sum = 0.
      have hF1_empty : (∑ β ∈ Finset.range (m - m),
          (s - (m : ℚ) - 2 * ((((m - 1 - m : ℕ))) : ℚ) + (β : ℚ)) ^ a * (t + (β : ℚ)) ^ b) = 0 := by
        have hmm : m - m = 0 := Nat.sub_self m
        rw [hmm]
        simp
      have hQ2_zero : ∀ ij ∈ Finset.range (a + 1) ×ˢ Finset.range (b + 1),
          (faulhaberPoly (ij.1 + ij.2)).eval ((m : ℚ) - (m : ℚ)) = 0 := by
        intro ij _
        rw [sub_self]
        exact faulhaber_zero _
      have hR_eq_m : (truncPoly a b m s t).eval (m : ℚ) =
          (∑ β ∈ Finset.range (m - m + 1),
            (s - (m : ℚ) - 2 * (((m - m : ℕ)) : ℚ) + (β : ℚ)) ^ a * (t + (β : ℚ)) ^ b) -
          (∑ β ∈ Finset.range (m - m),
            (s - (m : ℚ) - 2 * ((((m - 1 - m : ℕ))) : ℚ) + (β : ℚ)) ^ a * (t + (β : ℚ)) ^ b) := by
        have hmm : m - m = 0 := Nat.sub_self m
        rw [hR_form_m, hF1_empty, sub_zero, hmm]
        rw [hF0_0]
        have hsecond_zero : (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
            ((a.choose i : ℚ) * (b.choose j : ℚ) * t ^ (b - j)) *
              (((m : ℚ) + (s - 2 * (m : ℚ) + 2)) ^ (a - i) *
                (faulhaberPoly (i + j)).eval ((m : ℚ) - (m : ℚ)))) = 0 := by
          apply Finset.sum_eq_zero
          intro i _
          apply Finset.sum_eq_zero
          intro j _
          have hQ : (faulhaberPoly (i + j)).eval ((m : ℚ) - (m : ℚ)) = 0 := by
            rw [sub_self]
            exact faulhaber_zero _
          rw [hQ, mul_zero, mul_zero]
        have hfirst_match : (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
            ((a.choose i : ℚ) * (b.choose j : ℚ) * t ^ (b - j)) *
              ((((m : ℚ) + (s - 2 * (m : ℚ)))) ^ (a - i) *
                (faulhaberPoly (i + j)).eval (((m : ℚ) + 1) - (m : ℚ)))) =
            ∑ β ∈ Finset.range (0 + 1),
              (s - (m : ℚ) - 2 * (((0 : ℕ)) : ℚ) + (β : ℚ)) ^ a * (t + (β : ℚ)) ^ b := by
          have hF0_0_rw := hF0_0
          rw [hF0_0_rw]
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          have hP1m : (((m : ℚ) + (s - 2 * (m : ℚ)))) ^ (a - i) =
              (s - (m : ℚ) - 2 * (((0 : ℕ)) : ℚ)) ^ (a - i) := by
            congr 1
            simp only [Nat.cast_zero, mul_zero, sub_zero]
            ring
          have hQ1m : (faulhaberPoly (i + j)).eval (((m : ℚ) + 1) - (m : ℚ)) =
              (faulhaberPoly (i + j)).eval ((((0 : ℕ)) : ℚ) + 1) := by
            congr 1
            simp only [Nat.cast_zero, zero_add]
            ring
          rw [hP1m, hQ1m]
          ring
        have eAB : (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
            ((a.choose i : ℚ) * (b.choose j : ℚ) * t ^ (b - j)) *
              ((((m : ℚ) + (s - 2 * (m : ℚ)))) ^ (a - i) *
                (faulhaberPoly (i + j)).eval (((m : ℚ) + 1) - (m : ℚ)) -
              (((m : ℚ) + (s - 2 * (m : ℚ) + 2))) ^ (a - i) *
                (faulhaberPoly (i + j)).eval ((m : ℚ) - (m : ℚ)))) =
            (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
              ((a.choose i : ℚ) * (b.choose j : ℚ) * t ^ (b - j)) *
                ((((m : ℚ) + (s - 2 * (m : ℚ)))) ^ (a - i) *
                  (faulhaberPoly (i + j)).eval (((m : ℚ) + 1) - (m : ℚ)))) -
            (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
              ((a.choose i : ℚ) * (b.choose j : ℚ) * t ^ (b - j)) *
                ((((m : ℚ) + (s - 2 * (m : ℚ) + 2))) ^ (a - i) *
                  (faulhaberPoly (i + j)).eval ((m : ℚ) - (m : ℚ)))) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i _
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro j _
          rw [mul_sub]
        rw [eAB, hsecond_zero, sub_zero]
        exact hfirst_match.trans hF0_0
      exact hR_eq_m
  rw [hS0, hS1, ← Finset.sum_add_distrib]
  have hRdeg : (truncPoly a b m s t).natDegree < e :=
    truncPoly_natDegree_lt a b m e hab s t
  have hmom := IncidenceMoments.alternating_polynomial_moment_zero e
    (truncPoly a b m s t) hRdeg
  have efin : (∑ k ∈ Finset.range (e + 1),
        ((e.choose k : ℚ) * (((-1 : ℚ) ^ (m - k)) * ∑ β ∈ Finset.range (m - k + 1),
          (s - (k : ℚ) - 2 * (((m - k : ℕ)) : ℚ) + (β : ℚ)) ^ a * (t + (β : ℚ)) ^ b) +
        (e.choose k : ℚ) * (if k + 1 ≤ m then ((-1 : ℚ) ^ (m - 1 - k)) * ∑ β ∈ Finset.range (m - k),
          (s - (k : ℚ) - 2 * ((((m - 1 - k : ℕ))) : ℚ) + (β : ℚ)) ^ a * (t + (β : ℚ)) ^ b else 0))) =
      (-1 : ℚ) ^ m * ∑ k ∈ Finset.range (e + 1),
        (-1 : ℚ) ^ k * (e.choose k : ℚ) * (truncPoly a b m s t).eval (k : ℚ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hkm : k ≤ m := hk_le k hk
    have eR := hR_eq k hk
    by_cases hk1 : k + 1 ≤ m
    · rw [if_pos hk1]
      have hr1_eq : m - 1 - k + 1 = m - k := by omega
      have eY : (-1 : ℚ) ^ (m - 1 - k) = -(-1 : ℚ) ^ (m - k) := by
        have e : (-1 : ℚ) ^ (m - k) = (-1 : ℚ) ^ (m - 1 - k) * (-1) := by
          conv_lhs => rw [← hr1_eq]
          rw [pow_succ]
        linear_combination e
      rw [eR, eY, neg_one_pow_sub m k hkm]
      ring
    · rw [if_neg hk1]
      have hkm_eq : k = m := by omega
      rw [hkm_eq]
      have hmem : m ∈ Finset.range (e + 1) := by rw [← hkm_eq]; exact hk
      have eRm := hR_eq m hmem
      rw [eRm]
      have hF1z : (∑ β ∈ Finset.range (m - m),
          (s - (m : ℚ) - 2 * ((((m - 1 - m : ℕ))) : ℚ) + (β : ℚ)) ^ a * (t + (β : ℚ)) ^ b) = 0 := by
        have hmm0 : m - m = 0 := Nat.sub_self m
        rw [hmm0]
        simp
      rw [hF1z, sub_zero]
      rw [Nat.sub_self m]
      rw [pow_zero, one_mul]
      simp only [mul_zero, add_zero]
      have hsq : (-1 : ℚ) ^ m * (-1 : ℚ) ^ m = 1 := by
        rw [← pow_add]
        have : m + m = 2 * m := by omega
        rw [this, pow_mul]
        simp
      have hsq_symm : (1 : ℚ) = (-1 : ℚ) ^ m * (-1 : ℚ) ^ m := hsq.symm
      linear_combination ((e.choose m : ℚ) *
        (∑ β ∈ Finset.range (0 + 1),
          (s - (m : ℚ) - 2 * (((0 : ℕ)) : ℚ) + (β : ℚ)) ^ a * (t + (β : ℚ)) ^ b)) * hsq_symm
  rw [efin, hmom, mul_zero]


/-- Evaluation of a monomial at a truncation point. -/
theorem eval_monomial_trunc (c : ℚ) (d : Fin 2 →₀ ℕ) (s t : ℚ) (k l β : ℕ) :
    MvPolynomial.eval (Fin.cons (s - k - 2 * l - β) (fun _ : Fin 1 => t + β))
      (MvPolynomial.monomial d c)
      = c * (s - k - 2 * l - β) ^ (d 0) * (t + β) ^ (d 1) := by
  rw [MvPolynomial.eval_monomial,
    Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fin.prod_univ_two]
  simp only [Fin.cons_zero, Fin.cons_one]
  ring

/-- Evaluation over the support at a truncation point. -/
theorem eval_trunc_eq_sum (P : BaseHilbertPolynomial) (s t : ℚ) (k l β : ℕ) :
    MvPolynomial.eval (Fin.cons (s - k - 2 * l - β) (fun _ : Fin 1 => t + β)) P =
      ∑ d ∈ P.support,
        P.coeff d * (s - k - 2 * l - β) ^ (d 0) * (t + β) ^ (d 1) := by
  conv_lhs => rw [MvPolynomial.as_sum P]
  rw [MvPolynomial.eval_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [eval_monomial_trunc]

/-- (P4) Truncation for a general base polynomial, from the monomial case. -/
theorem truncation (e : ℕ) (P : BaseHilbertPolynomial) (hP : P.totalDegree + 1 ≤ e)
    (m : ℕ) (hm : e ≤ m) (s t : ℚ) :
    (∑ δ ∈ Finset.range 2, ∑ k ∈ Finset.range (e + 1),
      ∑ l ∈ Finset.range (m + 1), ∑ β ∈ Finset.range (m + 1),
        if δ + k + l + β = m then
          ((-1 : ℚ) ^ (l + β) * (e.choose k : ℚ)) *
            MvPolynomial.eval (Fin.cons (s - k - 2 * l - β) (fun _ : Fin 1 => t + β)) P
        else 0) = 0 := by
  classical
  have hif : ∀ (c : Prop) [Decidable c] (G : (Fin 2 →₀ ℕ) → ℚ),
      (if c then ∑ d ∈ P.support, G d else 0) =
      ∑ d ∈ P.support, (if c then G d else 0) := by
    intro c _ G
    split_ifs with h <;> simp [h]
  have swap1 : ∀ (G : ℕ → (Fin 2 →₀ ℕ) → ℚ),
      (∑ β ∈ Finset.range (m + 1), ∑ d ∈ P.support, G β d) =
      (∑ d ∈ P.support, ∑ β ∈ Finset.range (m + 1), G β d) :=
    fun _ => Finset.sum_comm
  have swap2 : ∀ (G : ℕ → (Fin 2 →₀ ℕ) → ℚ),
      (∑ l ∈ Finset.range (m + 1), ∑ d ∈ P.support, G l d) =
      (∑ d ∈ P.support, ∑ l ∈ Finset.range (m + 1), G l d) :=
    fun _ => Finset.sum_comm
  have swap3 : ∀ (G : ℕ → (Fin 2 →₀ ℕ) → ℚ),
      (∑ k ∈ Finset.range (e + 1), ∑ d ∈ P.support, G k d) =
      (∑ d ∈ P.support, ∑ k ∈ Finset.range (e + 1), G k d) :=
    fun _ => Finset.sum_comm
  have swap4 : ∀ (G : ℕ → (Fin 2 →₀ ℕ) → ℚ),
      (∑ δ ∈ Finset.range 2, ∑ d ∈ P.support, G δ d) =
      (∑ d ∈ P.support, ∑ δ ∈ Finset.range 2, G δ d) :=
    fun _ => Finset.sum_comm
  simp only [eval_trunc_eq_sum]
  simp only [Finset.mul_sum]
  simp only [hif]
  simp only [swap1, swap2, swap3, swap4]
  apply Finset.sum_eq_zero
  intro d hd
  have hle := MvPolynomial.le_totalDegree (p := P) (s := d) hd
  have hsum : d.sum (fun _ e => e) = d 0 + d 1 := by
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]
  have hdeg : d 0 + d 1 + 1 ≤ e := by omega
  have hM : (∑ δ ∈ Finset.range 2, ∑ k ∈ Finset.range (e + 1),
      ∑ l ∈ Finset.range (m + 1), ∑ β ∈ Finset.range (m + 1),
        if δ + k + l + β = m then (-1 : ℚ) ^ (l + β) * (e.choose k : ℚ) *
          (s - k - 2 * l - β) ^ (d 0) * (t + β) ^ (d 1)
        else 0) = 0 :=
    monomial_truncation e (d 0) (d 1) m hdeg hm s t
  have efac : (∑ δ ∈ Finset.range 2, ∑ k ∈ Finset.range (e + 1),
      ∑ l ∈ Finset.range (m + 1), ∑ β ∈ Finset.range (m + 1),
        if δ + k + l + β = m then
          ((-1 : ℚ) ^ (l + β) * (e.choose k : ℚ)) *
            (P.coeff d * (s - k - 2 * l - β) ^ (d 0) * (t + β) ^ (d 1))
        else 0) =
      P.coeff d * (∑ δ ∈ Finset.range 2, ∑ k ∈ Finset.range (e + 1),
        ∑ l ∈ Finset.range (m + 1), ∑ β ∈ Finset.range (m + 1),
          if δ + k + l + β = m then (-1 : ℚ) ^ (l + β) * (e.choose k : ℚ) *
            (s - k - 2 * l - β) ^ (d 0) * (t + β) ^ (d 1)
          else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro δ _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro β _
    by_cases h : δ + k + l + β = m
    · simp only [if_pos h]
      ring
    · simp only [if_neg h, mul_zero]
  rw [efac, hM, mul_zero]


end TripleRankTrunc
end DistinctDistances.TrackB
