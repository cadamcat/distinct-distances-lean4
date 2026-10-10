import DistinctDistances.TrackB.MixedHilbert
import OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertDegree

/-!
Bigraded Hilbert toolkit for the two `pairHilbert` requests (B18).

`mixed_top_nonnegative` is proved by induction on the total degree bound:
slicing with an arbitrary first-factor linear form outside the ideal either
strictly enlarges the ideal twice (Noetherian step, via the unconditional
`colon_rank_step`), or the form is regular and the quotient polynomial is the
first finite difference (degree step). Pure `(0,d)` coefficients are
univariate slices. No prime avoidance or Artinian input is needed.
-/

namespace DistinctDistances.TrackB.BridgesBMixed

open scoped BigOperators

attribute [local instance] MvPolynomial.weightedGradedAlgebra

set_option autoImplicit false
noncomputable section

/-- Bivariate evaluation matching the frozen `hevent` form. -/
abbrev evalPair (P : BaseHilbertPolynomial) (s t : ℕ) : ℚ :=
  MvPolynomial.eval (Fin.cons (s : ℚ) (fun _ : Fin 1 => (t : ℚ))) P

theorem eval_monomial_pair (c : ℚ) (e : Fin 2 →₀ ℕ) (s t : ℕ) :
    MvPolynomial.eval (Fin.cons (s : ℚ) (fun _ : Fin 1 => (t : ℚ)))
      (MvPolynomial.monomial e c)
      = c * (s : ℚ) ^ (e 0) * (t : ℚ) ^ (e 1) := by
  rw [MvPolynomial.eval_monomial,
    Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fin.prod_univ_two]
  simp only [Fin.cons_zero, Fin.cons_one]
  ring

theorem evalPair_eq_sum (P : BaseHilbertPolynomial) (s t : ℕ) :
    evalPair P s t = ∑ e ∈ P.support,
      P.coeff e * (s : ℚ) ^ (e 0) * (t : ℚ) ^ (e 1) := by
  unfold evalPair
  conv_lhs => rw [MvPolynomial.as_sum P]
  rw [MvPolynomial.eval_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [eval_monomial_pair]

/-- Every exponent splits into its two coordinates. -/
theorem fin2_decomp (e : Fin 2 →₀ ℕ) :
    e = Finsupp.single 0 (e 0) + Finsupp.single 1 (e 1) := by
  ext i
  fin_cases i <;> simp [Finsupp.add_apply]

theorem fin2_sum (e : Fin 2 →₀ ℕ) : e.sum (fun _ e => e) = e 0 + e 1 := by
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]

/-- Agreement on a quadrant forces equality (both variables range over naturals). -/
theorem pairPoly_unique {P Q : BaseHilbertPolynomial} {N : ℕ}
    (h : ∀ s t : ℕ, N ≤ s → N ≤ t → evalPair P s t = evalPair Q s t) :
    P = Q := by
  apply MvPolynomial.funext_set
    (fun _ : Fin 2 => Set.range (fun n : ℕ => ((N + n : ℕ) : ℚ)))
  · intro i
    apply Set.infinite_range_of_injective
    intro a b hab
    simp only at hab
    have h2 : N + a = N + b := by exact_mod_cast hab
    omega
  · intro x hx
    have h0 := hx 0 (Set.mem_univ 0)
    have h1 := hx 1 (Set.mem_univ 1)
    rw [Set.mem_range] at h0 h1
    obtain ⟨s, hs0⟩ := h0
    obtain ⟨t, ht1⟩ := h1
    have hxeq : x = Fin.cons (((N + s : ℕ)) : ℚ) (fun _ : Fin 1 => (((N + t : ℕ)) : ℚ)) := by
      ext i
      fin_cases i
      · simpa [Fin.cons_zero] using hs0.symm
      · simpa [Fin.cons_one] using ht1.symm
    rw [hxeq]
    exact h (N + s) (N + t) (Nat.le_add_right _ _) (Nat.le_add_right _ _)

/-- Univariate t-slice at fixed `s₀`, as an explicit polynomial. -/
noncomputable def sliceT (P : BaseHilbertPolynomial) (s₀ : ℕ) : Polynomial ℚ :=
  ∑ b ∈ Finset.range (P.totalDegree + 1),
    Polynomial.monomial b (∑ a ∈ Finset.range (P.totalDegree + 1),
      P.coeff (Finsupp.single 0 a + Finsupp.single 1 b) * (s₀ : ℚ) ^ a)

theorem sliceT_eval (P : BaseHilbertPolynomial) (s₀ t : ℕ) :
    (sliceT P s₀).eval (t : ℚ) = evalPair P s₀ t := by
  classical
  have hev : ∀ (s : Finset ℕ) (f : ℕ → Polynomial ℚ),
      Polynomial.eval (t : ℚ) (∑ i ∈ s, f i)
        = ∑ i ∈ s, Polynomial.eval (t : ℚ) (f i) :=
    fun s f => map_sum (Polynomial.evalRingHom (t : ℚ)) f s
  have hLHS : (sliceT P s₀).eval (t : ℚ) = ∑ x ∈ Finset.range (P.totalDegree + 1) ×ˢ
      Finset.range (P.totalDegree + 1), P.coeff (Finsupp.single 0 x.1 + Finsupp.single 1 x.2) *
      (s₀ : ℚ) ^ x.1 * (t : ℚ) ^ x.2 := by
    unfold sliceT
    rw [hev]
    simp only [Polynomial.eval_monomial, Finset.sum_mul]
    rw [Finset.sum_comm, ← Finset.sum_product']
  have hRHS : evalPair P s₀ t = ∑ x ∈ Finset.range (P.totalDegree + 1) ×ˢ
      Finset.range (P.totalDegree + 1), P.coeff (Finsupp.single 0 x.1 + Finsupp.single 1 x.2) *
      (s₀ : ℚ) ^ x.1 * (t : ℚ) ^ x.2 := by
    rw [evalPair_eq_sum]
    set S := (Finset.range (P.totalDegree + 1) ×ˢ Finset.range (P.totalDegree + 1)).filter
      (fun x : ℕ × ℕ => Finsupp.single 0 x.1 + Finsupp.single 1 x.2 ∈ P.support) with hS
    have step1 : (∑ e ∈ P.support, P.coeff e * (s₀ : ℚ) ^ (e 0) * (t : ℚ) ^ (e 1)) =
        ∑ x ∈ S, P.coeff (Finsupp.single 0 x.1 + Finsupp.single 1 x.2) *
          (s₀ : ℚ) ^ x.1 * (t : ℚ) ^ x.2 := by
      apply Finset.sum_bij (fun e _ => (e 0, e 1))
      · intro e he
        simp only [hS, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
        have hle := MvPolynomial.le_totalDegree he
        have hsum : e.sum (fun _ e => e) = e 0 + e 1 := fin2_sum e
        refine ⟨⟨by omega, by omega⟩, ?_⟩
        rw [← fin2_decomp e]
        exact he
      · intro e _ e' _ hee
        simp only [Prod.mk.injEq] at hee
        rw [fin2_decomp e, fin2_decomp e', hee.1, hee.2]
      · intro x hx
        simp only [hS, Finset.mem_filter, Finset.mem_product] at hx
        refine ⟨Finsupp.single 0 x.1 + Finsupp.single 1 x.2, hx.2, ?_⟩
        have h0 : (Finsupp.single 0 x.1 + Finsupp.single 1 x.2 : Fin 2 →₀ ℕ) 0
            = x.1 := by simp
        have h1 : (Finsupp.single 0 x.1 + Finsupp.single 1 x.2 : Fin 2 →₀ ℕ) 1
            = x.2 := by simp
        simp [h0, h1]
      · intro e he
        rw [← fin2_decomp e]
    have step2 : (∑ x ∈ S, P.coeff (Finsupp.single 0 x.1 + Finsupp.single 1 x.2) *
          (s₀ : ℚ) ^ x.1 * (t : ℚ) ^ x.2) =
        ∑ x ∈ Finset.range (P.totalDegree + 1) ×ˢ Finset.range (P.totalDegree + 1),
        P.coeff (Finsupp.single 0 x.1 + Finsupp.single 1 x.2) *
          (s₀ : ℚ) ^ x.1 * (t : ℚ) ^ x.2 := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro x hxR hxS
      have hnc : Finsupp.single 0 x.1 + Finsupp.single 1 x.2 ∉ P.support := by
        intro hc
        exact hxS (Finset.mem_filter.mpr ⟨hxR, hc⟩)
      have h0 : P.coeff (Finsupp.single 0 x.1 + Finsupp.single 1 x.2) = 0 := by
        by_contra hcon
        exact hnc (MvPolynomial.mem_support_iff.mpr hcon)
      simp [h0]
    rw [step1, step2]
  rw [hLHS, hRHS]

theorem sliceT_coeff_top (P : BaseHilbertPolynomial) (s₀ d : ℕ)
    (hdeg : P.totalDegree ≤ d) :
    (sliceT P s₀).coeff d = P.coeff (Finsupp.single 0 0 + Finsupp.single 1 d) := by
  have hsum : ∀ (e : Fin 2 →₀ ℕ), e.sum (fun _ e => e) = e 0 + e 1 := fun e => fin2_sum e
  unfold sliceT
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  by_cases hd : d ∈ Finset.range (P.totalDegree + 1)
  · rw [Finset.sum_eq_single d]
    · simp only [eq_self_iff_true, if_true]
      rw [Finset.sum_eq_single 0]
      · simp
      · intro a _ ha0
        have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha0
        have hoff : Finsupp.single 0 a + Finsupp.single 1 d ∉ P.support := by
          intro hc
          have hle := MvPolynomial.le_totalDegree hc
          rw [hsum] at hle
          have e0 : ((Finsupp.single 0 a + Finsupp.single 1 d : Fin 2 →₀ ℕ)) 0
              = a := by simp
          have e1 : ((Finsupp.single 0 a + Finsupp.single 1 d : Fin 2 →₀ ℕ)) 1
              = d := by simp
          omega
        have h0 : P.coeff (Finsupp.single 0 a + Finsupp.single 1 d) = 0 := by
          by_contra hcon
          exact hoff (MvPolynomial.mem_support_iff.mpr hcon)
        simp [h0]
      · intro hcon
        exact False.elim (hcon (Finset.mem_range.mpr (Nat.succ_pos _)))
    · intro b _ hbd
      rw [if_neg hbd]
    · intro hcon
      exact False.elim (hcon hd)
  · have hLHS : (∑ b ∈ Finset.range (P.totalDegree + 1),
        (if b = d then (∑ a ∈ Finset.range (P.totalDegree + 1),
          P.coeff (Finsupp.single 0 a + Finsupp.single 1 b) * (s₀ : ℚ) ^ a) else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      rw [if_neg]
      intro hcon
      exact hd (hcon ▸ hb)
    rw [hLHS]
    have hdD : P.totalDegree < d := by
      by_contra hcon
      push_neg at hcon
      exact hd (Finset.mem_range.mpr (by omega))
    have hoff : Finsupp.single (0 : Fin 2) 0 + Finsupp.single (1 : Fin 2) d ∉ P.support := by
      intro hc
      have hle := MvPolynomial.le_totalDegree hc
      have hs0 : ((Finsupp.single 0 0 + Finsupp.single 1 d : Fin 2 →₀ ℕ)).sum (fun _ e => e)
          = 0 + d := by
        rw [hsum]
        simp
      omega
    have hfin : P.coeff (Finsupp.single 0 0 + Finsupp.single 1 d) = 0 := by
      by_contra hcon
      exact hoff (MvPolynomial.mem_support_iff.mpr hcon)
    exact hfin.symm

theorem sliceT_natDegree_le (P : BaseHilbertPolynomial) (s₀ : ℕ) :
    (sliceT P s₀).natDegree ≤ P.totalDegree := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  unfold sliceT
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro b hb
  rw [Polynomial.coeff_monomial, if_neg]
  intro hcon
  have hbD : b < P.totalDegree + 1 := Finset.mem_range.mp hb
  omega

/-- Pure `(0,d)` coefficients are univariate slice leading coefficients. -/
theorem pure_top_nonneg (P : BaseHilbertPolynomial) (d : ℕ)
    (hdeg : P.totalDegree ≤ d) (N : ℕ)
    (hval : ∀ t : ℕ, N ≤ t → 0 ≤ evalPair P N t) :
    0 ≤ mixedHilbertCoefficient P 0 d := by
  unfold mixedHilbertCoefficient
  simp only [Nat.factorial_zero, Nat.cast_one, one_mul]
  have hRval : ∀ n : ℕ, N ≤ n →
      0 ≤ (sliceT P N).eval (n : ℚ) := by
    intro n hn
    rw [sliceT_eval]
    exact hval n hn
  have hdegR : (sliceT P N).natDegree ≤ d :=
    (sliceT_natDegree_le P N).trans hdeg
  have hcoeff : (sliceT P N).coeff d
      = P.coeff (Finsupp.single 0 0 + Finsupp.single 1 d) :=
    sliceT_coeff_top P N d hdeg
  by_cases hc : P.coeff (Finsupp.single 0 0 + Finsupp.single 1 d) = 0
  · rw [hc, mul_zero]
  · have hnat : (sliceT P N).natDegree = d := by
      apply le_antisymm hdegR
      have hlt : d ≤ (sliceT P N).natDegree := by
        by_contra hcon
        have hlt' : (sliceT P N).natDegree < d := not_le.mp hcon
        have hz := Polynomial.coeff_eq_zero_of_natDegree_lt hlt'
        rw [hcoeff] at hz
        exact hc hz
      exact hlt
    have hlead : (sliceT P N).leadingCoeff
        = P.coeff (Finsupp.single 0 0 + Finsupp.single 1 d) := by
      show (sliceT P N).coeff (sliceT P N).natDegree = _
      rw [hnat]
      exact hcoeff
    have hnn := OAI.PiExponentJets.W27.polynomial_leadingCoeff_nonneg_of_eventually_nonneg
      (sliceT P N) N (fun n hn => hRval n hn)
    rw [hlead] at hnn
    exact mul_nonneg (Nat.cast_nonneg _) hnn

/-- Finite difference in the first variable, as an explicit polynomial. -/
noncomputable def shiftSub (P : BaseHilbertPolynomial) : BaseHilbertPolynomial :=
  ∑ k ∈ Finset.range (P.totalDegree + 1), ∑ b ∈ Finset.range (P.totalDegree + 1),
    MvPolynomial.monomial (Finsupp.single 0 k + Finsupp.single 1 b)
      (∑ a ∈ Finset.range (P.totalDegree + 1),
        P.coeff (Finsupp.single 0 a + Finsupp.single 1 b) *
          (a.choose k : ℚ) * (-1 : ℚ) ^ (a - k))

theorem binom_sum_sub_one (s : ℚ) (a D : ℕ) (ha : a ≤ D) :
    (∑ k ∈ Finset.range (D + 1), (a.choose k : ℚ) * (-1 : ℚ) ^ (a - k) * s ^ k)
      = (s - 1) ^ a := by
  have hsub : Finset.range (a + 1) ⊆ Finset.range (D + 1) := by
    intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  have hzero : ∀ k ∈ Finset.range (D + 1), k ∉ Finset.range (a + 1) →
      (a.choose k : ℚ) * (-1 : ℚ) ^ (a - k) * s ^ k = 0 := by
    intro k _ hk
    have hlt : a < k := by
      simp only [Finset.mem_range, not_lt] at hk
      omega
    rw [Nat.choose_eq_zero_of_lt hlt, Nat.cast_zero, zero_mul, zero_mul]
  have hadd : (s - 1) ^ a
      = ∑ k ∈ Finset.range (a + 1), (a.choose k : ℚ) * (-1 : ℚ) ^ (a - k) * s ^ k := by
    have h := Commute.add_pow (mul_comm s (-1 : ℚ)) a
    rw [sub_eq_add_neg, h]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hadd]
  exact (Finset.sum_subset hsub hzero).symm

theorem eval_monomial_pair' (c : ℚ) (e : Fin 2 →₀ ℕ) (u v : ℚ) :
    MvPolynomial.eval (Fin.cons u (fun _ : Fin 1 => v))
      (MvPolynomial.monomial e c)
      = c * u ^ (e 0) * v ^ (e 1) := by
  rw [MvPolynomial.eval_monomial,
    Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fin.prod_univ_two]
  simp only [Fin.cons_zero, Fin.cons_one]
  ring

theorem shiftSub_inner_eq (P : BaseHilbertPolynomial) (d p q : ℕ)
    (hdeg : P.totalDegree ≤ d) (hpq : p + q = d) (hp : 1 ≤ p) :
    (∑ a ∈ Finset.range (P.totalDegree + 1),
      P.coeff (Finsupp.single 0 a + Finsupp.single 1 q) *
        (a.choose (p - 1) : ℚ) * (-1 : ℚ) ^ (a - (p - 1)))
    = P.coeff (Finsupp.single 0 (p - 1) + Finsupp.single 1 q)
      - (p : ℚ) * P.coeff (Finsupp.single 0 p + Finsupp.single 1 q) := by
  classical
  have hsum : ∀ (f : Fin 2 →₀ ℕ), f.sum (fun _ e => e) = f 0 + f 1 := fun f => fin2_sum f
  have hsub : Finset.range (P.totalDegree + 1) ⊆ Finset.range (d + 1) := by
    intro a ha
    simp only [Finset.mem_range] at ha ⊢
    omega
  have hext : (∑ a ∈ Finset.range (P.totalDegree + 1),
        P.coeff (Finsupp.single 0 a + Finsupp.single 1 q) *
          (a.choose (p - 1) : ℚ) * (-1 : ℚ) ^ (a - (p - 1)))
      = ∑ a ∈ Finset.range (d + 1),
        P.coeff (Finsupp.single 0 a + Finsupp.single 1 q) *
          (a.choose (p - 1) : ℚ) * (-1 : ℚ) ^ (a - (p - 1)) := by
    apply Finset.sum_subset hsub
    intro a _ haR
    have haD : P.totalDegree < a := by
      simp only [Finset.mem_range, not_lt] at haR
      omega
    have hoff : Finsupp.single 0 a + Finsupp.single 1 q ∉ P.support := by
      intro hc
      have hle := MvPolynomial.le_totalDegree hc
      rw [hsum] at hle
      have ea0 : ((Finsupp.single 0 a + Finsupp.single 1 q : Fin 2 →₀ ℕ)) 0
          = a := by simp
      have ea1 : ((Finsupp.single 0 a + Finsupp.single 1 q : Fin 2 →₀ ℕ)) 1
          = q := by simp
      omega
    have h0 : P.coeff (Finsupp.single 0 a + Finsupp.single 1 q) = 0 := by
      by_contra hcon
      exact hoff (MvPolynomial.mem_support_iff.mpr hcon)
    simp [h0]
  rw [hext]
  have hpair : ({p - 1, p} : Finset ℕ) ⊆ Finset.range (d + 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_range] at ha ⊢
    omega
  have hcoll : (∑ a ∈ Finset.range (d + 1),
        P.coeff (Finsupp.single 0 a + Finsupp.single 1 q) *
          (a.choose (p - 1) : ℚ) * (-1 : ℚ) ^ (a - (p - 1)))
      = ∑ a ∈ ({p - 1, p} : Finset ℕ),
        P.coeff (Finsupp.single 0 a + Finsupp.single 1 q) *
          (a.choose (p - 1) : ℚ) * (-1 : ℚ) ^ (a - (p - 1)) := by
    symm
    apply Finset.sum_subset hpair
    intro a _ haP
    simp only [Finset.mem_insert, Finset.mem_singleton] at haP
    by_cases ha : a < p - 1
    · have hb0 : (a.choose (p - 1) : ℚ) = 0 := by
        rw [Nat.choose_eq_zero_of_lt ha, Nat.cast_zero]
      simp [hb0]
    · have hgt : p < a := by omega
      have hoff : Finsupp.single 0 a + Finsupp.single 1 q ∉ P.support := by
        intro hc
        have hle := MvPolynomial.le_totalDegree hc
        rw [hsum] at hle
        have ea0 : ((Finsupp.single 0 a + Finsupp.single 1 q : Fin 2 →₀ ℕ)) 0
            = a := by simp
        have ea1 : ((Finsupp.single 0 a + Finsupp.single 1 q : Fin 2 →₀ ℕ)) 1
            = q := by simp
        omega
      have h0 : P.coeff (Finsupp.single 0 a + Finsupp.single 1 q) = 0 := by
        by_contra hcon
        exact hoff (MvPolynomial.mem_support_iff.mpr hcon)
      simp [h0]
  rw [hcoll]
  have hne : p - 1 ≠ p := by omega
  rw [Finset.sum_pair hne]
  have hF1 : P.coeff (Finsupp.single 0 (p - 1) + Finsupp.single 1 q) *
        ((p - 1).choose (p - 1) : ℚ) * (-1 : ℚ) ^ ((p - 1) - (p - 1))
      = P.coeff (Finsupp.single 0 (p - 1) + Finsupp.single 1 q) := by
    simp
  have hFp : P.coeff (Finsupp.single 0 p + Finsupp.single 1 q) *
        (p.choose (p - 1) : ℚ) * (-1 : ℚ) ^ (p - (p - 1))
      = - (p : ℚ) * P.coeff (Finsupp.single 0 p + Finsupp.single 1 q) := by
    obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
    have e1 : m + 1 - m = 1 := by omega
    have e2 : m + 1 - 1 = m := by omega
    rw [e2, Nat.choose_succ_self_right, e1, pow_one]
    ring
  rw [hF1, hFp]
  ring

/-- The first finite difference `ΔP(s,t) = P(s,t) - P(s-1,t)`. -/
theorem fin2_eq_of_single_eq {e : Fin 2 →₀ ℕ} {k b : ℕ}
    (h : Finsupp.single (0 : Fin 2) k + Finsupp.single (1 : Fin 2) b = e) :
    k = e 0 ∧ b = e 1 := by
  have h0 := congrArg (fun f : Fin 2 →₀ ℕ => f 0) h
  have h1 := congrArg (fun f : Fin 2 →₀ ℕ => f 1) h
  have e0 : ((Finsupp.single 0 k + Finsupp.single 1 b : Fin 2 →₀ ℕ)) 0 = k := by simp
  have e1 : ((Finsupp.single 0 k + Finsupp.single 1 b : Fin 2 →₀ ℕ)) 1 = b := by simp
  rw [e0] at h0
  rw [e1] at h1
  exact ⟨h0, h1⟩

theorem shiftSub_coeff_form (P : BaseHilbertPolynomial) (e : Fin 2 →₀ ℕ) :
    (shiftSub P).coeff e = ∑ k ∈ Finset.range (P.totalDegree + 1),
      ∑ b ∈ Finset.range (P.totalDegree + 1),
      (if Finsupp.single 0 k + Finsupp.single 1 b = e
        then (∑ a ∈ Finset.range (P.totalDegree + 1),
          P.coeff (Finsupp.single 0 a + Finsupp.single 1 b) *
            (a.choose k : ℚ) * (-1 : ℚ) ^ (a - k))
        else 0) := by
  unfold shiftSub
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]

theorem shiftSub_totalDegree_le (P : BaseHilbertPolynomial) :
    (shiftSub P).totalDegree ≤ P.totalDegree := by
  classical
  have hsum : ∀ (f : Fin 2 →₀ ℕ), f.sum (fun _ e => e) = f 0 + f 1 := fun f => fin2_sum f
  have hsup : ∀ e ∈ (shiftSub P).support,
      e.sum (fun _ e => e) ≤ P.totalDegree := by
    intro e he
    have hne : (shiftSub P).coeff e ≠ 0 :=
      MvPolynomial.mem_support_iff.mp he
    rw [shiftSub_coeff_form] at hne
    -- if e.sum > D, every (k,b,a) term vanishes
    by_contra hcon
    have hgt : P.totalDegree < e.sum (fun _ e => e) := not_le.mp hcon
    apply hne
    apply Finset.sum_eq_zero
    intro k _
    apply Finset.sum_eq_zero
    intro b _
    by_cases hkb : Finsupp.single 0 k + Finsupp.single 1 b = e
    · have hkb' := fin2_eq_of_single_eq hkb
      rw [if_pos hkb]
      apply Finset.sum_eq_zero
      intro a _
      by_cases ha : a < k
      · have hb0 : (a.choose k : ℚ) = 0 := by
          rw [Nat.choose_eq_zero_of_lt ha, Nat.cast_zero]
        simp [hb0]
      · have hka : k ≤ a := not_lt.mp ha
        have hoff : Finsupp.single 0 a + Finsupp.single 1 b ∉ P.support := by
          intro hc
          have hle := MvPolynomial.le_totalDegree hc
          rw [hsum] at hle
          have ea0 : ((Finsupp.single 0 a + Finsupp.single 1 b : Fin 2 →₀ ℕ)) 0
              = a := by simp
          have ea1 : ((Finsupp.single 0 a + Finsupp.single 1 b : Fin 2 →₀ ℕ)) 1
              = b := by simp
          have hse : e.sum (fun _ e => e) = e 0 + e 1 := hsum e
          omega
        have h0 : P.coeff (Finsupp.single 0 a + Finsupp.single 1 b) = 0 := by
          by_contra hcon2
          exact hoff (MvPolynomial.mem_support_iff.mpr hcon2)
        simp [h0]
    · rw [if_neg hkb]
  show (shiftSub P).support.sup (fun s => s.sum fun _ e => e) ≤ P.totalDegree
  exact Finset.sup_le hsup

theorem shiftSub_coeff_top (P : BaseHilbertPolynomial) (d : ℕ)
    (hdeg : P.totalDegree ≤ d) (e : Fin 2 →₀ ℕ)
    (he : e.sum (fun _ e => e) = d) :
    (shiftSub P).coeff e = P.coeff e := by
  classical
  have hkb : ∀ k b : ℕ, Finsupp.single (0 : Fin 2) k + Finsupp.single (1 : Fin 2) b = e →
      k = e 0 ∧ b = e 1 := by
    intro k b h
    have h0 := congrArg (fun f : Fin 2 →₀ ℕ => f 0) h
    have h1 := congrArg (fun f : Fin 2 →₀ ℕ => f 1) h
    have e0 : ((Finsupp.single 0 k + Finsupp.single 1 b : Fin 2 →₀ ℕ)) 0 = k := by simp
    have e1 : ((Finsupp.single 0 k + Finsupp.single 1 b : Fin 2 →₀ ℕ)) 1 = b := by simp
    rw [e0] at h0
    rw [e1] at h1
    exact ⟨h0, h1⟩
  have hsum : ∀ (f : Fin 2 →₀ ℕ), f.sum (fun _ e => e) = f 0 + f 1 := fun f => fin2_sum f
  rw [shiftSub_coeff_form]
  by_cases hmem : e 0 ∈ Finset.range (P.totalDegree + 1) ∧
      e 1 ∈ Finset.range (P.totalDegree + 1)
  · rw [Finset.sum_eq_single (e 0)]
    · rw [Finset.sum_eq_single (e 1)]
      · have hif : Finsupp.single (0 : Fin 2) (e 0) + Finsupp.single (1 : Fin 2) (e 1)
            = e := (fin2_decomp e).symm
        rw [if_pos hif]
        rw [Finset.sum_eq_single (e 0)]
        · simp only [Nat.choose_self, Nat.cast_one, Nat.sub_self, pow_zero, mul_one, hif]
        · intro a _ hae
          by_cases ha : a < e 0
          · have hb0 : (a.choose (e 0) : ℚ) = 0 := by
              rw [Nat.choose_eq_zero_of_lt ha, Nat.cast_zero]
            simp [hb0]
          · have hlt : e 0 < a := by
              have hle : e 0 ≤ a := not_lt.mp ha
              omega
            have hoff : Finsupp.single 0 a + Finsupp.single 1 (e 1) ∉ P.support := by
              intro hc
              have hle2 := MvPolynomial.le_totalDegree hc
              rw [hsum] at hle2
              have ea0 : ((Finsupp.single 0 a + Finsupp.single 1 (e 1) : Fin 2 →₀ ℕ)) 0
                  = a := by simp
              have ea1 : ((Finsupp.single 0 a + Finsupp.single 1 (e 1) : Fin 2 →₀ ℕ)) 1
                  = e 1 := by simp
              have hse : e.sum (fun _ e => e) = e 0 + e 1 := hsum e
              omega
            have h0 : P.coeff (Finsupp.single 0 a + Finsupp.single 1 (e 1)) = 0 := by
              by_contra hcon
              exact hoff (MvPolynomial.mem_support_iff.mpr hcon)
            simp [h0]
        · intro hcon
          exact False.elim (hcon hmem.1)
      · intro b _ hbe
        rw [if_neg]
        intro hcon
        exact hbe ((hkb _ _ hcon).2)
      · intro hcon
        exact False.elim (hcon hmem.2)
    · intro k _ hke
      apply Finset.sum_eq_zero
      intro b _
      rw [if_neg]
      intro hcon
      exact hke ((hkb _ _ hcon).1)
    · intro hcon
      exact False.elim (hcon hmem.1)
  · -- outside the ranges: both sides vanish
    have hLHS : (∑ k ∈ Finset.range (P.totalDegree + 1),
        ∑ b ∈ Finset.range (P.totalDegree + 1),
        (if Finsupp.single 0 k + Finsupp.single 1 b = e
          then (∑ a ∈ Finset.range (P.totalDegree + 1),
            P.coeff (Finsupp.single 0 a + Finsupp.single 1 b) *
              (a.choose k : ℚ) * (-1 : ℚ) ^ (a - k))
          else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      apply Finset.sum_eq_zero
      intro b hb
      rw [if_neg]
      intro hcon
      have hkb' := hkb k b hcon
      exact hmem ⟨hkb'.1 ▸ hk, hkb'.2 ▸ hb⟩
    rw [hLHS]
    have hbig : P.totalDegree < e.sum (fun _ e => e) := by
      rw [hsum]
      simp only [Finset.mem_range, not_lt] at hmem ⊢
      omega
    have hoff : e ∉ P.support := by
      intro hc
      have hle := MvPolynomial.le_totalDegree hc
      omega
    have hfin : P.coeff e = 0 := by
      by_contra hcon
      exact hoff (MvPolynomial.mem_support_iff.mpr hcon)
    exact hfin.symm

/-- `evalPair` as nested range sums (no support reindexing needed by callers). -/
theorem evalPair_eq_nested (P : BaseHilbertPolynomial) (u t : ℕ) :
    evalPair P u t = ∑ b ∈ Finset.range (P.totalDegree + 1),
      ∑ a ∈ Finset.range (P.totalDegree + 1),
      P.coeff (Finsupp.single 0 a + Finsupp.single 1 b) * (u : ℚ) ^ a * (t : ℚ) ^ b := by
  have hev : ∀ (s : Finset ℕ) (f : ℕ → Polynomial ℚ),
      Polynomial.eval (t : ℚ) (∑ i ∈ s, f i)
        = ∑ i ∈ s, Polynomial.eval (t : ℚ) (f i) :=
    fun s f => map_sum (Polynomial.evalRingHom (t : ℚ)) f s
  rw [← sliceT_eval]
  unfold sliceT
  rw [hev]
  simp only [Polynomial.eval_monomial, Finset.sum_mul]

/-- `shiftSub P` evaluates as `P` with the first variable decreased by one. -/
theorem shiftSub_eval_nested (P : BaseHilbertPolynomial) (s : ℚ) (t : ℕ) :
    MvPolynomial.eval (Fin.cons s (fun _ : Fin 1 => (t : ℚ))) (shiftSub P) =
    ∑ b ∈ Finset.range (P.totalDegree + 1), ∑ a ∈ Finset.range (P.totalDegree + 1),
      P.coeff (Finsupp.single 0 a + Finsupp.single 1 b) * (s - 1) ^ a * (t : ℚ) ^ b := by
  classical
  have hevM : ∀ (S : Finset (Fin 2 →₀ ℕ)) (f : (Fin 2 →₀ ℕ) → MvPolynomial (Fin 2) ℚ),
      MvPolynomial.eval (Fin.cons s (fun _ : Fin 1 => (t : ℚ))) (∑ i ∈ S, f i)
        = ∑ i ∈ S, MvPolynomial.eval (Fin.cons s (fun _ : Fin 1 => (t : ℚ))) (f i) :=
    fun S f => MvPolynomial.eval_sum S f _
  have hev1 : ∀ (k b : ℕ), MvPolynomial.eval (Fin.cons s (fun _ : Fin 1 => (t : ℚ)))
      (MvPolynomial.monomial (Finsupp.single 0 k + Finsupp.single 1 b)
        (∑ a ∈ Finset.range (P.totalDegree + 1),
          P.coeff (Finsupp.single 0 a + Finsupp.single 1 b) *
            (a.choose k : ℚ) * (-1 : ℚ) ^ (a - k)))
      = (∑ a ∈ Finset.range (P.totalDegree + 1),
          P.coeff (Finsupp.single 0 a + Finsupp.single 1 b) *
            (a.choose k : ℚ) * (-1 : ℚ) ^ (a - k)) *
        s ^ k * (t : ℚ) ^ b := by
    intro k b
    have e0 : ((Finsupp.single 0 k + Finsupp.single 1 b : Fin 2 →₀ ℕ)) 0 = k := by simp
    have e1 : ((Finsupp.single 0 k + Finsupp.single 1 b : Fin 2 →₀ ℕ)) 1 = b := by simp
    rw [eval_monomial_pair' _ _ s _, e0, e1]
  unfold shiftSub
  simp only [MvPolynomial.eval_sum]
  simp only [hev1, Finset.sum_mul]
  have perm : (∑ k ∈ Finset.range (P.totalDegree + 1),
        ∑ b ∈ Finset.range (P.totalDegree + 1), ∑ a ∈ Finset.range (P.totalDegree + 1),
        P.coeff (Finsupp.single 0 a + Finsupp.single 1 b) *
          (a.choose k : ℚ) * (-1 : ℚ) ^ (a - k) * s ^ k * (t : ℚ) ^ b)
      = ∑ a ∈ Finset.range (P.totalDegree + 1), ∑ b ∈ Finset.range (P.totalDegree + 1),
        ∑ k ∈ Finset.range (P.totalDegree + 1),
        P.coeff (Finsupp.single 0 a + Finsupp.single 1 b) *
          (a.choose k : ℚ) * (-1 : ℚ) ^ (a - k) * s ^ k * (t : ℚ) ^ b := by
    calc (∑ k ∈ Finset.range (P.totalDegree + 1),
          ∑ b ∈ Finset.range (P.totalDegree + 1), ∑ a ∈ Finset.range (P.totalDegree + 1), _) =
        _ := Finset.sum_congr rfl (fun k _ => Finset.sum_comm)
      _ = _ := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
  rw [perm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have hbin : (∑ k ∈ Finset.range (P.totalDegree + 1),
        P.coeff (Finsupp.single 0 a + Finsupp.single 1 b) *
          (a.choose k : ℚ) * (-1 : ℚ) ^ (a - k) * s ^ k * (t : ℚ) ^ b)
      = P.coeff (Finsupp.single 0 a + Finsupp.single 1 b) * (s - 1) ^ a * (t : ℚ) ^ b := by
    have hfactor : ∀ k ∈ Finset.range (P.totalDegree + 1),
        P.coeff (Finsupp.single 0 a + Finsupp.single 1 b) *
          (a.choose k : ℚ) * (-1 : ℚ) ^ (a - k) * s ^ k * (t : ℚ) ^ b =
        P.coeff (Finsupp.single 0 a + Finsupp.single 1 b) * (t : ℚ) ^ b *
          ((a.choose k : ℚ) * (-1 : ℚ) ^ (a - k) * s ^ k) := by
      intro k _
      ring
    rw [Finset.sum_congr rfl hfactor, ← Finset.mul_sum]
    by_cases ha : a ∈ Finset.range (P.totalDegree + 1)
    · have ha' : a ≤ P.totalDegree := by
        simp only [Finset.mem_range] at ha
        omega
      rw [binom_sum_sub_one s a _ ha']
      ring
    · have h0 : P.coeff (Finsupp.single 0 a + Finsupp.single 1 b) = 0 := by
        have haD : P.totalDegree < a := by
          simp only [Finset.mem_range, not_lt] at ha
          omega
        have hoff : Finsupp.single 0 a + Finsupp.single 1 b ∉ P.support := by
          intro hc
          have hle := MvPolynomial.le_totalDegree hc
          have hsum : ∀ (e : Fin 2 →₀ ℕ), e.sum (fun _ e => e) = e 0 + e 1 :=
            fun e => fin2_sum e
          rw [hsum] at hle
          have e0 : ((Finsupp.single 0 a + Finsupp.single 1 b : Fin 2 →₀ ℕ)) 0
              = a := by simp
          have e1 : ((Finsupp.single 0 a + Finsupp.single 1 b : Fin 2 →₀ ℕ)) 1
              = b := by simp
          omega
        by_contra hcon
        exact hoff (MvPolynomial.mem_support_iff.mpr hcon)
      simp [h0]
  exact hbin

noncomputable def deltaP (P : BaseHilbertPolynomial) : BaseHilbertPolynomial :=
  P - shiftSub P

theorem shiftSub_eval_nat (P : BaseHilbertPolynomial) (s t : ℕ) (hs : 1 ≤ s) :
    evalPair (shiftSub P) s t = evalPair P (s - 1) t := by
  have h1 := shiftSub_eval_nested P (s : ℚ) t
  have h2 := evalPair_eq_nested P (s - 1) t
  have hcast : (s : ℚ) - 1 = (((s - 1 : ℕ)) : ℚ) := (Nat.cast_sub hs).symm
  show MvPolynomial.eval (Fin.cons (s : ℚ) _) (shiftSub P) = evalPair P (s - 1) t
  rw [h1]
  rw [hcast]
  rw [← h2]

theorem deltaP_eval (P : BaseHilbertPolynomial) (s t : ℕ) (hs : 1 ≤ s) :
    evalPair (deltaP P) s t = evalPair P s t - evalPair P (s - 1) t := by
  have hssE : MvPolynomial.eval (Fin.cons (s : ℚ) (fun _ : Fin 1 => (t : ℚ))) (shiftSub P)
      = evalPair P (s - 1) t :=
    shiftSub_eval_nat P s t hs
  unfold deltaP
  show MvPolynomial.eval (Fin.cons (s : ℚ) _) (P - shiftSub P)
    = evalPair P s t - evalPair P (s - 1) t
  rw [MvPolynomial.eval_sub, hssE]

theorem deltaP_totalDegree (P : BaseHilbertPolynomial) (d : ℕ)
    (hdeg : P.totalDegree ≤ d) (hd : 1 ≤ d) :
    (deltaP P).totalDegree ≤ d - 1 := by
  classical
  have hsum : ∀ (f : Fin 2 →₀ ℕ), f.sum (fun _ e => e) = f 0 + f 1 := fun f => fin2_sum f
  have hsup : ∀ e ∈ (deltaP P).support,
      e.sum (fun _ e => e) ≤ d - 1 := by
    intro e he
    have hle : e.sum (fun _ e => e) ≤ d := by
      have hmem : e ∈ (deltaP P).support := he
      -- coeff is difference of coeffs, support in union
      have hmem' : e ∈ P.support ∨ e ∈ (shiftSub P).support := by
        by_contra hcon
        push_neg at hcon
        have hP0 : P.coeff e = 0 := by
          by_contra hc2
          exact hcon.1 (MvPolynomial.mem_support_iff.mpr hc2)
        have hS0 : (shiftSub P).coeff e = 0 := by
          by_contra hc2
          exact hcon.2 (MvPolynomial.mem_support_iff.mpr hc2)
        have hD0 : (deltaP P).coeff e = 0 := by
          unfold deltaP
          simp only [MvPolynomial.coeff_sub, hP0, hS0, sub_zero]
        exact (MvPolynomial.mem_support_iff.mp he) hD0
      rcases hmem' with hP | hS
      · have := MvPolynomial.le_totalDegree hP
        omega
      · have hleS : e.sum (fun _ e => e) ≤ (shiftSub P).totalDegree := by
          have := MvPolynomial.le_totalDegree hS
          omega
        have := shiftSub_totalDegree_le P
        omega
    by_contra hcon
    have hcon' : d - 1 < e.sum (fun _ e => e) := not_le.mp hcon
    -- e.sum ≤ d but ≰ d-1, so = d; top cancels
    have heq : e.sum (fun _ e => e) = d := by omega
    have htop : (deltaP P).coeff e = 0 := by
      unfold deltaP
      rw [MvPolynomial.coeff_sub]
      rw [shiftSub_coeff_top P d hdeg e heq]
      simp
    exact (MvPolynomial.mem_support_iff.mp he) htop
  show (deltaP P).support.sup (fun s => s.sum fun _ e => e) ≤ d - 1
  exact Finset.sup_le hsup

theorem deltaP_coeff_mid (P : BaseHilbertPolynomial) (d p q : ℕ)
    (hdeg : P.totalDegree ≤ d) (hpq : p + q = d) (hp : 1 ≤ p) :
    (deltaP P).coeff (Finsupp.single 0 (p - 1) + Finsupp.single 1 q)
      = (p : ℚ) * P.coeff (Finsupp.single 0 p + Finsupp.single 1 q) := by
  classical
  have hD : ∀ (f : Fin 2 →₀ ℕ), f.sum (fun _ e => e) = f 0 + f 1 := fun f => fin2_sum f
  have hmain : (deltaP P).coeff (Finsupp.single 0 (p - 1) + Finsupp.single 1 q)
      = P.coeff (Finsupp.single 0 (p - 1) + Finsupp.single 1 q)
        - (shiftSub P).coeff (Finsupp.single 0 (p - 1) + Finsupp.single 1 q) := by
    unfold deltaP
    rw [MvPolynomial.coeff_sub]
  rw [hmain, shiftSub_coeff_form]
  -- S(p-1,q) = c_{(p-1,q)} - p * c_{(p,q)}
  have hS : (∑ k ∈ Finset.range (P.totalDegree + 1),
        ∑ b ∈ Finset.range (P.totalDegree + 1),
        (if Finsupp.single (0 : Fin 2) k + Finsupp.single (1 : Fin 2) b
            = Finsupp.single 0 (p - 1) + Finsupp.single 1 q
          then (∑ a ∈ Finset.range (P.totalDegree + 1),
            P.coeff (Finsupp.single 0 a + Finsupp.single 1 b) *
              (a.choose k : ℚ) * (-1 : ℚ) ^ (a - k))
          else 0))
      = P.coeff (Finsupp.single 0 (p - 1) + Finsupp.single 1 q)
        - (p : ℚ) * P.coeff (Finsupp.single 0 p + Finsupp.single 1 q) := by
    have hbase : ∀ k b : ℕ,
        Finsupp.single (0 : Fin 2) k + Finsupp.single (1 : Fin 2) b
          = Finsupp.single 0 (p - 1) + Finsupp.single 1 q ↔ k = p - 1 ∧ b = q :=
      fun k b => DistinctDistances.TrackB.IncidenceBinomial.base_exponents_eq k b (p - 1) q
    have hSval : (∑ a ∈ Finset.range (P.totalDegree + 1),
          P.coeff (Finsupp.single 0 a + Finsupp.single 1 q) *
            (a.choose (p - 1) : ℚ) * (-1 : ℚ) ^ (a - (p - 1)))
        = P.coeff (Finsupp.single 0 (p - 1) + Finsupp.single 1 q)
          - (p : ℚ) * P.coeff (Finsupp.single 0 p + Finsupp.single 1 q) :=
      shiftSub_inner_eq P d p q hdeg hpq hp
    by_cases hmem : (p - 1 ∈ Finset.range (P.totalDegree + 1)) ∧
        (q ∈ Finset.range (P.totalDegree + 1))
    · obtain ⟨hk, hq⟩ := hmem
      rw [Finset.sum_eq_single (p - 1)]
      · rw [Finset.sum_eq_single q]
        · rw [if_pos rfl]
          exact hSval
        · intro b _ hbe
          rw [if_neg]
          intro hcon
          exact hbe ((hbase _ _).mp hcon).2
        · intro hcon
          exact False.elim (hcon hq)
      · intro k _ hke
        apply Finset.sum_eq_zero
        intro b _
        rw [if_neg]
        intro hcon
        exact hke (((hbase _ _).mp hcon).1)
      · intro hcon
        exact False.elim (hcon hk)
    · -- outside: double sum vanishes, and both target coeffs vanish
      have hDbl : (∑ k ∈ Finset.range (P.totalDegree + 1),
          ∑ b ∈ Finset.range (P.totalDegree + 1),
          (if Finsupp.single (0 : Fin 2) k + Finsupp.single (1 : Fin 2) b
              = Finsupp.single 0 (p - 1) + Finsupp.single 1 q
            then (∑ a ∈ Finset.range (P.totalDegree + 1),
              P.coeff (Finsupp.single 0 a + Finsupp.single 1 b) *
                (a.choose k : ℚ) * (-1 : ℚ) ^ (a - k))
            else 0)) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        apply Finset.sum_eq_zero
        intro b hb
        rw [if_neg]
        intro hcon
        have hkb := (hbase _ _).mp hcon
        exact hmem ⟨hkb.1 ▸ hk, hkb.2 ▸ hb⟩
      have hsum2 : ∀ (f : Fin 2 →₀ ℕ), f.sum (fun _ e => e) = f 0 + f 1 :=
        fun f => fin2_sum f
      have hc1 : P.coeff (Finsupp.single 0 (p - 1) + Finsupp.single 1 q) = 0 := by
        have h1 : P.totalDegree < (p - 1) + q := by
          simp only [Finset.mem_range] at hmem
          omega
        have hoff : Finsupp.single 0 (p - 1) + Finsupp.single 1 q ∉ P.support := by
          intro hc
          have hle := MvPolynomial.le_totalDegree hc
          rw [hsum2] at hle
          have ea0 : ((Finsupp.single 0 (p - 1) + Finsupp.single 1 q : Fin 2 →₀ ℕ)) 0
              = p - 1 := by simp
          have ea1 : ((Finsupp.single 0 (p - 1) + Finsupp.single 1 q : Fin 2 →₀ ℕ)) 1
              = q := by simp
          omega
        by_contra hcon
        exact hoff (MvPolynomial.mem_support_iff.mpr hcon)
      have hc2 : P.coeff (Finsupp.single 0 p + Finsupp.single 1 q) = 0 := by
        have h2 : P.totalDegree < p + q := by
          simp only [Finset.mem_range] at hmem
          omega
        have hoff : Finsupp.single 0 p + Finsupp.single 1 q ∉ P.support := by
          intro hc
          have hle := MvPolynomial.le_totalDegree hc
          rw [hsum2] at hle
          have ea0 : ((Finsupp.single 0 p + Finsupp.single 1 q : Fin 2 →₀ ℕ)) 0
              = p := by simp
          have ea1 : ((Finsupp.single 0 p + Finsupp.single 1 q : Fin 2 →₀ ℕ)) 1
              = q := by simp
          omega
        by_contra hcon
        exact hoff (MvPolynomial.mem_support_iff.mpr hcon)
      rw [hDbl, hc1, hc2, mul_zero, sub_zero]
  rw [hS]
  ring

/-! ## §B. Bigraded Hilbert side -/

variable {n m : ℕ}

/-- Section rank for an arbitrary block-homogeneous ideal. -/
def rankJ (J : Ideal (MvPolynomial (Fin (n + m)) ℂ)) (s t : ℕ) : ℕ :=
  Module.finrank ℂ ↥(HilbertMulti.sectionSpace
    (HilbertMulti.blockWeight (HilbertMulti.pairBlocks n m)) J
    (HilbertMulti.pairDegree s t))

theorem canonHP_eventually (J : Ideal (MvPolynomial (Fin (n + m)) ℂ))
    (hJ : J.IsHomogeneous (MvPolynomial.weightedHomogeneousSubmodule ℂ
      (HilbertMulti.blockWeight (HilbertMulti.pairBlocks n m)))) :
    ∃ Q : BaseHilbertPolynomial, ∃ N : ℕ, ∀ s t : ℕ, N ≤ s → N ≤ t →
      evalPair Q s t = ((rankJ J s t : ℕ) : ℚ) := by
  obtain ⟨Q, N, hQ⟩ := HilbertMulti.exists_polynomial (HilbertMulti.pairBlocks n m) J hJ
  refine ⟨Q, N, fun s t hs ht => ?_⟩
  have hd : ∀ j : Fin 2, N ≤ HilbertMulti.pairDegree s t j := by
    intro j
    fin_cases j
    · simpa [HilbertMulti.pairDegree] using hs
    · simpa [HilbertMulti.pairDegree] using ht
  have h := hQ (HilbertMulti.pairDegree s t) hd
  have hev : (fun j : Fin 2 => ((HilbertMulti.pairDegree s t j : ℕ) : ℚ))
      = Fin.cons (s : ℚ) (fun _ : Fin 1 => (t : ℚ)) := by
    ext j
    fin_cases j <;> rfl
  rw [hev] at h
  exact h

theorem pairDegree_add {s t : ℕ} (hs : 1 ≤ s) :
    HilbertMulti.pairDegree (s - 1) t + Finsupp.single (0 : Fin 2) 1
      = HilbertMulti.pairDegree s t := by
  ext j
  fin_cases j
  · simp [HilbertMulti.pairDegree, Finsupp.add_apply]
    omega
  · simp [HilbertMulti.pairDegree, Finsupp.add_apply]

/-- For a vanishing ideal, `rankJ` is the actual `pairHilbert` function. -/
theorem rankJ_pairHilbert (T : Set (ProjectivePoint n × ProjectivePoint m))
    (s t : ℕ) :
    rankJ (MvPolynomial.vanishingIdeal ℂ (pairRepresentatives T)) s t
      = pairHilbert T s t := by
  have hsub : HilbertMulti.sectionSpace
      (HilbertMulti.blockWeight (HilbertMulti.pairBlocks n m))
      (MvPolynomial.vanishingIdeal ℂ (pairRepresentatives T))
      (HilbertMulti.pairDegree s t) = pairSection T s t := by
    unfold HilbertMulti.sectionSpace pairSection
    rw [HilbertMulti.pairBlockPiece]
  unfold rankJ pairHilbert
  rw [hsub]

theorem rankJ_mono {J K : Ideal (MvPolynomial (Fin (n + m)) ℂ)} (hJK : J ≤ K)
    (s t : ℕ) : rankJ K s t ≤ rankJ J s t := by
  unfold rankJ
  have hsurj := HilbertMulti.sectionFactor_surjective
    (HilbertMulti.blockWeight (HilbertMulti.pairBlocks n m)) J K hJK
    (HilbertMulti.pairDegree s t)
  have hdim := (HilbertMulti.sectionFactor
    (HilbertMulti.blockWeight (HilbertMulti.pairBlocks n m)) J K hJK
    (HilbertMulti.pairDegree s t)).finrank_range_le
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at hdim
  exact hdim

/-- Top homogeneous part (degree `e`) as a polynomial. -/
noncomputable def topPart (R : BaseHilbertPolynomial) (e : ℕ) : BaseHilbertPolynomial :=
  ∑ e' ∈ R.support.filter (fun e' => e'.sum (fun _ e => e) = e),
    MvPolynomial.monomial e' (R.coeff e')

theorem topPart_eval (R : BaseHilbertPolynomial) (e s₀ t₀ : ℕ) :
    evalPair (topPart R e) s₀ t₀ = ∑ e' ∈ R.support.filter
      (fun e' => e'.sum (fun _ e => e) = e),
      R.coeff e' * (s₀ : ℚ) ^ (e' 0) * (t₀ : ℚ) ^ (e' 1) := by
  unfold topPart evalPair
  rw [MvPolynomial.eval_sum]
  apply Finset.sum_congr rfl
  intro e' _
  rw [eval_monomial_pair]

/-- A nonzero homogeneous polynomial takes a nonzero value at a positive point. -/
theorem topPart_pos_point {T : BaseHilbertPolynomial} {eQ : ℕ}
    (hne : T ≠ 0) (hhom : ∀ e ∈ T.support, e.sum (fun _ e => e) = eQ) :
    ∃ s₀ t₀ : ℕ, 1 ≤ s₀ ∧ 1 ≤ t₀ ∧
      MvPolynomial.eval (Fin.cons ((s₀ : ℕ) : ℚ) (fun _ : Fin 1 => ((t₀ : ℕ) : ℚ))) T ≠ 0 := by
  classical
  -- U(λ) := T(1+λ, 1)
  set U : Polynomial ℚ := ∑ e ∈ T.support,
    Polynomial.C (T.coeff e) * ((Polynomial.X + 1) ^ (e 0)) with hU
  have hUeval : ∀ lam : ℚ, U.eval lam
      = MvPolynomial.eval (Fin.cons (1 + lam) (fun _ : Fin 1 => 1)) T := by
    intro lam
    have hevP : ∀ (s : Finset (Fin 2 →₀ ℕ)) (f : (Fin 2 →₀ ℕ) → Polynomial ℚ),
        Polynomial.eval lam (∑ i ∈ s, f i)
          = ∑ i ∈ s, Polynomial.eval lam (f i) :=
      fun s f => map_sum (Polynomial.evalRingHom lam) f s
    rw [hU, hevP]
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_C]
    conv_rhs => rw [MvPolynomial.as_sum T, MvPolynomial.eval_sum]
    apply Finset.sum_congr rfl
    intro e _
    rw [eval_monomial_pair']
    ring
  have hUne : U ≠ 0 := by
    intro hU0
    -- V(s) := T(s,1) vanishes everywhere, so V = 0, so all coeffs vanish
    have hV0 : ∀ s : ℚ, MvPolynomial.eval (Fin.cons s (fun _ : Fin 1 => 1)) T = 0 := by
      intro s
      have hzz : U.eval (s - 1) = 0 := by rw [hU0]; simp
      rw [hUeval] at hzz
      have hsimp : (1 : ℚ) + (s - 1) = s := by ring
      rwa [hsimp] at hzz
    set V : Polynomial ℚ := ∑ e ∈ T.support,
      Polynomial.monomial (e 0) (T.coeff e) with hV
    have hVeval : ∀ s : ℚ, V.eval s
        = MvPolynomial.eval (Fin.cons s (fun _ : Fin 1 => 1)) T := by
      intro s
      have hevP : ∀ (st : Finset (Fin 2 →₀ ℕ)) (f : (Fin 2 →₀ ℕ) → Polynomial ℚ),
          Polynomial.eval s (∑ i ∈ st, f i)
            = ∑ i ∈ st, Polynomial.eval s (f i) :=
        fun st f => map_sum (Polynomial.evalRingHom s) f st
      rw [hV, hevP]
      simp only [Polynomial.eval_monomial]
      conv_rhs => rw [MvPolynomial.as_sum T, MvPolynomial.eval_sum]
      apply Finset.sum_congr rfl
      intro e _
      rw [eval_monomial_pair']
      ring
    have hVeq : V = 0 := by
      apply Polynomial.eq_of_infinite_eval_eq
      have hinf : (Set.univ : Set ℚ).Infinite := Set.infinite_univ
      apply hinf.mono
      intro x _
      show V.eval x = (0 : Polynomial ℚ).eval x
      rw [hVeval x, hV0 x, Polynomial.eval_zero]
    -- every support coefficient is a coefficient of V, hence 0
    have hcall : ∀ e ∈ T.support, T.coeff e = 0 := by
      intro e he
      have hcoeff : V.coeff (e 0) = T.coeff e := by
        rw [hV, Polynomial.finsetSum_coeff]
        rw [Finset.sum_eq_single e]
        · simp
        · intro e' he' hne
          rw [Polynomial.coeff_monomial, if_neg]
          intro hcon
          -- e' 0 = e 0 plus homogeneity forces e' = e
          have h1 : e' 1 = e 1 := by
            have s1 := hhom e' he'
            have s2 := hhom e he
            have t1 : e'.sum (fun _ e => e) = e' 0 + e' 1 := fin2_sum e'
            have t2 : e.sum (fun _ e => e) = e 0 + e 1 := fin2_sum e
            omega
          exact hne (by rw [fin2_decomp e, fin2_decomp e', hcon, h1])
        · intro hcon
          exact False.elim (hcon he)
      rw [hVeq] at hcoeff
      simpa using hcoeff.symm
    apply hne
    rw [MvPolynomial.ext_iff]
    intro e
    by_cases he : e ∈ T.support
    · exact hcall e he
    · have h0 : T.coeff e = 0 := by
        by_contra hcon
        exact he (MvPolynomial.mem_support_iff.mpr hcon)
      rw [h0]
      simp
  -- pick λ₀ with U(λ₀) ≠ 0
  have hex : ∃ lam : ℕ, U.eval (lam : ℚ) ≠ 0 := by
    by_contra hcon
    have h0 : ∀ n : ℕ, U.eval (n : ℚ) = 0 :=
      fun n => not_not.mp (not_exists.mp hcon n)
    have hU0 : U = 0 := by
      apply Polynomial.eq_of_infinite_eval_eq
      have hinf := Set.infinite_range_of_injective
        (f := fun n : ℕ => (n : ℚ)) (fun a b hab => by
          simp only [] at hab
          exact_mod_cast hab)
      apply hinf.mono
      intro x hx
      obtain ⟨n, rfl⟩ := Set.mem_range.mp hx
      show U.eval _ = (0 : Polynomial ℚ).eval _
      rw [h0 n, Polynomial.eval_zero]
    exact hUne hU0
  obtain ⟨lam, hlam⟩ := hex
  refine ⟨1 + lam, 1, Nat.le_add_right _ _, le_rfl, ?_⟩
  simp only [Nat.cast_add, Nat.cast_one]
  rw [← hUeval]
  exact hlam


/-- If every first-factor linear form lies in `J`, all positive-`s` ranks vanish. -/
theorem rankJ_eq_zero_of_firstSpace_le (J : Ideal (MvPolynomial (Fin (n + m)) ℂ))
    (hV : ∀ ℓ ∈ MvPolynomial.weightedHomogeneousSubmodule ℂ
      (HilbertMulti.blockWeight (HilbertMulti.pairBlocks n m)) (Finsupp.single 0 1),
      ℓ ∈ J)
    (s t : ℕ) (hs : 1 ≤ s) : rankJ J s t = 0 := by
  classical
  have hpb : ∀ j : Fin n,
      HilbertMulti.pairBlocks n m (Fin.castAdd m j) = 0 := by
    intro j
    simp [HilbertMulti.pairBlocks]
  have hXmem : ∀ j : Fin n, MvPolynomial.X (Fin.castAdd m j : Fin (n + m))
      ∈ MvPolynomial.weightedHomogeneousSubmodule ℂ
        (HilbertMulti.blockWeight (HilbertMulti.pairBlocks n m))
        (Finsupp.single 0 1) := by
    intro j
    rw [MvPolynomial.mem_weightedHomogeneousSubmodule]
    have hX := MvPolynomial.isWeightedHomogeneous_X ℂ
      (HilbertMulti.blockWeight (HilbertMulti.pairBlocks n m)) (Fin.castAdd m j)
    have hw : HilbertMulti.blockWeight (HilbertMulti.pairBlocks n m) (Fin.castAdd m j)
        = Finsupp.single (0 : Fin 2) 1 := by
      show Finsupp.single (HilbertMulti.pairBlocks n m (Fin.castAdd m j)) 1 = _
      rw [hpb j]
    rw [hw] at hX
    exact hX
  have hmon : ∀ (a : Fin (n + m) →₀ ℕ) (c : ℂ),
      (∑ i : Fin n, a (Fin.castAdd m i)) = s →
      MvPolynomial.monomial a c ∈ J := by
    intro a c ha
    -- some first-block coordinate is positive
    have hex : ∃ j : Fin n, 1 ≤ a (Fin.castAdd m j) := by
      by_contra hcon
      have h0 : ∀ j : Fin n, a (Fin.castAdd m j) = 0 := by
        intro j
        have hj := not_exists.mp hcon j
        omega
      have hsum0 : (∑ i : Fin n, a (Fin.castAdd m i)) = 0 :=
        Finset.sum_eq_zero (fun j _ => h0 j)
      omega
    obtain ⟨j, hj⟩ := hex
    have hle : Finsupp.single (Fin.castAdd m j) 1 ≤ a :=
      Finsupp.single_le_iff.mpr hj
    have hsplit : a = Finsupp.single (Fin.castAdd m j) 1 +
        (a - Finsupp.single (Fin.castAdd m j) 1) :=
      (add_tsub_cancel_of_le hle).symm
    have hXeq : MvPolynomial.monomial (Finsupp.single (Fin.castAdd m j) 1) (1 : ℂ)
        = MvPolynomial.X (Fin.castAdd m j : Fin (n + m)) := rfl
    have hXu : MvPolynomial.X (Fin.castAdd m j : Fin (n + m)) ∈ J :=
      hV _ (hXmem j)
    have hprod : MvPolynomial.monomial (Finsupp.single (Fin.castAdd m j) 1) (1 : ℂ) *
        MvPolynomial.monomial (a - Finsupp.single (Fin.castAdd m j) 1) c
        = MvPolynomial.monomial a c := by
      rw [MvPolynomial.monomial_mul_monomial, one_mul, hsplit.symm]
    rw [← hprod, hXeq]
    exact Ideal.mul_mem_right _ _ hXu
  -- every piece element lies in J, so the section is zero
  have hbot : HilbertMulti.sectionSpace
      (HilbertMulti.blockWeight (HilbertMulti.pairBlocks n m)) J
      (HilbertMulti.pairDegree s t) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hx
    -- p is in the weighted piece; rewrite to restrictSupport form
    have hpS : p ∈ MvPolynomial.restrictSupport ℂ {a : Fin (n + m) →₀ ℕ |
        (∑ i : Fin n, a (Fin.castAdd m i)) = s ∧
        (∑ i : Fin m, a (Fin.natAdd n i)) = t} := by
      have hpiece : MvPolynomial.weightedHomogeneousSubmodule ℂ
          (HilbertMulti.blockWeight (HilbertMulti.pairBlocks n m))
          (HilbertMulti.pairDegree s t)
          = MvPolynomial.restrictSupport ℂ {a : Fin (n + m) →₀ ℕ |
            (∑ i : Fin n, a (Fin.castAdd m i)) = s ∧
            (∑ i : Fin m, a (Fin.natAdd n i)) = t} := by
        rw [HilbertMulti.pairBlockPiece]
      rw [hpiece] at hp
      -- hpiece RHS set vs goal set: same up to bound names; exact hp after defeq? use `exact hp` (defeq via rfl-proof? hpiece's proof ends with rfl meaning the two sides are defeq, so hp already has goal type up to defeq → `exact hp` works)
      exact hp
    have hmem : p ∈ J := by
      have hsum : p = ∑ a ∈ p.support, MvPolynomial.monomial a (p.coeff a) :=
        MvPolynomial.as_sum p
      rw [hsum]
      refine Ideal.sum_mem _ fun a ha => ?_
      have haS : (∑ i : Fin n, a (Fin.castAdd m i)) = s ∧
          (∑ i : Fin m, a (Fin.natAdd n i)) = t := by
        have hsub : (↑p.support : Set (Fin (n + m) →₀ ℕ)) ⊆ {a : Fin (n + m) →₀ ℕ |
            (∑ i : Fin n, a (Fin.castAdd m i)) = s ∧
            (∑ i : Fin m, a (Fin.natAdd n i)) = t} := by
          rwa [MvPolynomial.mem_restrictSupport_iff] at hpS
        exact hsub (Finset.mem_coe.mpr ha)
      exact hmon a _ haS.1
    have hzero : (Ideal.Quotient.mkₐ ℂ J).toLinearMap p = 0 := by
      have h1 : (Ideal.Quotient.mkₐ ℂ J).toLinearMap p = Ideal.Quotient.mk J p := rfl
      rw [h1]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    exact hzero
  unfold rankJ
  rw [hbot]
  exact finrank_bot ℂ _

/-- In the trivial case the Hilbert polynomial itself vanishes. -/
theorem trivial_poly_eq_zero (J : Ideal (MvPolynomial (Fin (n + m)) ℂ))
    (hV : ∀ ℓ ∈ MvPolynomial.weightedHomogeneousSubmodule ℂ
      (HilbertMulti.blockWeight (HilbertMulti.pairBlocks n m)) (Finsupp.single 0 1),
      ℓ ∈ J)
    (P : BaseHilbertPolynomial)
    (hevent : ∃ N : ℕ, ∀ s t : ℕ, N ≤ s → N ≤ t →
      evalPair P s t = ((rankJ J s t : ℕ) : ℚ)) : P = 0 := by
  obtain ⟨N, hN⟩ := hevent
  apply pairPoly_unique (Q := 0) (N := max N 1)
  intro s t hs ht
  have hs1 : 1 ≤ s := le_trans (Nat.le_max_right _ _) hs
  have hNs : N ≤ s := le_trans (Nat.le_max_left _ _) hs
  have hNt : N ≤ t := le_trans (Nat.le_max_left _ _) ht
  have hPs : evalPair P s t = 0 := by
    rw [hN s t hNs hNt, rankJ_eq_zero_of_firstSpace_le J hV s t hs1, Nat.cast_zero]
  have hQs : evalPair (0 : BaseHilbertPolynomial) s t = 0 := by
    show MvPolynomial.eval (Fin.cons (s : ℚ) (fun _ : Fin 1 => (t : ℚ)))
      (0 : BaseHilbertPolynomial) = 0
    exact map_zero _
  rw [hPs, hQs]

/-- The top part of a positive-degree polynomial is nonzero. -/
theorem topPart_ne_zero {Q : BaseHilbertPolynomial} {eQ : ℕ}
    (hdeg : 1 ≤ eQ) (heQ : Q.totalDegree = eQ) : topPart Q eQ ≠ 0 := by
  intro h0
  have hneQ : Q ≠ 0 := by
    intro hQ0
    rw [hQ0, MvPolynomial.totalDegree_zero] at heQ
    omega
  have hsupN : Q.support.Nonempty := by
    by_contra hcon
    apply hneQ
    rw [MvPolynomial.ext_iff]
    intro e
    by_contra hc2
    exact hcon ⟨e, MvPolynomial.mem_support_iff.mpr hc2⟩
  obtain ⟨e₀, he₀mem, he₀sup⟩ := Finset.exists_mem_eq_sup _
    hsupN (fun s => s.sum fun _ e => e)
  have he₀deg : e₀.sum (fun _ e => e) = eQ := by
    have hdef : Q.support.sup (fun s => s.sum fun _ e => e) = Q.totalDegree := rfl
    omega
  have hQc : Q.coeff e₀ ≠ 0 := MvPolynomial.mem_support_iff.mp he₀mem
  have hTc : (topPart Q eQ).coeff e₀ = Q.coeff e₀ := by
    unfold topPart
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    rw [Finset.sum_eq_single e₀]
    · simp
    · intro e' _ hne
      rw [if_neg]
      intro hcon
      exact hne hcon
    · intro hcon
      exact False.elim (hcon (Finset.mem_filter.mpr ⟨he₀mem, he₀deg⟩))
  have hTne : (topPart Q eQ).coeff e₀ ≠ 0 := by
    rw [hTc]
    exact hQc
  exact hTne (by rw [h0]; simp)

/-- Evaluation on the ray `k ↦ (k·s₀, k·t₀)` as a univariate polynomial. -/
noncomputable def linePoly (F : BaseHilbertPolynomial) (s₀ t₀ : ℕ) : Polynomial ℚ :=
  ∑ e ∈ F.support,
    Polynomial.monomial (e.sum (fun _ e => e))
      (F.coeff e * (s₀ : ℚ) ^ (e 0) * (t₀ : ℚ) ^ (e 1))

theorem linePoly_eval (F : BaseHilbertPolynomial) (s₀ t₀ k : ℕ) :
    (linePoly F s₀ t₀).eval (k : ℚ)
      = evalPair F (k * s₀) (k * t₀) := by
  have hev : ∀ (s : Finset (Fin 2 →₀ ℕ)) (f : (Fin 2 →₀ ℕ) → Polynomial ℚ),
      Polynomial.eval (k : ℚ) (∑ i ∈ s, f i)
        = ∑ i ∈ s, Polynomial.eval (k : ℚ) (f i) :=
    fun s f => map_sum (Polynomial.evalRingHom (k : ℚ)) f s
  unfold linePoly
  rw [hev]
  simp only [Polynomial.eval_monomial]
  rw [evalPair_eq_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [fin2_sum e]
  simp only [Nat.cast_mul]
  ring

theorem linePoly_coeff_top (F : BaseHilbertPolynomial) (eQ s₀ t₀ : ℕ)
    (hdeg : F.totalDegree ≤ eQ) :
    (linePoly F s₀ t₀).coeff eQ
      = ∑ e' ∈ F.support.filter (fun e' => e'.sum (fun _ e => e) = eQ),
      F.coeff e' * (s₀ : ℚ) ^ (e' 0) * (t₀ : ℚ) ^ (e' 1) := by
  classical
  unfold linePoly
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [← Finset.sum_filter]

/-- Hilbert functions control polynomial degrees from above. -/
theorem totalDegree_le_of_rank_le {J K : Ideal (MvPolynomial (Fin (n + m)) ℂ)}
    (hle : ∀ s t : ℕ, rankJ K s t ≤ rankJ J s t)
    {P Q : BaseHilbertPolynomial} {d N : ℕ}
    (hP : ∀ s t : ℕ, N ≤ s → N ≤ t → evalPair P s t = ((rankJ J s t : ℕ) : ℚ))
    (hQ : ∀ s t : ℕ, N ≤ s → N ≤ t → evalPair Q s t = ((rankJ K s t : ℕ) : ℚ))
    (hdeg : P.totalDegree ≤ d) : Q.totalDegree ≤ d := by
  classical
  by_contra hcon
  have hlt : d < Q.totalDegree := not_le.mp hcon
  have heQ1 : 1 ≤ Q.totalDegree := by omega
  -- top part of Q (also of R := Q - P)
  set T : BaseHilbertPolynomial := topPart Q Q.totalDegree with hT
  have hTne : T ≠ 0 :=
    topPart_ne_zero (by omega) rfl
  have hhomT : ∀ e ∈ T.support, e.sum (fun _ e => e) = Q.totalDegree := by
    intro e he
    by_contra hcon2
    have h0 : T.coeff e = 0 := by
      rw [hT]
      unfold topPart
      simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
      apply Finset.sum_eq_zero
      intro e' he'
      rw [if_neg]
      intro hcon3
      -- e' = e would put e in the filter
      have hmem : e ∈ Q.support.filter (fun e' => e'.sum (fun _ e => e) = Q.totalDegree) := by
        rw [← hcon3]
        exact he'
      have := (Finset.mem_filter.mp hmem).2
      exact hcon2 this
    exact (MvPolynomial.mem_support_iff.mp he) h0
  obtain ⟨s₀, t₀, hs₀, ht₀, hTne0⟩ := topPart_pos_point hTne hhomT
  -- line polynomials and their top coefficients
  have hTeval : (linePoly Q s₀ t₀).coeff Q.totalDegree
      = MvPolynomial.eval (Fin.cons ((s₀ : ℕ) : ℚ) (fun _ : Fin 1 => ((t₀ : ℕ) : ℚ))) T := by
    rw [linePoly_coeff_top Q _ _ _ le_rfl, ← topPart_eval, hT]
  -- support degree bounds for Q and R := Q - P
  have hQsup : ∀ e ∈ Q.support, e.sum (fun _ e => e) ≤ Q.totalDegree := by
    intro e he
    exact MvPolynomial.le_totalDegree he
  have hRsup : ∀ e ∈ (Q - P).support, e.sum (fun _ e => e) ≤ Q.totalDegree := by
    intro e he
    have hne : (Q - P).coeff e ≠ 0 := MvPolynomial.mem_support_iff.mp he
    rw [MvPolynomial.coeff_sub] at hne
    by_cases hQc : Q.coeff e = 0
    · have hPc : P.coeff e ≠ 0 := by
        intro hPc
        rw [hQc, hPc, sub_zero] at hne
        exact hne rfl
      have hmem : e ∈ P.support := MvPolynomial.mem_support_iff.mpr hPc
      have hle := MvPolynomial.le_totalDegree hmem
      omega
    · have hmem : e ∈ Q.support := MvPolynomial.mem_support_iff.mpr hQc
      exact MvPolynomial.le_totalDegree hmem
  have hRdeg : (Q - P).totalDegree ≤ Q.totalDegree := by
    show (Q - P).support.sup (fun s => s.sum fun _ e => e) ≤ Q.totalDegree
    exact Finset.sup_le hRsup
  -- P vanishes on degree-eQ exponents
  have hPvan : ∀ e : Fin 2 →₀ ℕ, e.sum (fun _ e => e) = Q.totalDegree → P.coeff e = 0 := by
    intro e he
    by_contra hcon
    have hmem : e ∈ P.support := MvPolynomial.mem_support_iff.mpr hcon
    have hle := MvPolynomial.le_totalDegree hmem
    omega
  -- R and Q agree on degree-eQ exponents, hence have the same top filter
  have hRQc : ∀ e : Fin 2 →₀ ℕ, e.sum (fun _ e => e) = Q.totalDegree →
      (Q - P).coeff e = Q.coeff e := by
    intro e he
    rw [MvPolynomial.coeff_sub, hPvan e he, sub_zero]
  have hfilT_eq : (Q - P).support.filter (fun e => e.sum (fun _ e => e) = Q.totalDegree)
      = Q.support.filter (fun e => e.sum (fun _ e => e) = Q.totalDegree) := by
    apply Finset.ext
    intro e
    simp only [Finset.mem_filter]
    constructor
    · intro ⟨hr, hdeg⟩
      have hR : (Q - P).coeff e ≠ 0 := MvPolynomial.mem_support_iff.mp hr
      rw [hRQc e hdeg] at hR
      exact ⟨MvPolynomial.mem_support_iff.mpr hR, hdeg⟩
    · intro ⟨hq, hdeg⟩
      have hR : (Q - P).coeff e ≠ 0 := by
        rw [hRQc e hdeg]
        exact MvPolynomial.mem_support_iff.mp hq
      exact ⟨MvPolynomial.mem_support_iff.mpr hR, hdeg⟩
  have hTevalR : (linePoly (Q - P) s₀ t₀).coeff Q.totalDegree
      = MvPolynomial.eval (Fin.cons ((s₀ : ℕ) : ℚ) (fun _ : Fin 1 => ((t₀ : ℕ) : ℚ))) T := by
    rw [linePoly_coeff_top _ _ _ _ hRdeg]
    have hconv : (∑ e' ∈ (Q - P).support.filter (fun e' => e'.sum (fun _ e => e) = Q.totalDegree),
        (Q - P).coeff e' * (s₀ : ℚ) ^ (e' 0) * (t₀ : ℚ) ^ (e' 1))
        = ∑ e' ∈ Q.support.filter (fun e' => e'.sum (fun _ e => e) = Q.totalDegree),
        Q.coeff e' * (s₀ : ℚ) ^ (e' 0) * (t₀ : ℚ) ^ (e' 1) := by
      rw [hfilT_eq]
      apply Finset.sum_congr rfl
      intro e he
      have hdeg : e.sum (fun _ e => e) = Q.totalDegree :=
        (Finset.mem_filter.mp he).2
      rw [hRQc e hdeg]
    rw [hconv]
    exact (linePoly_coeff_top Q _ _ _ le_rfl).symm.trans hTeval
  -- natDegree bounds
  have hdegQ : (linePoly Q s₀ t₀).natDegree ≤ Q.totalDegree := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    unfold linePoly
    rw [Polynomial.finsetSum_coeff]
    apply Finset.sum_eq_zero
    intro e he
    rw [Polynomial.coeff_monomial, if_neg]
    intro hcon
    have hle := hQsup e he
    omega
  have hdegR : (linePoly (Q - P) s₀ t₀).natDegree ≤ Q.totalDegree := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    unfold linePoly
    rw [Polynomial.finsetSum_coeff]
    apply Finset.sum_eq_zero
    intro e he
    rw [Polynomial.coeff_monomial, if_neg]
    intro hcon
    have hle := hRsup e he
    omega
  -- exact degrees and leading coefficients
  have hnatQ : (linePoly Q s₀ t₀).natDegree = Q.totalDegree := by
    apply le_antisymm hdegQ
    by_contra hcon
    have hlt' : (linePoly Q s₀ t₀).natDegree < Q.totalDegree := not_le.mp hcon
    have hz := Polynomial.coeff_eq_zero_of_natDegree_lt hlt'
    rw [hTeval] at hz
    exact hTne0 hz
  have hnatR : (linePoly (Q - P) s₀ t₀).natDegree = Q.totalDegree := by
    apply le_antisymm hdegR
    by_contra hcon
    have hlt' : (linePoly (Q - P) s₀ t₀).natDegree < Q.totalDegree := not_le.mp hcon
    have hz := Polynomial.coeff_eq_zero_of_natDegree_lt hlt'
    rw [hTevalR] at hz
    exact hTne0 hz
  have hleadQ : (linePoly Q s₀ t₀).leadingCoeff
      = MvPolynomial.eval (Fin.cons ((s₀ : ℕ) : ℚ) (fun _ : Fin 1 => ((t₀ : ℕ) : ℚ))) T := by
    show (linePoly Q s₀ t₀).coeff (linePoly Q s₀ t₀).natDegree = _
    rw [hnatQ]
    exact hTeval
  have hleadR : (linePoly (Q - P) s₀ t₀).leadingCoeff
      = MvPolynomial.eval (Fin.cons ((s₀ : ℕ) : ℚ) (fun _ : Fin 1 => ((t₀ : ℕ) : ℚ))) T := by
    show (linePoly (Q - P) s₀ t₀).coeff (linePoly (Q - P) s₀ t₀).natDegree = _
    rw [hnatR]
    exact hTevalR
  -- eventual signs on the ray
  have hmemN : ∀ k : ℕ, N ≤ k → N ≤ k * s₀ ∧ N ≤ k * t₀ := by
    intro k hk
    have hs1 : 1 ≤ s₀ := hs₀
    have ht1 : 1 ≤ t₀ := ht₀
    have hks : k ≤ k * s₀ := by
      conv_lhs => rw [← mul_one k]
      exact Nat.mul_le_mul_left k hs1
    have hkt : k ≤ k * t₀ := by
      conv_lhs => rw [← mul_one k]
      exact Nat.mul_le_mul_left k ht1
    exact ⟨le_trans hk hks, le_trans hk hkt⟩
  have hQnn : 0 ≤ (linePoly Q s₀ t₀).leadingCoeff := by
    apply OAI.PiExponentJets.W27.polynomial_leadingCoeff_nonneg_of_eventually_nonneg _ N
    intro n hn
    rw [linePoly_eval]
    obtain ⟨hs, ht⟩ := hmemN n hn
    rw [hQ _ _ hs ht]
    positivity
  rw [hleadQ] at hQnn
  have hRval : ∀ s t : ℕ, N ≤ s → N ≤ t →
      evalPair (Q - P) s t = ((rankJ K s t : ℕ) : ℚ) - ((rankJ J s t : ℕ) : ℚ) := by
    intro s t hs ht
    have e1 : MvPolynomial.eval (Fin.cons (s : ℚ) (fun _ : Fin 1 => (t : ℚ))) Q
        = ((rankJ K s t : ℕ) : ℚ) := hQ s t hs ht
    have e2 : MvPolynomial.eval (Fin.cons (s : ℚ) (fun _ : Fin 1 => (t : ℚ))) P
        = ((rankJ J s t : ℕ) : ℚ) := hP s t hs ht
    show MvPolynomial.eval (Fin.cons (s : ℚ) _) (Q - P) = _ - _
    rw [MvPolynomial.eval_sub, e1, e2]
  have hRnn : 0 ≤ (-(linePoly (Q - P) s₀ t₀)).leadingCoeff := by
    apply OAI.PiExponentJets.W27.polynomial_leadingCoeff_nonneg_of_eventually_nonneg _ N
    intro n hn
    have hneg : (-(linePoly (Q - P) s₀ t₀)).eval (n : ℚ)
        = -((linePoly (Q - P) s₀ t₀).eval (n : ℚ)) :=
      map_neg (Polynomial.evalRingHom (n : ℚ)) _
    rw [hneg, linePoly_eval]
    obtain ⟨hs, ht⟩ := hmemN n hn
    rw [hRval _ _ hs ht]
    have hle' : ((rankJ K (n * s₀) (n * t₀) : ℕ) : ℚ)
        ≤ ((rankJ J (n * s₀) (n * t₀) : ℕ) : ℚ) :=
      Nat.cast_le.mpr (hle _ _)
    have : ((rankJ K (n * s₀) (n * t₀) : ℕ) : ℚ) - ((rankJ J (n * s₀) (n * t₀) : ℕ) : ℚ) ≤ 0 :=
      sub_nonpos.mpr hle'
    linarith
  rw [Polynomial.leadingCoeff_neg, hleadR] at hRnn
  -- conclude: T-eval is both ≤ 0 and ≥ 0, hence 0, contradiction
  have hTeq : MvPolynomial.eval (Fin.cons ((s₀ : ℕ) : ℚ) (fun _ : Fin 1 => ((t₀ : ℕ) : ℚ))) T
      = 0 := le_antisymm (neg_nonneg.mp hRnn) hQnn
  exact hTne0 hTeq



/-- Nonnegativity for arbitrary block-homogeneous ideals, by induction. -/
theorem mixed_nonneg_aux (d : ℕ) :
    ∀ (J : Ideal (MvPolynomial (Fin (n + m)) ℂ)),
    J.IsHomogeneous (MvPolynomial.weightedHomogeneousSubmodule ℂ
      (HilbertMulti.blockWeight (HilbertMulti.pairBlocks n m))) →
    ∀ (P : BaseHilbertPolynomial), P.totalDegree ≤ d →
    (∃ N : ℕ, ∀ s t : ℕ, N ≤ s → N ≤ t →
      evalPair P s t = ((rankJ J s t : ℕ) : ℚ)) →
    ∀ p q : ℕ, p + q = d → 0 ≤ mixedHilbertCoefficient P p q := by
  induction d with
  | zero =>
    intro J hJ P hdeg hevent p q hpq
    classical
    obtain ⟨N, hN⟩ := hevent
    have hp0 : p = 0 := by omega
    have hq0 : q = 0 := by omega
    subst hp0
    subst hq0
    apply pure_top_nonneg P 0 hdeg N
    intro t ht
    rw [hN N t le_rfl ht]
    positivity
  | succ d ihd =>
    intro J hJ
    induction J using WellFoundedGT.induction with
    | _ J ihJ =>
      intro P hdeg hevent p q hpq
      classical
      obtain ⟨N, hN⟩ := hevent
      by_cases hp0 : p = 0
      · subst hp0
        simp only [zero_add] at hpq
        subst hpq
        apply pure_top_nonneg P (d + 1) hdeg N
        intro t ht
        rw [hN N t le_rfl ht]
        positivity
      · -- p ≥ 1: slice in the first factor
        obtain ⟨mm, rfl⟩ : ∃ mm, p = mm + 1 := ⟨p - 1, by omega⟩
        have hpq' : mm + 1 + q = d + 1 := hpq
        -- split on whether all (1,0)-forms lie in J
        by_cases hV : ∀ ℓ ∈ MvPolynomial.weightedHomogeneousSubmodule ℂ
            (HilbertMulti.blockWeight (HilbertMulti.pairBlocks n m))
            (Finsupp.single 0 1), ℓ ∈ J
        · -- trivial case: P vanishes
          have hP0 : P = 0 := trivial_poly_eq_zero J hV P ⟨N, hN⟩
          rw [hP0]
          unfold mixedHilbertCoefficient
          simp
        · -- pick ℓ outside J
          obtain ⟨ℓ, hℓV, hℓJ⟩ : ∃ ℓ ∈ MvPolynomial.weightedHomogeneousSubmodule ℂ
              (HilbertMulti.blockWeight (HilbertMulti.pairBlocks n m))
              (Finsupp.single 0 1), ℓ ∉ J := by
            by_contra hcon
            apply hV
            intro l hl
            by_contra hc
            exact hcon ⟨l, hl, hc⟩
          have hℓ : MvPolynomial.IsWeightedHomogeneous
              (HilbertMulti.blockWeight (HilbertMulti.pairBlocks n m)) ℓ
              (Finsupp.single 0 1) :=
            (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mp hℓV
          set J' : Ideal (MvPolynomial (Fin (n + m)) ℂ) :=
            Ideal.span {ℓ} ⊔ J with hJ'def
          have hJ' : J'.IsHomogeneous (MvPolynomial.weightedHomogeneousSubmodule ℂ
              (HilbertMulti.blockWeight (HilbertMulti.pairBlocks n m))) := by
            show (Ideal.span {ℓ} ⊔ J).IsHomogeneous _
            apply Ideal.IsHomogeneous.sup _ hJ
            apply Ideal.homogeneous_span
            intro x hx
            obtain rfl := Set.mem_singleton_iff.mp hx
            exact ⟨_, hℓ⟩
          set C : Ideal (MvPolynomial (Fin (n + m)) ℂ) :=
            J.colon {ℓ} with hCdef
          have hC : C.IsHomogeneous (MvPolynomial.weightedHomogeneousSubmodule ℂ
              (HilbertMulti.blockWeight (HilbertMulti.pairBlocks n m))) := by
            show (J.colon {ℓ}).IsHomogeneous _
            exact HilbertMulti.homogeneous_colon _ J hJ hℓ
          obtain ⟨P', N', hP'⟩ := canonHP_eventually J' hJ'
          obtain ⟨Cpoly, NC, hCpoly⟩ := canonHP_eventually C hC
          -- pointwise rank identity for s ≥ 1
          have hrank : ∀ s t : ℕ, 1 ≤ s →
              rankJ J s t = rankJ J' s t + rankJ C (s - 1) t := by
            intro s t hs
            unfold rankJ
            have hstep := HilbertMulti.colon_rank_step
              (HilbertMulti.blockWeight (HilbertMulti.pairBlocks n m)) J hJ ℓ hℓ
              (HilbertMulti.pairDegree (s - 1) t)
            rw [pairDegree_add hs] at hstep
            rw [hJ'def, hCdef]
            omega
          -- polynomial identity
          have hpoly : P = P' + shiftSub Cpoly := by
            apply pairPoly_unique (N := N + N' + NC + 2)
            intro s t hs ht
            have eP := hN s t (by omega) (by omega)
            have eP' := hP' s t (by omega) (by omega)
            have eC := hCpoly (s - 1) t (by omega) (by omega)
            have hrank := hrank s t (by omega)
            have eS := shiftSub_eval_nat Cpoly s t (by omega)
            have heq : evalPair (P' + shiftSub Cpoly) s t
                = evalPair P' s t + evalPair (shiftSub Cpoly) s t := by
              show MvPolynomial.eval _ (P' + shiftSub Cpoly) = _ + _
              exact MvPolynomial.eval_add
            rw [heq, eP', eS, eC]
            rw [eP, hrank]
            push_cast
            ring
          -- degree bounds via comparison (align thresholds first)
          have hNat : ∀ s t : ℕ, max N (max N' NC) ≤ s → max N (max N' NC) ≤ t →
              evalPair P s t = ((rankJ J s t : ℕ) : ℚ) := by
            intro s t hs ht
            exact hN s t (by omega) (by omega)
          have hNat' : ∀ s t : ℕ, max N (max N' NC) ≤ s → max N (max N' NC) ≤ t →
              evalPair P' s t = ((rankJ J' s t : ℕ) : ℚ) := by
            intro s t hs ht
            exact hP' s t (by omega) (by omega)
          have hNatC : ∀ s t : ℕ, max N (max N' NC) ≤ s → max N (max N' NC) ≤ t →
              evalPair Cpoly s t = ((rankJ C s t : ℕ) : ℚ) := by
            intro s t hs ht
            exact hCpoly s t (by omega) (by omega)
          have hdegP' : P'.totalDegree ≤ d + 1 :=
            totalDegree_le_of_rank_le (fun s t => rankJ_mono le_sup_right s t)
              hNat hNat' hdeg
          have hdegC : Cpoly.totalDegree ≤ d + 1 :=
            totalDegree_le_of_rank_le
              (fun s t => rankJ_mono
                (OAI.PiExponentJets.W64.ideal_le_colon_singleton J ℓ) s t)
              hNat hNatC hdeg
          by_cases hreg : C = J
          · -- regular: quotient is the finite difference; degree drops
            have hCP : Cpoly = P := by
              apply pairPoly_unique (N := max NC N)
              intro s t hs ht
              have h1 : N ≤ s := le_trans (Nat.le_max_right _ _) hs
              have h2 : N ≤ t := le_trans (Nat.le_max_right _ _) ht
              have h3 : NC ≤ s := le_trans (Nat.le_max_left _ _) hs
              have h4 : NC ≤ t := le_trans (Nat.le_max_left _ _) ht
              rw [hCpoly s t h3 h4, hreg]
              rw [← hN s t h1 h2]
            have hP'delta : P' = deltaP P := by
              have h2 : P = P' + shiftSub P := hCP ▸ hpoly
              unfold deltaP
              exact eq_sub_iff_add_eq.mpr h2.symm
            -- mixed(P,m+1,q) = mixed(P',m,q) ≥ 0 by IH at d
            have hval : mixedHilbertCoefficient P' mm q
                = mixedHilbertCoefficient P (mm + 1) q := by
              have hmid : (deltaP P).coeff
                  (Finsupp.single 0 mm + Finsupp.single 1 q)
                  = ((mm + 1 : ℕ) : ℚ) * P.coeff
                    (Finsupp.single 0 (mm + 1) + Finsupp.single 1 q) := by
                have h := deltaP_coeff_mid P (d + 1) (mm + 1) q hdeg hpq' (by omega)
                simpa only [Nat.add_sub_cancel] using h
              unfold mixedHilbertCoefficient
              rw [hP'delta]
              rw [hmid, Nat.factorial_succ]
              push_cast
              ring
            rw [← hval]
            apply ihd J' hJ' P' _ ⟨N', hP'⟩ mm q (by omega)
            rw [hP'delta]
            exact deltaP_totalDegree P (d + 1) hdeg (by omega)
          · -- zerodivisor: both pieces are strictly bigger; Noetherian step
            have hJlt : J < J' := by
              have hle : J ≤ Ideal.span {ℓ} ⊔ J := le_sup_right
              have hne : J ≠ Ideal.span {ℓ} ⊔ J := by
                intro hcon
                have hmem : ℓ ∈ Ideal.span {ℓ} ⊔ J :=
                  Submodule.mem_sup_left (Ideal.mem_span_singleton_self ℓ)
                rw [← hcon] at hmem
                exact hℓJ hmem
              exact lt_of_le_of_ne hle hne
            have hClt : J < C := by
              show J < J.colon {ℓ}
              apply lt_of_le_of_ne
                (OAI.PiExponentJets.W64.ideal_le_colon_singleton J ℓ)
              exact Ne.symm hreg
            have hcoeff : mixedHilbertCoefficient P (mm + 1) q
                = mixedHilbertCoefficient P' (mm + 1) q
                  + mixedHilbertCoefficient Cpoly (mm + 1) q := by
              have h1 : mixedHilbertCoefficient (P' + shiftSub Cpoly) (mm + 1) q
                  = mixedHilbertCoefficient P' (mm + 1) q
                    + mixedHilbertCoefficient (shiftSub Cpoly) (mm + 1) q := by
                have h := map_add
                  (DistinctDistances.TrackB.IncidenceBinomial.mixedHilbertLinearMap
                    (mm + 1) q) P' (shiftSub Cpoly)
                rwa [DistinctDistances.TrackB.IncidenceBinomial.mixedHilbertLinearMap_apply,
                  DistinctDistances.TrackB.IncidenceBinomial.mixedHilbertLinearMap_apply,
                  DistinctDistances.TrackB.IncidenceBinomial.mixedHilbertLinearMap_apply] at h
              have hS : mixedHilbertCoefficient (shiftSub Cpoly) (mm + 1) q
                  = mixedHilbertCoefficient Cpoly (mm + 1) q := by
                have hSc : (shiftSub Cpoly).coeff
                    (Finsupp.single 0 (mm + 1) + Finsupp.single 1 q)
                    = Cpoly.coeff
                    (Finsupp.single 0 (mm + 1) + Finsupp.single 1 q) := by
                  apply shiftSub_coeff_top Cpoly (d + 1) hdegC
                  have hsum : ((Finsupp.single (0 : Fin 2) (mm + 1)
                      + Finsupp.single (1 : Fin 2) q : Fin 2 →₀ ℕ)).sum
                      (fun _ e => e) = (mm + 1) + q := by
                    have e0 : ((Finsupp.single (0 : Fin 2) (mm + 1)
                        + Finsupp.single (1 : Fin 2) q : Fin 2 →₀ ℕ)) 0
                        = mm + 1 := by simp
                    have e1 : ((Finsupp.single (0 : Fin 2) (mm + 1)
                        + Finsupp.single (1 : Fin 2) q : Fin 2 →₀ ℕ)) 1
                        = q := by simp
                    simp only [fin2_sum, e0, e1]
                  omega
                unfold mixedHilbertCoefficient
                rw [hSc]
              rw [hpoly, h1, hS]
            rw [hcoeff]
            apply add_nonneg
            · exact ihJ J' hJlt hJ' P' hdegP' ⟨N', hP'⟩ (mm + 1) q hpq'
            · exact ihJ C hClt hC Cpoly hdegC ⟨NC, hCpoly⟩ (mm + 1) q hpq'
/-- Specialization to actual pair sets. -/
theorem mixed_nonneg_pair {n m d : ℕ}
    (T : Set (ProjectivePoint n × ProjectivePoint m)) (P : BaseHilbertPolynomial)
    (hdeg : P.totalDegree ≤ d)
    (hevent : ∃ N : ℕ, ∀ s t : ℕ, N ≤ s → N ≤ t →
      MvPolynomial.eval (Fin.cons (s : ℚ) (fun _ : Fin 1 => (t : ℚ))) P =
        (pairHilbert T s t : ℚ)) :
    ∀ p q : ℕ, p + q = d → 0 ≤ mixedHilbertCoefficient P p q := by
  intro p q hpq
  have hJ := pairRepresentatives_blockHomogeneous T
  have hevent' : ∃ N : ℕ, ∀ s t : ℕ, N ≤ s → N ≤ t →
      evalPair P s t
        = ((rankJ (MvPolynomial.vanishingIdeal ℂ (pairRepresentatives T)) s t : ℕ) : ℚ) := by
    obtain ⟨N, hN⟩ := hevent
    refine ⟨N, fun s t hs ht => ?_⟩
    have e := hN s t hs ht
    rwa [← rankJ_pairHilbert] at e
  exact mixed_nonneg_aux d _ hJ P hdeg hevent' p q hpq
