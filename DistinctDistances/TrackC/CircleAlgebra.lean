import DistinctDistances.TrackC.Basic

open scoped BigOperators
open MvPolynomial

namespace DistinctDistances.TrackC

noncomputable def circleEquation (a b r : ℝ) : Poly 2 :=
  (X 0 - C a) ^ 2 + (X 1 - C b) ^ 2 - C (r ^ 2)

/-- The degree-one restriction needed to exclude linear factorization. -/
theorem bivariate_linear_form (p : Poly 2) (hp : p.totalDegree ≤ 1) :
    p = C (p.coeff 0) + C (p.coeff (Finsupp.single 0 1)) * X 0 +
      C (p.coeff (Finsupp.single 1 1)) * X 1 := by
  classical
  apply MvPolynomial.ext
  intro m
  by_cases hm : m = 0 ∨ m = Finsupp.single 0 1 ∨ m = Finsupp.single 1 1
  · rcases hm with rfl | rfl | rfl
    all_goals simp [MvPolynomial.coeff_X, Finsupp.single_eq_single_iff, eq_comm]
  · have hc : p.coeff m = 0 := by
      by_contra hc
      have hdegree := (MvPolynomial.le_totalDegree (mem_support_iff.mpr hc)).trans hp
      have hsum : m.sum (fun _ n => n) = m 0 + m 1 := by
        rw [Finsupp.sum_fintype] <;> simp [Fin.sum_univ_two]
      rw [hsum] at hdegree
      apply hm
      by_cases h0 : m 0 = 0
      · by_cases h1 : m 1 = 0
        · left
          ext i
          fin_cases i <;> simp [h0, h1]
        · right; right
          have h1' : m 1 = 1 := by omega
          ext i
          fin_cases i <;> simp [h0, h1']
      · right; left
        have h0' : m 0 = 1 := by omega
        have h1 : m 1 = 0 := by omega
        ext i
        fin_cases i <;> simp [h0', h1]
    simp only [not_or] at hm
    simp [MvPolynomial.coeff_X, hc, hm.1, hm.2.1, hm.2.2, eq_comm]

/-- Translation does not change the positive definite top-degree part. -/
theorem circleEquation_totalDegree (a b r : ℝ) :
    (circleEquation a b r).totalDegree = 2 := by
  classical
  have hlin (i : Fin 2) (c : ℝ) : ((X i - C c : Poly 2)).totalDegree ≤ 1 := by
    exact (totalDegree_sub _ _).trans (by simp)
  have hsq (i : Fin 2) (c : ℝ) : ((X i - C c : Poly 2) ^ 2).totalDegree ≤ 2 := by
    exact (totalDegree_pow _ _).trans (by have := hlin i c; omega)
  have hup : (circleEquation a b r).totalDegree ≤ 2 := by
    exact (totalDegree_sub _ _).trans (max_le ((totalDegree_add _ _).trans
      (max_le (hsq 0 a) (hsq 1 b))) (by simp only [totalDegree_C]; omega))
  have hc : (circleEquation a b r).coeff (Finsupp.single 0 2) = 1 := by
    have he : circleEquation a b r = X 0 ^ 2 + X 1 ^ 2 +
        C (-2 * a) * X 0 + C (-2 * b) * X 1 + C (a ^ 2 + b ^ 2 - r ^ 2) := by
      norm_num only [circleEquation, map_sub, map_add, map_mul, map_pow, map_neg, map_ofNat]
      ring
    rw [he]
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
    norm_num [Finsupp.single_eq_single_iff, eq_comm]
  have hlow := le_totalDegree (mem_support_iff.mpr (by rw [hc]; norm_num))
  have : 2 ≤ (circleEquation a b r).totalDegree := by simpa using hlow
  omega

/-- A nonzero degree-zero real polynomial is a unit. -/
private theorem isUnit_of_totalDegree_zero (p : Poly 2) (hp : p ≠ 0)
    (hdeg : p.totalDegree = 0) : IsUnit p := by
  apply MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mpr
  refine ⟨isUnit_iff_ne_zero.mpr ?_, hdeg⟩
  intro hc
  apply hp
  rw [totalDegree_eq_zero_iff_eq_C.mp hdeg, hc]
  simp

/-- The real circle equation cannot split into two real affine linear factors. -/
theorem circleEquation_irreducible (a b r : ℝ) : Irreducible (circleEquation a b r) := by
  classical
  have hdeg := circleEquation_totalDegree a b r
  have hne : circleEquation a b r ≠ 0 := by
    intro h
    rw [h, totalDegree_zero] at hdeg
    omega
  refine ⟨?_, ?_⟩
  · intro hunit
    have hz := (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hunit).2
    omega
  · intro g h heq
    by_cases hgu : IsUnit g
    · exact Or.inl hgu
    by_cases hhu : IsUnit h
    · exact Or.inr hhu
    exfalso
    have hg0 : g ≠ 0 := by intro hz; rw [hz, zero_mul] at heq; exact hne heq
    have hh0 : h ≠ 0 := by intro hz; rw [hz, mul_zero] at heq; exact hne heq
    have hsum : g.totalDegree + h.totalDegree = 2 := by
      rw [← totalDegree_mul_of_isDomain hg0 hh0, ← heq]
      exact hdeg
    have hgpos : 0 < g.totalDegree := by
      by_contra! hn
      exact hgu (isUnit_of_totalDegree_zero g hg0 (Nat.le_zero.mp hn))
    have hhpos : 0 < h.totalDegree := by
      by_contra! hn
      exact hhu (isUnit_of_totalDegree_zero h hh0 (Nat.le_zero.mp hn))
    have hgdeg : g.totalDegree ≤ 1 := by omega
    have hhdeg : h.totalDegree ≤ 1 := by omega
    let g0 := g.coeff 0
    let gx := g.coeff (Finsupp.single 0 1)
    let gy := g.coeff (Finsupp.single 1 1)
    let h0 := h.coeff 0
    let hx := h.coeff (Finsupp.single 0 1)
    let hy := h.coeff (Finsupp.single 1 1)
    have heval (x y : ℝ) :
        (x-a)^2 + (y-b)^2 - r^2 = (g0 + gx*x + gy*y) * (h0 + hx*x + hy*y) := by
      have hv := congrArg (MvPolynomial.eval (![x,y] : Fin 2 → ℝ)) heq
      rw [bivariate_linear_form g hgdeg, bivariate_linear_form h hhdeg] at hv
      simpa [circleEquation, g0, gx, gy, h0, hx, hy] using hv
    have hxx : gx * hx = 1 := by
      have h1 := heval 1 0
      have hn := heval (-1) 0
      have hz := heval 0 0
      nlinarith
    have hyy : gy * hy = 1 := by
      have h1 := heval 0 1
      have hn := heval 0 (-1)
      have hz := heval 0 0
      nlinarith
    have hxy : gx * hy + gy * hx = 0 := by
      have h1 := heval 1 1
      have hn := heval (-1) (-1)
      have hz := heval 0 0
      nlinarith
    have hp : (gx * hy) * (gy * hx) = 1 := by
      calc
        (gx * hy) * (gy * hx) = (gx * hx) * (gy * hy) := by ring
        _ = 1 := by rw [hxx, hyy]; norm_num
    have hz : (gx * hy + gy * hx)^2 = 0 := by rw [hxy]; norm_num
    nlinarith [sq_nonneg (gx * hy - gy * hx)]

/-- A one-variable coefficient vanishing on an interval is zero. -/
private theorem coefficient_eq_zero_of_interval (p : MvPolynomial (Fin 1) ℝ)
    (l u : ℝ) (hlu : l < u)
    (hp : ∀ y ∈ Set.Ioo l u, MvPolynomial.eval (fun _ => y) p = 0) : p = 0 := by
  apply (MvPolynomial.uniqueAlgEquiv ℝ (Fin 1)).injective
  rw [map_zero]
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply (Set.Ioo_infinite hlu).mono
  intro y hy
  change ((MvPolynomial.uniqueAlgEquiv ℝ (Fin 1)) p).eval y = 0
  have he := MvPolynomial.eval₂_const_uniqueAlgEquiv
    (f := p) (φ := RingHom.id ℝ) (a := y)
  change ((MvPolynomial.uniqueAlgEquiv ℝ (Fin 1)) p).eval y =
    MvPolynomial.eval (fun _ => y) p at he
  rw [he]
  exact hp y hy

/-- Vanishing on the positive-radius real circle forces quadratic divisibility. -/
theorem circleEquation_dvd_of_vanish (a b r : ℝ) (hr : 0 < r) (f : Poly 2)
    (hf : ∀ x y : ℝ, (x-a)^2 + (y-b)^2 = r^2 →
      MvPolynomial.eval (![x,y] : Fin 2 → ℝ) f = 0) :
    circleEquation a b r ∣ f := by
  classical
  let e := MvPolynomial.finSuccEquiv ℝ 1
  let q : Polynomial (MvPolynomial (Fin 1) ℝ) :=
    (Polynomial.X - Polynomial.C (C a))^2 +
      Polynomial.C ((X 0 - C b)^2 - C (r^2))
  have hqeq : e (circleEquation a b r) = q := by
    have hcases : Fin.cases (Polynomial.X : Polynomial (MvPolynomial (Fin 1) ℝ))
        (fun i => Polynomial.C (X i)) (1 : Fin 2) = Polynomial.C (X 0) := rfl
    simp [e, q, circleEquation, MvPolynomial.finSuccEquiv_apply, hcases] <;> ring
  have hsq : ((Polynomial.X - Polynomial.C (C a))^2 :
      Polynomial (MvPolynomial (Fin 1) ℝ)).Monic :=
    (Polynomial.monic_X_sub_C (C a)).pow 2
  have hsdeg : ((Polynomial.X - Polynomial.C (C a))^2 :
      Polynomial (MvPolynomial (Fin 1) ℝ)).natDegree = 2 := by
    rw [(Polynomial.monic_X_sub_C (C a)).natDegree_pow]
    simp
  have hqmon : q.Monic := by
    apply hsq.add_of_left
    apply lt_of_le_of_lt Polynomial.degree_C_le
    rw [Polynomial.degree_eq_natDegree hsq.ne_zero, hsdeg]
    norm_num
  have hqdeg : q.natDegree = 2 := by
    simpa only [q, Polynomial.natDegree_add_C] using hsdeg
  have hqone : q ≠ 1 := by
    intro h
    rw [h, Polynomial.natDegree_one] at hqdeg
    omega
  let v := (e f) %ₘ q
  have hvdeg : v.natDegree ≤ 1 := by
    have h := Polynomial.natDegree_modByMonic_lt (e f) hqmon hqone
    change ((e f) %ₘ q).natDegree ≤ 1
    omega
  have hvlinear : v = Polynomial.C (v.coeff 1) * Polynomial.X + Polynomial.C (v.coeff 0) :=
    Polynomial.eq_X_add_C_of_natDegree_le_one hvdeg
  have heval (x y : ℝ) : (e f).eval₂ (MvPolynomial.eval (fun _ => y)) x =
      MvPolynomial.eval (![x,y] : Fin 2 → ℝ) f := by
    have h := (MvPolynomial.eval_eq_eval_mv_eval' (fun _ : Fin 1 => y) x f).symm
    have hvec : Fin.cons x (fun _ : Fin 1 => y) = (![x,y] : Fin 2 → ℝ) := by
      ext i
      fin_cases i <;> rfl
    simpa [e, Polynomial.eval_map, hvec] using h
  have hcoeff (y : ℝ) (hy : y ∈ Set.Ioo (b-r) (b+r)) :
      MvPolynomial.eval (fun _ => y) (v.coeff 1) = 0 ∧
      MvPolynomial.eval (fun _ => y) (v.coeff 0) = 0 := by
    let t := Real.sqrt (r^2 - (y-b)^2)
    have hinner : 0 < r^2 - (y-b)^2 := by
      have hp := mul_pos (show 0 < r - (y-b) by linarith [hy.2])
        (show 0 < r + (y-b) by linarith [hy.1])
      nlinarith
    have ht : 0 < t := Real.sqrt_pos.mpr hinner
    have htsq : t^2 = r^2 - (y-b)^2 := Real.sq_sqrt hinner.le
    have hroot (x : ℝ) (hx : (x-a)^2 + (y-b)^2 = r^2) :
        q.eval₂ (MvPolynomial.eval (fun _ => y)) x = 0 := by
      simp only [q, Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_sub,
        Polynomial.eval₂_C, Polynomial.eval₂_X, map_sub, map_pow, eval_X, eval_C]
      nlinarith
    have hrem (x : ℝ) (hx : (x-a)^2 + (y-b)^2 = r^2) :
        MvPolynomial.eval (fun _ => y) (v.coeff 1) * x +
          MvPolynomial.eval (fun _ => y) (v.coeff 0) = 0 := by
      have hv : v.eval₂ (MvPolynomial.eval (fun _ => y)) x = 0 := by
        rw [show v = (e f) %ₘ q from rfl,
          Polynomial.eval₂_modByMonic_eq_self_of_root (hroot x hx), heval]
        exact hf x y hx
      rw [hvlinear] at hv
      simpa using hv
    have hp := hrem (a+t) (by nlinarith [htsq])
    have hm := hrem (a-t) (by nlinarith [htsq])
    have hmul : MvPolynomial.eval (fun _ => y) (v.coeff 1) * t = 0 := by nlinarith
    have hA : MvPolynomial.eval (fun _ => y) (v.coeff 1) = 0 :=
      (mul_eq_zero.mp hmul).resolve_right (ne_of_gt ht)
    refine ⟨hA, ?_⟩
    rw [hA] at hp
    simpa using hp
  have hA : v.coeff 1 = 0 := coefficient_eq_zero_of_interval _ (b-r) (b+r)
    (by linarith) (fun y hy => (hcoeff y hy).1)
  have hB : v.coeff 0 = 0 := coefficient_eq_zero_of_interval _ (b-r) (b+r)
    (by linarith) (fun y hy => (hcoeff y hy).2)
  have hvzero : v = 0 := by rw [hvlinear, hA, hB]; simp
  have hdiv : q ∣ e f := (Polynomial.modByMonic_eq_zero_iff_dvd hqmon).mp hvzero
  obtain ⟨g, hg⟩ := hdiv
  refine ⟨e.symm g, ?_⟩
  apply e.injective
  rw [map_mul, hqeq, e.apply_symm_apply]
  exact hg

end DistinctDistances.TrackC
