import DistinctDistances.TrackE.PairFlats
import DistinctDistances.Bridges.Homogenization
import DistinctDistances.TrackA.Intersections

/-!
Literal physical parameters consumed by global concentration (`reduction.tex:358–381`).
The finitary inputs keep the original pairs in `W`, including pairs with equal coordinates.
-/

namespace DistinctDistances.Reduction

open scoped BigOperators
open Classical
noncomputable section

variable {d : ℕ}

/-- The affine representative `[(v₀,1):(y₀,-v₀·y₀)]`, reduction.tex:330. -/
def globalParameter (x : RPoint d × RPoint d) :
    (Fin (d + 1) → ℂ) × (Fin (d + 1) → ℂ) :=
  (pairParamV x.1 x.2, pairParamY x.1 x.2)

private lemma sum_cplx_mul_global (a b : RPoint d) :
    ∑ i, cplx a i * cplx b i = ((inner ℝ a b : ℝ) : ℂ) := by
  simp only [cplx, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Literal parameters satisfy the affine quadric constraint, reduction.tex:342. -/
theorem global_parameter_quadric (x : RPoint d × RPoint d) :
    (globalParameter x).1 ≠ 0 ∧
      ∑ i, (globalParameter x).2 i * (globalParameter x).1 i = 0 := by
  constructor
  · intro hv
    have hlast := congrFun hv (Fin.last d)
    have hfalse : (1 : ℂ) = 0 := by
      simpa [globalParameter, pairParamV] using hlast
    exact one_ne_zero hfalse
  · change ∑ i, pairParamY x.1 x.2 i * pairParamV x.1 x.2 i = 0
    rw [Fin.sum_univ_castSucc]
    simp only [pairParamY, pairParamV, Fin.snoc_castSucc, Fin.snoc_last]
    rw [sum_cplx_mul_global, real_inner_comm]
    simp

/-- Midpoint and half-difference recover both physical points, reduction.tex:316. -/
theorem global_parameter_injective :
    Function.Injective (globalParameter (d := d)) := by
  intro x x' h
  have hV := congrArg Prod.fst h
  have hY := congrArg Prod.snd h
  change pairParamV x.1 x.2 = pairParamV x'.1 x'.2 at hV
  change pairParamY x.1 x.2 = pairParamY x'.1 x'.2 at hY
  have hmidC : cplx (pairMid x.1 x.2) = cplx (pairMid x'.1 x'.2) := by
    funext i
    have hi := congrFun hV i.castSucc
    simpa [pairParamV] using hi
  have hdiffC : cplx (pairHalfDiff x.1 x.2) = cplx (pairHalfDiff x'.1 x'.2) := by
    funext i
    have hi := congrFun hY i.castSucc
    simpa [pairParamY] using hi
  have hcplx : Function.Injective (cplx (d := d)) := by
    intro a b hab
    ext i
    exact Complex.ofReal_injective (by simpa [cplx] using congrFun hab i)
  have hmid : pairMid x.1 x.2 = pairMid x'.1 x'.2 := hcplx hmidC
  have hdiff : pairHalfDiff x.1 x.2 = pairHalfDiff x'.1 x'.2 := hcplx hdiffC
  have hmidAdd (p q : RPoint d) : pairMid p q + pairHalfDiff p q = p := by
    dsimp [pairMid, pairHalfDiff]
    module
  have hmidSub (p q : RPoint d) : pairMid p q - pairHalfDiff p q = q := by
    dsimp [pairMid, pairHalfDiff]
    module
  have hp : x.1 = x'.1 := by
    calc
      x.1 = pairMid x.1 x.2 + pairHalfDiff x.1 x.2 := (hmidAdd x.1 x.2).symm
      _ = pairMid x'.1 x'.2 + pairHalfDiff x'.1 x'.2 := by rw [hmid, hdiff]
      _ = x'.1 := hmidAdd x'.1 x'.2
  have hq : x.2 = x'.2 := by
    calc
      x.2 = pairMid x.1 x.2 - pairHalfDiff x.1 x.2 := (hmidSub x.1 x.2).symm
      _ = pairMid x'.1 x'.2 - pairHalfDiff x'.1 x'.2 := by rw [hmid, hdiff]
      _ = x'.2 := hmidSub x'.1 x'.2
  exact Prod.ext hp hq

/-- The last coordinate of `v` fixes the projective scaling, reduction.tex:330. -/
theorem global_parameter_nonproportional (x x' : RPoint d × RPoint d) (c : ℂ)
    (hc : globalParameter x' = c • globalParameter x) :
    globalParameter x' = globalParameter x := by
  have hlast := congrFun (congrArg Prod.fst hc) (Fin.last d)
  have hc1 : c = 1 := by
    simpa [globalParameter, pairParamV] using hlast.symm
  subst c
  simpa using hc

private lemma global_parameter_pairing_formula (x x' : RPoint d × RPoint d) :
    ∑ i, ((globalParameter x).2 i * (globalParameter x').1 i +
      (globalParameter x').2 i * (globalParameter x).1 i) =
        - ((inner ℝ (pairMid x.1 x.2 - pairMid x'.1 x'.2)
          (pairHalfDiff x.1 x.2 - pairHalfDiff x'.1 x'.2) : ℝ) : ℂ) := by
  change ∑ i, (pairParamY x.1 x.2 i * pairParamV x'.1 x'.2 i +
      pairParamY x'.1 x'.2 i * pairParamV x.1 x.2 i) = _
  rw [Fin.sum_univ_castSucc]
  simp only [pairParamY, pairParamV, Fin.snoc_castSucc, Fin.snoc_last]
  rw [Finset.sum_add_distrib, sum_cplx_mul_global, sum_cplx_mul_global]
  rw [real_inner_comm (pairMid x'.1 x'.2) (pairHalfDiff x.1 x.2),
    real_inner_comm (pairMid x.1 x.2) (pairHalfDiff x'.1 x'.2)]
  simp only [mul_one]
  push_cast
  have hreal :
      inner ℝ (pairMid x'.1 x'.2) (pairHalfDiff x.1 x.2) +
      inner ℝ (pairMid x.1 x.2) (pairHalfDiff x'.1 x'.2) +
      (-inner ℝ (pairMid x.1 x.2) (pairHalfDiff x.1 x.2) +
        -inner ℝ (pairMid x'.1 x'.2) (pairHalfDiff x'.1 x'.2)) =
        - inner ℝ (pairMid x.1 x.2 - pairMid x'.1 x'.2)
          (pairHalfDiff x.1 x.2 - pairHalfDiff x'.1 x'.2) := by
    simp only [inner_sub_left, inner_sub_right]
    ring
  exact_mod_cast hreal

/-- The two physical separators, homogenized in `v_last = 1`, give one positive-degree
separator on all literal parameters, reduction.tex:361–365. Consumer: global concentration. -/
theorem global_parameter_separators (P Q : Finset (RPoint d)) (A : ℝ) (hA : 1 ≤ A)
    (hP : Mcount P ≤ A) (hQ : Mcount Q ≤ A)
    (x : RPoint d × RPoint d) (hx : x ∈ P ×ˢ Q) :
    ∃ (k : ℕ) (f : MvPolynomial (Fin (d + 1) ⊕ Fin (d + 1)) ℂ),
      1 ≤ k ∧ (k : ℝ) ≤ 5 * A ∧ f.IsHomogeneous k ∧
      MvPolynomial.eval (Sum.elim (globalParameter x).1 (globalParameter x).2) f ≠ 0 ∧
      ∀ x' ∈ P ×ˢ Q, x' ≠ x →
      MvPolynomial.eval (Sum.elim (globalParameter x').1 (globalParameter x').2) f = 0 := by
  classical
  obtain ⟨hxP, hxQ⟩ := Finset.mem_product.mp hx
  obtain ⟨sP, hsPdeg, hsPone, hsPzero⟩ := TrackA.poly_separators_physical P x.1 hxP
  obtain ⟨sQ, hsQdeg, hsQone, hsQzero⟩ := TrackA.poly_separators_physical Q x.2 hxQ
  have hsPdeg' : sP.totalDegree ≤ 2 * distinctDistances P := by
    simpa [distinctDistances, distanceSet, OAI.ErdosDistinctDistances.distances] using hsPdeg
  have hsQdeg' : sQ.totalDegree ≤ 2 * distinctDistances Q := by
    simpa [distinctDistances, distanceSet, OAI.ErdosDistinctDistances.distances] using hsQdeg
  have hsPdegR : (sP.totalDegree : ℝ) ≤ 2 * (distinctDistances P : ℝ) := by
    exact_mod_cast hsPdeg'
  have hsQdegR : (sQ.totalDegree : ℝ) ≤ 2 * (distinctDistances Q : ℝ) := by
    exact_mod_cast hsQdeg'
  have hPbound : (distinctDistances P : ℝ) + 1 ≤ A := by
    simpa [Mcount] using hP
  have hQbound : (distinctDistances Q : ℝ) + 1 ≤ A := by
    simpa [Mcount] using hQ
  have hcomplex (p : RPoint d) : OAI.ErdosDistinctDistances.complexPoint p = cplx p := by
    funext i
    rfl
  have hsPone' : MvPolynomial.eval (cplx x.1) sP = 1 := by
    rw [← hcomplex x.1]
    exact hsPone
  have hsQone' : MvPolynomial.eval (cplx x.2) sQ = 1 := by
    rw [← hcomplex x.2]
    exact hsQone
  have hsPzero' (p : RPoint d) (hp : p ∈ P) (hne : p ≠ x.1) :
      MvPolynomial.eval (cplx p) sP = 0 := by
    rw [← hcomplex p]
    exact hsPzero p hp hne
  have hsQzero' (q : RPoint d) (hq : q ∈ Q) (hne : q ≠ x.2) :
      MvPolynomial.eval (cplx q) sQ = 0 := by
    rw [← hcomplex q]
    exact hsQzero q hq hne

  let α := Fin (d + 1) ⊕ Fin (d + 1)
  let σp : Fin (d + 1) → MvPolynomial α ℂ := Fin.cases
    (MvPolynomial.X (Sum.inl (Fin.last d)))
    (fun i => MvPolynomial.X (Sum.inl i.castSucc) + MvPolynomial.X (Sum.inr i.castSucc))
  let σq : Fin (d + 1) → MvPolynomial α ℂ := Fin.cases
    (MvPolynomial.X (Sum.inl (Fin.last d)))
    (fun i => MvPolynomial.X (Sum.inl i.castSucc) - MvPolynomial.X (Sum.inr i.castSucc))
  have hσp (i : Fin (d + 1)) : (σp i).IsHomogeneous 1 := by
    cases i using Fin.cases with
    | zero =>
        simpa [σp] using (MvPolynomial.isHomogeneous_X ℂ (Sum.inl (Fin.last d)))
    | succ j =>
        simpa [σp] using
          (MvPolynomial.isHomogeneous_X ℂ (Sum.inl j.castSucc)).add
            (MvPolynomial.isHomogeneous_X ℂ (Sum.inr j.castSucc))
  have hσq (i : Fin (d + 1)) : (σq i).IsHomogeneous 1 := by
    cases i using Fin.cases with
    | zero =>
        simpa [σq] using (MvPolynomial.isHomogeneous_X ℂ (Sum.inl (Fin.last d)))
    | succ j =>
        simpa [σq] using
          (MvPolynomial.isHomogeneous_X ℂ (Sum.inl j.castSucc)).sub
            (MvPolynomial.isHomogeneous_X ℂ (Sum.inr j.castSucc))

  have hcplxAdd (a b : RPoint d) : cplx (a + b) = cplx a + cplx b := by
    funext i
    simp [cplx]
  have hcplxSub (a b : RPoint d) : cplx (a - b) = cplx a - cplx b := by
    funext i
    simp [cplx]
  have hmidAdd (a b : RPoint d) : pairMid a b + pairHalfDiff a b = a := by
    dsimp [pairMid, pairHalfDiff]
    module
  have hmidSub (a b : RPoint d) : pairMid a b - pairHalfDiff a b = b := by
    dsimp [pairMid, pairHalfDiff]
    module
  have hmidAddC (a b : RPoint d) :
      cplx (pairMid a b) + cplx (pairHalfDiff a b) = cplx a := by
    calc
      _ = cplx (pairMid a b + pairHalfDiff a b) := (hcplxAdd _ _).symm
      _ = cplx a := congrArg cplx (hmidAdd a b)
  have hmidSubC (a b : RPoint d) :
      cplx (pairMid a b) - cplx (pairHalfDiff a b) = cplx b := by
    calc
      _ = cplx (pairMid a b - pairHalfDiff a b) := (hcplxSub _ _).symm
      _ = cplx b := congrArg cplx (hmidSub a b)
  have hσpEval (x' : RPoint d × RPoint d) :
      (fun i => MvPolynomial.eval (Sum.elim (globalParameter x').1 (globalParameter x').2)
        (σp i)) = Fin.cons (1 : ℂ) (cplx x'.1) := by
    funext i
    cases i using Fin.cases with
    | zero => simp [σp, globalParameter, pairParamV]
    | succ j =>
        simp only [σp, Fin.cases_succ, MvPolynomial.eval_add, MvPolynomial.eval_X,
          Sum.elim_inl, Sum.elim_inr, globalParameter, pairParamV, pairParamY,
          Fin.snoc_castSucc, Fin.cons_succ]
        exact congrFun (hmidAddC x'.1 x'.2) j
  have hσqEval (x' : RPoint d × RPoint d) :
      (fun i => MvPolynomial.eval (Sum.elim (globalParameter x').1 (globalParameter x').2)
        (σq i)) = Fin.cons (1 : ℂ) (cplx x'.2) := by
    funext i
    cases i using Fin.cases with
    | zero => simp [σq, globalParameter, pairParamV]
    | succ j =>
        simp only [σq, Fin.cases_succ, MvPolynomial.eval_sub, MvPolynomial.eval_X,
          Sum.elim_inl, Sum.elim_inr, globalParameter, pairParamV, pairParamY,
          Fin.snoc_castSucc, Fin.cons_succ]
        exact congrFun (hmidSubC x'.1 x'.2) j

  have hevsub (z : α → ℂ) (σ : Fin (d + 1) → MvPolynomial α ℂ)
      (g : MvPolynomial (Fin (d + 1)) ℂ) :
      MvPolynomial.eval z (MvPolynomial.aeval σ g) =
        MvPolynomial.aeval (fun i => MvPolynomial.eval z (σ i)) g := by
    induction g using MvPolynomial.induction_on with
    | C a => simp
    | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
    | mul_X a i ha =>
        rw [map_mul, map_mul, MvPolynomial.aeval_X, map_mul,
          MvPolynomial.aeval_X, ha]

  let sPh := Bridges.homogenize sP
  let sQh := Bridges.homogenize sQ
  have hsPh : sPh.IsHomogeneous sP.totalDegree := Bridges.homogenize_homogeneous sP
  have hsQh : sQh.IsHomogeneous sQ.totalDegree := Bridges.homogenize_homogeneous sQ
  have hsubP := hsPh.aeval σp hσp
  have hsubQ := hsQh.aeval σq hσq
  have hEvalP (x' : RPoint d × RPoint d) :
      MvPolynomial.eval (Sum.elim (globalParameter x').1 (globalParameter x').2)
        (MvPolynomial.aeval σp sPh) = MvPolynomial.eval (cplx x'.1) sP := by
    calc
      _ = MvPolynomial.aeval
          (fun i => MvPolynomial.eval (Sum.elim (globalParameter x').1 (globalParameter x').2)
            (σp i)) sPh := hevsub _ _ _
      _ = MvPolynomial.aeval (Fin.cons (1 : ℂ) (cplx x'.1)) sPh := by rw [hσpEval x']
      _ = MvPolynomial.eval (cplx x'.1) sP := by
        rw [MvPolynomial.aeval_eq_eval, Bridges.eval_homogenize_cons]
  have hEvalQ (x' : RPoint d × RPoint d) :
      MvPolynomial.eval (Sum.elim (globalParameter x').1 (globalParameter x').2)
        (MvPolynomial.aeval σq sQh) = MvPolynomial.eval (cplx x'.2) sQ := by
    calc
      _ = MvPolynomial.aeval
          (fun i => MvPolynomial.eval (Sum.elim (globalParameter x').1 (globalParameter x').2)
            (σq i)) sQh := hevsub _ _ _
      _ = MvPolynomial.aeval (Fin.cons (1 : ℂ) (cplx x'.2)) sQh := by rw [hσqEval x']
      _ = MvPolynomial.eval (cplx x'.2) sQ := by
        rw [MvPolynomial.aeval_eq_eval, Bridges.eval_homogenize_cons]

  let k := sP.totalDegree + sQ.totalDegree + 1
  let f := (MvPolynomial.aeval σp sPh * MvPolynomial.aeval σq sQh) *
    MvPolynomial.X (Sum.inl (Fin.last d))
  have hfHom : f.IsHomogeneous k := by
    simpa [f, k] using (hsubP.mul hsubQ).mul
      (MvPolynomial.isHomogeneous_X ℂ (Sum.inl (Fin.last d)))
  have hkBound : (k : ℝ) ≤ 5 * A := by
    dsimp [k]
    push_cast
    nlinarith [hsPdegR, hsQdegR, hPbound, hQbound, hA]
  have hEvalF (x' : RPoint d × RPoint d) :
      MvPolynomial.eval (Sum.elim (globalParameter x').1 (globalParameter x').2) f =
        MvPolynomial.eval (cplx x'.1) sP * MvPolynomial.eval (cplx x'.2) sQ := by
    simp only [f, MvPolynomial.eval_mul]
    rw [hEvalP x', hEvalQ x']
    simp [globalParameter, pairParamV]
  refine ⟨k, f, by dsimp [k]; omega, hkBound, hfHom, ?_, ?_⟩
  · rw [hEvalF x, hsPone', hsQone']
    norm_num
  · intro x' hx' hne
    obtain ⟨hxP', hxQ'⟩ := Finset.mem_product.mp hx'
    by_cases hpEq : x'.1 = x.1
    · have hqNe : x'.2 ≠ x.2 := by
        intro hqEq
        exact hne (Prod.ext hpEq hqEq)
      rw [hEvalF x', hsQzero' x'.2 hxQ' hqNe]
      simp
    · rw [hEvalF x', hsPzero' x'.1 hxP' hpEq, zero_mul]

/-- Polarization on an isotropic space makes the first physical projection injective,
reduction.tex:367–377. No dimension assumption on the isotropic space is needed. -/
theorem global_parameter_isotropic_first_injective
    (L : Submodule ℂ ((Fin (d + 1) → ℂ) × (Fin (d + 1) → ℂ)))
    (hL : ∀ l ∈ L, ∀ l' ∈ L,
      ∑ i, (l.2 i * l'.1 i + l'.2 i * l.1 i) = 0)
    (x x' : RPoint d × RPoint d) (hx : globalParameter x ∈ L)
    (hx' : globalParameter x' ∈ L) (hp : x.1 = x'.1) : x = x' := by
  have hpair := hL (globalParameter x) hx (globalParameter x') hx'
  rw [global_parameter_pairing_formula] at hpair
  have hmid : pairMid x.1 x.2 - pairMid x'.1 x'.2 =
      (1 / 2 : ℝ) • (x.2 - x'.2) := by
    rw [hp]
    dsimp [pairMid]
    module
  have hdiff : pairHalfDiff x.1 x.2 - pairHalfDiff x'.1 x'.2 =
      (-1 / 2 : ℝ) • (x.2 - x'.2) := by
    rw [hp]
    dsimp [pairHalfDiff]
    module
  rw [hmid, hdiff] at hpair
  have hinner : inner ℝ ((1 / 2 : ℝ) • (x.2 - x'.2))
      ((-1 / 2 : ℝ) • (x.2 - x'.2)) = 0 := by
    apply Complex.ofReal_injective
    exact neg_eq_zero.mp hpair
  have hnormsq : ‖x.2 - x'.2‖ ^ 2 = 0 := by
    simp only [real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq] at hinner
    nlinarith [hinner]
  have hnorm : ‖x.2 - x'.2‖ = 0 := by nlinarith [hnormsq]
  have hq : x.2 = x'.2 := sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  exact Prod.ext hp hq

/-- `N ≤ A^(d-1)` and `N² = A^d` in dimension at least three, reduction.tex:377–378. -/
theorem global_parameter_scale (hd : 3 ≤ d) (N : ℕ) (hN : 2 ≤ N) :
    1 ≤ Ascale d N ∧ (N : ℝ) ≤ Ascale d N ^ (d - 1) ∧
      (N : ℝ) ^ 2 = Ascale d N ^ d := by
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (show 1 ≤ N by omega)
  have hdreal : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hA : 1 ≤ Ascale d N := by
    unfold Ascale
    exact Real.one_le_rpow hNreal (by positivity)
  have hscalePow : Ascale d N ^ (d - 1) =
      (N : ℝ) ^ (((2 : ℝ) / (d : ℝ)) * ((d - 1 : ℕ) : ℝ)) := by
    change ((N : ℝ) ^ ((2 : ℝ) / (d : ℝ))) ^ (d - 1) = _
    rw [← Real.rpow_natCast ((N : ℝ) ^ ((2 : ℝ) / (d : ℝ))) (d - 1),
      ← Real.rpow_mul (Nat.cast_nonneg N)]
  have hexp : (1 : ℝ) ≤ ((2 : ℝ) / (d : ℝ)) * ((d - 1 : ℕ) : ℝ) := by
    have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
    have hsub : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ d)]
      simp
    rw [hsub, div_mul_eq_mul_div]
    apply (le_div_iff₀ hdpos).2
    nlinarith
  have hNpow : (N : ℝ) ≤
      (N : ℝ) ^ (((2 : ℝ) / (d : ℝ)) * ((d - 1 : ℕ) : ℝ)) := by
    have h := Real.rpow_le_rpow_of_exponent_le hNreal hexp
    simpa only [Real.rpow_one] using h
  have hsq : (N : ℝ) ^ 2 = Ascale d N ^ d := by
    unfold Ascale
    rw [← Real.rpow_natCast (_ ^ _), ← Real.rpow_mul (Nat.cast_nonneg N)]
    have hdne : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
    rw [div_mul_cancel₀ _ hdne]
    norm_cast
  refine ⟨hA, ?_, hsq⟩
  rw [hscalePow]
  exact hNpow

/-- The actual parameters in any isotropic space inject into `P`, reduction.tex:377. -/
theorem global_parameter_isotropic_count (P Q : Finset (RPoint d))
    (W : Finset (RPoint d × RPoint d)) (hW : W ⊆ P ×ˢ Q)
    (L : Submodule ℂ ((Fin (d + 1) → ℂ) × (Fin (d + 1) → ℂ)))
    (hL : ∀ l ∈ L, ∀ l' ∈ L,
      ∑ i, (l.2 i * l'.1 i + l'.2 i * l.1 i) = 0) :
    (((W.image globalParameter).filter (· ∈ L)).card : ℝ) ≤ P.card := by
  classical
  let U := W.filter fun x => globalParameter x ∈ L
  let S := (W.image globalParameter).filter (· ∈ L)
  have himage : U.image globalParameter = S := by
    ext l
    simp only [U, S, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨x, ⟨hx, hLx⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, hLx⟩
    · rintro ⟨⟨x, hx, rfl⟩, hLx⟩
      exact ⟨x, ⟨hx, hLx⟩, rfl⟩
  have hmaps : Set.MapsTo Prod.fst (U : Set (RPoint d × RPoint d)) P := by
    intro x hx
    have hxU : x ∈ U := hx
    have hxW : x ∈ W := (Finset.mem_filter.mp hxU).1
    have hxp := hW hxW
    exact (Finset.mem_product.mp hxp).1
  have hinj : Set.InjOn Prod.fst (U : Set (RPoint d × RPoint d)) := by
    intro x hx x' hx' hfirst
    have hxU : x ∈ U := hx
    have hx'U : x' ∈ U := hx'
    exact global_parameter_isotropic_first_injective L hL x x'
      (Finset.mem_filter.mp hxU).2 (Finset.mem_filter.mp hx'U).2 hfirst
  have hcardU : U.card ≤ P.card := Finset.card_le_card_of_injOn Prod.fst hmaps hinj
  have hcardImage : S.card ≤ U.card := by
    rw [← himage]
    exact Finset.card_image_le
  calc
    (S.card : ℝ) ≤ U.card := by exact_mod_cast hcardImage
    _ ≤ P.card := by exact_mod_cast hcardU

end
end DistinctDistances.Reduction
