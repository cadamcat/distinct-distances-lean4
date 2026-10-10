import DistinctDistances.TrackB.MixedHilbert
import DistinctDistances.TrackB.MBHilbAux
import DistinctDistances.TrackB.RulingMapsAux
import DistinctDistances.Foundations.GenericFiber
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.RingTheory.Algebraic.LinearIndependent
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.Cardinality

/-!
Support for B12 `point_integral`. The first section is the purely numerical coefficient
extraction: if the incidence Hilbert polynomial P(s,t,u) is, for every fixed large (s,t),
`r(s,t)·G(u) + O(u^(k-1))` and the slope r(s,t) is `Q(s+t)`, then the factorial-normalized
coefficient of `t^j u^k` in P is `(j!·Q_j)·(k!·G_k)`.
-/

namespace DistinctDistances.TrackB.PointIntegral

set_option autoImplicit false
noncomputable section
open Polynomial Filter

/-! ### A polynomial bounded by `C·u^m` on large naturals has degree at most `m`. -/

theorem natDegree_le_of_nat_bound (q : ℚ[X]) (m M : ℕ) (C : ℚ)
    (h : ∀ u : ℕ, M ≤ u → |q.eval (u : ℚ)| ≤ C * (u : ℚ) ^ m) : q.natDegree ≤ m := by
  by_contra hlt
  push_neg at hlt
  have hq : q ≠ 0 := by
    rintro rfl
    simp at hlt
  let B : ℚ[X] := Polynomial.C (C ^ 2) * X ^ (2 * m)
  let P : ℚ[X] := q ^ 2 - B
  have hBdeg : B.degree < (q ^ 2).degree := by
    have h1 : B.degree ≤ ((2 * m : ℕ) : WithBot ℕ) := by
      dsimp [B]
      exact (degree_C_mul_X_pow_le _ _)
    have h2 : (q ^ 2).degree = ((2 * q.natDegree : ℕ) : WithBot ℕ) := by
      rw [degree_pow, degree_eq_natDegree hq]
      push_cast
      ring_nf
    rw [h2]
    exact lt_of_le_of_lt h1 (by exact_mod_cast (by omega : 2 * m < 2 * q.natDegree))
  have hPlc : P.leadingCoeff = q.leadingCoeff ^ 2 := by
    dsimp [P]
    rw [leadingCoeff_sub_of_degree_lt hBdeg, leadingCoeff_pow]
  have hPdeg : 0 < P.degree := by
    dsimp [P]
    rw [degree_sub_eq_left_of_degree_lt hBdeg, degree_pow, degree_eq_natDegree hq]
    have : 0 < 2 * q.natDegree := by omega
    exact_mod_cast (by simpa [nsmul_eq_mul] using this)
  have hlc : 0 ≤ P.leadingCoeff := by rw [hPlc]; positivity
  have htend := (P.tendsto_atTop_of_leadingCoeff_nonneg hPdeg hlc).comp
    tendsto_natCast_atTop_atTop
  obtain ⟨u, hu⟩ := ((htend.eventually (eventually_gt_atTop (0 : ℚ))).and
    (eventually_ge_atTop M)).exists
  have hbound := h u hu.2
  have hpos : 0 < P.eval (u : ℚ) := hu.1
  have hle : (q.eval (u : ℚ)) ^ 2 ≤ C ^ 2 * (u : ℚ) ^ (2 * m) := by
    have habs : |q.eval (u : ℚ)| ^ 2 ≤ (C * (u : ℚ) ^ m) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) hbound 2
    rw [sq_abs] at habs
    calc (q.eval (u : ℚ)) ^ 2 ≤ (C * (u : ℚ) ^ m) ^ 2 := habs
      _ = C ^ 2 * (u : ℚ) ^ (2 * m) := by ring
  have heval : P.eval (u : ℚ) = (q.eval (u : ℚ)) ^ 2 - C ^ 2 * (u : ℚ) ^ (2 * m) := by
    simp [P, B]
  linarith

/-! ### Slicing the incidence polynomial along its last variable. -/

@[simp] theorem cons3_two {α : Type*} (a b c : α) :
    (Fin.cons a (Fin.cons b (fun _ : Fin 1 => c)) : Fin 3 → α) 2 = c := rfl

/-- Keep the last variable as the polynomial variable, the first two as coefficients. -/
def lastSlice : MvPolynomial (Fin 3) ℚ →ₐ[ℚ] Polynomial (MvPolynomial (Fin 2) ℚ) :=
  MvPolynomial.aeval (Fin.cons (Polynomial.C (MvPolynomial.X 0))
    (Fin.cons (Polynomial.C (MvPolynomial.X 1)) (fun _ : Fin 1 => Polynomial.X)))

/-- Set the first variable to zero and the second to the polynomial variable. -/
def zeroFirst : MvPolynomial (Fin 2) ℚ →ₐ[ℚ] Polynomial ℚ :=
  MvPolynomial.aeval (Fin.cons (0 : Polynomial ℚ) (fun _ : Fin 1 => Polynomial.X))

theorem eval_lastSlice (P : MvPolynomial (Fin 3) ℚ) (s t u : ℚ) :
    ((lastSlice P).map (MvPolynomial.eval (Fin.cons s (fun _ : Fin 1 => t)))).eval u =
      MvPolynomial.eval (Fin.cons s (Fin.cons t (fun _ : Fin 1 => u))) P := by
  have hhom : ((Polynomial.evalRingHom u).comp ((Polynomial.mapRingHom
      (MvPolynomial.eval (Fin.cons s (fun _ : Fin 1 => t)))).comp
        (lastSlice.toRingHom : MvPolynomial (Fin 3) ℚ →+* _))) =
      MvPolynomial.eval (Fin.cons s (Fin.cons t (fun _ : Fin 1 => u))) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [lastSlice]
    · intro i
      fin_cases i
      · simp [lastSlice]
      · simp [lastSlice]
      · simp [lastSlice, cons3_two]
  exact congrArg (fun F : MvPolynomial (Fin 3) ℚ →+* ℚ => F P) hhom

theorem coeff_coeff_zeroFirst_lastSlice (P : MvPolynomial (Fin 3) ℚ) (j k : ℕ) :
    ((Polynomial.map zeroFirst.toRingHom (lastSlice P)).coeff k).coeff j =
      P.coeff (Finsupp.single (1 : Fin 3) j + Finsupp.single (2 : Fin 3) k) := by
  classical
  let sig : MvPolynomial (Fin 3) ℚ →ₐ[ℚ] Polynomial (Polynomial ℚ) :=
    MvPolynomial.aeval (Fin.cons (0 : Polynomial (Polynomial ℚ))
      (Fin.cons (Polynomial.C Polynomial.X) (fun _ : Fin 1 => Polynomial.X)))
  have hcomp : ∀ F : MvPolynomial (Fin 3) ℚ,
      Polynomial.map zeroFirst.toRingHom (lastSlice F) = sig F := by
    intro F
    have hhom : (Polynomial.mapRingHom zeroFirst.toRingHom).comp
        (lastSlice.toRingHom : MvPolynomial (Fin 3) ℚ →+* _) = sig.toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp [lastSlice, sig, zeroFirst]
      · intro i
        fin_cases i
        · simp [lastSlice, sig, zeroFirst]
        · simp [lastSlice, sig, zeroFirst]
        · simp [lastSlice, sig, zeroFirst, cons3_two]
    exact congrArg (fun G : MvPolynomial (Fin 3) ℚ →+* Polynomial (Polynomial ℚ) => G F) hhom
  rw [hcomp]
  have hm : ∀ m : Fin 3 →₀ ℕ,
      m = Finsupp.single (1 : Fin 3) j + Finsupp.single (2 : Fin 3) k ↔
        m 0 = 0 ∧ m 1 = j ∧ m 2 = k := by
    intro m
    constructor
    · rintro rfl
      simp [Finsupp.single_apply]
    · rintro ⟨h0, h1, h2⟩
      ext i
      fin_cases i <;> simp [Finsupp.single_apply, h0, h1, h2]
  induction P using MvPolynomial.induction_on' with
  | monomial m c =>
    have hval : sig (MvPolynomial.monomial m c) =
        Polynomial.C (Polynomial.C c) * (0 : Polynomial (Polynomial ℚ)) ^ (m 0) *
          (Polynomial.C Polynomial.X) ^ (m 1) * Polynomial.X ^ (m 2) := by
      rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
        Fin.prod_univ_three]
      simp only [Fin.cons_zero, Fin.cons_one, cons3_two]
      simp [mul_assoc]
    rw [hval, MvPolynomial.coeff_monomial]
    by_cases h0 : m 0 = 0
    · have e1 : Polynomial.C (Polynomial.C c) * (0 : Polynomial (Polynomial ℚ)) ^ (m 0) *
          (Polynomial.C Polynomial.X) ^ (m 1) * Polynomial.X ^ (m 2) =
          Polynomial.C (Polynomial.C c * Polynomial.X ^ (m 1)) * Polynomial.X ^ (m 2) := by
        rw [h0, pow_zero, mul_one, Polynomial.C_mul, Polynomial.C_pow]
      rw [e1, Polynomial.coeff_C_mul_X_pow]
      by_cases h2 : k = m 2
      · rw [if_pos h2, Polynomial.coeff_C_mul_X_pow]
        by_cases h1 : j = m 1
        · rw [if_pos h1, if_pos ((hm m).mpr ⟨h0, h1.symm, h2.symm⟩)]
        · rw [if_neg h1, if_neg (fun h => h1 ((hm m).mp h).2.1.symm)]
      · rw [if_neg h2, if_neg (fun h => h2 ((hm m).mp h).2.2.symm)]
        simp
    · rw [if_neg (fun h => h0 ((hm m).mp h).1), zero_pow h0]
      simp
  | add p q hp hq =>
    simp [hp, hq]

theorem natGrid_infinite (N : ℕ) : {q : ℚ | ∃ n : ℕ, N ≤ n ∧ q = n}.Infinite := by
  have hinj : Function.Injective (fun n : ℕ => ((N + n : ℕ) : ℚ)) := by
    intro a b hab
    have h' : ((N + a : ℕ) : ℚ) = ((N + b : ℕ) : ℚ) := hab
    have : N + a = N + b := by exact_mod_cast h'
    omega
  apply (Set.infinite_range_of_injective hinj).mono
  rintro _ ⟨n, rfl⟩
  exact ⟨N + n, by omega, rfl⟩

/-- L-extract: the numerical extraction of the point/parameter coefficient. -/
theorem coefficient_extraction (P : MvPolynomial (Fin 3) ℚ) (F : ℕ → ℕ → ℕ → ℚ)
    (G Q : ℚ[X]) (r : ℕ → ℕ → ℚ) (k j N : ℕ) (hk : 1 ≤ k)
    (hP : ∀ s t u : ℕ, N ≤ s → N ≤ t → N ≤ u →
      MvPolynomial.eval (Fin.cons (s : ℚ) (Fin.cons (t : ℚ) (fun _ : Fin 1 => (u : ℚ)))) P =
        F s t u)
    (hr : ∀ s t : ℕ, N ≤ s → N ≤ t → ∃ C : ℚ, ∃ M : ℕ, ∀ u : ℕ, M ≤ u →
      |F s t u - r s t * G.eval (u : ℚ)| ≤ C * (u : ℚ) ^ (k - 1))
    (hQ : ∀ s t : ℕ, N ≤ s → N ≤ t → r s t = Q.eval ((s : ℚ) + t)) :
    (k.factorial : ℚ) * (j.factorial : ℚ) *
        P.coeff (Finsupp.single (1 : Fin 3) j + Finsupp.single (2 : Fin 3) k) =
      ((j.factorial : ℚ) * Q.coeff j) * ((k.factorial : ℚ) * G.coeff k) := by
  set Pk := (lastSlice P).coeff k with hPk
  have hslice : ∀ s t : ℕ, N ≤ s → N ≤ t →
      MvPolynomial.eval (Fin.cons (s : ℚ) (fun _ : Fin 1 => (t : ℚ))) Pk =
        G.coeff k * Q.eval ((s : ℚ) + t) := by
    intro s t hs ht
    obtain ⟨C, M, hM⟩ := hr s t hs ht
    set p := (lastSlice P).map (MvPolynomial.eval (Fin.cons (s : ℚ) (fun _ : Fin 1 => (t : ℚ))))
      with hp
    have hdeg : (p - Polynomial.C (r s t) * G).natDegree ≤ k - 1 := by
      apply natDegree_le_of_nat_bound _ (k - 1) (max M N) C
      intro u hu
      rw [eval_sub, eval_mul, eval_C, hp, eval_lastSlice,
        hP s t u hs ht (le_of_max_le_right hu)]
      exact hM u (le_of_max_le_left hu)
    have hc : (p - Polynomial.C (r s t) * G).coeff k = 0 :=
      coeff_eq_zero_of_natDegree_lt (by omega)
    rw [coeff_sub, coeff_C_mul, sub_eq_zero, hp, coeff_map] at hc
    rw [hc, hQ s t hs ht]
    ring
  let W : MvPolynomial (Fin 2) ℚ := MvPolynomial.C (G.coeff k) *
    Polynomial.aeval (MvPolynomial.X 0 + MvPolynomial.X 1 : MvPolynomial (Fin 2) ℚ) Q
  have hW : Pk = W := by
    apply MvPolynomial.funext_set (fun _ => {q : ℚ | ∃ n : ℕ, N ≤ n ∧ q = n})
      (fun _ => natGrid_infinite N)
    intro x hx
    obtain ⟨s, hs, hxs⟩ := hx 0 trivial
    obtain ⟨t, ht, hxt⟩ := hx 1 trivial
    have hx' : x = Fin.cons (s : ℚ) (fun _ : Fin 1 => (t : ℚ)) := by
      funext i
      fin_cases i
      · exact hxs
      · exact hxt
    rw [hx', hslice s t hs ht]
    simp only [W, map_mul, MvPolynomial.eval_C]
    congr 1
    have key := (Polynomial.aeval_algHom_apply
      (MvPolynomial.aeval (Fin.cons (s : ℚ) (fun _ : Fin 1 => (t : ℚ)) : Fin 2 → ℚ))
      (MvPolynomial.X 0 + MvPolynomial.X 1 : MvPolynomial (Fin 2) ℚ) Q).symm
    rw [← MvPolynomial.coe_aeval_eq_eval]
    refine Eq.trans ?_ key.symm
    simp
  have h1 := coeff_coeff_zeroFirst_lastSlice P j k
  rw [Polynomial.coeff_map, ← hPk, hW] at h1
  have hz : zeroFirst W = Polynomial.C (G.coeff k) * Q := by
    simp only [W, map_mul, MvPolynomial.aeval_C, ← Polynomial.aeval_algHom_apply, map_add]
    simp [zeroFirst]
  change (zeroFirst W).coeff j = _ at h1
  rw [hz, Polynomial.coeff_C_mul] at h1
  rw [← h1]
  ring

/-! ### Fibres of a triple incidence over affine points of the last factor -/

/-- The bidegree-(s,t) part of `Poly (n+m) ⧸ J`, for an arbitrary ideal J. -/
def idealPairSection {n m : ℕ} (J : Ideal (Poly (n + m))) (s t : ℕ) :
    Submodule ℂ (Poly (n + m) ⧸ J) :=
  (MvPolynomial.restrictSupport ℂ {d : Fin (n + m) →₀ ℕ |
    (∑ i : Fin n, d (Fin.castAdd m i)) = s ∧
      (∑ i : Fin m, d (Fin.natAdd n i)) = t}).map
    (Ideal.Quotient.mkₐ ℂ J).toLinearMap

theorem idealPairSection_finite {n m : ℕ} (J : Ideal (Poly (n + m))) (s t : ℕ) :
    Module.Finite ℂ (idealPairSection J s t) := by
  classical
  let S := {d : Fin (n + m) →₀ ℕ |
    (∑ i : Fin n, d (Fin.castAdd m i)) = s ∧
      (∑ i : Fin m, d (Fin.natAdd n i)) = t}
  have hS : MvPolynomial.restrictSupport ℂ S ≤
      MvPolynomial.restrictDegree (Fin (n + m)) ℂ (s + t) := by
    apply MvPolynomial.restrictSupport_mono
    intro d hd i
    have htotal : (∑ j : Fin (n + m), d j) = s + t := by
      rw [Fin.sum_univ_add, hd.1, hd.2]
    calc
      d i ≤ ∑ j : Fin (n + m), d j :=
        Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
      _ = s + t := htotal
  haveI : Module.Finite ℂ (MvPolynomial.restrictSupport ℂ S) :=
    Module.Finite.of_injective (Submodule.inclusion hS) (by
      intro x y hxy
      apply Subtype.ext
      exact congrArg (fun z : MvPolynomial.restrictDegree (Fin (n + m)) ℂ (s + t) =>
        (z : MvPolynomial (Fin (n + m)) ℂ)) hxy)
  change Module.Finite ℂ ((MvPolynomial.restrictSupport ℂ S).map
    (Ideal.Quotient.mkₐ ℂ J).toLinearMap)
  infer_instance

noncomputable instance idealPairSectionFinite {n m : ℕ} (J : Ideal (Poly (n + m)))
    (s t : ℕ) : Module.Finite ℂ (idealPairSection J s t) := idealPairSection_finite J s t

def idealPairHilbert {n m : ℕ} (J : Ideal (Poly (n + m))) (s t : ℕ) : ℕ :=
  Module.finrank ℂ (idealPairSection J s t)

/-- Specialize the last block of variables at the affine point `(1, z)`. -/
def fibreSpecialize {q o : ℕ} (z : Point o) : Poly (q + (o + 1)) →ₐ[ℂ] Poly q :=
  MvPolynomial.aeval (Fin.append (fun i : Fin q => (MvPolynomial.X i : Poly q))
    (Fin.cons (1 : Poly q) (fun l : Fin o => MvPolynomial.C (z l))))

/-- The scheme-theoretic fibre ideal of a triple set over the affine point `[1:z]`. -/
def tripleFibreIdeal {n m o : ℕ}
    (T : Set ((ProjectivePoint n × ProjectivePoint m) × ProjectivePoint (o + 1)))
    (z : Point o) : Ideal (Poly (n + m)) :=
  (MvPolynomial.vanishingIdeal ℂ (tripleRepresentatives T)).map (fibreSpecialize z)

/-! ### Weighted cones: homogeneous components stay in vanishing ideals -/

/-- Vandermonde extraction. If `S` is closed under weighted scaling, weighted-homogeneous
components of elements of its vanishing ideal lie in the ideal. -/
theorem whc_mem_of_mem_weightedCone {N : ℕ} (w : Fin N → ℕ) (S : Set (Point N))
    (hcone : ∀ v ∈ S, ∀ c : ℂ, c ≠ 0 → (fun i => c ^ (w i) • v i) ∈ S)
    {F : Poly N} (hF : F ∈ MvPolynomial.vanishingIdeal ℂ S) (D : ℕ) :
    MvPolynomial.weightedHomogeneousComponent w D F ∈ MvPolynomial.vanishingIdeal ℂ S := by
  classical
  rw [MvPolynomial.mem_vanishingIdeal_iff] at hF ⊢
  intro v hv
  let cD : ℕ → ℂ := fun D => MvPolynomial.aeval v
    (MvPolynomial.weightedHomogeneousComponent w D F)
  have hWmem : ∀ i, w i ≤ Finset.univ.sup w := fun i => Finset.le_sup (Finset.mem_univ i)
  have hdeg : ∀ m : Fin N →₀ ℕ, m.degree = ∑ i, m i := by
    intro m
    classical
    change ∑ i ∈ m.support, m i = _
    exact Finset.sum_subset (Finset.subset_univ _)
      (fun i _ hi => Finsupp.notMem_support_iff.mp hi)
  -- A nonzero weighted component forces its degree below the support bound.
  have key : ∀ D, MvPolynomial.weightedHomogeneousComponent w D F ≠ 0 →
      D ≤ Finset.univ.sup w * F.totalDegree := by
    intro D hne
    obtain ⟨m, hm⟩ : ∃ m, (MvPolynomial.weightedHomogeneousComponent w D F).coeff m ≠ 0 := by
      by_contra h
      apply hne
      apply MvPolynomial.ext
      intro m
      rw [MvPolynomial.coeff_zero]
      by_contra hm'
      exact h ⟨m, hm'⟩
    rw [MvPolynomial.coeff_weightedHomogeneousComponent] at hm
    have hDm : Finsupp.weight w m = D := by
      by_contra hcon
      rw [if_neg hcon] at hm
      exact hm rfl
    have hmsupp : m ∈ F.support := by
      rw [MvPolynomial.mem_support_iff]
      intro hcon
      rw [if_pos hDm] at hm
      exact hm hcon
    have hle : m.degree ≤ F.totalDegree := MvPolynomial.le_totalDegree hmsupp
    calc D = Finsupp.weight w m := hDm.symm
      _ = ∑ i, w i * m i := by
            have hwm : m.sum (fun i c => c • w i) = ∑ i, w i * m i := by
              rw [Finsupp.sum_fintype _ _ (fun i => by simp)]
              exact Finset.sum_congr rfl (fun i _ => by simp [smul_eq_mul, mul_comm])
            rw [Finsupp.weight_apply]
            exact hwm
      _ ≤ Finset.univ.sup w * m.degree := by
            rw [hdeg, Finset.mul_sum]
            exact Finset.sum_le_sum
              (fun i _ => Nat.mul_le_mul (hWmem i) (le_refl _))
      _ ≤ Finset.univ.sup w * F.totalDegree :=
            Nat.mul_le_mul (le_refl _) hle
  have hbound : ∀ D, cD D ≠ 0 → D ≤ Finset.univ.sup w * F.totalDegree := by
    intro D hD
    apply key
    intro h
    exact hD (by simp [cD, h])
  set B := Finset.univ.sup w * F.totalDegree with hB
  -- Finite decomposition into weighted components.
  have hsum : F = ∑ D ∈ Finset.range (B + 1),
      MvPolynomial.weightedHomogeneousComponent w D F := by
    have h := MvPolynomial.sum_weightedHomogeneousComponent w F
    have hsub : Function.support
        (fun D => MvPolynomial.weightedHomogeneousComponent w D F) ⊆
        ↑(Finset.range (B + 1)) := by
      intro D hD
      have hne : MvPolynomial.weightedHomogeneousComponent w D F ≠ 0 :=
        Function.mem_support.mp hD
      have hle := key D hne
      simp only [Finset.coe_range, Set.mem_Iio]
      omega
    rw [finsum_eq_sum_of_support_subset _ hsub] at h
    exact h.symm
  -- The univariate polynomial recording the scaling action.
  set P : Polynomial ℂ :=
    ∑ D ∈ Finset.range (B + 1), Polynomial.C (cD D) * Polynomial.X ^ D with hPdef
  have hPeval : ∀ c : ℂ, c ≠ 0 → P.eval c = 0 := by
    intro c hc
    have e1 : MvPolynomial.aeval (fun i => c ^ (w i) • v i) F =
        ∑ D ∈ Finset.range (B + 1), c ^ D * cD D := by
      conv_lhs => rw [hsum]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro D _
      have hwh := GenericFiber.aeval_scale_of_isWeightedHomogeneous
        (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous (w := w) D F)
        (R := ℂ) (b := v) (c := c)
      simpa [cD, smul_eq_mul] using hwh
    have e2 : P.eval c = ∑ D ∈ Finset.range (B + 1), c ^ D * cD D := by
      rw [hPdef, Polynomial.eval_finsetSum]
      exact Finset.sum_congr rfl (fun D _ => by
        rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
          mul_comm])
    rw [e2, ← e1]
    exact hF _ (hcone v hv c hc)
  have hPzero : P = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.Infinite.mono (s := ({(0 : ℂ)} : Set ℂ)ᶜ) ?_
      (Set.finite_singleton (0 : ℂ)).infinite_compl
    intro c hc
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hc
    exact hPeval c hc
  have hcoeff : ∀ D, D ≤ B → cD D = 0 := by
    intro D hD
    have h0 : P.coeff D = 0 := by rw [hPzero]; simp
    have hDmem : D ∈ Finset.range (B + 1) := Finset.mem_range.mpr (by omega)
    rw [hPdef, Polynomial.finsetSum_coeff] at h0
    simp only [Polynomial.coeff_C_mul_X_pow] at h0
    rw [Finset.sum_eq_single D] at h0
    · simpa using h0
    · intro D_ _ hne
      rw [if_neg (Ne.symm hne)]
    · intro hcon
      exact absurd hDmem hcon
  by_cases hDB : D ≤ B
  · exact hcoeff D hDB
  · show cD D = 0
    by_contra hcon
    exact absurd (hbound D hcon) (by omega)

/-! ### Triple representatives are tricones -/

/-- Weight selecting the first block of `Fin (n + m + o)`. -/
def xWeight (n m o : ℕ) : Fin (n + m + o) → ℕ :=
  Fin.addCases (Fin.addCases (fun _ => 1) (fun _ => 0)) (fun _ => 0)

/-- Weight selecting the second block. -/
def yWeight (n m o : ℕ) : Fin (n + m + o) → ℕ :=
  Fin.addCases (Fin.addCases (fun _ => 0) (fun _ => 1)) (fun _ => 0)

/-- Weight selecting the third block. -/
def zWeight (n m o : ℕ) : Fin (n + m + o) → ℕ :=
  Fin.addCases (fun _ => 0) (fun _ => 1)

/-- Every triple index lies in exactly one block. -/
theorem triple_index_trichotomy {n m o : ℕ} (i : Fin (n + m + o)) :
    (∃ k : Fin n, Fin.castAdd o (Fin.castAdd m k) = i) ∨
    (∃ k : Fin m, Fin.castAdd o (Fin.natAdd n k) = i) ∨
    (∃ l : Fin o, Fin.natAdd (n + m) l = i) := by
  by_cases hxy : i.val < n + m
  · by_cases hx : i.val < n
    · left
      refine ⟨⟨i.val, hx⟩, ?_⟩
      ext
      simp [Fin.coe_castAdd]
    · right
      left
      refine ⟨⟨i.val - n, by omega⟩, ?_⟩
      ext
      simp [Fin.coe_castAdd, Fin.coe_natAdd]
      omega
  · right
    right
    refine ⟨⟨i.val - (n + m), by omega⟩, ?_⟩
    ext
    simp [Fin.coe_natAdd]
    omega

/-- Scaling the first block of a triple representative stays inside. -/
theorem tripleRepresentatives_xscale {n m o : ℕ}
    (T : Set ((ProjectivePoint n × ProjectivePoint m) × ProjectivePoint o))
    {w : Point (n + m + o)} (hw : w ∈ tripleRepresentatives T)
    {c : ℂ} (hc : c ≠ 0) :
    (fun i => c ^ (xWeight n m o i) • w i) ∈ tripleRepresentatives T := by
  obtain ⟨x, y, z, hx, hy, hz, hmem, rfl⟩ := hw
  have heq : (fun i => c ^ (xWeight n m o i) • (joinPoints (joinPoints x y) z) i)
      = joinPoints (joinPoints (c • x) y) z := by
    funext i
    rcases triple_index_trichotomy i with ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨l, rfl⟩
    · simp [xWeight, joinPoints, Fin.addCases_left, pow_one]
    · simp [xWeight, joinPoints, Fin.addCases_left, Fin.addCases_right, pow_zero]
    · simp [xWeight, joinPoints, Fin.addCases_right, pow_zero]
  rw [heq]
  refine ⟨c • x, y, z, smul_ne_zero hc hx, hy, hz, ?_, rfl⟩
  have hxproj : Projectivization.mk ℂ (c • x) (smul_ne_zero hc hx) =
      Projectivization.mk ℂ x hx :=
    (Projectivization.mk_eq_mk_iff' ℂ (c • x) x _ _).2 ⟨c, rfl⟩
  rw [hxproj]
  exact hmem

/-- Scaling the second block of a triple representative stays inside. -/
theorem tripleRepresentatives_yscale {n m o : ℕ}
    (T : Set ((ProjectivePoint n × ProjectivePoint m) × ProjectivePoint o))
    {w : Point (n + m + o)} (hw : w ∈ tripleRepresentatives T)
    {c : ℂ} (hc : c ≠ 0) :
    (fun i => c ^ (yWeight n m o i) • w i) ∈ tripleRepresentatives T := by
  obtain ⟨x, y, z, hx, hy, hz, hmem, rfl⟩ := hw
  have heq : (fun i => c ^ (yWeight n m o i) • (joinPoints (joinPoints x y) z) i)
      = joinPoints (joinPoints x (c • y)) z := by
    funext i
    rcases triple_index_trichotomy i with ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨l, rfl⟩
    · simp [yWeight, joinPoints, Fin.addCases_left, pow_zero]
    · simp [yWeight, joinPoints, Fin.addCases_left, Fin.addCases_right, pow_one]
    · simp [yWeight, joinPoints, Fin.addCases_right, pow_zero]
  rw [heq]
  refine ⟨x, c • y, z, hx, smul_ne_zero hc hy, hz, ?_, rfl⟩
  have hyproj : Projectivization.mk ℂ (c • y) (smul_ne_zero hc hy) =
      Projectivization.mk ℂ y hy :=
    (Projectivization.mk_eq_mk_iff' ℂ (c • y) y _ _).2 ⟨c, rfl⟩
  rw [hyproj]
  exact hmem

/-- Scaling the third block of a triple representative stays inside. -/
theorem tripleRepresentatives_zscale {n m o : ℕ}
    (T : Set ((ProjectivePoint n × ProjectivePoint m) × ProjectivePoint o))
    {w : Point (n + m + o)} (hw : w ∈ tripleRepresentatives T)
    {c : ℂ} (hc : c ≠ 0) :
    (fun i => c ^ (zWeight n m o i) • w i) ∈ tripleRepresentatives T := by
  obtain ⟨x, y, z, hx, hy, hz, hmem, rfl⟩ := hw
  have heq : (fun i => c ^ (zWeight n m o i) • (joinPoints (joinPoints x y) z) i)
      = joinPoints (joinPoints x y) (c • z) := by
    funext i
    rcases triple_index_trichotomy i with ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨l, rfl⟩
    · simp [zWeight, joinPoints, Fin.addCases_left, pow_zero]
    · simp [zWeight, joinPoints, Fin.addCases_left, Fin.addCases_right, pow_zero]
    · simp [zWeight, joinPoints, Fin.addCases_right, pow_one]
  rw [heq]
  refine ⟨x, y, c • z, hx, hy, smul_ne_zero hc hz, ?_, rfl⟩
  have hzproj : Projectivization.mk ℂ (c • z) (smul_ne_zero hc hz) =
      Projectivization.mk ℂ z hz :=
    (Projectivization.mk_eq_mk_iff' ℂ (c • z) z _ _).2 ⟨c, rfl⟩
  rw [hzproj]
  exact hmem

/-- The triple vanishing ideal is closed under first-block homogeneous components. -/
theorem tripleIx_mem_whc_x {n m o : ℕ}
    (T : Set ((ProjectivePoint n × ProjectivePoint m) × ProjectivePoint o))
    {F : Poly (n + m + o)} (hF : F ∈ MvPolynomial.vanishingIdeal ℂ (tripleRepresentatives T))
    (D : ℕ) :
    MvPolynomial.weightedHomogeneousComponent (xWeight n m o) D F ∈
      MvPolynomial.vanishingIdeal ℂ (tripleRepresentatives T) :=
  whc_mem_of_mem_weightedCone _ _ (fun v hv c hc => tripleRepresentatives_xscale T hv hc) hF D

/-- The triple vanishing ideal is closed under second-block homogeneous components. -/
theorem tripleIx_mem_whc_y {n m o : ℕ}
    (T : Set ((ProjectivePoint n × ProjectivePoint m) × ProjectivePoint o))
    {F : Poly (n + m + o)} (hF : F ∈ MvPolynomial.vanishingIdeal ℂ (tripleRepresentatives T))
    (D : ℕ) :
    MvPolynomial.weightedHomogeneousComponent (yWeight n m o) D F ∈
      MvPolynomial.vanishingIdeal ℂ (tripleRepresentatives T) :=
  whc_mem_of_mem_weightedCone _ _ (fun v hv c hc => tripleRepresentatives_yscale T hv hc) hF D

/-- The triple vanishing ideal is closed under third-block homogeneous components. -/
theorem tripleIx_mem_whc_z {n m o : ℕ}
    (T : Set ((ProjectivePoint n × ProjectivePoint m) × ProjectivePoint o))
    {F : Poly (n + m + o)} (hF : F ∈ MvPolynomial.vanishingIdeal ℂ (tripleRepresentatives T))
    (D : ℕ) :
    MvPolynomial.weightedHomogeneousComponent (zWeight n m o) D F ∈
      MvPolynomial.vanishingIdeal ℂ (tripleRepresentatives T) :=
  whc_mem_of_mem_weightedCone _ _ (fun v hv c hc => tripleRepresentatives_zscale T hv hc) hF D

/-! ### Bidegree coordinates over the third block -/

/-- The bidegree-(s,t) exponent set in the first two blocks. -/
abbrev bidegIndex (n m s t : ℕ) :=
  {d : Fin (n + m) →₀ ℕ // (∑ i : Fin n, d (Fin.castAdd m i)) = s ∧
    (∑ i : Fin m, d (Fin.natAdd n i)) = t}

instance bidegIndexFintype (n m s t : ℕ) : Fintype (bidegIndex n m s t) := by
  classical
  have hfin := DistinctDistances.TrackB.finite_pairExponents (n := n) (m := m) (s := s) (t := t)
  haveI hfin' : Finite (bidegIndex n m s t) := hfin
  exact Fintype.ofFinite _

/-- Embedding of the first two blocks into the triple ring. -/
def embXY (n m o : ℕ) : Fin (n + m) ↪ Fin (n + m + o) := Fin.castAddEmb o

/-- Embedding of the third block into the triple ring. -/
def embZ (n m o : ℕ) : Fin o ↪ Fin (n + m + o) := Fin.natAddEmb (n + m)

theorem embXY_val (n m o : ℕ) (j : Fin (n + m)) : (embXY n m o j).val = j.val := rfl

theorem embZ_val (n m o : ℕ) (l : Fin o) : (embZ n m o l).val = (n + m) + l.val := rfl

/-- Inclusion of third-block polynomials into the triple ring. -/
def zInclusion (n m o : ℕ) : Poly o →ₐ[ℂ] Poly (n + m + o) :=
  MvPolynomial.rename (embZ n m o)

/-- First-two-block part of an exponent. -/
def xyPart (n m o : ℕ) (D : Fin (n + m + o) →₀ ℕ) : Fin (n + m) →₀ ℕ :=
  Finsupp.comapDomain (embXY n m o) D (embXY n m o).injective.injOn

/-- Third-block part of an exponent. -/
def zPart (n m o : ℕ) (D : Fin (n + m + o) →₀ ℕ) : Fin o →₀ ℕ :=
  Finsupp.comapDomain (embZ n m o) D (embZ n m o).injective.injOn

/-- Evaluating an embedded function at an embedded point recovers the value. -/
theorem embDomain_at {α β : Type*} (f : α ↪ β) (v : α →₀ ℕ) (a : α) :
    Finsupp.embDomain f v (f a) = v a := by
  have h := congrArg (fun w => w a) (Finsupp.comapDomain_embDomain f v)
  rwa [Finsupp.comapDomain_apply] at h

/-- Embedded functions vanish off the range. -/
theorem embDomain_notin {α β : Type*} (f : α ↪ β) (v : α →₀ ℕ) {b : β}
    (hb : ∀ a, f a ≠ b) : Finsupp.embDomain f v b = 0 := by
  rw [Finsupp.embDomain_apply, dif_neg (not_exists.mpr hb)]

theorem xyPart_apply (n m o : ℕ) (D : Fin (n + m + o) →₀ ℕ) (j : Fin (n + m)) :
    xyPart n m o D j = D (embXY n m o j) :=
  Finsupp.comapDomain_apply _ _ _ _

theorem zPart_apply (n m o : ℕ) (D : Fin (n + m + o) →₀ ℕ) (l : Fin o) :
    zPart n m o D l = D (embZ n m o l) :=
  Finsupp.comapDomain_apply _ _ _ _

/-- For an embedding, `mapDomain` agrees with `embDomain`. -/
theorem mapDomain_eq_embDomain {α β : Type*} (e : α ↪ β) (d : α →₀ ℕ) :
    Finsupp.mapDomain (⇑e) d = Finsupp.embDomain e d := by
  apply Finsupp.ext
  intro b
  rw [Finsupp.mapDomain_apply]
  show d.sum (fun a m => (Finsupp.single (e a) m) b) = Finsupp.embDomain e d b
  by_cases hb : ∃ a, e a = b
  · obtain ⟨a, rfl⟩ := hb
    rw [embDomain_at]
    show ∑ a' ∈ d.support, (Finsupp.single (e a') (d a')) (e a) = d a
    rw [Finset.sum_eq_single a]
    · rw [Finsupp.single_eq_same]
    · intro a' _ hne
      have hne' : e a' ≠ e a := fun hcon => hne (e.injective hcon)
      exact Finsupp.single_eq_of_ne hne'.symm
    · intro hcon
      rw [Finsupp.single_eq_same]
      exact Finsupp.notMem_support_iff.mp hcon
  · have h0 : Finsupp.embDomain e d b = 0 :=
      embDomain_notin _ _ (fun a ha => hb ⟨a, ha⟩)
    rw [h0]
    show ∑ a' ∈ d.support, (Finsupp.single (e a') (d a')) b = 0
    apply Finset.sum_eq_zero
    intro a' _
    have hne' : e a' ≠ b := fun hcon => hb ⟨a', hcon⟩
    exact Finsupp.single_eq_of_ne hne'.symm

/-- Inclusion sends monomials to embedded monomials. -/
theorem zInclusion_monomial (n m o : ℕ) (γ : Fin o →₀ ℕ) (c : ℂ) :
    zInclusion n m o (MvPolynomial.monomial γ c) =
      MvPolynomial.monomial (Finsupp.embDomain (embZ n m o) γ) c := by
  simp only [zInclusion, MvPolynomial.rename_monomial]
  rw [mapDomain_eq_embDomain]

/-- Recombining the parts recovers the exponent. -/
theorem parts_recombine (n m o : ℕ) (D : Fin (n + m + o) →₀ ℕ) :
    Finsupp.embDomain (embXY n m o) (xyPart n m o D) +
      Finsupp.embDomain (embZ n m o) (zPart n m o D) = D := by
  apply Finsupp.ext
  intro i
  by_cases h : ∃ j : Fin (n + m), embXY n m o j = i
  · obtain ⟨j, rfl⟩ := h
    rw [Finsupp.add_apply, embDomain_at, xyPart_apply]
    have hz : Finsupp.embDomain (embZ n m o) (zPart n m o D) (embXY n m o j) = 0 := by
      apply embDomain_notin
      intro l hl
      have h2 := congrArg Fin.val hl
      rw [embZ_val, embXY_val] at h2
      have := j.isLt
      omega
    rw [hz, add_zero]
  · rw [not_exists] at h
    have hi := i.isLt
    have h' : ∃ l : Fin o, embZ n m o l = i := by
      by_contra hc
      rw [not_exists] at hc
      by_cases hlt : i.val < n + m
      · exact h ⟨i.val, hlt⟩ (Fin.ext (by show i.val = i.val; rfl))
      · have hcon' : n + m ≤ i.val := not_lt.mp hlt
        have hmem : i.val - (n + m) < o := by omega
        have heq : (embZ n m o ⟨i.val - (n + m), hmem⟩).val = i.val := by
          show (n + m) + (i.val - (n + m)) = i.val
          omega
        exact hc ⟨i.val - (n + m), hmem⟩ (Fin.ext heq)
    obtain ⟨l, rfl⟩ := h'
    rw [Finsupp.add_apply, embDomain_at, zPart_apply]
    have hx : Finsupp.embDomain (embXY n m o) (xyPart n m o D) (embZ n m o l) = 0 := by
      apply embDomain_notin
      intro j hj
      have h2 := congrArg Fin.val hj
      rw [embZ_val, embXY_val] at h2
      have := j.isLt
      omega
    rw [hx, zero_add]

/-- The bidegree-(s,t) piece (all third-block degrees) of the triple ring. -/
def bidegPiece (n m o s t : ℕ) : Submodule ℂ (Poly (n + m + o)) :=
  MvPolynomial.restrictSupport ℂ {D : Fin (n + m + o) →₀ ℕ |
    (∑ i : Fin n, D (Fin.castAdd o (Fin.castAdd m i))) = s ∧
    (∑ i : Fin m, D (Fin.castAdd o (Fin.natAdd n i))) = t}

/-- Bidegree-(s,t) monomials of the first two blocks, embedded in the triple ring. -/
def bidegMonomial (n m o s t : ℕ) (α : bidegIndex n m s t) : Poly (n + m + o) :=
  MvPolynomial.monomial (Finsupp.embDomain (embXY n m o) α.1) 1

/-- Third-block coefficient of `F` at the bidegree monomial `α`. -/
def bidegCoeff (n m o s t : ℕ) (F : Poly (n + m + o)) (α : bidegIndex n m s t) : Poly o :=
  ∑ D ∈ F.support with xyPart n m o D = α.1, MvPolynomial.monomial (zPart n m o D) (F.coeff D)

/-- The bidegree parts of an exponent in the piece lie in the index set. -/
theorem xyPart_mem_bideg (n m o s t : ℕ) (F : Poly (n + m + o))
    (hF : F ∈ bidegPiece n m o s t) (D : Fin (n + m + o) →₀ ℕ) (hD : D ∈ F.support) :
    xyPart n m o D ∈ {d : Fin (n + m) →₀ ℕ |
      (∑ i : Fin n, d (Fin.castAdd m i)) = s ∧
      (∑ i : Fin m, d (Fin.natAdd n i)) = t} := by
  have hsupp : ↑F.support ⊆ {D : Fin (n + m + o) →₀ ℕ |
      (∑ i : Fin n, D (Fin.castAdd o (Fin.castAdd m i))) = s ∧
      (∑ i : Fin m, D (Fin.castAdd o (Fin.natAdd n i))) = t} := by
    have := (MvPolynomial.mem_restrictSupport_iff ℂ).mp hF
    simpa [bidegPiece] using this
  have hDm := hsupp (Finset.mem_coe.mpr hD)
  constructor
  · -- x-sum: transport along the embedding
    have e1 : ∀ i : Fin n, (xyPart n m o D) (Fin.castAdd m i) =
        D (Fin.castAdd o (Fin.castAdd m i)) := by
      intro i
      rw [xyPart_apply]
      congr 1
    simp only [e1]
    exact hDm.1
  · have e2 : ∀ i : Fin m, (xyPart n m o D) (Fin.natAdd n i) =
        D (Fin.castAdd o (Fin.natAdd n i)) := by
      intro i
      rw [xyPart_apply]
      congr 1
    simp only [e2]
    exact hDm.2

/-- Total fiber index with junk fallback. -/
def fiberIdx (n m o s t : ℕ) (junk : bidegIndex n m s t) (D : Fin (n + m + o) →₀ ℕ) :
    bidegIndex n m s t :=
  if h : xyPart n m o D ∈ {d : Fin (n + m) →₀ ℕ |
      (∑ i : Fin n, d (Fin.castAdd m i)) = s ∧
      (∑ i : Fin m, d (Fin.natAdd n i)) = t} then ⟨_, h⟩ else junk

theorem fiberIdx_val (n m o s t : ℕ) (junk : bidegIndex n m s t) (D : Fin (n + m + o) →₀ ℕ)
    (hD : xyPart n m o D ∈ {d : Fin (n + m) →₀ ℕ |
      (∑ i : Fin n, d (Fin.castAdd m i)) = s ∧
      (∑ i : Fin m, d (Fin.natAdd n i)) = t}) :
    (fiberIdx n m o s t junk D).1 = xyPart n m o D := by
  unfold fiberIdx
  rw [dif_pos hD]

/-- Coordinate decomposition: every element of the bidegree piece is a combination
of bidegree monomials with third-block coefficients. -/
theorem coord_decomp (n m o s t : ℕ) (F : Poly (n + m + o)) (hF : F ∈ bidegPiece n m o s t) :
    F = ∑ α : bidegIndex n m s t,
      bidegMonomial n m o s t α * zInclusion n m o (bidegCoeff n m o s t F α) := by
  classical
  by_cases hsupp : F.support.Nonempty
  · obtain ⟨D₀, hD₀⟩ := hsupp
    have hmem : ∀ D ∈ F.support, xyPart n m o D ∈ {d : Fin (n + m) →₀ ℕ |
        (∑ i : Fin n, d (Fin.castAdd m i)) = s ∧
        (∑ i : Fin m, d (Fin.natAdd n i)) = t} :=
      fun D hD => xyPart_mem_bideg n m o s t F hF D hD
    -- Total fiber index, with junk value outside the support.
    set g := fiberIdx n m o s t ⟨xyPart n m o D₀, hmem D₀ hD₀⟩ with hgdef
    have hg : ∀ D ∈ F.support, (g D).1 = xyPart n m o D := by
      intro D hD
      rw [hgdef]
      exact fiberIdx_val n m o s t _ D (hmem D hD)
    -- Expand each summand into monomials.
    have hexpand : ∀ α : bidegIndex n m s t,
        bidegMonomial n m o s t α * zInclusion n m o (bidegCoeff n m o s t F α) =
        ∑ D ∈ F.support with xyPart n m o D = α.1,
          MvPolynomial.monomial (Finsupp.embDomain (embXY n m o) α.1 +
            Finsupp.embDomain (embZ n m o) (zPart n m o D)) (F.coeff D) := by
      intro α
      unfold bidegMonomial bidegCoeff
      rw [map_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro D _
      rw [zInclusion_monomial, MvPolynomial.monomial_mul_monomial]
      simp only [one_mul]
    -- Fibers of g match the xyPart fibers on the support.
    have hfilter : ∀ α : bidegIndex n m s t,
        F.support.filter (fun D => g D = α) =
        F.support.filter (fun D => xyPart n m o D = α.1) := by
      intro α
      apply Finset.ext
      intro D
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hD, h1⟩
        exact ⟨hD, (hg D hD).symm.trans (Subtype.ext_iff.mp h1)⟩
      · rintro ⟨hD, h1⟩
        exact ⟨hD, Subtype.ext ((hg D hD).trans h1)⟩
    -- Swap the sums via the fiberwise identity.
    have hswap : (∑ α : bidegIndex n m s t, ∑ D ∈ F.support with xyPart n m o D = α.1,
          MvPolynomial.monomial (Finsupp.embDomain (embXY n m o) α.1 +
            Finsupp.embDomain (embZ n m o) (zPart n m o D)) (F.coeff D)) =
        ∑ D ∈ F.support, MvPolynomial.monomial (Finsupp.embDomain (embXY n m o) (xyPart n m o D) +
            Finsupp.embDomain (embZ n m o) (zPart n m o D)) (F.coeff D) := by
      have hstep : ∀ α : bidegIndex n m s t,
          (∑ D ∈ F.support with xyPart n m o D = α.1,
            MvPolynomial.monomial (Finsupp.embDomain (embXY n m o) α.1 +
              Finsupp.embDomain (embZ n m o) (zPart n m o D)) (F.coeff D)) =
          (∑ D ∈ F.support with g D = α,
            MvPolynomial.monomial (Finsupp.embDomain (embXY n m o) (g D).1 +
              Finsupp.embDomain (embZ n m o) (zPart n m o D)) (F.coeff D)) := by
        intro α
        rw [← hfilter α]
        apply Finset.sum_congr rfl
        intro D hD
        have hDα : g D = α := (Finset.mem_filter.mp hD).2
        rw [hDα]
      have hfib := Finset.sum_fiberwise_of_maps_to (s := F.support) (t := Finset.univ)
        (fun D _ => Finset.mem_univ (g D))
        (fun D => MvPolynomial.monomial (Finsupp.embDomain (embXY n m o) (g D).1 +
          Finsupp.embDomain (embZ n m o) (zPart n m o D)) (F.coeff D))
      calc (∑ α : bidegIndex n m s t, ∑ D ∈ F.support with xyPart n m o D = α.1,
            MvPolynomial.monomial (Finsupp.embDomain (embXY n m o) α.1 +
              Finsupp.embDomain (embZ n m o) (zPart n m o D)) (F.coeff D))
          = ∑ α : bidegIndex n m s t, ∑ D ∈ F.support with g D = α,
            MvPolynomial.monomial (Finsupp.embDomain (embXY n m o) (g D).1 +
              Finsupp.embDomain (embZ n m o) (zPart n m o D)) (F.coeff D) :=
            Finset.sum_congr rfl (fun α _ => hstep α)
        _ = ∑ D ∈ F.support, MvPolynomial.monomial (Finsupp.embDomain (embXY n m o) (g D).1 +
            Finsupp.embDomain (embZ n m o) (zPart n m o D)) (F.coeff D) := hfib
        _ = ∑ D ∈ F.support, MvPolynomial.monomial (Finsupp.embDomain (embXY n m o) (xyPart n m o D) +
            Finsupp.embDomain (embZ n m o) (zPart n m o D)) (F.coeff D) := by
            apply Finset.sum_congr rfl
            intro D hD
            rw [hg D hD]
    rw [Finset.sum_congr rfl (fun α _ => hexpand α), hswap]
    have hrecombine : ∀ D ∈ F.support, MvPolynomial.monomial
        (Finsupp.embDomain (embXY n m o) (xyPart n m o D) +
          Finsupp.embDomain (embZ n m o) (zPart n m o D)) (F.coeff D) =
        MvPolynomial.monomial D (F.coeff D) := by
      intro D _
      rw [parts_recombine]
    rw [Finset.sum_congr rfl hrecombine]
    exact MvPolynomial.as_sum F
  · -- Empty support: both sides vanish.
    have hempty : F.support = ∅ := Finset.not_nonempty_iff_eq_empty.mp hsupp
    have hF0 : F = 0 := MvPolynomial.support_eq_empty.mp hempty
    have hzero : ∀ α : bidegIndex n m s t, bidegCoeff n m o s t 0 α = 0 := by
      intro α
      unfold bidegCoeff
      simp
    rw [hF0]
    symm
    apply Finset.sum_eq_zero
    intro α _
    rw [hzero α, map_zero, mul_zero]

/-! ### Fibre specialization of bidegree coordinates -/

/-- The x/y-block sums of an exponent agree with those of its xy-part. -/
theorem bideg_sums_xyPart {n m o : ℕ} (D : Fin (n + m + o) →₀ ℕ) :
    (∑ i : Fin n, D (Fin.castAdd o (Fin.castAdd m i))
      = ∑ i : Fin n, (xyPart n m o D) (Fin.castAdd m i)) ∧
    (∑ i : Fin m, D (Fin.castAdd o (Fin.natAdd n i)))
      = ∑ i : Fin m, (xyPart n m o D) (Fin.natAdd n i) := by
  refine ⟨?_, ?_⟩ <;> (apply Finset.sum_congr rfl; intro i _; simp only [xyPart_apply, embXY, embZ, Fin.coe_castAddEmb, Fin.natAddEmb_apply])

/-- Specializing a monomial splits into the xy-monomial and evaluated z-part. -/
theorem fibreSpecialize_monomial {n m o : ℕ} (z : Point o)
    (D : Fin (n + m + (o + 1)) →₀ ℕ) (c : ℂ) :
    fibreSpecialize (q := n + m) (o := o) z (MvPolynomial.monomial D c)
      = MvPolynomial.monomial (xyPart n m (o + 1) D)
        (c * MvPolynomial.eval ((Fin.cons (1 : ℂ) z : Fin (o + 1) → ℂ))
          (MvPolynomial.monomial (zPart n m (o + 1) D) 1)) := by
  classical
  have eX : ∀ j : Fin (n + m),
      Fin.append (fun i : Fin (n + m) => (MvPolynomial.X i : Poly (n + m)))
        (Fin.cons (1 : Poly (n + m)) (fun l : Fin o => MvPolynomial.C (z l)))
        ((embXY n m (o + 1)) j) = MvPolynomial.X j := by
    intro j
    show Fin.append _ _ (Fin.castAdd _ j) = _
    rw [Fin.append_left]
  have eZ : ∀ l : Fin (o + 1),
      Fin.append (fun i : Fin (n + m) => (MvPolynomial.X i : Poly (n + m)))
        (Fin.cons (1 : Poly (n + m)) (fun l : Fin o => MvPolynomial.C (z l)))
        ((embZ n m (o + 1)) l)
        = MvPolynomial.C (((Fin.cons (1 : ℂ) z : Fin (o + 1) → ℂ)) l) := by
    intro l
    show Fin.append _ _ (Fin.natAdd _ l) = _
    rw [Fin.append_right]
    cases l using Fin.cases with
    | zero => simp
    | succ k => simp
  have hsplit : D.prod (fun i k => Fin.append
        (fun i : Fin (n + m) => (MvPolynomial.X i : Poly (n + m)))
        (Fin.cons (1 : Poly (n + m)) (fun l : Fin o => MvPolynomial.C (z l))) i ^ k)
      = (xyPart n m (o + 1) D).prod (fun j k => Fin.append
        (fun i : Fin (n + m) => (MvPolynomial.X i : Poly (n + m)))
        (Fin.cons (1 : Poly (n + m)) (fun l : Fin o => MvPolynomial.C (z l)))
        ((embXY n m (o + 1)) j) ^ k)
        * (zPart n m (o + 1) D).prod (fun l k => Fin.append
        (fun i : Fin (n + m) => (MvPolynomial.X i : Poly (n + m)))
        (Fin.cons (1 : Poly (n + m)) (fun l : Fin o => MvPolynomial.C (z l)))
        ((embZ n m (o + 1)) l) ^ k) := by
    conv_lhs => rw [← parts_recombine n m (o + 1) D,
      Finsupp.prod_add_index' (fun a => pow_zero _) (fun a b₁ b₂ => pow_add _ _ _)]
    simp only [Finsupp.prod_embDomain]
  have exy : (xyPart n m (o + 1) D).prod
        (fun j k => Fin.append (fun i : Fin (n + m) => (MvPolynomial.X i : Poly (n + m)))
          (Fin.cons (1 : Poly (n + m)) (fun l : Fin o => MvPolynomial.C (z l)))
          ((embXY n m (o + 1)) j) ^ k)
        = MvPolynomial.monomial (xyPart n m (o + 1) D) 1 := by
    show (∏ j ∈ (xyPart n m (o + 1) D).support, Fin.append
          (fun i : Fin (n + m) => (MvPolynomial.X i : Poly (n + m)))
          (Fin.cons (1 : Poly (n + m)) (fun l : Fin o => MvPolynomial.C (z l)))
          ((embXY n m (o + 1)) j) ^ (xyPart n m (o + 1) D) j)
      = MvPolynomial.monomial (xyPart n m (o + 1) D) 1
    rw [← MvPolynomial.prod_X_pow_eq_monomial]
    apply Finset.prod_congr rfl
    intro j _
    rw [eX j]
  have ez : (zPart n m (o + 1) D).prod
        (fun l k => Fin.append (fun i : Fin (n + m) => (MvPolynomial.X i : Poly (n + m)))
          (Fin.cons (1 : Poly (n + m)) (fun l : Fin o => MvPolynomial.C (z l)))
          ((embZ n m (o + 1)) l) ^ k)
        = MvPolynomial.C (MvPolynomial.eval ((Fin.cons (1 : ℂ) z : Fin (o + 1) → ℂ))
          (MvPolynomial.monomial (zPart n m (o + 1) D) 1)) := by
    show (∏ l ∈ (zPart n m (o + 1) D).support, Fin.append
          (fun i : Fin (n + m) => (MvPolynomial.X i : Poly (n + m)))
          (Fin.cons (1 : Poly (n + m)) (fun l : Fin o => MvPolynomial.C (z l)))
          ((embZ n m (o + 1)) l) ^ (zPart n m (o + 1) D) l)
      = MvPolynomial.C (MvPolynomial.eval ((Fin.cons (1 : ℂ) z : Fin (o + 1) → ℂ))
        (MvPolynomial.monomial (zPart n m (o + 1) D) 1))
    rw [MvPolynomial.eval_monomial, one_mul]
    trans ∏ l ∈ (zPart n m (o + 1) D).support,
      MvPolynomial.C ((((Fin.cons (1 : ℂ) z : Fin (o + 1) → ℂ)) l) ^ (zPart n m (o + 1) D) l)
    · apply Finset.prod_congr rfl
      intro l _
      rw [eZ l, ← map_pow]
    · rw [← map_prod]
      congr 1
  simp only [fibreSpecialize, MvPolynomial.aeval_monomial]
  rw [hsplit, exy, ez, MvPolynomial.algebraMap_eq,
    mul_comm (MvPolynomial.monomial _ 1) _, ← mul_assoc, ← map_mul,
    MvPolynomial.C_mul_monomial, mul_one]

/-- Specializing a bidegree monomial drops the third block. -/
theorem fibreSpecialize_bidegMonomial {n m o s t : ℕ} (z : Point o)
    (α : bidegIndex n m s t) :
    fibreSpecialize (q := n + m) (o := o) z
      (bidegMonomial n m (o + 1) s t α) = MvPolynomial.monomial α.1 1 := by
  classical
  have eσ : ∀ j : Fin (n + m),
      Fin.append (fun i : Fin (n + m) => (MvPolynomial.X i : Poly (n + m)))
        (Fin.cons (1 : Poly (n + m)) (fun l : Fin o => MvPolynomial.C (z l)))
        ((embXY n m (o + 1)) j) = MvPolynomial.X j := by
    intro j
    show Fin.append _ _ (Fin.castAdd _ j) = _
    rw [Fin.append_left]
  simp only [bidegMonomial, fibreSpecialize, MvPolynomial.aeval_monomial, map_one, one_mul,
    Finsupp.prod_embDomain]
  rw [← MvPolynomial.prod_X_pow_eq_monomial]
  show (∏ a ∈ α.1.support,
      Fin.append (fun i : Fin (n + m) => (MvPolynomial.X i : Poly (n + m)))
        (Fin.cons (1 : Poly (n + m)) (fun l : Fin o => MvPolynomial.C (z l)))
        ((embXY n m (o + 1)) a) ^ α.1 a)
      = ∏ x ∈ α.1.support, MvPolynomial.X x ^ α.1 x
  apply Finset.prod_congr rfl
  intro j _
  simp only [eσ j]

/-- Specializing a third-block inclusion evaluates the coefficients at `(1, z)`. -/
theorem fibreSpecialize_zInclusion {n m o : ℕ} (z : Point o) (q : Poly (o + 1)) :
    fibreSpecialize (q := n + m) (o := o) z (zInclusion n m (o + 1) q)
      = MvPolynomial.C (MvPolynomial.eval (Fin.cons (1 : ℂ) z) q) := by
  classical
  have eσ : ∀ l : Fin (o + 1),
      Fin.append (fun i : Fin (n + m) => (MvPolynomial.X i : Poly (n + m)))
        (Fin.cons (1 : Poly (n + m)) (fun l : Fin o => MvPolynomial.C (z l)))
        ((embZ n m (o + 1)) l)
        = MvPolynomial.C (((Fin.cons (1 : ℂ) z : Fin (o + 1) → ℂ)) l) := by
    intro l
    show Fin.append _ _ (Fin.natAdd _ l) = _
    rw [Fin.append_right]
    cases l using Fin.cases with
    | zero => simp
    | succ k => simp
  have hcomp : (Fin.append (fun i : Fin (n + m) => (MvPolynomial.X i : Poly (n + m)))
        (Fin.cons (1 : Poly (n + m)) (fun l : Fin o => MvPolynomial.C (z l))))
        ∘ (embZ n m (o + 1))
      = MvPolynomial.C ∘ ((Fin.cons (1 : ℂ) z : Fin (o + 1) → ℂ)) := funext eσ
  simp only [zInclusion, fibreSpecialize, MvPolynomial.aeval_rename, hcomp]
  induction q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    simp only [MvPolynomial.aeval_eq_bind₁] at hp hq
    simp [hp, hq]
  | mul_X p k hp =>
    simp only [MvPolynomial.aeval_eq_bind₁] at hp
    simp [hp]


/-! ### Trihomogeneous generators of the triple ideal -/

/-- A nonzero polynomial has a nonzero coefficient. -/
theorem exists_coeff_ne_zero_of_ne_zero {N : ℕ} (G : Poly N) (h : G ≠ 0) :
    ∃ m, G.coeff m ≠ 0 := by
  by_contra hc
  apply h
  apply MvPolynomial.ext
  intro m
  rw [MvPolynomial.coeff_zero]
  by_contra hm'
  exact hc ⟨m, hm'⟩

/-- Weighted degree as a sum. -/
theorem weight_eq_sum {N : ℕ} (w : Fin N → ℕ) (m : Fin N →₀ ℕ) :
    Finsupp.weight w m = ∑ i, w i * m i := by
  have hwm : m.sum (fun i c => c • w i) = ∑ i, w i * m i := by
    rw [Finsupp.sum_fintype _ _ (fun i => by simp)]
    exact Finset.sum_congr rfl (fun i _ => by simp [smul_eq_mul, mul_comm])
  rw [Finsupp.weight_apply]
  exact hwm

/-- 0/1-weighted degree is bounded by total degree. -/
theorem weight_le_totalDegree {N : ℕ} (w : Fin N → ℕ) (hw : ∀ i, w i ≤ 1) (F : Poly N)
    (m : Fin N →₀ ℕ) (hm : m ∈ F.support) : Finsupp.weight w m ≤ F.totalDegree := by
  calc Finsupp.weight w m = ∑ i, w i * m i := weight_eq_sum w m
    _ ≤ ∑ i, 1 * m i := by
          apply Finset.sum_le_sum
          intro i _
          exact Nat.mul_le_mul (hw i) (le_refl _)
    _ = m.degree := by
          simp only [one_mul]
          exact (RulingMaps.degree_eq_sum_univ m).symm
    _ ≤ F.totalDegree := MvPolynomial.le_totalDegree hm

/-- Block weights are 0/1-valued. -/
theorem xWeight_le_one (n m o : ℕ) (i : Fin (n + m + o)) : xWeight n m o i ≤ 1 := by
  rcases triple_index_trichotomy i with ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨l, rfl⟩
  · simp [xWeight, Fin.addCases_left]
  · simp [xWeight, Fin.addCases_left, Fin.addCases_right]
  · simp [xWeight, Fin.addCases_right]

theorem yWeight_le_one (n m o : ℕ) (i : Fin (n + m + o)) : yWeight n m o i ≤ 1 := by
  rcases triple_index_trichotomy i with ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨l, rfl⟩
  · simp [yWeight, Fin.addCases_left]
  · simp [yWeight, Fin.addCases_left, Fin.addCases_right]
  · simp [yWeight, Fin.addCases_right]

theorem zWeight_le_one (n m o : ℕ) (i : Fin (n + m + o)) : zWeight n m o i ≤ 1 := by
  rcases triple_index_trichotomy i with ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨l, rfl⟩
  · simp [zWeight, Fin.addCases_left]
  · simp [zWeight, Fin.addCases_left, Fin.addCases_right]
  · simp [zWeight, Fin.addCases_right]

/-- A nonzero weighted component forces its degree below the total-degree bound. -/
theorem whc_oneNE_zero_bound {N : ℕ} (w : Fin N → ℕ) (hw : ∀ i, w i ≤ 1) (F : Poly N)
    (D : ℕ) (hne : MvPolynomial.weightedHomogeneousComponent w D F ≠ 0) :
    D ≤ F.totalDegree := by
  obtain ⟨m, hm⟩ := exists_coeff_ne_zero_of_ne_zero _ hne
  rw [MvPolynomial.coeff_weightedHomogeneousComponent] at hm
  have hDm : Finsupp.weight w m = D := by
    by_contra hcon
    rw [if_neg hcon] at hm
    exact hm rfl
  rw [if_pos hDm] at hm
  have hmsupp : m ∈ F.support := MvPolynomial.mem_support_iff.mpr hm
  calc D = Finsupp.weight w m := hDm.symm
    _ ≤ F.totalDegree := weight_le_totalDegree w hw F m hmsupp

/-- Weighted components are supported inside the support. -/
theorem whc_support_subset {N : ℕ} (w : Fin N → ℕ) (F : Poly N) (D : ℕ) :
    (MvPolynomial.weightedHomogeneousComponent w D F).support ⊆ F.support := by
  intro m hm
  rw [MvPolynomial.mem_support_iff] at hm ⊢
  rw [MvPolynomial.coeff_weightedHomogeneousComponent] at hm
  by_cases hwd : Finsupp.weight w m = D
  · rw [if_pos hwd] at hm
    exact hm
  · rw [if_neg hwd] at hm
    exact absurd rfl hm

/-- Weighted components preserve homogeneity in another weight. -/
theorem whc_preserves_homog {N : ℕ} (w v : Fin N → ℕ) (H : Poly N) (a d : ℕ)
    (hH : MvPolynomial.IsWeightedHomogeneous w H a) :
    MvPolynomial.IsWeightedHomogeneous w
      (MvPolynomial.weightedHomogeneousComponent v d H) a := by
  intro m hm
  rw [MvPolynomial.coeff_weightedHomogeneousComponent] at hm
  by_cases hwd : Finsupp.weight v m = d
  · rw [if_pos hwd] at hm
    exact hH hm
  · rw [if_neg hwd] at hm
    exact absurd rfl hm

/-- Bidegree component (y-filter outside, x-filter inside). -/
def BComp (n m o : ℕ) (a b : ℕ) (F : Poly (n + m + o)) : Poly (n + m + o) :=
  MvPolynomial.weightedHomogeneousComponent (yWeight n m o) b
    (MvPolynomial.weightedHomogeneousComponent (xWeight n m o) a F)

/-- Bidegree components lie in the triple ideal. -/
theorem BComp_mem_Ix {n m o : ℕ}
    (T : Set ((ProjectivePoint n × ProjectivePoint m) × ProjectivePoint o))
    {F : Poly (n + m + o)} (hF : F ∈ MvPolynomial.vanishingIdeal ℂ (tripleRepresentatives T))
    (a b : ℕ) : BComp n m o a b F ∈ MvPolynomial.vanishingIdeal ℂ (tripleRepresentatives T) :=
  tripleIx_mem_whc_y T (tripleIx_mem_whc_x T hF a) b

/-- Finite bidegree decomposition. -/
theorem bidegComp_sum (n m o : ℕ) (F : Poly (n + m + o)) :
    F = ∑ a ∈ Finset.range (F.totalDegree + 1), ∑ b ∈ Finset.range (F.totalDegree + 1),
      BComp n m o a b F := by
  have hx : F = ∑ a ∈ Finset.range (F.totalDegree + 1),
      MvPolynomial.weightedHomogeneousComponent (xWeight n m o) a F := by
    have h := MvPolynomial.sum_weightedHomogeneousComponent (xWeight n m o) F
    have hsub : Function.support
        (fun D => MvPolynomial.weightedHomogeneousComponent (xWeight n m o) D F) ⊆
        ↑(Finset.range (F.totalDegree + 1)) := by
      intro D hD
      have hne := Function.mem_support.mp hD
      have hle := whc_oneNE_zero_bound _ (xWeight_le_one n m o) F D hne
      simp only [Finset.coe_range, Set.mem_Iio]
      omega
    rw [finsum_eq_sum_of_support_subset _ hsub] at h
    exact h.symm
  calc F = ∑ a ∈ Finset.range (F.totalDegree + 1),
        MvPolynomial.weightedHomogeneousComponent (xWeight n m o) a F := hx
    _ = ∑ a ∈ Finset.range (F.totalDegree + 1), ∑ b ∈ Finset.range (F.totalDegree + 1),
        BComp n m o a b F := by
        apply Finset.sum_congr rfl
        intro a _
        have hy : MvPolynomial.weightedHomogeneousComponent (xWeight n m o) a F =
            ∑ b ∈ Finset.range (F.totalDegree + 1),
              MvPolynomial.weightedHomogeneousComponent (yWeight n m o) b
                (MvPolynomial.weightedHomogeneousComponent (xWeight n m o) a F) := by
          have h := MvPolynomial.sum_weightedHomogeneousComponent (yWeight n m o)
            (MvPolynomial.weightedHomogeneousComponent (xWeight n m o) a F)
          have hsub : Function.support (fun D =>
              MvPolynomial.weightedHomogeneousComponent (yWeight n m o) D
                (MvPolynomial.weightedHomogeneousComponent (xWeight n m o) a F)) ⊆
              ↑(Finset.range (F.totalDegree + 1)) := by
            intro D hD
            have hne := Function.mem_support.mp hD
            obtain ⟨e, he⟩ := exists_coeff_ne_zero_of_ne_zero _ hne
            rw [MvPolynomial.coeff_weightedHomogeneousComponent] at he
            have hDe : Finsupp.weight (yWeight n m o) e = D := by
              by_contra hc2
              rw [if_neg hc2] at he
              exact he rfl
            rw [if_pos hDe] at he
            have heF : e ∈ F.support :=
              whc_support_subset _ _ _ (MvPolynomial.mem_support_iff.mpr he)
            have hle := weight_le_totalDegree (yWeight n m o) (yWeight_le_one n m o) F e heF
            simp only [Finset.coe_range, Set.mem_Iio]
            omega
          rw [finsum_eq_sum_of_support_subset _ hsub] at h
          exact h.symm
        -- `BComp` unfolds to the same double filtering
        rw [hy]
        rfl

/-- Finite third-block decomposition. -/
theorem zComp_sum (n m o : ℕ) (G : Poly (n + m + o)) :
    G = ∑ d ∈ Finset.range (G.totalDegree + 1),
      MvPolynomial.weightedHomogeneousComponent (zWeight n m o) d G := by
  have h := MvPolynomial.sum_weightedHomogeneousComponent (zWeight n m o) G
  have hsub : Function.support
      (fun D => MvPolynomial.weightedHomogeneousComponent (zWeight n m o) D G) ⊆
      ↑(Finset.range (G.totalDegree + 1)) := by
    intro D hD
    have hne := Function.mem_support.mp hD
    have hle := whc_oneNE_zero_bound _ (zWeight_le_one n m o) G D hne
    simp only [Finset.coe_range, Set.mem_Iio]
    omega
  rw [finsum_eq_sum_of_support_subset _ hsub] at h
  exact h.symm

/-- Weighted components vanish beyond the total-degree bound. -/
theorem whc_eq_zero_of_gt {N : ℕ} (w : Fin N → ℕ) (hw : ∀ i, w i ≤ 1) (F : Poly N)
    (D : ℕ) (hD : F.totalDegree < D) :
    MvPolynomial.weightedHomogeneousComponent w D F = 0 := by
  by_contra hne
  exact absurd (whc_oneNE_zero_bound w hw F D hne) (by omega)

/-- Bidegree components vanish beyond the total-degree bound in the first block. -/
theorem BComp_eq_zero_of_gt_x (n m o : ℕ) (F : Poly (n + m + o)) (a b : ℕ)
    (ha : F.totalDegree < a) : BComp n m o a b F = 0 := by
  have h0 : MvPolynomial.weightedHomogeneousComponent (xWeight n m o) a F = 0 :=
    whc_eq_zero_of_gt _ (xWeight_le_one n m o) F a ha
  simp only [BComp, h0, map_zero]

/-- Bidegree components vanish beyond the total-degree bound in the second block. -/
theorem BComp_eq_zero_of_gt_y (n m o : ℕ) (F : Poly (n + m + o)) (a b : ℕ)
    (hb : F.totalDegree < b) : BComp n m o a b F = 0 := by
  by_contra hne
  obtain ⟨e, he⟩ := exists_coeff_ne_zero_of_ne_zero _ hne
  simp only [BComp] at he
  rw [MvPolynomial.coeff_weightedHomogeneousComponent] at he
  have hDm : Finsupp.weight (yWeight n m o) e = b := by
    by_contra hc2
    rw [if_neg hc2] at he
    exact he rfl
  rw [if_pos hDm] at he
  have heF : e ∈ F.support :=
    whc_support_subset _ _ _ (MvPolynomial.mem_support_iff.mpr he)
  exact absurd (weight_le_totalDegree _ (yWeight_le_one n m o) F e heF) (by omega)

/-! ### Weighted-component algebra: extraction, products, sums -/

/-- A weighted component of a homogeneous element is itself or zero. -/
theorem whc_of_homog {N : ℕ} (w : Fin N → ℕ) (H : Poly N) (D E : ℕ)
    (hH : MvPolynomial.IsWeightedHomogeneous w H E) :
    MvPolynomial.weightedHomogeneousComponent w D H = if D = E then H else 0 := by
  by_cases hDE : D = E
  · rw [if_pos hDE]
    apply MvPolynomial.ext
    intro m
    rw [MvPolynomial.coeff_weightedHomogeneousComponent]
    by_cases hwm : Finsupp.weight w m = D
    · rw [if_pos hwm]
    · rw [if_neg hwm]
      have h0 : H.coeff m = 0 := by
        by_contra hcon
        have hcon' : H.coeff m ≠ 0 := fun h => hcon h
        have hE := hH hcon'
        omega
      exact h0.symm
  · rw [if_neg hDE]
    apply MvPolynomial.ext
    intro m
    by_cases hwm : Finsupp.weight w m = D
    · rw [MvPolynomial.coeff_weightedHomogeneousComponent, if_pos hwm]
      by_contra hcon
      have hE := hH hcon
      omega
    · simp [MvPolynomial.coeff_weightedHomogeneousComponent, hwm]

/-- Bidegree components distribute over sums. -/
theorem BComp_map_sum {n m o : ℕ} (a b : ℕ) {ι : Type*} (F : Finset ι)
    (g : ι → Poly (n + m + o)) :
    BComp n m o a b (∑ i ∈ F, g i) = ∑ i ∈ F, BComp n m o a b (g i) := by
  simp only [BComp, map_sum]

/-- Bidegree extraction is the identity on bidegree elements. -/
theorem BComp_eq_self_of_bideg {n m o A B : ℕ} (H : Poly (n + m + o))
    (hA : MvPolynomial.IsWeightedHomogeneous (xWeight n m o) H A)
    (hB : MvPolynomial.IsWeightedHomogeneous (yWeight n m o) H B) :
    BComp n m o A B H = H := by
  simp only [BComp]
  rw [whc_of_homog _ _ _ _ hA, if_pos rfl, whc_of_homog _ _ _ _ hB, if_pos rfl]

/-- Bidegree extraction kills wrong-bidegree elements. -/
theorem BComp_eq_zero_of_bideg_ne {n m o s t A B : ℕ} (H : Poly (n + m + o))
    (hA : MvPolynomial.IsWeightedHomogeneous (xWeight n m o) H A)
    (hB : MvPolynomial.IsWeightedHomogeneous (yWeight n m o) H B)
    (h : s ≠ A ∨ t ≠ B) : BComp n m o s t H = 0 := by
  simp only [BComp]
  rcases h with hs | ht
  · rw [whc_of_homog _ _ _ _ hA, if_neg hs, map_zero]
  · have hpres : MvPolynomial.IsWeightedHomogeneous (yWeight n m o)
        (MvPolynomial.weightedHomogeneousComponent (xWeight n m o) s H) B :=
      whc_preserves_homog _ _ _ _ _ hB
    rw [whc_of_homog _ _ _ _ hpres, if_neg ht]

/-- Bidegree extraction of a product piece with known bidegrees. -/
theorem BComp_product_piece {n m o s t a b sk tk : ℕ} (H Gk : Poly (n + m + o))
    (hHx : MvPolynomial.IsWeightedHomogeneous (xWeight n m o) H a)
    (hHy : MvPolynomial.IsWeightedHomogeneous (yWeight n m o) H b)
    (hGx : MvPolynomial.IsWeightedHomogeneous (xWeight n m o) Gk sk)
    (hGy : MvPolynomial.IsWeightedHomogeneous (yWeight n m o) Gk tk) :
    BComp n m o s t (H * Gk) =
      if (a + sk = s ∧ b + tk = t) then H * Gk else 0 := by
  have hA : MvPolynomial.IsWeightedHomogeneous (xWeight n m o) (H * Gk) (a + sk) :=
    hHx.mul hGx
  have hB : MvPolynomial.IsWeightedHomogeneous (yWeight n m o) (H * Gk) (b + tk) :=
    hHy.mul hGy
  by_cases h : (a + sk = s ∧ b + tk = t)
  · rw [if_pos h]
    obtain ⟨h1, h2⟩ := h
    rw [← h1, ← h2]
    exact BComp_eq_self_of_bideg _ hA hB
  · rw [if_neg h]
    by_cases ha : a + sk = s
    · have htb : b + tk ≠ t := fun ht => h ⟨ha, ht⟩
      exact BComp_eq_zero_of_bideg_ne _ hA hB (Or.inr (Ne.symm htb))
    · exact BComp_eq_zero_of_bideg_ne _ hA hB (Or.inl (Ne.symm ha))

/-- Bidegree extraction of a product with known bidegree factor. -/
theorem BComp_product_eq {n m o s t : ℕ} (c Gk : Poly (n + m + o)) (sk tk : ℕ)
    (hGx : MvPolynomial.IsWeightedHomogeneous (xWeight n m o) Gk sk)
    (hGy : MvPolynomial.IsWeightedHomogeneous (yWeight n m o) Gk tk)
    (hsk : sk ≤ s) (htk : tk ≤ t) :
    BComp n m o s t (c * Gk) = (BComp n m o (s - sk) (t - tk) c) * Gk := by
  classical
  have hcsum := bidegComp_sum n m o c
  have hmul : c * Gk
      = ∑ a ∈ Finset.range (c.totalDegree + 1), ∑ b ∈ Finset.range (c.totalDegree + 1),
        (BComp n m o a b c) * Gk := by
    conv_lhs => rw [hcsum]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_mul]
  have hlin : BComp n m o s t (c * Gk)
      = ∑ a ∈ Finset.range (c.totalDegree + 1), ∑ b ∈ Finset.range (c.totalDegree + 1),
        BComp n m o s t ((BComp n m o a b c) * Gk) := by
    rw [hmul]
    simp only [BComp_map_sum]
  have hpiece : ∀ a b : ℕ, BComp n m o s t ((BComp n m o a b c) * Gk)
      = if (a + sk = s ∧ b + tk = t) then (BComp n m o a b c) * Gk else 0 := by
    intro a b
    apply BComp_product_piece
    · exact whc_preserves_homog _ _ _ _ _
        (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous _ _)
    · exact MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous _ _
    · exact hGx
    · exact hGy
  -- Evaluate the double indicator sum.
  have hA : ∀ a : ℕ, (a + sk = s) = (a = s - sk) := fun a => propext (by omega)
  have hB : ∀ b : ℕ, (b + tk = t) = (b = t - tk) := fun b => propext (by omega)
  have hinner : ∀ a : ℕ, (∑ b ∈ Finset.range (c.totalDegree + 1),
        (if (a + sk = s ∧ b + tk = t) then (BComp n m o a b c) * Gk else 0))
      = if a + sk = s then
        (if (t - tk) ∈ Finset.range (c.totalDegree + 1)
          then (BComp n m o a (t - tk) c) * Gk else 0) else 0 := by
    intro a
    by_cases ha : a + sk = s
    · have hpred : ∀ b : ℕ, ((a + sk = s ∧ b + tk = t) = (b = t - tk)) :=
        fun b => propext (by omega)
      simp only [if_pos ha, hpred]
      rw [Finset.sum_ite_eq']
    · simp only [if_neg ha]
      apply Finset.sum_eq_zero
      intro b _
      rw [if_neg]
      exact fun hcon => ha hcon.1
  rw [hlin]
  simp only [hpiece]
  rw [Finset.sum_congr rfl (fun a _ => hinner a)]
  simp only [hA]
  rw [Finset.sum_ite_eq']
  -- goal: (if A ∈ Ra then (if B2 ∈ Rb then X A B2 else 0) else 0) = BComp_{A,B2}(c)·Gk
  by_cases hAmem : (s - sk) ∈ Finset.range (c.totalDegree + 1)
  · rw [if_pos hAmem]
    by_cases hBmem : (t - tk) ∈ Finset.range (c.totalDegree + 1)
    · rw [if_pos hBmem]
    · rw [if_neg hBmem]
      have hB2 : c.totalDegree < t - tk := by
        simp only [Finset.mem_range, not_lt] at hBmem
        omega
      have h0 : BComp n m o (s - sk) (t - tk) c = 0 :=
        BComp_eq_zero_of_gt_y n m o c (s - sk) (t - tk) hB2
      rw [h0, zero_mul]
  · rw [if_neg hAmem]
    have hA2 : c.totalDegree < s - sk := by
      simp only [Finset.mem_range, not_lt] at hAmem
      omega
    have h0 : BComp n m o (s - sk) (t - tk) c = 0 :=
      BComp_eq_zero_of_gt_x n m o c (s - sk) (t - tk) hA2
    rw [h0, zero_mul]

/-- The triple vanishing ideal has finitely many trihomogeneous generators. -/
theorem tripleIx_trihomog_gens {n m o : ℕ}
    (T : Set ((ProjectivePoint n × ProjectivePoint m) × ProjectivePoint o)) :
    ∃ (ι : Type) (_ : Fintype ι) (G : ι → Poly (n + m + o)) (sk tk uk : ι → ℕ),
      (∀ i, G i ∈ MvPolynomial.vanishingIdeal ℂ (tripleRepresentatives T)) ∧
      (∀ i, MvPolynomial.IsWeightedHomogeneous (xWeight n m o) (G i) (sk i)) ∧
      (∀ i, MvPolynomial.IsWeightedHomogeneous (yWeight n m o) (G i) (tk i)) ∧
      (∀ i, MvPolynomial.IsWeightedHomogeneous (zWeight n m o) (G i) (uk i)) ∧
      MvPolynomial.vanishingIdeal ℂ (tripleRepresentatives T) ≤ Ideal.span (Set.range G) := by
  classical
  obtain ⟨s, hs⟩ : ∃ s : Finset (Poly (n + m + o)),
      Submodule.span (Poly (n + m + o)) ↑s =
        MvPolynomial.vanishingIdeal ℂ (tripleRepresentatives T) :=
    IsNoetherian.noetherian _
  -- Global degree bound over the finite generating set.
  set B : ℕ := s.sup (fun g => g.totalDegree) with hBdef
  have hBle : ∀ g ∈ s, g.totalDegree ≤ B := fun g hg => Finset.le_sup hg
  refine ⟨(Σ g : ↥s, Σ a : Fin (g.1.totalDegree + 1), Σ b : Fin (g.1.totalDegree + 1),
      Fin ((BComp n m o a b g.1).totalDegree + 1)), inferInstance,
    fun i => MvPolynomial.weightedHomogeneousComponent (zWeight n m o) i.2.2.2
      (BComp n m o i.2.1 i.2.2.1 i.1.1),
    fun i => i.2.1, fun i => i.2.2.1, fun i => i.2.2.2, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have hmem : (i.1.1 : Poly (n + m + o)) ∈
        MvPolynomial.vanishingIdeal ℂ (tripleRepresentatives T) := by
      have h1 : (i.1.1 : Poly (n + m + o)) ∈
          Submodule.span (Poly (n + m + o)) (↑s : Set (Poly (n + m + o))) :=
        Submodule.subset_span (Finset.mem_coe.mpr i.1.2)
      rw [hs] at h1
      exact h1
    exact tripleIx_mem_whc_z T (BComp_mem_Ix T hmem _ _) _
  · intro i
    exact whc_preserves_homog _ _ _ _ _
      (whc_preserves_homog _ _ _ _ _
        (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous _ _))
  · intro i
    exact whc_preserves_homog _ _ _ _ _
      (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous _ _)
  · intro i
    exact MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous _ _
  · -- Spanning: each generator is a sum of its (zero-padded) components.
    have hgen : ∀ g : ↥s, (g.1 : Poly (n + m + o)) ∈
        Ideal.span (Set.range (fun i : (Σ g : ↥s, Σ a : Fin (g.1.totalDegree + 1),
            Σ b : Fin (g.1.totalDegree + 1),
            Fin ((BComp n m o a b g.1).totalDegree + 1)) =>
          MvPolynomial.weightedHomogeneousComponent (zWeight n m o) i.2.2.2
            (BComp n m o i.2.1 i.2.2.1 i.1.1))) := by
      intro g
      -- Per-(a,b) third-block decomposition as a Fin sum.
      have e2 : ∀ a b : ℕ, BComp n m o a b g.1 =
          ∑ d : Fin ((BComp n m o a b g.1).totalDegree + 1),
            MvPolynomial.weightedHomogeneousComponent (zWeight n m o) d
              (BComp n m o a b g.1) := by
        intro a b
        have hz := zComp_sum n m o (BComp n m o a b g.1)
        nth_rewrite 1 [hz]
        simp only [← Fin.sum_univ_eq_sum_range]
      have hdecomp : (g.1 : Poly (n + m + o)) =
          ∑ a : Fin (g.1.totalDegree + 1), ∑ b : Fin (g.1.totalDegree + 1),
          ∑ d : Fin ((BComp n m o a b g.1).totalDegree + 1),
            MvPolynomial.weightedHomogeneousComponent (zWeight n m o) d
              (BComp n m o a b g.1) := by
        have hbd := bidegComp_sum n m o g.1
        nth_rewrite 1 [hbd]
        simp only [← Fin.sum_univ_eq_sum_range]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        exact e2 a b
      nth_rewrite 1 [hdecomp]
      apply Ideal.sum_mem
      intro a _
      apply Ideal.sum_mem
      intro b _
      apply Ideal.sum_mem
      intro d _
      apply Ideal.subset_span
      exact ⟨⟨g, a, b, d⟩, rfl⟩
    rw [← hs]
    apply Submodule.span_le.mpr
    intro g hg
    obtain ⟨g', rfl⟩ : ∃ g' : ↥s, ((g'.1 : Poly (n + m + o)) = g) :=
      ⟨⟨g, Finset.mem_coe.mp hg⟩, rfl⟩
    exact hgen g'

/-! ### The N-generator family and its spanning property -/

/-! ### Block weights as block sums -/

/-- The x-weight is 1 on x-block indices. -/
theorem xWeight_castAdd (n m o : ℕ) (j : Fin n) :
    xWeight n m o (Fin.castAdd o (Fin.castAdd m j)) = 1 := by
  simp [xWeight, Fin.addCases_left]

/-- The x-weight of an exponent is its x-block sum. -/
theorem xWeight_eq_sum (n m o : ℕ) (d : Fin (n + m + o) →₀ ℕ) :
    Finsupp.weight (xWeight n m o) d
      = ∑ i : Fin n, d (Fin.castAdd o (Fin.castAdd m i)) := by
  rw [weight_eq_sum]
  have him : ∀ j : Fin n, xWeight n m o (Fin.castAdd o (Fin.castAdd m j)) *
      d (Fin.castAdd o (Fin.castAdd m j)) = d (Fin.castAdd o (Fin.castAdd m j)) := by
    intro j
    rw [xWeight_castAdd]
    exact one_mul _
  have hinj : Function.Injective
      (fun j : Fin n => Fin.castAdd o (Fin.castAdd m j)) := by
    intro a b hab
    have h2 : a.val = b.val := by
      have h3 := congrArg Fin.val hab
      simpa [Fin.coe_castAdd] using h3
    exact Fin.ext h2
  calc ∑ i, xWeight n m o i * d i
      = ∑ i ∈ Finset.univ.image (fun j : Fin n => Fin.castAdd o (Fin.castAdd m j)),
        xWeight n m o i * d i := by
        apply Eq.symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro i _ hi
        have hw0 : xWeight n m o i = 0 := by
          rcases triple_index_trichotomy i with ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨l, rfl⟩
          · exact absurd (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩) hi
          · simp [xWeight, Fin.addCases_left, Fin.addCases_right]
          · simp [xWeight, Fin.addCases_right]
        rw [hw0, zero_mul]
    _ = ∑ j : Fin n, d (Fin.castAdd o (Fin.castAdd m j)) := by
        rw [Finset.sum_image hinj.injOn]
        exact Finset.sum_congr rfl (fun j _ => him j)

/-- The y-weight is 1 on y-block indices. -/
theorem yWeight_castAdd (n m o : ℕ) (j : Fin m) :
    yWeight n m o (Fin.castAdd o (Fin.natAdd n j)) = 1 := by
  simp [yWeight, Fin.addCases_left, Fin.addCases_right]

/-- The y-weight of an exponent is its y-block sum. -/
theorem yWeight_eq_sum (n m o : ℕ) (d : Fin (n + m + o) →₀ ℕ) :
    Finsupp.weight (yWeight n m o) d
      = ∑ i : Fin m, d (Fin.castAdd o (Fin.natAdd n i)) := by
  rw [weight_eq_sum]
  have him : ∀ j : Fin m, yWeight n m o (Fin.castAdd o (Fin.natAdd n j)) *
      d (Fin.castAdd o (Fin.natAdd n j)) = d (Fin.castAdd o (Fin.natAdd n j)) := by
    intro j
    rw [yWeight_castAdd]
    exact one_mul _
  have hinj : Function.Injective
      (fun j : Fin m => Fin.castAdd o (Fin.natAdd n j)) := by
    intro a b hab
    have h2 : a.val = b.val := by
      have h3 := congrArg Fin.val hab
      simpa [Fin.coe_castAdd, Fin.coe_natAdd] using h3
    exact Fin.ext h2
  calc ∑ i, yWeight n m o i * d i
      = ∑ i ∈ Finset.univ.image (fun j : Fin m => Fin.castAdd o (Fin.natAdd n j)),
        yWeight n m o i * d i := by
        apply Eq.symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro i _ hi
        have hw0 : yWeight n m o i = 0 := by
          rcases triple_index_trichotomy i with ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨l, rfl⟩
          · simp [yWeight, Fin.addCases_left]
          · exact absurd (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩) hi
          · simp [yWeight, Fin.addCases_right]
        rw [hw0, zero_mul]
    _ = ∑ j : Fin m, d (Fin.castAdd o (Fin.natAdd n j)) := by
        rw [Finset.sum_image hinj.injOn]
        exact Finset.sum_congr rfl (fun j _ => him j)

/-- Specializing the bidegree part of a monomial extracts its bidegree coefficients. -/
theorem fibreSpecialize_BComp_monomial {n m o s t : ℕ} (z : Point o)
    (D : Fin (n + m + (o + 1)) →₀ ℕ) (e : ℂ) :
    fibreSpecialize (q := n + m) (o := o) z
      (BComp n m (o + 1) s t (MvPolynomial.monomial D e))
      = ∑ β : bidegIndex n m s t, MvPolynomial.monomial β.1
        ((fibreSpecialize (q := n + m) (o := o) z (MvPolynomial.monomial D e)).coeff β.1) := by
  classical
  have hHx : MvPolynomial.IsWeightedHomogeneous (xWeight n m (o + 1))
      (MvPolynomial.monomial D e) (Finsupp.weight (xWeight n m (o + 1)) D) :=
    MvPolynomial.isWeightedHomogeneous_monomial _ _ _ rfl
  have hHy : MvPolynomial.IsWeightedHomogeneous (yWeight n m (o + 1))
      (MvPolynomial.monomial D e) (Finsupp.weight (yWeight n m (o + 1)) D) :=
    MvPolynomial.isWeightedHomogeneous_monomial _ _ _ rfl
  have hfib1 : fibreSpecialize z (MvPolynomial.monomial D e)
      = MvPolynomial.monomial (xyPart n m (o + 1) D)
        (e * (zPart n m (o + 1) D).prod
          (fun a e' => ((Fin.cons (1 : ℂ) z : Fin (o + 1) → ℂ)) a ^ e')) := by
    rw [fibreSpecialize_monomial z D e, MvPolynomial.eval_monomial, one_mul]
  by_cases hs : s = Finsupp.weight (xWeight n m (o + 1)) D
  · by_cases ht : t = Finsupp.weight (yWeight n m (o + 1)) D
    · -- BComp is the identity; the coefficient sum has a single term.
      have hB : BComp n m (o + 1) s t (MvPolynomial.monomial D e)
          = MvPolynomial.monomial D e := by
        rw [hs, ht]
        exact BComp_eq_self_of_bideg _ hHx hHy
      have hmem : xyPart n m (o + 1) D ∈ {d : Fin (n + m) →₀ ℕ |
          (∑ i : Fin n, d (Fin.castAdd m i)) = s ∧
          (∑ i : Fin m, d (Fin.natAdd n i)) = t} := by
        have t1 := (bideg_sums_xyPart (n := n) (m := m) (o := o + 1) D).1
        have t2 := (bideg_sums_xyPart (n := n) (m := m) (o := o + 1) D).2
        refine ⟨?_, ?_⟩
        · rw [← t1, ← xWeight_eq_sum]; exact hs.symm
        · rw [← t2, ← yWeight_eq_sum]; exact ht.symm
      rw [hB, hfib1]
      have hcoeff : ∀ β : bidegIndex n m s t,
          (MvPolynomial.monomial (xyPart n m (o + 1) D)
            (e * (zPart n m (o + 1) D).prod
              (fun a e' => ((Fin.cons (1 : ℂ) z : Fin (o + 1) → ℂ)) a ^ e'))).coeff β.1
          = if xyPart n m (o + 1) D = β.1 then
            e * (zPart n m (o + 1) D).prod
              (fun a e' => ((Fin.cons (1 : ℂ) z : Fin (o + 1) → ℂ)) a ^ e') else 0 := by
        intro β
        rw [MvPolynomial.coeff_monomial]
      simp only [hcoeff]
      rw [Finset.sum_eq_single (⟨xyPart n m (o + 1) D, hmem⟩ : bidegIndex n m s t)]
      · have hif : xyPart n m (o + 1) D
            = (⟨xyPart n m (o + 1) D, hmem⟩ : bidegIndex n m s t).1 := rfl
        rw [if_pos hif]
      · intro β _ hne
        have hcon : ¬ (xyPart n m (o + 1) D = β.1) := by
          intro h
          exact hne (Subtype.ext h).symm
        rw [if_neg hcon, MvPolynomial.monomial_zero]
      · intro hcon
        exact absurd (Finset.mem_univ _) hcon
    · -- BComp vanishes; every coefficient vanishes.
      have hB : BComp n m (o + 1) s t (MvPolynomial.monomial D e) = 0 := by
        apply BComp_eq_zero_of_bideg_ne _ hHx hHy
        right
        exact ht
      rw [hB, map_zero, hfib1]
      symm
      apply Finset.sum_eq_zero
      intro β _
      have hcon : ¬ (xyPart n m (o + 1) D = β.1) := by
        intro h
        have e1 : s = Finsupp.weight (xWeight n m (o + 1)) D := hs
        have e2 : t = Finsupp.weight (yWeight n m (o + 1)) D := by
          have t2 := (bideg_sums_xyPart (n := n) (m := m) (o := o + 1) D).2
          have hβ : (∑ i : Fin m, β.1 (Fin.natAdd n i)) = t := β.2.2
          rw [← h] at hβ
          rw [← t2, ← yWeight_eq_sum] at hβ
          exact hβ.symm
        exact ht e2
      rw [MvPolynomial.coeff_monomial, if_neg hcon, MvPolynomial.monomial_zero]
  · -- BComp vanishes; every coefficient vanishes.
    have hB : BComp n m (o + 1) s t (MvPolynomial.monomial D e) = 0 := by
      apply BComp_eq_zero_of_bideg_ne _ hHx hHy
      left
      exact hs
    rw [hB, map_zero, hfib1]
    symm
    apply Finset.sum_eq_zero
    intro β _
    have hcon : ¬ (xyPart n m (o + 1) D = β.1) := by
      intro h
      have e1 : s = Finsupp.weight (xWeight n m (o + 1)) D := by
        have t1 := (bideg_sums_xyPart (n := n) (m := m) (o := o + 1) D).1
        have hβ : (∑ i : Fin n, β.1 (Fin.castAdd m i)) = s := β.2.1
        rw [← h] at hβ
        rw [← t1, ← xWeight_eq_sum] at hβ
        exact hβ.symm
      exact hs e1
    rw [MvPolynomial.coeff_monomial, if_neg hcon, MvPolynomial.monomial_zero]

/-- Bidegree extraction is the identity on the bidegree piece. -/
theorem BComp_eq_self_of_mem_piece (n m o s t : ℕ) (F : Poly (n + m + o))
    (hF : F ∈ bidegPiece n m o s t) : BComp n m o s t F = F := by
  have hsupp : ↑F.support ⊆ {D : Fin (n + m + o) →₀ ℕ |
      (∑ i : Fin n, D (Fin.castAdd o (Fin.castAdd m i))) = s ∧
      (∑ i : Fin m, D (Fin.castAdd o (Fin.natAdd n i))) = t} := by
    have := (MvPolynomial.mem_restrictSupport_iff ℂ).mp hF
    simpa [bidegPiece] using this
  have hx : MvPolynomial.weightedHomogeneousComponent (xWeight n m o) s F = F := by
    apply MvPolynomial.ext
    intro d
    rw [MvPolynomial.coeff_weightedHomogeneousComponent]
    by_cases hwm : Finsupp.weight (xWeight n m o) d = s
    · rw [if_pos hwm]
    · rw [if_neg hwm]
      have h0 : F.coeff d = 0 := by
        by_contra hcon
        have hsupp'd : d ∈ F.support := MvPolynomial.mem_support_iff.mpr hcon
        have hMs := hsupp (Finset.mem_coe.mpr hsupp'd)
        have e : Finsupp.weight (xWeight n m o) d = s := by
          rw [xWeight_eq_sum]
          exact hMs.1
        exact hwm e
      exact h0.symm
  have hy : MvPolynomial.weightedHomogeneousComponent (yWeight n m o) t F = F := by
    apply MvPolynomial.ext
    intro d
    rw [MvPolynomial.coeff_weightedHomogeneousComponent]
    by_cases hwm : Finsupp.weight (yWeight n m o) d = t
    · rw [if_pos hwm]
    · rw [if_neg hwm]
      have h0 : F.coeff d = 0 := by
        by_contra hcon
        have hsupp'd : d ∈ F.support := MvPolynomial.mem_support_iff.mpr hcon
        have hMs := hsupp (Finset.mem_coe.mpr hsupp'd)
        have e : Finsupp.weight (yWeight n m o) d = t := by
          rw [yWeight_eq_sum]
          exact hMs.2
        exact hwm e
      exact h0.symm
  show MvPolynomial.weightedHomogeneousComponent (yWeight n m o) t
    (MvPolynomial.weightedHomogeneousComponent (xWeight n m o) s F) = F
  rw [hx]
  exact hy

/-- Elements with given bidegree lie in the bidegree piece. -/
theorem mem_bidegPiece_of_homog (n m o s t : ℕ) (H : Poly (n + m + o))
    (hA : MvPolynomial.IsWeightedHomogeneous (xWeight n m o) H s)
    (hB : MvPolynomial.IsWeightedHomogeneous (yWeight n m o) H t) :
    H ∈ bidegPiece n m o s t := by
  have hset : bidegPiece n m o s t = MvPolynomial.restrictSupport ℂ {D : Fin (n + m + o) →₀ ℕ |
      (∑ i : Fin n, D (Fin.castAdd o (Fin.castAdd m i))) = s ∧
      (∑ i : Fin m, D (Fin.castAdd o (Fin.natAdd n i))) = t} := rfl
  rw [hset, MvPolynomial.mem_restrictSupport_iff]
  intro D hD
  rw [Finset.mem_coe] at hD
  constructor
  · rw [← xWeight_eq_sum]
    exact hA (MvPolynomial.mem_support_iff.mp hD)
  · rw [← yWeight_eq_sum]
    exact hB (MvPolynomial.mem_support_iff.mp hD)

/-- N-generator index: trihomog-generator × complementary bidegree monomial. -/
abbrev NGenIdx (n m s t : ℕ) (ι : Type) (sk tk : ι → ℕ) : Type :=
  Σ k : ι, bidegIndex n m (s - sk k) (t - tk k)

instance NGenIdxFintype (n m s t : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (sk tk : ι → ℕ) : Fintype (NGenIdx n m s t ι sk tk) := inferInstance

/-- N-generator element (zero outside range). -/
def NGenElem (n m o s t : ℕ) {ι : Type} (G : ι → Poly (n + m + o)) (sk tk : ι → ℕ)
    (k : ι) (α : bidegIndex n m (s - sk k) (t - tk k)) : Poly (n + m + o) :=
  if _ : sk k ≤ s ∧ tk k ≤ t then
    bidegMonomial n m o (s - sk k) (t - tk k) α * G k
  else 0

/-- Embedded bidegree monomials have the expected block sums. -/
theorem embDomain_bideg_sums (n m o s t : ℕ) (α : bidegIndex n m s t) :
    (∑ i : Fin n, (Finsupp.embDomain (embXY n m o) α.1) (Fin.castAdd o (Fin.castAdd m i))) = s ∧
    (∑ i : Fin m, (Finsupp.embDomain (embXY n m o) α.1) (Fin.castAdd o (Fin.natAdd n i))) = t := by
  constructor
  · have e : ∀ i : Fin n, (Finsupp.embDomain (embXY n m o) α.1)
        (Fin.castAdd o (Fin.castAdd m i)) = α.1 (Fin.castAdd m i) := by
      intro i
      have h := embDomain_at (embXY n m o) α.1 (Fin.castAdd m i)
      exact h
    simp only [e]
    exact α.2.1
  · have e : ∀ i : Fin m, (Finsupp.embDomain (embXY n m o) α.1)
        (Fin.castAdd o (Fin.natAdd n i)) = α.1 (Fin.natAdd n i) := by
      intro i
      have h := embDomain_at (embXY n m o) α.1 (Fin.natAdd n i)
      exact h
    simp only [e]
    exact α.2.2

/-- N-generators lie in the bidegree piece and the triple ideal. -/
theorem NGenElem_mem (n m o s t : ℕ) {ι : Type}
    (T : Set ((ProjectivePoint n × ProjectivePoint m) × ProjectivePoint o))
    (G : ι → Poly (n + m + o)) (sk tk : ι → ℕ)
    (hG : ∀ k, G k ∈ MvPolynomial.vanishingIdeal ℂ (tripleRepresentatives T))
    (hx : ∀ k, MvPolynomial.IsWeightedHomogeneous (xWeight n m o) (G k) (sk k))
    (hy : ∀ k, MvPolynomial.IsWeightedHomogeneous (yWeight n m o) (G k) (tk k))
    (k : ι) (α : bidegIndex n m (s - sk k) (t - tk k)) :
    NGenElem n m o s t G sk tk k α ∈ bidegPiece n m o s t ∧
    NGenElem n m o s t G sk tk k α ∈ MvPolynomial.vanishingIdeal ℂ (tripleRepresentatives T) := by
  unfold NGenElem
  by_cases h : sk k ≤ s ∧ tk k ≤ t
  · simp only [dif_pos h]
    obtain ⟨hsk, htk⟩ := h
    have hA : MvPolynomial.IsWeightedHomogeneous (xWeight n m o)
        (bidegMonomial n m o (s - sk k) (t - tk k) α * G k) s := by
      have he : MvPolynomial.IsWeightedHomogeneous (xWeight n m o)
          (bidegMonomial n m o (s - sk k) (t - tk k) α) (s - sk k) := by
        have hw : Finsupp.weight (xWeight n m o)
            (Finsupp.embDomain (embXY n m o) α.1) = s - sk k := by
          have hsums := embDomain_bideg_sums n m o (s - sk k) (t - tk k) α
          rw [xWeight_eq_sum]
          exact hsums.1
        have := MvPolynomial.isWeightedHomogeneous_monomial (xWeight n m o)
          (Finsupp.embDomain (embXY n m o) α.1) (1 : ℂ) hw
        simpa [bidegMonomial] using this
      have hmul := he.mul (hx k)
      rwa [Nat.sub_add_cancel hsk] at hmul
    have hB : MvPolynomial.IsWeightedHomogeneous (yWeight n m o)
        (bidegMonomial n m o (s - sk k) (t - tk k) α * G k) t := by
      have he : MvPolynomial.IsWeightedHomogeneous (yWeight n m o)
          (bidegMonomial n m o (s - sk k) (t - tk k) α) (t - tk k) := by
        have hw : Finsupp.weight (yWeight n m o)
            (Finsupp.embDomain (embXY n m o) α.1) = t - tk k := by
          have hsums := embDomain_bideg_sums n m o (s - sk k) (t - tk k) α
          rw [yWeight_eq_sum]
          exact hsums.2
        have := MvPolynomial.isWeightedHomogeneous_monomial (yWeight n m o)
          (Finsupp.embDomain (embXY n m o) α.1) (1 : ℂ) hw
        simpa [bidegMonomial] using this
      have hmul := he.mul (hy k)
      rwa [Nat.sub_add_cancel htk] at hmul
    exact ⟨mem_bidegPiece_of_homog _ _ _ _ _ _ hA hB,
      Ideal.mul_mem_left _ _ (hG k)⟩
  · simp only [dif_neg h]
    exact ⟨Submodule.zero_mem _, Ideal.zero_mem _⟩

/-- Specializing an N-generator gives the explicit fibre relation with evaluated
third-block coefficients. -/
theorem fibreSpecialize_NGenElem {n m o s t : ℕ} {ι : Type} (z : Point o)
    (T : Set ((ProjectivePoint n × ProjectivePoint m) × ProjectivePoint (o + 1)))
    (G : ι → Poly (n + m + (o + 1))) (sk tk : ι → ℕ)
    (hG : ∀ k, G k ∈ MvPolynomial.vanishingIdeal ℂ (tripleRepresentatives T))
    (hx : ∀ k, MvPolynomial.IsWeightedHomogeneous (xWeight n m (o + 1)) (G k) (sk k))
    (hy : ∀ k, MvPolynomial.IsWeightedHomogeneous (yWeight n m (o + 1)) (G k) (tk k))
    (l : NGenIdx n m s t ι sk tk) :
    fibreSpecialize (q := n + m) (o := o) z
      (NGenElem n m (o + 1) s t G sk tk l.1 l.2)
      = ∑ β : bidegIndex n m s t, MvPolynomial.monomial β.1
        (MvPolynomial.eval (Fin.cons (1 : ℂ) z)
          (bidegCoeff n m (o + 1) s t (NGenElem n m (o + 1) s t G sk tk l.1 l.2) β)) := by
  classical
  have hpiece : NGenElem n m (o + 1) s t G sk tk l.1 l.2 ∈ bidegPiece n m (o + 1) s t :=
    (NGenElem_mem n m (o + 1) s t T G sk tk hG hx hy l.1 l.2).1
  conv_lhs => rw [coord_decomp n m (o + 1) s t _ hpiece, map_sum]
  apply Finset.sum_congr rfl
  intro β _
  rw [map_mul, fibreSpecialize_bidegMonomial z β, fibreSpecialize_zInclusion z,
    mul_comm, MvPolynomial.C_mul_monomial, mul_one]

/-- Inserting a vector outside the span preserves independence. -/
theorem linearIndependent_insert_of_not_mem_span {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → V) (S : Finset ι) (a : ι)
    (hS : LinearIndependent K (fun i : ↥S => v i)) (ha : a ∉ S)
    (hspan : v a ∉ Submodule.span K (Set.range (fun i : ↥S => v i))) :
    LinearIndependent K (fun i : ↥(insert a S) => v i) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  set i₀ : ↥(insert a S) := ⟨a, Finset.mem_insert_self a S⟩ with hi0def
  have hsplit : (∑ i, g i • v (i.1 : ι))
      = g i₀ • v a + ∑ i ∈ Finset.univ.erase i₀, g i • v (i.1 : ι) :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ i₀)).symm
  rw [hsplit] at hg
  -- reindex the remainder onto S
  have hreidx : (∑ i ∈ Finset.univ.erase i₀, g i • v (i.1 : ι))
      = ∑ j : ↥S, g ⟨j.1, Finset.mem_insert_of_mem j.2⟩ • v j.1 := by
    apply Finset.sum_bij (fun i hi => (⟨i.1, by
      have h1 : (i.1 : ι) ∈ insert a S := i.2
      have h2 : (i.1 : ι) ≠ a := by
        intro hcon
        have h3 : i = i₀ := Subtype.ext hcon
        exact (Finset.mem_erase.mp hi).1 h3
      exact Finset.mem_of_mem_insert_of_ne h1 h2⟩ : ↥S))
    · intro i hi
      exact Finset.mem_univ _
    · intro i hi j hj hij
      have h12 : (i.1 : ι) = (j.1 : ι) := congrArg (Subtype.val : ↥S → ι) hij
      exact Subtype.ext h12
    · intro j _
      refine ⟨⟨j.1, Finset.mem_insert_of_mem j.2⟩, ?_, ?_⟩
      · rw [Finset.mem_erase]
        refine ⟨?_, Finset.mem_univ _⟩
        intro hcon
        have hcon' : (j.1 : ι) = a := congrArg Subtype.val hcon
        exact ha (hcon' ▸ j.2)
      · apply Subtype.ext
        rfl
    · intro i hi
      rfl
  -- each remainder term lies in the span
  have hterm : ∀ i ∈ Finset.univ.erase i₀, g i • v (i.1 : ι) ∈
      Submodule.span K (Set.range (fun i : ↥S => v i)) := by
    intro i hi
    have hiS : (i.1 : ι) ∈ S := by
      have h1 : (i.1 : ι) ∈ insert a S := i.2
      have h2 : (i.1 : ι) ≠ a := by
        intro hcon
        have h3 : i = i₀ := Subtype.ext hcon
        exact (Finset.mem_erase.mp hi).1 h3
      exact Finset.mem_of_mem_insert_of_ne h1 h2
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨⟨i.1, hiS⟩, rfl⟩
  have hrest : (∑ i ∈ Finset.univ.erase i₀, g i • v (i.1 : ι)) ∈
      Submodule.span K (Set.range (fun i : ↥S => v i)) :=
    Submodule.sum_mem _ hterm
  -- the pivot coefficient vanishes
  have hg0 : g i₀ = 0 := by
    by_contra hne
    apply hspan
    have h1 : g i₀ • v a
        = -(∑ i ∈ Finset.univ.erase i₀, g i • v (i.1 : ι)) :=
      eq_neg_of_add_eq_zero_left hg
    have h2 : v a = (g i₀)⁻¹ • (g i₀ • v a) := by
      rw [← mul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [h2, h1, smul_neg]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ hrest)
  -- the remainder vanishes; conclude by cases
  have hrest0 : (∑ i ∈ Finset.univ.erase i₀, g i • v (i.1 : ι)) = 0 := by
    rw [hg0, zero_smul, zero_add] at hg
    exact hg
  rw [hreidx] at hrest0
  have hgJ := (Fintype.linearIndependent_iff.mp hS) _ hrest0
  by_cases hi : i = i₀
  · rw [hi]; exact hg0
  · have hiS : (i.1 : ι) ∈ S := by
      have h1 : (i.1 : ι) ∈ insert a S := i.2
      have h2 : (i.1 : ι) ≠ a := by
        intro hcon
        apply hi
        apply Subtype.ext
        exact hcon
      exact Finset.mem_of_mem_insert_of_ne h1 h2
    exact hgJ ⟨i.1, hiS⟩

/-- The z-weight of an exponent is its third-block degree. -/
theorem zWeight_eq_sum (n m o : ℕ) (D : Fin (n + m + o) →₀ ℕ) :
    Finsupp.weight (zWeight n m o) D = (zPart n m o D).degree := by
  rw [weight_eq_sum, RulingMaps.degree_eq_sum_univ]
  have eimg : (∑ i ∈ Finset.univ.image (embZ n m o), D i)
      = ∑ l : Fin o, zPart n m o D l := by
    rw [Finset.sum_image (embZ n m o).injective.injOn]
    exact Finset.sum_congr rfl (fun l _ => (zPart_apply n m o D l).symm)
  calc ∑ i, zWeight n m o i * D i
      = ∑ i ∈ Finset.univ.image (embZ n m o), D i := by
        have h1 : ∀ i ∈ Finset.univ.image (embZ n m o),
            zWeight n m o i * D i = D i := by
          intro i hi
          obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hi
          have hw1 : zWeight n m o (embZ n m o l) = 1 := by
            simp [zWeight, embZ]
          rw [hw1, one_mul]
        have h0 : ∀ i ∈ (Finset.univ : Finset (Fin (n + m + o))),
            i ∉ Finset.univ.image (embZ n m o) → zWeight n m o i * D i = 0 := by
          intro i _ hi
          have hw0 : zWeight n m o i = 0 := by
            rcases triple_index_trichotomy i with ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨l, rfl⟩
            · simp [zWeight, Fin.addCases_left]
            · simp [zWeight, Fin.addCases_left]
            · exact absurd (Finset.mem_image.mpr ⟨l, Finset.mem_univ l, rfl⟩) hi
          rw [hw0, zero_mul]
        have hsub := Finset.sum_subset (Finset.subset_univ _) h0
        rw [← hsub]
        exact Finset.sum_congr rfl (fun i hi => h1 i hi)
    _ = ∑ l : Fin o, zPart n m o D l := eimg

/-- Third-block coefficients of a Z-homogeneous element are homogeneous. -/
theorem bidegCoeff_homog (n m o s t : ℕ) (F : Poly (n + m + o)) (δ : ℕ)
    (hF : MvPolynomial.IsWeightedHomogeneous (zWeight n m o) F δ)
    (α : bidegIndex n m s t) :
    (bidegCoeff n m o s t F α).IsHomogeneous δ := by
  unfold bidegCoeff
  apply MvPolynomial.IsHomogeneous.sum
  intro D hD
  have hDs : D ∈ F.support := (Finset.mem_filter.mp hD).1
  apply MvPolynomial.isHomogeneous_monomial
  have e1 : Finsupp.weight (zWeight n m o) D = δ := hF (MvPolynomial.mem_support_iff.mp hDs)
  rw [zWeight_eq_sum] at e1
  exact e1

/-- Embedded bidegree monomials are Z-homogeneous of degree zero. -/
theorem bidegMonomial_zhomog_zero (n m o s t : ℕ) (α : bidegIndex n m s t) :
    MvPolynomial.IsWeightedHomogeneous (zWeight n m o)
      (bidegMonomial n m o s t α) 0 := by
  intro d hd
  -- support is the singleton x,y-monomial, whose z-weight is 0
  have hsupp : d = Finsupp.embDomain (embXY n m o) α.1 := by
    by_contra hcon
    have h0 : (bidegMonomial n m o s t α).coeff d = 0 := by
      simp only [bidegMonomial]
      rw [MvPolynomial.coeff_monomial, if_neg (Ne.symm hcon)]
    exact hd h0
  subst hsupp
  -- z-weight of an x,y-monomial is 0
  have hz : ∀ i : Fin (n + m + o), zWeight n m o i *
      (Finsupp.embDomain (embXY n m o) α.1) i = 0 := by
    intro i
    by_cases hi : ∃ j : Fin (n + m), embXY n m o j = i
    · obtain ⟨j, rfl⟩ := hi
      have hzw : zWeight n m o (Fin.castAdd o j) = 0 := by
        simp [zWeight, Fin.addCases_left]
      have heq : (embXY n m o j) = Fin.castAdd o j := rfl
      rw [heq, hzw, zero_mul]
    · have : (Finsupp.embDomain (embXY n m o) α.1) i = 0 := by
        apply embDomain_notin
        intro a ha
        exact hi ⟨a, ha⟩
      rw [this, mul_zero]
  calc Finsupp.weight (zWeight n m o) (Finsupp.embDomain (embXY n m o) α.1)
      = ∑ i, zWeight n m o i * (Finsupp.embDomain (embXY n m o) α.1) i := weight_eq_sum _ _
    _ = 0 := Finset.sum_eq_zero (fun i _ => hz i)

/-! ### Generic rank: independent columns have a nonzero minor -/

/-- Elimination step: independent columns over a field have a nonzero maximal minor.
Induction on the number of columns; Schur-complement the first column. -/
theorem exists_ne_zero_minor_of_linearIndependent {K : Type*} [Field K]
    {ρ : ℕ} {S : Type*} [Fintype S] [DecidableEq S]
    (B : Matrix S (Fin ρ) K)
    (h : LinearIndependent K (fun j : Fin ρ => fun i : S => B i j)) :
    ∃ e : Fin ρ ↪ S, Matrix.det (B.submatrix (⇑e) id) ≠ 0 := by
  revert S B h
  induction ρ with
  | zero =>
    intro S _ _ B _
    refine ⟨⟨Fin.elim0, fun a => Fin.elim0 a⟩, ?_⟩
    rw [Matrix.det_fin_zero]
    exact one_ne_zero
  | succ ρ ih =>
    intro S _ _ B h
    -- First column is nonzero: pick a pivot row.
    have h0 : (fun i : S => B i 0) ≠ 0 := h.ne_zero 0
    obtain ⟨r, hr⟩ : ∃ r, B r 0 ≠ 0 := by
      by_contra hc
      rw [not_exists] at hc
      apply h0
      funext i
      exact not_not.mp (hc i)
    -- Schur complement on the remaining rows.
    set t : Fin ρ → K := fun j => B r (Fin.succ j) / B r 0 with htdef
    set B' : Matrix { s : S // s ≠ r } (Fin ρ) K :=
      fun s j => B ↑s (Fin.succ j) - B ↑s 0 * t j with hB'def
    have hB' : LinearIndependent K (fun j : Fin ρ => fun s : { s : S // s ≠ r } => B' s j) := by
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      -- Extend the relation by the pivot-row value.
      set c : Fin (ρ + 1) → K := Fin.cons (-(∑ j, g j * t j)) g with hcdef
      have hBc : ∑ k, c k • (fun i : S => B i k) = 0 := by
        have hrow : ∀ i' : S, (∑ k, c k • (fun i : S => B i k)) i'
            = c 0 • B i' 0 + ∑ j, c (Fin.succ j) • B i' (Fin.succ j) := by
          intro i'
          rw [Finset.sum_apply, Fin.sum_univ_succ]
          simp only [Pi.smul_apply]
        have hR : (∑ k, c k • (fun i : S => B i k)) r = 0 := by
          rw [hrow r]
          simp only [hcdef, Fin.cons_zero, Fin.cons_succ, smul_eq_mul]
          have hmul : (∑ j, g j * B r (Fin.succ j)) = (∑ j, g j * t j) * B r 0 := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro j _
            simp only [htdef]
            field_simp
          rw [hmul]
          ring
        have hN : ∀ i' : S, i' ≠ r →
            (∑ k, c k • (fun i : S => B i k)) i' = 0 := by
          intro i' hir
          rw [hrow i']
          simp only [hcdef, Fin.cons_zero, Fin.cons_succ, smul_eq_mul]
          have hs0 : (∑ j, g j • (fun s : { s : S // s ≠ r } => B' s j)) ⟨i', hir⟩ = 0 :=
            congrFun hg ⟨i', hir⟩
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hs0
          have hs1 : (∑ j, g j * B i' (Fin.succ j)) = (∑ j, g j * t j) * B i' 0 := by
            have hrel : (∑ j, g j * (B i' (Fin.succ j) - B i' 0 * t j)) = 0 := by
              have := hs0
              simp only [hB'def] at this
              exact this
            simp only [mul_sub, Finset.sum_sub_distrib] at hrel
            have e2 : (∑ j, g j * (B i' 0 * t j)) = (∑ j, g j * t j) * B i' 0 := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro j _
              ring
            have hsub := sub_eq_zero.mp hrel
            rwa [e2] at hsub
          rw [hs1]
          ring
        funext i'
        by_cases hir : i' = r
        · rw [hir]; exact hR
        · exact hN i' hir
      have hc0 := (Fintype.linearIndependent_iff.mp h) c hBc (Fin.succ i)
      simpa [hcdef, Fin.cons_succ] using hc0
    -- Lift the IH minor, putting the pivot row first.
    obtain ⟨e', he'⟩ := ih _ hB'
    set f : Fin ρ → S := fun j => ((e' j) : S) with hfdef
    have mk_succ : ∀ (a : Fin (ρ + 1)) (k : ℕ) (hk : k < ρ),
        a.val = k + 1 → a = Fin.succ ⟨k, hk⟩ := by
      intro a k hk h
      apply Fin.ext
      rw [Fin.val_succ]
      show a.val = k + 1
      exact h
    have einj : Function.Injective (Fin.cons r f) := by
      intro a b hab
      have hai := a.isLt
      have hbi := b.isLt
      match ha : a.val, hb : b.val with
      | 0, 0 => exact Fin.ext (by omega)
      | 0, k + 1 =>
        have a0 : a = 0 := Fin.ext ha
        have hbk : b = Fin.succ ⟨k, by omega⟩ := mk_succ b k (by omega) hb
        rw [a0, hbk, Fin.cons_zero, Fin.cons_succ] at hab
        exact absurd hab.symm (e' ⟨k, by omega⟩).2
      | k + 1, 0 =>
        have b0 : b = 0 := Fin.ext hb
        have hak : a = Fin.succ ⟨k, by omega⟩ := mk_succ a k (by omega) ha
        rw [b0, hak, Fin.cons_zero, Fin.cons_succ] at hab
        exact absurd hab (e' ⟨k, by omega⟩).2
      | k + 1, l + 1 =>
        have hak : a = Fin.succ ⟨k, by omega⟩ := mk_succ a k (by omega) ha
        have hbl : b = Fin.succ ⟨l, by omega⟩ := mk_succ b l (by omega) hb
        rw [hak, hbl, Fin.cons_succ, Fin.cons_succ] at hab
        have heq : e' ⟨k, by omega⟩ = e' ⟨l, by omega⟩ := Subtype.ext hab
        have hij : (⟨k, by omega⟩ : Fin ρ) = ⟨l, by omega⟩ := e'.injective heq
        have hkl : k = l := congrArg Fin.val hij
        exact Fin.ext (by omega)
    -- Column operations clearing the pivot row.
    set U : Matrix (Fin (ρ + 1)) (Fin (ρ + 1)) K := fun i j =>
      if j = 0 then (if i = 0 then 1 else 0)
      else (if i = j then (1 : K) else if i = 0 then -(B r j / B r 0) else 0) with hUdef
    have hU00 : U 0 0 = 1 := by
      rw [hUdef]
      show (if (0 : Fin (ρ+1)) = 0 then (if (0 : Fin (ρ+1)) = 0 then (1:K) else 0) else _) = 1
      rw [if_pos rfl, if_pos rfl]
    have hUsucc0 : ∀ i : Fin ρ, U i.succ 0 = 0 := by
      intro i
      rw [hUdef]
      show (if (0 : Fin (ρ+1)) = 0 then (if i.succ = 0 then (1:K) else 0) else _) = 0
      rw [if_pos rfl, if_neg (Fin.succ_ne_zero i)]
    have hU0succ : ∀ j : Fin ρ, U 0 j.succ = -(B r j.succ / B r 0) := by
      intro j
      rw [hUdef]
      show (if j.succ = 0 then _ else (if (0 : Fin (ρ+1)) = j.succ then (1:K)
        else if (0 : Fin (ρ+1)) = 0 then -(B r j.succ / B r 0) else 0)) = _
      rw [if_neg (Fin.succ_ne_zero j), if_neg (Ne.symm (Fin.succ_ne_zero j)), if_pos rfl]
    have hUsuccsucc : ∀ i j : Fin ρ, U i.succ j.succ
        = (if i = j then (1 : K) else 0) := by
      intro i j
      rw [hUdef]
      show (if j.succ = 0 then _ else (if i.succ = j.succ then (1:K)
        else if i.succ = 0 then _ else 0)) = _
      rw [if_neg (Fin.succ_ne_zero j)]
      by_cases hij : i = j
      · rw [if_pos (by rw [hij])]
        simp only [if_pos hij]
      · rw [if_neg (fun hcon => hij (Fin.succ_inj.mp hcon))]
        rw [if_neg (Fin.succ_ne_zero i), if_neg hij]
    -- First-row entries of the product.
    have hsub00 : (B.submatrix (⇑(⟨Fin.cons r f, einj⟩ : Fin (ρ + 1) ↪ S)) id) 0 0 = B r 0 := by
      simp [Matrix.submatrix_apply, Fin.cons_zero]
    have hsubrow : ∀ j : Fin (ρ + 1),
        (B.submatrix (⇑(⟨Fin.cons r f, einj⟩ : Fin (ρ + 1) ↪ S)) id) 0 j = B r j := by
      intro j
      simp [Matrix.submatrix_apply, Fin.cons_zero]
    have hCU00 : ((B.submatrix (⇑(⟨Fin.cons r f, einj⟩ : Fin (ρ + 1) ↪ S)) id * U) 0 0) = B r 0 := by
      rw [Matrix.mul_apply]
      have hcol : ∀ k : Fin (ρ + 1),
          (B.submatrix (⇑(⟨Fin.cons r f, einj⟩ : Fin (ρ + 1) ↪ S)) id) 0 k * U k 0
            = (if k = 0 then (B.submatrix (⇑(⟨Fin.cons r f, einj⟩ : Fin (ρ + 1) ↪ S)) id) 0 k else 0) := by
        intro k
        by_cases hk : k = 0
        · rw [if_pos hk]
          have hUk : U k 0 = 1 := by rw [hk]; exact hU00
          rw [hUk, mul_one]
        · rw [if_neg hk]
          have hUk : U k 0 = 0 := by
            obtain ⟨k', hk'⟩ : ∃ k' : Fin ρ, k = k'.succ :=
              ⟨k.pred hk, (Fin.succ_pred k hk).symm⟩
            rw [hk', hUsucc0]
          rw [hUk, mul_zero]
      simp only [hcol]
      rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ 0), hsub00]
    -- Cleared first row off the pivot column.
    have hCUsucc : ∀ j : Fin ρ,
        ((B.submatrix (⇑(⟨Fin.cons r f, einj⟩ : Fin (ρ + 1) ↪ S)) id * U) 0 j.succ) = 0 := by
      intro j
      rw [Matrix.mul_apply, Fin.sum_univ_succ]
      have hrest : (∑ k : Fin ρ,
          (B.submatrix (⇑(⟨Fin.cons r f, einj⟩ : Fin (ρ + 1) ↪ S)) id) 0 k.succ
            * U k.succ j.succ)
          = (B.submatrix (⇑(⟨Fin.cons r f, einj⟩ : Fin (ρ + 1) ↪ S)) id) 0 j.succ := by
        have hterm : ∀ k : Fin ρ,
            (B.submatrix (⇑(⟨Fin.cons r f, einj⟩ : Fin (ρ + 1) ↪ S)) id) 0 k.succ
              * U k.succ j.succ
            = (if k = j then (B.submatrix (⇑(⟨Fin.cons r f, einj⟩ : Fin (ρ + 1) ↪ S)) id) 0 k.succ else 0) := by
          intro k
          rw [hUsuccsucc]
          split_ifs with hkj
          · rw [hkj, mul_one]
          · rw [mul_zero]
        simp only [hterm]
        rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ j)]
      rw [hrest]
      have e0 : (B.submatrix (⇑(⟨Fin.cons r f, einj⟩ : Fin (ρ + 1) ↪ S)) id) 0 0
          * U 0 j.succ
          = -(B.submatrix (⇑(⟨Fin.cons r f, einj⟩ : Fin (ρ + 1) ↪ S)) id) 0 0
            * (B r j.succ / B r 0) := by
        rw [hU0succ]
        ring
      rw [e0]
      simp only [hsubrow]
      field_simp
      ring
    -- Off-pivot first-row entries vanish.
    have hCU_ne : ∀ b : Fin (ρ + 1), b ≠ 0 →
        ((B.submatrix (⇑(⟨Fin.cons r f, einj⟩ : Fin (ρ + 1) ↪ S)) id * U) 0 b) = 0 := by
      intro b hb
      have hbb : b = (b.pred hb).succ := (Fin.succ_pred b hb).symm
      rw [hbb]
      exact hCUsucc _
    -- Determinant of the cleared matrix is nonzero.
    have hdetCU : (B.submatrix (⇑(⟨Fin.cons r f, einj⟩ : Fin (ρ + 1) ↪ S)) id * U).det ≠ 0 := by
      have hexp := Matrix.det_succ_row (B.submatrix (⇑(⟨Fin.cons r f, einj⟩ : Fin (ρ + 1) ↪ S)) id * U) 0
      rw [hexp, ← Finset.add_sum_erase _ _ (Finset.mem_univ 0)]
      have herase : (∑ x ∈ Finset.univ.erase (0 : Fin (ρ + 1)),
          (-1 : K) ^ ((0 : Fin (ρ + 1)).val + x.val)
            * ((B.submatrix (⇑(⟨Fin.cons r f, einj⟩ : Fin (ρ + 1) ↪ S)) id * U) 0 x)
            * (((B.submatrix (⇑(⟨Fin.cons r f, einj⟩ : Fin (ρ + 1) ↪ S)) id * U).submatrix
              (0 : Fin (ρ + 1)).succAbove x.succAbove).det)) = 0 := by
        apply Finset.sum_eq_zero
        intro b hb
        have hb0 : b ≠ 0 := Finset.ne_of_mem_erase hb
        have hCUb : ((B.submatrix (⇑(⟨Fin.cons r f, einj⟩ : Fin (ρ + 1) ↪ S)) id * U) 0 b) = 0 :=
          hCU_ne b hb0
        rw [hCUb, mul_zero, zero_mul]
      rw [herase, add_zero]
      apply mul_ne_zero
      apply mul_ne_zero
      · apply pow_ne_zero
        norm_num
      · rw [hCU00]
        exact hr
      · -- The remaining minor is the IH minor.
        have hminor : ((B.submatrix (⇑(⟨Fin.cons r f, einj⟩ : Fin (ρ + 1) ↪ S)) id * U).submatrix
            (0 : Fin (ρ + 1)).succAbove (0 : Fin (ρ + 1)).succAbove).det
            = (B'.submatrix (⇑e') id).det := by
          congr 1
          funext a b
          -- entries: (CU)(succ a)(succ b) = B'(e' a) b
          have eC0 : (B.submatrix (⇑(⟨Fin.cons r f, einj⟩ : Fin (ρ + 1) ↪ S)) id) a.succ 0
              = B (e' a) 0 := by simp [Matrix.submatrix_apply, Fin.cons_succ, hfdef]
          have eCs : ∀ k : Fin ρ, (B.submatrix (⇑(⟨Fin.cons r f, einj⟩ : Fin (ρ + 1) ↪ S)) id) a.succ k.succ
              = B (e' a) k.succ := by
            intro k
            simp [Matrix.submatrix_apply, Fin.cons_succ, hfdef]
          show ((B.submatrix (⇑(⟨Fin.cons r f, einj⟩ : Fin (ρ + 1) ↪ S)) id * U) a.succ b.succ)
            = B' (e' a) b
          rw [Matrix.mul_apply, Fin.sum_univ_succ]
          have hrest : (∑ k : Fin ρ,
              (B.submatrix (⇑(⟨Fin.cons r f, einj⟩ : Fin (ρ + 1) ↪ S)) id) a.succ k.succ
                * U k.succ b.succ)
              = B (e' a) b.succ := by
            have hterm : ∀ k : Fin ρ,
                (B.submatrix (⇑(⟨Fin.cons r f, einj⟩ : Fin (ρ + 1) ↪ S)) id) a.succ k.succ
                  * U k.succ b.succ
                = (if k = b then B (e' a) k.succ else 0) := by
              intro k
              rw [hUsuccsucc, eCs k]
              split_ifs with hkj
              · rw [hkj, mul_one]
              · rw [mul_zero]
            simp only [hterm, Finset.sum_ite_eq', if_pos (Finset.mem_univ b)]
          rw [hrest]
          have e0 : (B.submatrix (⇑(⟨Fin.cons r f, einj⟩ : Fin (ρ + 1) ↪ S)) id) a.succ 0
              * U 0 b.succ
              = -((B.submatrix (⇑(⟨Fin.cons r f, einj⟩ : Fin (ρ + 1) ↪ S)) id) a.succ 0
                * (B r b.succ / B r 0)) := by
            rw [hU0succ, mul_neg]
          rw [e0, eC0]
          simp only [hB'def, htdef]
          ring
        rw [hminor]
        exact he'
    -- Conclude by multiplicativity.
    refine ⟨⟨Fin.cons r f, einj⟩, ?_⟩
    by_contra hC0
    apply hdetCU
    rw [Matrix.det_mul, hC0, zero_mul]

/-- Every element of N is an explicit C[Z]-combination of N-generators. -/
theorem NGen_spanning {n m o s t : ℕ} {ι : Type} [Fintype ι]
    (T : Set ((ProjectivePoint n × ProjectivePoint m) × ProjectivePoint o))
    (G : ι → Poly (n + m + o)) (sk tk : ι → ℕ)
    (hG : ∀ k, G k ∈ MvPolynomial.vanishingIdeal ℂ (tripleRepresentatives T))
    (hx : ∀ k, MvPolynomial.IsWeightedHomogeneous (xWeight n m o) (G k) (sk k))
    (hy : ∀ k, MvPolynomial.IsWeightedHomogeneous (yWeight n m o) (G k) (tk k))
    (hspan : MvPolynomial.vanishingIdeal ℂ (tripleRepresentatives T) ≤
      Ideal.span (Set.range G))
    (F : Poly (n + m + o)) (hM : F ∈ bidegPiece n m o s t)
    (hIx : F ∈ MvPolynomial.vanishingIdeal ℂ (tripleRepresentatives T)) :
    ∃ (S : Finset (NGenIdx n m s t ι sk tk)) (q : NGenIdx n m s t ι sk tk → Poly o),
      F = ∑ l ∈ S, zInclusion n m o (q l) * NGenElem n m o s t G sk tk l.1 l.2 := by
  classical
  haveI := Classical.decEq ι
  haveI := Classical.decEq (NGenIdx n m s t ι sk tk)
  -- Combination over the trihomogeneous generators.
  have hC : F ∈ Submodule.span (Poly (n + m + o)) (Set.range G) := hspan hIx
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hC
  obtain ⟨c, hc⟩ := hC
  -- Take bidegree parts: F equals the sum of its (s,t)-pieces.
  have hcomb : F = ∑ k ∈ c.support, BComp n m o s t ((c k) • G k) := by
    have e1 : F = BComp n m o s t F := (BComp_eq_self_of_mem_piece n m o s t F hM).symm
    have e2 : F = c.sum (fun k a => a • G k) := hc.symm
    rw [e1, e2]
    show BComp n m o s t (∑ k ∈ c.support, (c k) • G k) = _
    exact BComp_map_sum _ _ _ _
  -- Each piece is a combination of N-generators (or zero).
  have hpiece : ∀ k ∈ c.support, BComp n m o s t ((c k) • G k)
      = ∑ α : bidegIndex n m (s - sk k) (t - tk k),
        zInclusion n m o (if h : sk k ≤ s ∧ tk k ≤ t then
            bidegCoeff n m o (s - sk k) (t - tk k) (BComp n m o (s - sk k) (t - tk k) (c k)) α
          else 0)
          * NGenElem n m o s t G sk tk k α := by
    intro k _
    by_cases h : sk k ≤ s ∧ tk k ≤ t
    · obtain ⟨hsk, htk⟩ := h
      have hle : sk k ≤ s ∧ tk k ≤ t := ⟨hsk, htk⟩
      have hprod : BComp n m o s t ((c k) • G k)
          = (BComp n m o (s - sk k) (t - tk k) (c k)) * G k := by
        rw [smul_eq_mul]
        exact BComp_product_eq _ _ _ _ (hx k) (hy k) hsk htk
      have hmemB : BComp n m o (s - sk k) (t - tk k) (c k) ∈
          bidegPiece n m o (s - sk k) (t - tk k) := by
        apply mem_bidegPiece_of_homog
        · exact whc_preserves_homog _ _ _ _ _
            (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous _ _)
        · exact MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous _ _
      have hcd := coord_decomp n m o (s - sk k) (t - tk k) _ hmemB
      rw [hprod]
      conv_lhs => rw [hcd]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro α _
      have hgen : NGenElem n m o s t G sk tk k α
          = bidegMonomial n m o (s - sk k) (t - tk k) α * G k := by
        simp only [NGenElem, dif_pos hle]
      have hq : (if h : sk k ≤ s ∧ tk k ≤ t then
          bidegCoeff n m o (s - sk k) (t - tk k) (BComp n m o (s - sk k) (t - tk k) (c k)) α
          else 0)
          = bidegCoeff n m o (s - sk k) (t - tk k) (BComp n m o (s - sk k) (t - tk k) (c k)) α := by
        rw [dif_pos hle]
      rw [hq, hgen]
      ring
    · -- Out of range: every bidegree piece misses (s,t).
      have hcsum := bidegComp_sum n m o (c k)
      have e1 : (c k) * G k = ∑ a ∈ Finset.range ((c k).totalDegree + 1),
          ∑ b ∈ Finset.range ((c k).totalDegree + 1), (BComp n m o a b (c k)) * G k := by
        conv_lhs => rw [hcsum]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_mul]
      have hzero : BComp n m o s t ((c k) • G k) = 0 := by
        rw [smul_eq_mul, e1]
        simp only [BComp_map_sum]
        apply Finset.sum_eq_zero
        intro a _
        apply Finset.sum_eq_zero
        intro b _
        have hHxx : MvPolynomial.IsWeightedHomogeneous (xWeight n m o)
            (BComp n m o a b (c k)) a :=
          whc_preserves_homog _ _ _ _ _
            (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous _ _)
        have hHyy : MvPolynomial.IsWeightedHomogeneous (yWeight n m o)
            (BComp n m o a b (c k)) b :=
          MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous _ _
        have hpc : BComp n m o s t ((BComp n m o a b (c k)) * G k) = 0 := by
          have hpiece0 := BComp_product_piece (s := s) (t := t) (BComp n m o a b (c k)) (G k)
            hHxx hHyy (hx k) (hy k)
          rw [hpiece0, if_neg]
          exact fun hcon => h ⟨by omega, by omega⟩
        exact hpc
      rw [hzero]
      symm
      apply Finset.sum_eq_zero
      intro α _
      have hgen0 : NGenElem n m o s t G sk tk k α = 0 := by
        simp only [NGenElem, dif_neg h]
      rw [hgen0]
      have hq0 : (if h : sk k ≤ s ∧ tk k ≤ t then
          bidegCoeff n m o (s - sk k) (t - tk k) (BComp n m o (s - sk k) (t - tk k) (c k)) α
          else 0) = 0 := dif_neg h
      rw [hq0, map_zero, zero_mul]
  -- Assemble over the sigma index.
  refine ⟨Finset.sigma c.support (fun _ => Finset.univ), fun l =>
    (if h : sk l.1 ≤ s ∧ tk l.1 ≤ t then
      bidegCoeff n m o (s - sk l.1) (t - tk l.1)
        (BComp n m o (s - sk l.1) (t - tk l.1) (c l.1)) l.2
    else 0), ?_⟩
  rw [hcomb, Finset.sum_sigma]
  exact Finset.sum_congr rfl (fun k hk => hpiece k hk)

/-! ### Clearing denominators over the fraction field -/

/-- A vector in the span of a finite family is an explicit linear combination. -/
theorem span_relation_apply {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {ρ : ℕ} (v : Fin ρ → V) (x : V)
    (h : x ∈ Submodule.span K (Set.range v)) :
    ∃ g : Fin ρ → K, x = ∑ j, g j • v j := by
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at h
  obtain ⟨c, hc⟩ := h
  refine ⟨fun j => c j, ?_⟩
  rw [← hc]
  show c.sum (fun i a => a • v i) = ∑ j, c j • v j
  show (∑ a ∈ c.support, c a • v a) = ∑ j, c j • v j
  apply Finset.sum_subset (Finset.subset_univ _)
  intro j _ hj
  rw [Finsupp.notMem_support_iff.mp hj, zero_smul]

/-- Clearing denominators: a relation over the fraction field descends to a relation
over the domain with a single nonzero denominator. -/
theorem exists_cleared_coords {A K : Type*} [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K]
    {S : Type*} [Fintype S]
    {ρ : ℕ} (V : S → Fin ρ → A) (x : S → A)
    (g : Fin ρ → K) (hg : ∀ β, algebraMap A K (x β) = ∑ j, g j * algebraMap A K (V β j)) :
    ∃ (c : Fin ρ → A) (δ : A), δ ≠ 0 ∧
      ∀ β, δ * x β = ∑ j, c j * V β j := by
  classical
  -- Write each coefficient as a fraction.
  have hfrac : ∀ j, ∃ (num : A) (den : A), den ≠ 0 ∧
      algebraMap A K den * g j = algebraMap A K num := by
    intro j
    obtain ⟨⟨num, den⟩, h⟩ :=
      IsLocalization.mk'_surjective (nonZeroDivisors A) (g j)
    refine ⟨num, den.1, mem_nonZeroDivisors_iff_ne_zero.mp den.2, ?_⟩
    have h' : g j * algebraMap A K den.1 = algebraMap A K num :=
      IsLocalization.eq_mk'_iff_mul_eq.mp h.symm
    rw [mul_comm] at h'
    exact h'
  choose num den hden hrel using hfrac
  -- Common denominator.
  set δ : A := ∏ j, den j with hδdef
  have hδ : δ ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => hden j)
  refine ⟨fun j => num j * ∏ k ∈ Finset.univ.erase j, den k, δ, hδ, ?_⟩
  intro β
  have hinj := IsFractionRing.injective A K
  apply hinj
  rw [map_mul, map_sum]
  have hK := hg β
  -- Multiply the K-relation by δ.
  have e1 : algebraMap A K δ * algebraMap A K (x β)
      = ∑ j, (algebraMap A K δ * g j) * algebraMap A K (V β j) := by
    rw [hK, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [e1]
  apply Finset.sum_congr rfl
  intro j _
  have e2 : algebraMap A K δ * g j = algebraMap A K (num j * ∏ k ∈ Finset.univ.erase j, den k) := by
    have hsplit : δ = den j * ∏ k ∈ Finset.univ.erase j, den k := by
      rw [hδdef, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
    rw [hsplit, map_mul, map_mul]
    have hden := hrel j
    calc algebraMap A K (den j) * algebraMap A K (∏ k ∈ Finset.univ.erase j, den k) * g j
        = algebraMap A K (∏ k ∈ Finset.univ.erase j, den k) * (algebraMap A K (den j) * g j) := by ring
      _ = algebraMap A K (∏ k ∈ Finset.univ.erase j, den k) * algebraMap A K (num j) := by rw [hden]
      _ = algebraMap A K (num j) * algebraMap A K (∏ k ∈ Finset.univ.erase j, den k) := by ring
  rw [e2]
  simp only [map_mul]

/-- The determinant of a column-homogeneous matrix is homogeneous. -/
theorem isHomogeneous_det {σ : Type*} {ρ : ℕ}
    (P : Matrix (Fin ρ) (Fin ρ) (MvPolynomial σ ℂ)) (d : Fin ρ → ℕ)
    (hP : ∀ i j, (P i j).IsHomogeneous (d j)) :
    (P.det).IsHomogeneous (∑ j, d j) := by
  rw [Matrix.det_apply']
  apply MvPolynomial.IsHomogeneous.sum _ _ _
  intro s _
  have hprod : (∏ i, P (s i) i).IsHomogeneous (∑ j, d j) :=
    MvPolynomial.IsHomogeneous.prod _ _ _ (fun i _ => hP (s i) i)
  have hscalar : ((Equiv.Perm.sign s : ℤ) : MvPolynomial σ ℂ)
      = MvPolynomial.C ((Equiv.Perm.sign s : ℤ) : ℂ) :=
    (map_intCast _ _).symm
  rw [hscalar]
  exact hprod.C_mul _

/-! ### Evaluation on the base and independence from a nonzero minor -/

/-- Evaluation at `(1, z)` factors through the coordinate ring when `[1:z]` lies on `W`. -/
theorem evalQuotientMk {o : ℕ} (W : ProjectiveVariety (o + 1)) (z : Point o)
    (hzW : affineEmbedding z ∈ W.points) :
    ∃ ε : (Poly (o + 1) ⧸ W.ideal) →+* ℂ,
      ∀ F : Poly (o + 1), ε (Ideal.Quotient.mk W.ideal F)
        = MvPolynomial.eval ((Fin.cons (1 : ℂ) z : Fin (o + 1) → ℂ)) F := by
  classical
  set cz : Fin (o + 1) → ℂ := Fin.cons 1 z with hczdef
  have hv : cz ≠ 0 := by
    intro hz
    have h0 := congrFun hz 0
    simp [hczdef] at h0
  have hcone : cz ∈ W.affineCone.points := by
    have h := (ProjectiveVariety.mem_points_mk_iff W _ hv).mp hzW
    simpa [hczdef, affineEmbedding] using h
  have hc : cz ∈ MvPolynomial.zeroLocus ℂ W.ideal := hcone
  have hkill : ∀ F ∈ W.ideal, MvPolynomial.aeval cz F = 0 :=
    fun F hF => MvPolynomial.mem_zeroLocus_iff.mp hc F hF
  refine ⟨Ideal.Quotient.lift W.ideal
    (MvPolynomial.aeval cz).toRingHom (fun F hF => hkill F hF), ?_⟩
  intro F
  simp [Ideal.Quotient.lift_mk, MvPolynomial.coe_aeval_eq_eval, hczdef]

/-- A family with a nonzero minor is independent on that index set. -/
theorem linearIndependent_of_ne_zero_minor {K : Type*} [Field K]
    {S : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι] {ρ : ℕ}
    (v : ι → (S → K)) (J : Finset ι) (eJ : ↥J ≃ Fin ρ) (e : Fin ρ ↪ S)
    (hminor : Matrix.det (fun i j' : Fin ρ => v ↑(eJ.symm j') (e i)) ≠ 0) :
    LinearIndependent K (fun j : ↥J => v ↑j) := by
  classical
  set M : Matrix (Fin ρ) (Fin ρ) K :=
    fun i j' => v ↑(eJ.symm j') (e i) with hMdef
  have hminor' : M.det ≠ 0 := hminor
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hminor'
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  set g' : Fin ρ → K := fun j' => g (eJ.symm j') with hg'def
  have h0 : ∀ i, ∑ j : ↥J, g j * v ↑j (e i) = 0 := by
    intro i
    have hβ := congrFun hg (e i)
    rw [Finset.sum_apply] at hβ
    simpa [Pi.smul_apply, smul_eq_mul] using hβ
  have hM : Matrix.mulVec M g' = 0 := by
    funext i
    show (∑ j', M i j' * g' j') = 0
    simp only [hMdef, hg'def]
    have h0i := h0 i
    have e1 : (∑ j' : Fin ρ, v ↑(eJ.symm j') (e i) * g (eJ.symm j'))
        = ∑ j : ↥J, v ↑j (e i) * g j :=
      Fintype.sum_equiv eJ.symm
        (fun j' : Fin ρ => v ↑(eJ.symm j') (e i) * g (eJ.symm j'))
        (fun j : ↥J => v ↑j (e i) * g j)
        (fun _ => rfl)
    rw [e1, ← h0i]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hginv : g' = 0 := by
    calc g' = Matrix.mulVec (M⁻¹ * M) g' := by
            rw [Matrix.nonsing_inv_mul M hunit, Matrix.one_mulVec]
      _ = Matrix.mulVec M⁻¹ (Matrix.mulVec M g') :=
            (Matrix.mulVec_mulVec _ _ _).symm
      _ = 0 := by rw [hM]; simp
  have hJ : g' (eJ j) = 0 := congrFun hginv (eJ j)
  simpa [hg'def, eJ.symm_apply_apply] using hJ

/-! ### Fibre section dimension from specialized relations -/

/-- Coefficient vectors on bidegree monomials as polynomials. -/
def bidegCombo (n m s t : ℕ) : (bidegIndex n m s t → ℂ) →ₗ[ℂ] Poly (n + m) where
  toFun c := ∑ β : bidegIndex n m s t, MvPolynomial.monomial β.1 (c β)
  map_add' c c' := by
    simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' a c := by
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum, MvPolynomial.smul_monomial]

theorem bidegCombo_coeff {n m s t : ℕ} (c : bidegIndex n m s t → ℂ) (β : bidegIndex n m s t) :
    (bidegCombo n m s t c).coeff β.1 = c β := by
  classical
  show (∑ γ : bidegIndex n m s t, MvPolynomial.monomial γ.1 (c γ)).coeff β.1 = c β
  rw [MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single β]
  · rw [MvPolynomial.coeff_monomial, if_pos rfl]
  · intro γ _ hne
    rw [MvPolynomial.coeff_monomial, if_neg]
    intro h
    exact hne (Subtype.ext h)
  · intro h
    exact absurd (Finset.mem_univ β) h

theorem bidegCombo_injective (n m s t : ℕ) : Function.Injective (bidegCombo n m s t) := by
  intro c c' h
  funext β
  rw [← bidegCombo_coeff c β, ← bidegCombo_coeff c' β, h]

theorem bidegCombo_range (n m s t : ℕ) :
    LinearMap.range (bidegCombo n m s t) = MvPolynomial.restrictSupport ℂ
      {d : Fin (n + m) →₀ ℕ | (∑ i : Fin n, d (Fin.castAdd m i)) = s ∧
        (∑ i : Fin m, d (Fin.natAdd n i)) = t} := by
  classical
  apply le_antisymm
  · rintro p ⟨c, rfl⟩
    show (∑ β : bidegIndex n m s t, MvPolynomial.monomial β.1 (c β)) ∈ _
    apply Submodule.sum_mem
    intro β _
    rw [MvPolynomial.mem_restrictSupport_iff]
    intro d hd
    have hd' := MvPolynomial.support_monomial_subset hd
    rw [Finset.mem_singleton] at hd'
    rw [hd']
    exact β.2
  · intro p hp
    rw [MvPolynomial.mem_restrictSupport_iff] at hp
    refine ⟨fun β => p.coeff β.1, ?_⟩
    ext d
    show (∑ β : bidegIndex n m s t, MvPolynomial.monomial β.1 (p.coeff β.1)).coeff d = p.coeff d
    rw [MvPolynomial.coeff_sum]
    by_cases hd : d ∈ {d : Fin (n + m) →₀ ℕ | (∑ i : Fin n, d (Fin.castAdd m i)) = s ∧
        (∑ i : Fin m, d (Fin.natAdd n i)) = t}
    · rw [Finset.sum_eq_single (⟨d, hd⟩ : bidegIndex n m s t)]
      · rw [MvPolynomial.coeff_monomial, if_pos rfl]
      · intro γ _ hne
        rw [MvPolynomial.coeff_monomial, if_neg]
        intro h
        exact hne (Subtype.ext h)
      · intro h
        exact absurd (Finset.mem_univ _) h
    · have hz : p.coeff d = 0 := by
        by_contra hne
        exact hd (hp (Finset.mem_coe.mpr (MvPolynomial.mem_support_iff.mpr hne)))
      rw [hz]
      apply Finset.sum_eq_zero
      intro γ _
      rw [MvPolynomial.coeff_monomial, if_neg]
      intro h
      exact hd (h ▸ γ.2)

/-- Rank–nullity for the bidegree section of a quotient. -/
theorem idealPairHilbert_add_finrank_ker {n m : ℕ} (J : Ideal (Poly (n + m))) (s t : ℕ) :
    idealPairHilbert J s t + Module.finrank ℂ
      (LinearMap.ker ((Ideal.Quotient.mkₐ ℂ J).toLinearMap ∘ₗ bidegCombo n m s t))
      = Fintype.card (bidegIndex n m s t) := by
  have hsec : idealPairSection J s t
      = LinearMap.range ((Ideal.Quotient.mkₐ ℂ J).toLinearMap ∘ₗ bidegCombo n m s t) := by
    rw [LinearMap.range_comp, bidegCombo_range]
    rfl
  have h := LinearMap.finrank_range_add_finrank_ker
    ((Ideal.Quotient.mkₐ ℂ J).toLinearMap ∘ₗ bidegCombo n m s t)
  rw [Module.finrank_fintype_fun_eq_card] at h
  unfold idealPairHilbert
  rw [hsec]
  exact h

theorem mem_ker_bidegCombo_iff {n m : ℕ} (J : Ideal (Poly (n + m))) (s t : ℕ)
    (c : bidegIndex n m s t → ℂ) :
    c ∈ LinearMap.ker ((Ideal.Quotient.mkₐ ℂ J).toLinearMap ∘ₗ bidegCombo n m s t) ↔
      bidegCombo n m s t c ∈ J := by
  rw [LinearMap.mem_ker, LinearMap.comp_apply]
  show Ideal.Quotient.mk J _ = 0 ↔ _
  exact Ideal.Quotient.eq_zero_iff_mem

/-- Specialization is surjective: it fixes the first-two-block variables. -/
theorem fibreSpecialize_rename {q o : ℕ} (z : Point o) (p : Poly q) :
    fibreSpecialize (q := q) (o := o) z (MvPolynomial.rename (Fin.castAdd (o + 1)) p) = p := by
  unfold fibreSpecialize
  rw [MvPolynomial.aeval_rename]
  have hfun : (Fin.append (fun i : Fin q => (MvPolynomial.X i : Poly q))
      (Fin.cons (1 : Poly q) (fun l : Fin o => MvPolynomial.C (z l))) ∘ Fin.castAdd (o + 1))
      = MvPolynomial.X := by
    funext i
    simp [Fin.append_left]
  rw [hfun, MvPolynomial.aeval_X_left_apply]

theorem fibreSpecialize_surjective {q o : ℕ} (z : Point o) :
    Function.Surjective (fibreSpecialize (q := q) (o := o) z) :=
  fun p => ⟨_, fibreSpecialize_rename z p⟩

/-- Specializing the bidegree part extracts the bidegree coefficients of the specialization. -/
theorem fibreSpecialize_BComp {n m o s t : ℕ} (z : Point o) (F : Poly (n + m + (o + 1))) :
    fibreSpecialize (q := n + m) (o := o) z (BComp n m (o + 1) s t F)
      = ∑ β : bidegIndex n m s t, MvPolynomial.monomial β.1
        ((fibreSpecialize (q := n + m) (o := o) z F).coeff β.1) := by
  classical
  induction F using MvPolynomial.induction_on' with
  | monomial D e => exact fibreSpecialize_BComp_monomial z D e
  | add p q hp hq =>
    have hB : BComp n m (o + 1) s t (p + q)
        = BComp n m (o + 1) s t p + BComp n m (o + 1) s t q := by
      unfold BComp
      rw [map_add, map_add]
    rw [hB, map_add, hp, hq, map_add, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro β _
    rw [MvPolynomial.coeff_add, map_add]

/-- Bidegree components lie in the bidegree piece. -/
theorem BComp_mem_bidegPiece (n m o s t : ℕ) (F : Poly (n + m + o)) :
    BComp n m o s t F ∈ bidegPiece n m o s t := by
  apply mem_bidegPiece_of_homog
  · exact whc_preserves_homog _ _ _ _ _
      (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous _ _)
  · exact MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous _ _

/-- F5: the fibre section dimension from explicit specialized relations of rank ρ. -/
theorem fibre_hilbert_of_relations {n m o s t : ℕ} {ι : Type} [Fintype ι]
    (T : Set ((ProjectivePoint n × ProjectivePoint m) × ProjectivePoint (o + 1)))
    (z : Point o) (G : ι → Poly (n + m + (o + 1))) (sk tk : ι → ℕ)
    (hG : ∀ k, G k ∈ MvPolynomial.vanishingIdeal ℂ (tripleRepresentatives T))
    (hx : ∀ k, MvPolynomial.IsWeightedHomogeneous (xWeight n m (o + 1)) (G k) (sk k))
    (hy : ∀ k, MvPolynomial.IsWeightedHomogeneous (yWeight n m (o + 1)) (G k) (tk k))
    (hspan : MvPolynomial.vanishingIdeal ℂ (tripleRepresentatives T) ≤
      Ideal.span (Set.range G))
    (R : NGenIdx n m s t ι sk tk → (bidegIndex n m s t → ℂ))
    (hR : ∀ l, bidegCombo n m s t (R l) =
      fibreSpecialize (q := n + m) (o := o) z (NGenElem n m (o + 1) s t G sk tk l.1 l.2))
    (J : Finset (NGenIdx n m s t ι sk tk))
    (hindep : LinearIndependent ℂ (fun j : ↥J => R ↑j))
    (hspanR : ∀ l, R l ∈ Submodule.span ℂ (Set.range (fun j : ↥J => R ↑j))) :
    idealPairHilbert (tripleFibreIdeal T z) s t = Fintype.card (bidegIndex n m s t) - J.card := by
  classical
  set Jz := tripleFibreIdeal T z with hJz
  set L := (Ideal.Quotient.mkₐ ℂ Jz).toLinearMap ∘ₗ bidegCombo n m s t with hL
  have hker : LinearMap.ker L = Submodule.span ℂ (Set.range R) := by
    apply le_antisymm
    · intro c hc
      have hc' : bidegCombo n m s t c ∈ Jz := (mem_ker_bidegCombo_iff Jz s t c).mp hc
      obtain ⟨F, hF, hFc⟩ := (Ideal.mem_map_iff_of_surjective _
        (fibreSpecialize_surjective (q := n + m) z)).mp hc'
      have hB : fibreSpecialize (q := n + m) (o := o) z (BComp n m (o + 1) s t F)
          = bidegCombo n m s t c := by
        rw [fibreSpecialize_BComp, hFc]
        show _ = ∑ β : bidegIndex n m s t, MvPolynomial.monomial β.1 (c β)
        apply Finset.sum_congr rfl
        intro β _
        rw [bidegCombo_coeff]
      obtain ⟨S', q, hq⟩ := NGen_spanning T G sk tk hG hx hy hspan (BComp n m (o + 1) s t F)
        (BComp_mem_bidegPiece _ _ _ _ _ F) (BComp_mem_Ix T hF s t)
      have hcomb : bidegCombo n m s t c = bidegCombo n m s t
          (∑ l ∈ S', MvPolynomial.eval (Fin.cons (1 : ℂ) z) (q l) • R l) := by
        rw [← hB, hq, map_sum, map_sum]
        apply Finset.sum_congr rfl
        intro l _
        rw [map_mul, fibreSpecialize_zInclusion, map_smul, hR l, MvPolynomial.C_mul']
      rw [bidegCombo_injective n m s t hcomb]
      apply Submodule.sum_mem
      intro l _
      apply Submodule.smul_mem
      exact Submodule.subset_span ⟨l, rfl⟩
    · rw [Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      rw [SetLike.mem_coe, mem_ker_bidegCombo_iff, hR l]
      exact Ideal.mem_map_of_mem _
        (NGenElem_mem n m (o + 1) s t T G sk tk hG hx hy l.1 l.2).2
  have hspaneq : Submodule.span ℂ (Set.range R)
      = Submodule.span ℂ (Set.range (fun j : ↥J => R ↑j)) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      exact hspanR l
    · apply Submodule.span_mono
      rintro _ ⟨j, rfl⟩
      exact ⟨j, rfl⟩
  have hrank : Module.finrank ℂ (LinearMap.ker L) = J.card := by
    rw [hker, hspaneq, finrank_span_eq_card hindep, Fintype.card_coe]
  have h := idealPairHilbert_add_finrank_ker Jz s t
  rw [← hL, hrank] at h
  omega

/-! ### Hilbert-function sandwich over the base -/

/-- Split off the third block as coefficients. -/
def splitZ (n m o : ℕ) : Poly (n + m + o) →ₐ[ℂ] MvPolynomial (Fin (n + m)) (Poly o) :=
  MvPolynomial.aeval (Fin.append (fun i : Fin (n + m) => (MvPolynomial.X i))
    (fun j : Fin o => MvPolynomial.C (MvPolynomial.X j)))

theorem splitZ_zInclusion (n m o : ℕ) (q : Poly o) :
    splitZ n m o (zInclusion n m o q) = MvPolynomial.C q := by
  have h : (splitZ n m o).comp (zInclusion n m o) =
      (Algebra.ofId (Poly o) (MvPolynomial (Fin (n + m)) (Poly o))).restrictScalars ℂ := by
    apply MvPolynomial.algHom_ext
    intro j
    rw [AlgHom.comp_apply, AlgHom.restrictScalars_apply, Algebra.ofId_apply,
      MvPolynomial.algebraMap_eq]
    simp only [zInclusion, MvPolynomial.rename_X, splitZ, MvPolynomial.aeval_X]
    show Fin.append _ _ (Fin.natAdd (n + m) j) = _
    rw [Fin.append_right]
  have h2 := congrArg (fun φ : Poly o →ₐ[ℂ] MvPolynomial (Fin (n + m)) (Poly o) => φ q) h
  simpa only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, Algebra.ofId_apply,
    MvPolynomial.algebraMap_eq] using h2

theorem splitZ_bidegMonomial (n m o s t : ℕ) (α : bidegIndex n m s t) :
    splitZ n m o (bidegMonomial n m o s t α) = MvPolynomial.monomial α.1 1 := by
  classical
  have eσ : ∀ j : Fin (n + m),
      Fin.append (fun i : Fin (n + m) => (MvPolynomial.X i : MvPolynomial (Fin (n + m)) (Poly o)))
        (fun j : Fin o => MvPolynomial.C (MvPolynomial.X j))
        ((embXY n m o) j) = MvPolynomial.X j := by
    intro j
    show Fin.append _ _ (Fin.castAdd _ j) = _
    rw [Fin.append_left]
  simp only [bidegMonomial, splitZ, MvPolynomial.aeval_monomial, map_one, one_mul,
    Finsupp.prod_embDomain]
  rw [← MvPolynomial.prod_X_pow_eq_monomial]
  apply Finset.prod_congr rfl
  intro j _
  simp only [eσ j]

/-- The third-block coefficient at a bidegree index, as a linear map. -/
def zcoeff (n m o s t : ℕ) (β : bidegIndex n m s t) : Poly (n + m + o) →ₗ[ℂ] Poly o where
  toFun F := (splitZ n m o F).coeff β.1
  map_add' F G := by rw [map_add, MvPolynomial.coeff_add]
  map_smul' c F := by
    rw [map_smul, MvPolynomial.coeff_smul]
    rfl

theorem zcoeff_zInclusion_mul (n m o s t : ℕ) (β : bidegIndex n m s t) (q : Poly o)
    (F : Poly (n + m + o)) :
    zcoeff n m o s t β (zInclusion n m o q * F) = q * zcoeff n m o s t β F := by
  show (splitZ n m o (zInclusion n m o q * F)).coeff β.1 = q * (splitZ n m o F).coeff β.1
  rw [map_mul, splitZ_zInclusion, MvPolynomial.coeff_C_mul]

theorem zcoeff_bidegMonomial (n m o s t : ℕ) (β γ : bidegIndex n m s t) :
    zcoeff n m o s t β (bidegMonomial n m o s t γ) = if γ = β then 1 else 0 := by
  show (splitZ n m o (bidegMonomial n m o s t γ)).coeff β.1 = _
  rw [splitZ_bidegMonomial, MvPolynomial.coeff_monomial]
  by_cases h : γ = β
  · rw [if_pos (congrArg Subtype.val h), if_pos h]
  · rw [if_neg (fun h' => h (Subtype.ext h')), if_neg h]

/-- Polynomials with third-block coefficient vector `y`. -/
def zCombo (n m o s t : ℕ) (y : bidegIndex n m s t → Poly o) : Poly (n + m + o) :=
  ∑ β : bidegIndex n m s t, bidegMonomial n m o s t β * zInclusion n m o (y β)

theorem zcoeff_zCombo (n m o s t : ℕ) (y : bidegIndex n m s t → Poly o)
    (β : bidegIndex n m s t) : zcoeff n m o s t β (zCombo n m o s t y) = y β := by
  classical
  unfold zCombo
  rw [map_sum]
  rw [Finset.sum_eq_single β]
  · rw [mul_comm, zcoeff_zInclusion_mul, zcoeff_bidegMonomial, if_pos rfl, mul_one]
  · intro γ _ hne
    rw [mul_comm, zcoeff_zInclusion_mul, zcoeff_bidegMonomial, if_neg hne, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ β) h

theorem zCombo_injective (n m o s t : ℕ) : Function.Injective (zCombo n m o s t) := by
  intro y y' h
  funext β
  rw [← zcoeff_zCombo n m o s t y β, ← zcoeff_zCombo n m o s t y' β, h]

/-- On the bidegree piece, `zcoeff` is the existing bidegree coefficient. -/
theorem zcoeff_eq_bidegCoeff (n m o s t : ℕ) (F : Poly (n + m + o))
    (hF : F ∈ bidegPiece n m o s t) (β : bidegIndex n m s t) :
    zcoeff n m o s t β F = bidegCoeff n m o s t F β := by
  have h := zcoeff_zCombo n m o s t (fun γ => bidegCoeff n m o s t F γ) β
  have hF' : zCombo n m o s t (fun γ => bidegCoeff n m o s t F γ) = F :=
    (coord_decomp n m o s t F hF).symm
  rw [hF'] at h
  exact h

theorem zcoeff_mul_of_mem {n m o s t : ℕ} (q : Poly o) (F : Poly (n + m + o))
    (hF : F ∈ bidegPiece n m o s t) (β : bidegIndex n m s t) :
    zcoeff n m o s t β (zInclusion n m o q * F) = q * bidegCoeff n m o s t F β := by
  rw [zcoeff_zInclusion_mul, zcoeff_eq_bidegCoeff n m o s t F hF]

/-- The tridegree exponent set, in `tripleSection`'s convention. -/
def triSet (n m o s t u : ℕ) : Set (Fin (n + m + o) →₀ ℕ) :=
  {d | (∑ i : Fin n, d (Fin.castAdd o (Fin.castAdd m i))) = s ∧
    (∑ i : Fin m, d (Fin.castAdd o (Fin.natAdd n i))) = t ∧
    (∑ i : Fin o, d (Fin.natAdd (n + m) i)) = u}

theorem support_bidegMonomial_mul_zInclusion {n m o s t : ℕ} (γ : bidegIndex n m s t)
    (q : Poly o) (D : Fin (n + m + o) →₀ ℕ)
    (hD : D ∈ (bidegMonomial n m o s t γ * zInclusion n m o q).support) :
    ∃ d ∈ q.support, D = Finsupp.embDomain (embXY n m o) γ.1 + Finsupp.embDomain (embZ n m o) d := by
  classical
  rw [MvPolynomial.mem_support_iff, bidegMonomial, MvPolynomial.coeff_monomial_mul'] at hD
  by_cases hle : Finsupp.embDomain (embXY n m o) γ.1 ≤ D
  · rw [if_pos hle, one_mul] at hD
    have hmem : D - Finsupp.embDomain (embXY n m o) γ.1 ∈ (zInclusion n m o q).support :=
      MvPolynomial.mem_support_iff.mpr hD
    rw [zInclusion, MvPolynomial.support_rename_of_injective (embZ n m o).injective,
      Finset.mem_image] at hmem
    obtain ⟨d, hd, hdD⟩ := hmem
    refine ⟨d, hd, ?_⟩
    rw [← mapDomain_eq_embDomain (embZ n m o) d, hdD, add_tsub_cancel_of_le hle]
  · rw [if_neg hle] at hD
    exact absurd rfl hD

theorem embDomain_parts_mem_triSet {n m o s t u : ℕ} (γ : bidegIndex n m s t)
    (d : Fin o →₀ ℕ) (hd : (∑ i : Fin o, d i) = u) :
    Finsupp.embDomain (embXY n m o) γ.1 + Finsupp.embDomain (embZ n m o) d ∈ triSet n m o s t u := by
  have hz0 : ∀ k : Fin (n + m), Finsupp.embDomain (embZ n m o) d (Fin.castAdd o k) = 0 := by
    intro k
    apply embDomain_notin
    intro l hl
    have := congrArg Fin.val hl
    simp [embZ_val] at this
    omega
  have hx0 : ∀ i : Fin o, Finsupp.embDomain (embXY n m o) γ.1 (Fin.natAdd (n + m) i) = 0 := by
    intro i
    apply embDomain_notin
    intro k hk
    have := congrArg Fin.val hk
    simp [embXY_val] at this
    omega
  have hxa : ∀ k : Fin (n + m), Finsupp.embDomain (embXY n m o) γ.1 (Fin.castAdd o k) = γ.1 k :=
    fun k => embDomain_at (embXY n m o) γ.1 k
  have hza : ∀ i : Fin o, Finsupp.embDomain (embZ n m o) d (Fin.natAdd (n + m) i) = d i :=
    fun i => embDomain_at (embZ n m o) d i
  refine ⟨?_, ?_, ?_⟩
  · simp only [Finsupp.add_apply, hz0, hxa, add_zero]
    exact γ.2.1
  · simp only [Finsupp.add_apply, hz0, hxa, add_zero]
    exact γ.2.2
  · simp only [Finsupp.add_apply, hx0, hza, zero_add]
    exact hd

/-- Coefficient vectors of degree-`u` third-block polynomials. -/
def zComboHom (n m o s t u : ℕ) :
    (bidegIndex n m s t → ↥(MvPolynomial.homogeneousSubmodule (Fin o) ℂ u)) →ₗ[ℂ]
      Poly (n + m + o) where
  toFun x := zCombo n m o s t (fun β => (x β : Poly o))
  map_add' x y := by
    simp only [zCombo, Pi.add_apply, Submodule.coe_add, map_add, mul_add,
      Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [zCombo, Pi.smul_apply, Submodule.coe_smul, map_smul, mul_smul_comm,
      Finset.smul_sum, RingHom.id_apply]

theorem zComboHom_range (n m o s t u : ℕ) :
    LinearMap.range (zComboHom n m o s t u) =
      MvPolynomial.restrictSupport ℂ (triSet n m o s t u) := by
  classical
  apply le_antisymm
  · rintro F ⟨x, rfl⟩
    show zCombo n m o s t (fun β => (x β : Poly o)) ∈ _
    apply Submodule.sum_mem
    intro β _
    rw [MvPolynomial.mem_restrictSupport_iff]
    intro D hD
    obtain ⟨d, hd, rfl⟩ := support_bidegMonomial_mul_zInclusion β _ D (Finset.mem_coe.mp hD)
    apply embDomain_parts_mem_triSet
    have hhom : (x β : Poly o).IsHomogeneous u := (x β).2
    have := hhom (MvPolynomial.mem_support_iff.mp hd)
    rw [← RulingMaps.degree_eq_sum_univ, Finsupp.degree_eq_weight_one]
    exact this
  · intro F hF
    have hsub : MvPolynomial.restrictSupport ℂ (triSet n m o s t u) ≤ bidegPiece n m o s t := by
      apply MvPolynomial.restrictSupport_mono
      intro D hD
      exact ⟨hD.1, hD.2.1⟩
    have hpiece := hsub hF
    have hzh : MvPolynomial.IsWeightedHomogeneous (zWeight n m o) F u := by
      intro D hD
      rw [MvPolynomial.mem_restrictSupport_iff] at hF
      have hDt := hF (Finset.mem_coe.mpr (MvPolynomial.mem_support_iff.mpr hD))
      rw [zWeight_eq_sum, RulingMaps.degree_eq_sum_univ]
      simp only [zPart_apply]
      exact hDt.2.2
    refine ⟨fun β => ⟨bidegCoeff n m o s t F β, bidegCoeff_homog n m o s t F u hzh β⟩, ?_⟩
    exact (coord_decomp n m o s t F hpiece).symm

/-- Rank–nullity for the tridegree section. -/
theorem tripleHilbert_add_finrank_ker {n m o : ℕ}
    (T : Set ((ProjectivePoint n × ProjectivePoint m) × ProjectivePoint o)) (s t u : ℕ) :
    tripleHilbert T s t u + Module.finrank ℂ (LinearMap.ker
      ((Ideal.Quotient.mkₐ ℂ (MvPolynomial.vanishingIdeal ℂ (tripleRepresentatives T))).toLinearMap
        ∘ₗ zComboHom n m o s t u))
      = Fintype.card (bidegIndex n m s t) *
        Module.finrank ℂ (MvPolynomial.homogeneousSubmodule (Fin o) ℂ u) := by
  have hsec : tripleSection T s t u = LinearMap.range
      ((Ideal.Quotient.mkₐ ℂ (MvPolynomial.vanishingIdeal ℂ (tripleRepresentatives T))).toLinearMap
        ∘ₗ zComboHom n m o s t u) := by
    rw [LinearMap.range_comp, zComboHom_range]
    rfl
  have h := LinearMap.finrank_range_add_finrank_ker
    ((Ideal.Quotient.mkₐ ℂ (MvPolynomial.vanishingIdeal ℂ (tripleRepresentatives T))).toLinearMap
      ∘ₗ zComboHom n m o s t u)
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h
  unfold tripleHilbert
  rw [hsec]
  exact h

/-- Third-block equations of the base lie in the triple ideal. -/
theorem zInclusion_mem_tripleIdeal {n m o : ℕ}
    (T : Set ((ProjectivePoint n × ProjectivePoint m) × ProjectivePoint o))
    (W : ProjectiveVariety o) (hTW : ∀ w ∈ T, w.2 ∈ W.points) (q : Poly o) (hq : q ∈ W.ideal) :
    zInclusion n m o q ∈ MvPolynomial.vanishingIdeal ℂ (tripleRepresentatives T) := by
  rw [MvPolynomial.mem_vanishingIdeal_iff]
  rintro w ⟨x, y, z, hx, hy, hz, hT, rfl⟩
  have hzW := hTW _ hT
  have hzero : z ∈ MvPolynomial.zeroLocus ℂ W.ideal := hzW z hz rfl
  have hfun : (joinPoints (joinPoints x y) z) ∘ (embZ n m o) = z := by
    funext l
    show Fin.addCases (joinPoints x y) z (Fin.natAdd (n + m) l) = z l
    rw [Fin.addCases_right]
  rw [zInclusion, MvPolynomial.aeval_rename, hfun]
  exact MvPolynomial.mem_zeroLocus_iff.mp hzero q hq

/-- Componentwise reduction of degree-`u` coefficient vectors modulo an ideal. -/
def quotVec {o : ℕ} (I : Ideal (Poly o)) (B : Type) (u : ℕ) :
    (B → ↥(MvPolynomial.homogeneousSubmodule (Fin o) ℂ u)) →ₗ[ℂ] (B → Poly o ⧸ I) where
  toFun x β := Ideal.Quotient.mk I (x β : Poly o)
  map_add' x y := by
    funext β
    simp only [Pi.add_apply, Submodule.coe_add, map_add]
  map_smul' c x := by
    funext β
    simp only [Pi.smul_apply, Submodule.coe_smul, RingHom.id_apply]
    rw [Algebra.smul_def, map_mul, Ideal.Quotient.mk_algebraMap, ← Algebra.smul_def]

theorem finrank_range_quotVec {o : ℕ} (W : ProjectiveVariety o) (B : Type) [Fintype B] (u : ℕ) :
    Module.finrank ℂ (LinearMap.range (quotVec W.ideal B u)) = Fintype.card B * W.hilbert u := by
  classical
  set P := MvPolynomial.homogeneousSubmodule (Fin o) ℂ u with hP
  set f := (Ideal.Quotient.mkₐ ℂ W.ideal).toLinearMap with hf
  have hA : W.restrictionSpace u = P.map f := rfl
  let ι : (B → ↥(P.map f)) →ₗ[ℂ] (B → Poly o ⧸ W.ideal) :=
    LinearMap.pi (fun β => (P.map f).subtype ∘ₗ LinearMap.proj β)
  have hιinj : Function.Injective ι := by
    intro y y' h
    funext β
    apply Subtype.ext
    exact congrFun h β
  have hrange : LinearMap.range (quotVec W.ideal B u) = LinearMap.range ι := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      refine ⟨fun β => ⟨f (x β), Submodule.mem_map_of_mem (x β).2⟩, ?_⟩
      funext β
      rfl
    · rintro _ ⟨y, rfl⟩
      have hpre : ∀ β, ∃ q : ↥P, f q = (y β : Poly o ⧸ W.ideal) := by
        intro β
        obtain ⟨q, hq, hqy⟩ := Submodule.mem_map.mp (y β).2
        exact ⟨⟨q, hq⟩, hqy⟩
      choose q hq using hpre
      refine ⟨q, ?_⟩
      funext β
      exact hq β
  rw [hrange, LinearMap.finrank_range_of_inj hιinj, Module.finrank_pi_fintype,
    Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rfl

/-- The image of the triple kernel in base-coordinate vectors computes the triple Hilbert
function: `tripleHilbert + dim(image) = S · HF_W`. -/
theorem tripleHilbert_add_finrank_image {n m o : ℕ}
    (T : Set ((ProjectivePoint n × ProjectivePoint m) × ProjectivePoint o))
    (W : ProjectiveVariety o) (hTW : ∀ w ∈ T, w.2 ∈ W.points) (s t u : ℕ) :
    tripleHilbert T s t u + Module.finrank ℂ ((LinearMap.ker
      ((Ideal.Quotient.mkₐ ℂ (MvPolynomial.vanishingIdeal ℂ (tripleRepresentatives T))).toLinearMap
        ∘ₗ zComboHom n m o s t u)).map (quotVec W.ideal (bidegIndex n m s t) u))
      = Fintype.card (bidegIndex n m s t) * W.hilbert u := by
  classical
  set K := LinearMap.ker
      ((Ideal.Quotient.mkₐ ℂ (MvPolynomial.vanishingIdeal ℂ (tripleRepresentatives T))).toLinearMap
        ∘ₗ zComboHom n m o s t u) with hK
  set κ := quotVec W.ideal (bidegIndex n m s t) u with hκ
  have h1 := tripleHilbert_add_finrank_ker T s t u
  rw [← hK] at h1
  have hle : LinearMap.ker κ ≤ K := by
    intro x hx
    rw [hK, LinearMap.mem_ker, LinearMap.comp_apply]
    show Ideal.Quotient.mk _ _ = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    show zCombo n m o s t (fun β => (x β : Poly o)) ∈ _
    apply Ideal.sum_mem
    intro β _
    apply Ideal.mul_mem_left
    apply zInclusion_mem_tripleIdeal T W hTW
    have hxβ := congrFun (LinearMap.mem_ker.mp hx) β
    exact Ideal.Quotient.eq_zero_iff_mem.mp hxβ
  have h2 := LinearMap.finrank_range_add_finrank_ker (K := ℂ) (V := ↥K)
    (V₂ := bidegIndex n m s t → Poly o ⧸ W.ideal) (κ.domRestrict K)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict,
    (Submodule.comapSubtypeEquivOfLe hle).finrank_eq] at h2
  have h3 := LinearMap.finrank_range_add_finrank_ker κ
  rw [finrank_range_quotVec, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ,
    smul_eq_mul] at h3
  omega

/-- Lower bound: independent columns times degree-shifted sections inject. -/
theorem finrank_ge_of_independent_products {o ρ : ℕ} {B : Type} [Fintype B]
    (W : ProjectiveVariety o) (Kbar : Submodule ℂ (B → Poly o ⧸ W.ideal))
    [Module.Finite ℂ Kbar] (col : Fin ρ → B → Poly o ⧸ W.ideal) (δ : Fin ρ → ℕ) (u : ℕ)
    (hind : ∀ a : Fin ρ → Poly o ⧸ W.ideal,
      (∑ j, fun β => a j * col j β) = 0 → ∀ j, a j = 0)
    (hmem : ∀ j (q : Poly o), q.IsHomogeneous (u - δ j) →
      (fun β => Ideal.Quotient.mk W.ideal q * col j β) ∈ Kbar) :
    ∑ j, W.hilbert (u - δ j) ≤ Module.finrank ℂ Kbar := by
  classical
  let Λ : (∀ j : Fin ρ, ↥(W.restrictionSpace (u - δ j))) →ₗ[ℂ] (B → Poly o ⧸ W.ideal) :=
    { toFun := fun a => ∑ j, fun β => (a j : Poly o ⧸ W.ideal) * col j β
      map_add' := by
        intro a b
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        funext β
        simp only [Pi.add_apply, Submodule.coe_add, add_mul]
      map_smul' := by
        intro c a
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro j _
        funext β
        simp only [Pi.smul_apply, Submodule.coe_smul, RingHom.id_apply, smul_mul_assoc] }
  have hinj : Function.Injective Λ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro a ha
    have h0 := hind (fun j => (a j : Poly o ⧸ W.ideal)) ha
    funext j
    exact Subtype.ext (h0 j)
  have hrange : LinearMap.range Λ ≤ Kbar := by
    rintro _ ⟨a, rfl⟩
    show (∑ j, fun β => ((a j : Poly o ⧸ W.ideal)) * col j β) ∈ Kbar
    apply Submodule.sum_mem
    intro j _
    obtain ⟨q, hq, hqa⟩ := Submodule.mem_map.mp (a j).2
    have := hmem j q hq
    have e : (Ideal.Quotient.mkₐ ℂ W.ideal).toLinearMap q = Ideal.Quotient.mk W.ideal q := rfl
    rw [e] at hqa
    rw [hqa] at this
    exact this
  have hdom : Module.finrank ℂ (∀ j : Fin ρ, ↥(W.restrictionSpace (u - δ j)))
      = ∑ j, W.hilbert (u - δ j) := by
    rw [Module.finrank_pi_fintype]
    rfl
  rw [← hdom, ← LinearMap.finrank_range_of_inj hinj]
  exact Submodule.finrank_mono hrange

/-- Upper bound: after an injective multiplication, the space lies in a column span with
degree-bounded coefficients. -/
theorem finrank_le_of_cleared_products {o ρ : ℕ} {B : Type} [Fintype B]
    (W : ProjectiveVariety o) (Kbar : Submodule ℂ (B → Poly o ⧸ W.ideal))
    [Module.Finite ℂ Kbar] (col : Fin ρ → B → Poly o ⧸ W.ideal) (c : Fin ρ → ℕ)
    (Δ : Poly o ⧸ W.ideal)
    (hΔ : ∀ y : B → Poly o ⧸ W.ideal, (fun β => Δ * y β) = 0 → y = 0)
    (hup : ∀ y ∈ Kbar, ∃ a : Fin ρ → Poly o ⧸ W.ideal, (∀ j, a j ∈ W.restrictionSpace (c j)) ∧
      (fun β => Δ * y β) = ∑ j, fun β => a j * col j β) :
    Module.finrank ℂ Kbar ≤ ∑ j, W.hilbert (c j) := by
  classical
  let Λ : (∀ j : Fin ρ, ↥(W.restrictionSpace (c j))) →ₗ[ℂ] (B → Poly o ⧸ W.ideal) :=
    { toFun := fun a => ∑ j, fun β => (a j : Poly o ⧸ W.ideal) * col j β
      map_add' := by
        intro a b
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        funext β
        simp only [Pi.add_apply, Submodule.coe_add, add_mul]
      map_smul' := by
        intro c a
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro j _
        funext β
        simp only [Pi.smul_apply, Submodule.coe_smul, RingHom.id_apply, smul_mul_assoc] }
  let mulΔ : (B → Poly o ⧸ W.ideal) →ₗ[ℂ] (B → Poly o ⧸ W.ideal) :=
    { toFun := fun y β => Δ * y β
      map_add' := by
        intro y y'
        funext β
        simp only [Pi.add_apply, mul_add]
      map_smul' := by
        intro a y
        funext β
        simp only [Pi.smul_apply, RingHom.id_apply, mul_smul_comm] }
  have hinj : Function.Injective mulΔ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    exact hΔ y hy
  have hmap : Kbar.map mulΔ ≤ LinearMap.range Λ := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨a, ha, hya⟩ := hup y hy
    exact ⟨fun j => ⟨a j, ha j⟩, hya.symm⟩
  have heq : Module.finrank ℂ (Kbar.map mulΔ) = Module.finrank ℂ Kbar :=
    (Submodule.equivMapOfInjective mulΔ hinj Kbar).finrank_eq.symm
  have hdom : Module.finrank ℂ (∀ j : Fin ρ, ↥(W.restrictionSpace (c j)))
      = ∑ j, W.hilbert (c j) := by
    rw [Module.finrank_pi_fintype]
    rfl
  rw [← heq, ← hdom]
  exact (Submodule.finrank_mono hmap).trans (LinearMap.finrank_range_le Λ)

/-- Homogeneous truncation of a cleared relation modulo the homogeneous base ideal. -/
theorem homogeneous_relation_trunc {o ρ : ℕ} {B : Type} (W : ProjectiveVariety o)
    (x : B → Poly o) (u Dg : ℕ) (hx : ∀ β, (x β).IsHomogeneous u)
    (P : Poly o) (hP : P.IsHomogeneous Dg)
    (pcol : Fin ρ → B → Poly o) (δ : Fin ρ → ℕ) (hpcol : ∀ j β, (pcol j β).IsHomogeneous (δ j))
    (hδ : ∀ j, δ j ≤ u + Dg) (c : Fin ρ → Poly o)
    (hrel : ∀ β, Ideal.Quotient.mk W.ideal (P * x β)
      = ∑ j, Ideal.Quotient.mk W.ideal (c j) * Ideal.Quotient.mk W.ideal (pcol j β)) :
    ∃ a : Fin ρ → Poly o ⧸ W.ideal, (∀ j, a j ∈ W.restrictionSpace (u + Dg - δ j)) ∧
      (fun β => Ideal.Quotient.mk W.ideal P * Ideal.Quotient.mk W.ideal (x β))
        = ∑ j, fun β => a j * Ideal.Quotient.mk W.ideal (pcol j β) := by
  classical
  refine ⟨fun j => Ideal.Quotient.mk W.ideal
    (MvPolynomial.homogeneousComponent (u + Dg - δ j) (c j)), fun j => ?_, ?_⟩
  · exact Submodule.mem_map_of_mem (MvPolynomial.homogeneousComponent_mem _ _)
  · funext β
    rw [Finset.sum_apply]
    have hdiff : P * x β - ∑ j, c j * pcol j β ∈ W.ideal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hrel β, map_sum]
      simp only [map_mul, sub_self]
    have hcomp := MvPolynomial.homogeneousComponent_mem_of_mem W.isHomogeneous hdiff (u + Dg)
    have hPx : (P * x β) ∈ MvPolynomial.homogeneousSubmodule (Fin o) ℂ (u + Dg) := by
      rw [MvPolynomial.mem_homogeneousSubmodule, add_comm]
      exact hP.mul (hx β)
    rw [map_sub, map_sum, MvPolynomial.homogeneousComponent_of_mem hPx, if_pos rfl] at hcomp
    have hterm : ∀ j, MvPolynomial.homogeneousComponent (u + Dg) (c j * pcol j β)
        = MvPolynomial.homogeneousComponent (u + Dg - δ j) (c j) * pcol j β :=
      fun j => RulingMaps.homogeneousComponent_mul_of_isHomogeneous (hpcol j β) (hδ j) (c j)
    simp only [hterm] at hcomp
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, map_sum] at hcomp
    rw [← map_mul, hcomp]
    simp only [map_mul]

/-- Shifting the argument of a polynomial changes it by lower order. -/
theorem poly_shift_bound (p : ℚ[X]) (c : ℚ) : ∃ C : ℚ, ∀ x : ℚ, 1 ≤ x →
    |p.eval (x + c) - p.eval x| ≤ C * x ^ (p.natDegree - 1) := by
  classical
  set q := p.comp (X + Polynomial.C c) - p with hq
  have hcomp_deg : (p.comp (X + Polynomial.C c)).natDegree = p.natDegree := by
    rw [Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one]
  have hqdeg : q.natDegree ≤ p.natDegree - 1 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    by_cases hNp : N = p.natDegree
    · by_cases hp0 : p.natDegree = 0
      · have hpC : p = Polynomial.C (p.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hp0
        have hq0 : q = 0 := by
          rw [hq, hpC, Polynomial.C_comp, sub_self]
        rw [hq0, Polynomial.coeff_zero]
      have hlc : (p.comp (X + Polynomial.C c)).leadingCoeff = p.leadingCoeff := by
        rw [Polynomial.leadingCoeff_comp (by rw [Polynomial.natDegree_X_add_C]; omega),
          Polynomial.leadingCoeff_X_add_C, one_pow, mul_one]
      rw [hq, Polynomial.coeff_sub, hNp]
      have e1 : (p.comp (X + Polynomial.C c)).coeff p.natDegree = p.leadingCoeff := by
        rw [← hlc, Polynomial.leadingCoeff, hcomp_deg]
      rw [e1, Polynomial.leadingCoeff, sub_self]
    · have hgt : p.natDegree < N := by
        have : (p.natDegree - 1 : ℕ) < N := by exact_mod_cast hN
        omega
      rw [hq, Polynomial.coeff_sub, Polynomial.coeff_eq_zero_of_natDegree_lt hgt,
        Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hcomp_deg]; exact hgt), sub_zero]
  refine ⟨∑ i ∈ Finset.range (q.natDegree + 1), |q.coeff i|, fun x hx => ?_⟩
  have heval : p.eval (x + c) - p.eval x = q.eval x := by
    rw [hq, Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C]
  rw [heval, Polynomial.eval_eq_sum_range, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  have hi' : i ≤ p.natDegree - 1 := by
    have := Finset.mem_range.mp hi
    omega
  rw [abs_mul, abs_pow, abs_of_nonneg (by linarith : (0 : ℚ) ≤ x)]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact pow_le_pow_right₀ hx hi'

/-- Hilbert function shifts are lower order. -/
theorem hilbert_shift_bound {o : ℕ} (W : ProjectiveVariety o) (a b : ℕ) :
    ∃ C : ℚ, ∃ M : ℕ, ∀ u : ℕ, M ≤ u →
      |(W.hilbert (u + a - b) : ℚ) - W.hilbert u| ≤ C * (u : ℚ) ^ (W.dimension - 1) := by
  obtain ⟨NW, hNW⟩ := W.hilbert_eventually
  obtain ⟨C, hC⟩ := poly_shift_bound W.hilbertPolynomial ((a : ℚ) - b)
  refine ⟨C, NW + b + 1, fun u hu => ?_⟩
  have h1 : NW < u + a - b := by omega
  have h2 : NW < u := by omega
  rw [hNW _ h1, hNW _ h2]
  have hcast : ((u + a - b : ℕ) : ℚ) = (u : ℚ) + ((a : ℚ) - b) := by
    rw [Nat.cast_sub (by omega), Nat.cast_add]
    ring
  rw [hcast]
  exact hC (u : ℚ) (by exact_mod_cast (show 1 ≤ u by omega))

/-- Pure arithmetic: the sandwich gives the slope estimate. -/
theorem slope_of_sandwich {o ρ : ℕ} (W : ProjectiveVariety o) (δ : Fin ρ → ℕ) (Dg S r M0 : ℕ)
    (hr : r + ρ = S) (tH kbar : ℕ → ℕ)
    (hA : ∀ u, tH u + kbar u = S * W.hilbert u)
    (hlow : ∀ u, M0 ≤ u → ∑ j, W.hilbert (u + 0 - δ j) ≤ kbar u)
    (hup : ∀ u, kbar u ≤ ∑ j, W.hilbert (u + Dg - δ j)) :
    ∃ C : ℚ, ∃ M : ℕ, ∀ u : ℕ, M ≤ u →
      |(tH u : ℚ) - r * W.hilbert u| ≤ C * (u : ℚ) ^ (W.dimension - 1) := by
  classical
  choose C1 M1 h1 using fun j : Fin ρ => hilbert_shift_bound W 0 (δ j)
  choose C2 M2 h2 using fun j : Fin ρ => hilbert_shift_bound W Dg (δ j)
  refine ⟨∑ j, (C1 j + C2 j),
    max M0 (∑ j, (M1 j + M2 j)), fun u hu => ?_⟩
  have hM1 : ∀ j, M1 j ≤ u := fun j => le_trans (le_trans (Nat.le_add_right _ _)
    (Finset.single_le_sum (f := fun j => M1 j + M2 j) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j))) (le_of_max_le_right hu)
  have hM2 : ∀ j, M2 j ≤ u := fun j => le_trans (le_trans (Nat.le_add_left _ _)
    (Finset.single_le_sum (f := fun j => M1 j + M2 j) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j))) (le_of_max_le_right hu)
  have hAq : (tH u : ℚ) = S * W.hilbert u - kbar u := by
    have := hA u
    have h' : ((tH u + kbar u : ℕ) : ℚ) = ((S * W.hilbert u : ℕ) : ℚ) := by rw [this]
    push_cast at h'
    linarith
  have hSq : (S : ℚ) = r + ρ := by exact_mod_cast hr.symm
  have hlowq : (∑ j, (W.hilbert (u + 0 - δ j) : ℚ)) ≤ kbar u := by
    exact_mod_cast hlow u (le_of_max_le_left hu)
  have hupq : (kbar u : ℚ) ≤ ∑ j, (W.hilbert (u + Dg - δ j) : ℚ) := by
    exact_mod_cast hup u
  have hρ : (ρ : ℚ) * W.hilbert u = ∑ _j : Fin ρ, (W.hilbert u : ℚ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hdiff : (tH u : ℚ) - r * W.hilbert u = (∑ _j : Fin ρ, (W.hilbert u : ℚ)) - kbar u := by
    rw [hAq, hSq, ← hρ]
    ring
  rw [hdiff, Finset.sum_mul, abs_le]
  constructor
  · -- lower side
    have hb : ∀ j, -(C2 j * (u : ℚ) ^ (W.dimension - 1)) ≤
        (W.hilbert u : ℚ) - W.hilbert (u + Dg - δ j) := by
      intro j
      have := h2 j u (hM2 j)
      rw [abs_le] at this
      linarith [this.2]
    have hpos : ∀ j, 0 ≤ C1 j * (u : ℚ) ^ (W.dimension - 1) :=
      fun j => le_trans (abs_nonneg _) (h1 j u (hM1 j))
    have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hb j)
    rw [Finset.sum_neg_distrib, Finset.sum_sub_distrib] at hs
    have hs1 := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => hpos j)
    have e : ∑ j, (C1 j + C2 j) * (u : ℚ) ^ (W.dimension - 1)
        = ∑ j, C1 j * (u : ℚ) ^ (W.dimension - 1) + ∑ j, C2 j * (u : ℚ) ^ (W.dimension - 1) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [e]
    linarith
  · have hb : ∀ j, (W.hilbert u : ℚ) - W.hilbert (u + 0 - δ j) ≤
        C1 j * (u : ℚ) ^ (W.dimension - 1) := by
      intro j
      have := h1 j u (hM1 j)
      rw [abs_le] at this
      linarith [this.1]
    have hpos : ∀ j, 0 ≤ C2 j * (u : ℚ) ^ (W.dimension - 1) :=
      fun j => le_trans (abs_nonneg _) (h2 j u (hM2 j))
    have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hb j)
    rw [Finset.sum_sub_distrib] at hs
    have hs2 := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => hpos j)
    have e : ∑ j, (C1 j + C2 j) * (u : ℚ) ^ (W.dimension - 1)
        = ∑ j, C1 j * (u : ℚ) ^ (W.dimension - 1) + ∑ j, C2 j * (u : ℚ) ^ (W.dimension - 1) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [e]
    linarith

theorem zCombo_mul_left {n m o s t : ℕ} (q : Poly o) (y : bidegIndex n m s t → Poly o) :
    zCombo n m o s t (fun β => q * y β) = zInclusion n m o q * zCombo n m o s t y := by
  unfold zCombo
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro β _
  rw [map_mul]
  ring

/-- Part 2 of the engine from abstract column data: the slope estimate. -/
theorem triple_slope_of_columns {n m o s t : ℕ} {ι : Type} [Fintype ι]
    (T : Set ((ProjectivePoint n × ProjectivePoint m) × ProjectivePoint o))
    (W : ProjectiveVariety o) (hW : W.IsIrreducible) (hTW : ∀ w ∈ T, w.2 ∈ W.points)
    (G : ι → Poly (n + m + o)) (sk tk uk : ι → ℕ)
    (hG : ∀ k, G k ∈ MvPolynomial.vanishingIdeal ℂ (tripleRepresentatives T))
    (hx : ∀ k, MvPolynomial.IsWeightedHomogeneous (xWeight n m o) (G k) (sk k))
    (hy : ∀ k, MvPolynomial.IsWeightedHomogeneous (yWeight n m o) (G k) (tk k))
    (hz : ∀ k, MvPolynomial.IsWeightedHomogeneous (zWeight n m o) (G k) (uk k))
    (hspan : MvPolynomial.vanishingIdeal ℂ (tripleRepresentatives T) ≤
      Ideal.span (Set.range G))
    {ρ : ℕ} (hρ : ρ ≤ Fintype.card (bidegIndex n m s t))
    (lj : Fin ρ → NGenIdx n m s t ι sk tk)
    (hind : ∀ a : Fin ρ → Poly o ⧸ W.ideal,
      (∑ j, fun β => a j * Ideal.Quotient.mk W.ideal
        (bidegCoeff n m o s t (NGenElem n m o s t G sk tk (lj j).1 (lj j).2) β)) = 0 →
        ∀ j, a j = 0)
    (Pd : Poly o) (Dg : ℕ) (hPd : Pd.IsHomogeneous Dg) (hPd0 : Pd ∉ W.ideal)
    (hδ : ∀ j, uk (lj j).1 ≤ Dg)
    (Nrel : Fin ρ → NGenIdx n m s t ι sk tk → Poly o ⧸ W.ideal)
    (hCr : ∀ (l : NGenIdx n m s t ι sk tk) (β : bidegIndex n m s t),
      Ideal.Quotient.mk W.ideal Pd * Ideal.Quotient.mk W.ideal
        (bidegCoeff n m o s t (NGenElem n m o s t G sk tk l.1 l.2) β)
        = ∑ j, Nrel j l * Ideal.Quotient.mk W.ideal
          (bidegCoeff n m o s t (NGenElem n m o s t G sk tk (lj j).1 (lj j).2) β)) :
    ∃ C : ℚ, ∃ M : ℕ, ∀ u : ℕ, M ≤ u →
      |(tripleHilbert T s t u : ℚ) - ((Fintype.card (bidegIndex n m s t) - ρ : ℕ) : ℚ) *
        W.hilbert u| ≤ C * (u : ℚ) ^ (W.dimension - 1) := by
  classical
  haveI : W.ideal.IsPrime := hW
  haveI : IsDomain (Poly o ⧸ W.ideal) := Ideal.Quotient.isDomain _
  set bc : NGenIdx n m s t ι sk tk → bidegIndex n m s t → Poly o :=
    fun l β => bidegCoeff n m o s t (NGenElem n m o s t G sk tk l.1 l.2) β with hbcdef
  have hgen_homog : ∀ l : NGenIdx n m s t ι sk tk,
      MvPolynomial.IsWeightedHomogeneous (zWeight n m o)
        (NGenElem n m o s t G sk tk l.1 l.2) (uk l.1) := by
    intro l
    unfold NGenElem
    by_cases h : sk l.1 ≤ s ∧ tk l.1 ≤ t
    · rw [dif_pos h]
      have he := bidegMonomial_zhomog_zero n m o (s - sk l.1) (t - tk l.1) l.2
      have hmul := he.mul (hz l.1)
      simpa using hmul
    · rw [dif_neg h]
      exact MvPolynomial.isWeightedHomogeneous_zero ℂ _ _
  have hbc_hom : ∀ l β, (bc l β).IsHomogeneous (uk l.1) :=
    fun l β => bidegCoeff_homog _ _ _ _ _ _ _ (hgen_homog l) _
  have hpieceN : ∀ l : NGenIdx n m s t ι sk tk,
      NGenElem n m o s t G sk tk l.1 l.2 ∈ bidegPiece n m o s t :=
    fun l => (NGenElem_mem n m o s t T G sk tk hG hx hy l.1 l.2).1
  have hIN : ∀ l : NGenIdx n m s t ι sk tk,
      NGenElem n m o s t G sk tk l.1 l.2 ∈ MvPolynomial.vanishingIdeal ℂ (tripleRepresentatives T) :=
    fun l => (NGenElem_mem n m o s t T G sk tk hG hx hy l.1 l.2).2
  set col : Fin ρ → bidegIndex n m s t → Poly o ⧸ W.ideal :=
    fun j β => Ideal.Quotient.mk W.ideal (bc (lj j) β) with hcoldef
  set δ : Fin ρ → ℕ := fun j => uk (lj j).1 with hδdef
  set Kb : ℕ → Submodule ℂ (bidegIndex n m s t → Poly o ⧸ W.ideal) := fun u =>
    (LinearMap.ker
      ((Ideal.Quotient.mkₐ ℂ (MvPolynomial.vanishingIdeal ℂ (tripleRepresentatives T))).toLinearMap
        ∘ₗ zComboHom n m o s t u)).map (quotVec W.ideal (bidegIndex n m s t) u) with hKbdef
  have hmemK : ∀ u (x : bidegIndex n m s t → ↥(MvPolynomial.homogeneousSubmodule (Fin o) ℂ u)),
      zCombo n m o s t (fun β => (x β : Poly o)) ∈
        MvPolynomial.vanishingIdeal ℂ (tripleRepresentatives T) →
      quotVec W.ideal (bidegIndex n m s t) u x ∈ Kb u := by
    intro u x hx'
    refine Submodule.mem_map_of_mem ?_
    rw [LinearMap.mem_ker, LinearMap.comp_apply]
    show Ideal.Quotient.mk _ _ = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hx'
  apply slope_of_sandwich W δ Dg (Fintype.card (bidegIndex n m s t)) _ Dg (by omega)
    (tripleHilbert T s t) (fun u => Module.finrank ℂ (Kb u))
  · intro u
    exact tripleHilbert_add_finrank_image T W hTW s t u
  · intro u hu
    simp only [add_zero]
    apply finrank_ge_of_independent_products W (Kb u) col δ u hind
    intro j q hq
    have hdeg : ∀ β, (q * bc (lj j) β).IsHomogeneous u := by
      intro β
      have h := hq.mul (hbc_hom (lj j) β)
      have hle : δ j ≤ u := le_trans (hδ j) hu
      rwa [Nat.sub_add_cancel hle] at h
    let x : bidegIndex n m s t → ↥(MvPolynomial.homogeneousSubmodule (Fin o) ℂ u) :=
      fun β => ⟨q * bc (lj j) β, (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (hdeg β)⟩
    have hx' : zCombo n m o s t (fun β => (x β : Poly o)) ∈
        MvPolynomial.vanishingIdeal ℂ (tripleRepresentatives T) := by
      show zCombo n m o s t (fun β => q * bc (lj j) β) ∈ _
      rw [zCombo_mul_left]
      have hdec : zCombo n m o s t (bc (lj j)) = NGenElem n m o s t G sk tk (lj j).1 (lj j).2 :=
        (coord_decomp n m o s t _ (hpieceN (lj j))).symm
      rw [hdec]
      exact Ideal.mul_mem_left _ _ (hIN (lj j))
    have h := hmemK u x hx'
    have hval : quotVec W.ideal (bidegIndex n m s t) u x
        = fun β => Ideal.Quotient.mk W.ideal q * col j β := by
      funext β
      show Ideal.Quotient.mk W.ideal (q * bc (lj j) β) = _
      rw [map_mul]
    rw [hval] at h
    exact h
  · intro u
    apply finrank_le_of_cleared_products W (Kb u) col (fun j => u + Dg - δ j)
      (Ideal.Quotient.mk W.ideal Pd)
    · intro y hy0
      funext β
      have h := congrFun hy0 β
      simp only [Pi.zero_apply] at h ⊢
      rcases mul_eq_zero.mp h with h0 | h0
      · exact absurd (Ideal.Quotient.eq_zero_iff_mem.mp h0) hPd0
      · exact h0
    · intro y hyK
      obtain ⟨x, hxK, rfl⟩ := Submodule.mem_map.mp hyK
      have hxI : zCombo n m o s t (fun β => (x β : Poly o)) ∈
          MvPolynomial.vanishingIdeal ℂ (tripleRepresentatives T) := by
        have := LinearMap.mem_ker.mp hxK
        rw [LinearMap.comp_apply] at this
        exact Ideal.Quotient.eq_zero_iff_mem.mp this
      have hxP : zCombo n m o s t (fun β => (x β : Poly o)) ∈ bidegPiece n m o s t := by
        have hr : zComboHom n m o s t u x ∈ LinearMap.range (zComboHom n m o s t u) := ⟨x, rfl⟩
        rw [zComboHom_range] at hr
        have hsub : MvPolynomial.restrictSupport ℂ (triSet n m o s t u) ≤
            bidegPiece n m o s t := by
          apply MvPolynomial.restrictSupport_mono
          intro D hD
          exact ⟨hD.1, hD.2.1⟩
        exact hsub hr
      obtain ⟨S', q, hq⟩ := NGen_spanning T G sk tk hG hx hy hspan _ hxP hxI
      have hxβ : ∀ β, (x β : Poly o) = ∑ l ∈ S', q l * bc l β := by
        intro β
        have h := zcoeff_zCombo n m o s t (fun β => (x β : Poly o)) β
        rw [hq, map_sum] at h
        rw [← h]
        apply Finset.sum_congr rfl
        intro l _
        exact zcoeff_mul_of_mem (q l) _ (hpieceN l) β
      have hNrep : ∀ j l, ∃ r : Poly o, Ideal.Quotient.mk W.ideal r = Nrel j l :=
        fun j l => Ideal.Quotient.mk_surjective (Nrel j l)
      choose Nrep hNrep using hNrep
      obtain ⟨a, ha, heq⟩ := homogeneous_relation_trunc W (fun β => (x β : Poly o)) u Dg
        (fun β => (x β).2) Pd hPd (fun j β => bc (lj j) β) δ
        (fun j β => hbc_hom (lj j) β) (fun j => le_trans (hδ j) (Nat.le_add_left _ _))
        (fun j => ∑ l ∈ S', q l * Nrep j l) (by
          intro β
          rw [hxβ β, Finset.mul_sum, map_sum]
          calc ∑ l ∈ S', Ideal.Quotient.mk W.ideal (Pd * (q l * bc l β))
              = ∑ l ∈ S', Ideal.Quotient.mk W.ideal (q l) *
                  (Ideal.Quotient.mk W.ideal Pd * Ideal.Quotient.mk W.ideal (bc l β)) := by
                apply Finset.sum_congr rfl
                intro l _
                simp only [map_mul]
                ring
            _ = ∑ l ∈ S', ∑ j, Ideal.Quotient.mk W.ideal (q l) *
                  (Nrel j l * Ideal.Quotient.mk W.ideal (bc (lj j) β)) := by
                apply Finset.sum_congr rfl
                intro l _
                rw [hCr l β, Finset.mul_sum]
            _ = ∑ j, ∑ l ∈ S', Ideal.Quotient.mk W.ideal (q l) *
                  (Nrel j l * Ideal.Quotient.mk W.ideal (bc (lj j) β)) := Finset.sum_comm
            _ = ∑ j, Ideal.Quotient.mk W.ideal (∑ l ∈ S', q l * Nrep j l) *
                  Ideal.Quotient.mk W.ideal (bc (lj j) β) := by
                apply Finset.sum_congr rfl
                intro j _
                rw [map_sum, Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro l _
                rw [map_mul, hNrep]
                ring)
      exact ⟨a, ha, heq⟩

/-- L-engine. For fixed (s,t), the u-graded module `⊕_u S_{s,t,u}` over the coordinate ring
A of W has a generic rank r: off a hypersurface of W its specialization has dimension r, and
`HF(s,t,u) = r·HF_W(u) + O(u^(dim W - 1))`. -/
theorem tripleHilbert_generic_rank {n m o : ℕ}
    (T : Set ((ProjectivePoint n × ProjectivePoint m) × ProjectivePoint (o + 1)))
    (W : ProjectiveVariety (o + 1)) (hW : W.IsIrreducible)
    (hTW : ∀ w ∈ T, w.2 ∈ W.points) (s t : ℕ) :
    ∃ r : ℕ, (∃ g : Poly (o + 1), ∃ D : ℕ, g.IsHomogeneous D ∧ g ∉ W.ideal ∧
      ∀ z : Point o, affineEmbedding z ∈ W.points →
        MvPolynomial.eval (Fin.cons 1 z) g ≠ 0 →
          idealPairHilbert (tripleFibreIdeal T z) s t = r) ∧
      ∃ C : ℚ, ∃ M : ℕ, ∀ u : ℕ, M ≤ u →
        |(tripleHilbert T s t u : ℚ) - r * W.hilbert u| ≤ C * (u : ℚ) ^ (W.dimension - 1) := by
  classical
  -- Coordinate ring and its fraction field.
  haveI : W.ideal.IsPrime := hW
  haveI : IsDomain (Poly (o + 1) ⧸ W.ideal) := Ideal.Quotient.isDomain _
  set A := Poly (o + 1) ⧸ W.ideal with hAdef
  set K := FractionRing A with hKdef
  -- Trihomogeneous generators.
  obtain ⟨ι, hιfin, G, sk, tk, uk, hGmem, hGx, hGy, hGz, hGspan⟩ :=
    tripleIx_trihomog_gens T
  haveI := hιfin
  haveI := Classical.decEq ι
  -- Generator coordinates are homogeneous of the generator's Z-degree.
  have hgen_homog : ∀ l : NGenIdx n m s t ι sk tk,
      MvPolynomial.IsWeightedHomogeneous (zWeight n m (o + 1))
        (NGenElem n m (o + 1) s t G sk tk l.1 l.2) (uk l.1) := by
    intro l
    unfold NGenElem
    by_cases h : sk l.1 ≤ s ∧ tk l.1 ≤ t
    · rw [dif_pos h]
      have he := bidegMonomial_zhomog_zero n m (o + 1) (s - sk l.1) (t - tk l.1) l.2
      have hmul := he.mul (hGz l.1)
      simpa using hmul
    · rw [dif_neg h]
      exact MvPolynomial.isWeightedHomogeneous_zero ℂ _ _
  -- Coordinate matrix over A.
  set V : (bidegIndex n m s t) → (NGenIdx n m s t ι sk tk) → A :=
    fun β l => Ideal.Quotient.mk _ (bidegCoeff n m (o + 1) s t (NGenElem n m (o + 1) s t G sk tk l.1 l.2) β) with hVdef
  have hVhomog : ∀ (l : NGenIdx n m s t ι sk tk) (β : bidegIndex n m s t),
      MvPolynomial.IsHomogeneous (bidegCoeff n m (o + 1) s t (NGenElem n m (o + 1) s t G sk tk l.1 l.2) β) (uk l.1) := by
    intro l β
    exact bidegCoeff_homog _ _ _ _ _ _ _ (hgen_homog l) _
  -- K-vectors and a maximal independent subfamily of generator columns.
  haveI := Classical.decEq (NGenIdx n m s t ι sk tk)
  set VK : (bidegIndex n m s t) → (NGenIdx n m s t ι sk tk) → K :=
    fun β l => algebraMap A K (V β l) with hVKdef
  -- columns as K-vectors
  set col : (NGenIdx n m s t ι sk tk) → (bidegIndex n m s t → K) :=
    fun l β => VK β l with hcoldef
  classical
  obtain ⟨J, hJmem, hJmax⟩ := Finset.exists_max_image
    (Finset.univ.powerset.filter (fun J : Finset (NGenIdx n m s t ι sk tk) =>
      LinearIndependent K (fun j : ↥J => col j.1)))
    (fun J => J.card)
    ⟨∅, by
      simp only [Finset.mem_powerset, Finset.empty_subset, Finset.mem_filter, true_and]
      rw [Fintype.linearIndependent_iff]
      intro g _ i
      exact absurd i.2 (Finset.notMem_empty _)⟩
  set ρ : ℕ := J.card with hρdef
  have hJindep : LinearIndependent K (fun j : ↥J => col j.1) :=
    (Finset.mem_filter.mp hJmem).2
  -- Every generator column lies in the K-span of J.
  have hspanJ : ∀ l : NGenIdx n m s t ι sk tk,
      col l ∈ Submodule.span K (Set.range (fun j : ↥J => col j.1)) := by
    intro l
    by_cases hl : l ∈ J
    · apply Submodule.subset_span
      exact ⟨⟨l, hl⟩, rfl⟩
    · by_contra hcon
      have hindep := linearIndependent_insert_of_not_mem_span
        (fun l : NGenIdx n m s t ι sk tk => col l) J l hJindep hl hcon
      have hle := hJmax (insert l J) (by
        simp only [Finset.mem_powerset, Finset.mem_filter]
        exact ⟨Finset.subset_univ _, hindep⟩)
      rw [Finset.card_insert_of_notMem hl] at hle
      omega
  -- Enumerate the basis; build the K-matrix and extract a nonzero minor.
  have hcardJ : Fintype.card ↥J = ρ := by rw [hρdef]; exact Fintype.card_coe J
  set eJ : ↥J ≃ Fin ρ := Fintype.equivFinOfCardEq hcardJ with heJdef
  set Bmat : Matrix (bidegIndex n m s t) (Fin ρ) K :=
    fun β j => VK β ↑(eJ.symm j) with hBmatdef
  have hBindep : LinearIndependent K (fun j : Fin ρ => fun β => Bmat β j) := by
    have hcomp := LinearIndependent.comp hJindep (⇑eJ.symm) eJ.symm.injective
    exact hcomp
  obtain ⟨e, he⟩ := exists_ne_zero_minor_of_linearIndependent Bmat hBindep
  -- Each generator column is a K-linear combination of the enumerated basis columns.
  have hKrel : ∀ l : NGenIdx n m s t ι sk tk, ∃ g : Fin ρ → K,
      ∀ β : bidegIndex n m s t,
        algebraMap A K (V β l) = ∑ j, g j * algebraMap A K (V β ↑(eJ.symm j)) := by
    intro l
    have hrange : Set.range (fun j : Fin ρ => col (↑(eJ.symm j) : NGenIdx n m s t ι sk tk))
        = Set.range (fun j : ↥J => col ↑j) := by
      have h := eJ.symm.surjective.range_comp (fun j : ↥J => col ↑j)
      exact h
    have hmem : col l ∈ Submodule.span K
        (Set.range (fun j : Fin ρ => col (↑(eJ.symm j) : NGenIdx n m s t ι sk tk))) := by
      rw [hrange]
      exact hspanJ l
    obtain ⟨g, hg⟩ := span_relation_apply _ _ hmem
    refine ⟨g, fun β => ?_⟩
    have hβ := congrFun hg β
    rw [Finset.sum_apply] at hβ
    simp only [hcoldef, smul_eq_mul, hVKdef] at hβ
    exact hβ
  -- Clear denominators column by column.
  have hArel : ∀ l : NGenIdx n m s t ι sk tk, ∃ (c : Fin ρ → A) (δ : A), δ ≠ 0 ∧
      ∀ β : bidegIndex n m s t, δ * V β l = ∑ j, c j * V β ↑(eJ.symm j) := by
    intro l
    obtain ⟨g, hg⟩ := hKrel l
    exact exists_cleared_coords (fun β j => V β ↑(eJ.symm j)) (fun β => V β l) g hg
  -- The A-valued minor matrix and its nonzero determinant.
  set Amat : Matrix (Fin ρ) (Fin ρ) A :=
    fun i j => V (e i) ↑(eJ.symm j) with hAmatdef
  have hsubK : (algebraMap A K).mapMatrix Amat = Bmat.submatrix ⇑e id := by
    rw [RingHom.mapMatrix_apply]
    funext i j
    show algebraMap A K (Amat i j) = Bmat (e i) j
    simp only [hAmatdef, hBmatdef, hVKdef]
  have hdetA : Amat.det ≠ 0 := by
    have hdetK : algebraMap A K Amat.det = (Bmat.submatrix ⇑e id).det := by
      rw [← hsubK, RingHom.map_det]
    intro h0
    rw [h0, map_zero] at hdetK
    exact he hdetK.symm
  -- Homogeneous polynomial representatives of the minor entries.
  set Pmat : Matrix (Fin ρ) (Fin ρ) (Poly (o + 1)) := fun i j =>
    bidegCoeff n m (o + 1) s t
      (NGenElem n m (o + 1) s t G sk tk (↑(eJ.symm j) : NGenIdx n m s t ι sk tk).1
        (↑(eJ.symm j) : NGenIdx n m s t ι sk tk).2) (e i) with hPmatdef
  have hPhom : ∀ i j,
      (Pmat i j).IsHomogeneous (uk (↑(eJ.symm j) : NGenIdx n m s t ι sk tk).1) := by
    intro i j
    have h := hVhomog (↑(eJ.symm j) : NGenIdx n m s t ι sk tk) (e i)
    simpa [hPmatdef] using h
  have hPdet : (Pmat.det).IsHomogeneous
      (∑ j, uk (↑(eJ.symm j) : NGenIdx n m s t ι sk tk).1) :=
    isHomogeneous_det Pmat _ hPhom
  have hAmk : (Ideal.Quotient.mk W.ideal).mapMatrix Pmat = Amat := by
    rw [RingHom.mapMatrix_apply]
    funext i j
    show Ideal.Quotient.mk W.ideal (Pmat i j) = Amat i j
    simp only [hPmatdef, hAmatdef, hVdef]
  have hAdet : Amat.det = Ideal.Quotient.mk W.ideal Pmat.det := by
    rw [← hAmk, RingHom.map_det]
  -- The discriminant: homogeneous and outside the base ideal.
  have hg0 : Pmat.det ∉ W.ideal := by
    intro hmem
    exact hdetA (hAdet.trans (Ideal.Quotient.eq_zero_iff_mem.mpr hmem))
  -- Cramer rule over A: det_A clears all denominators uniformly.
  have hCramer : ∀ l : NGenIdx n m s t ι sk tk, ∀ β : bidegIndex n m s t,
      Amat.det * V β l
        = ∑ j, (∑ i, Amat.adjugate j i * V (e i) l) * V β ↑(eJ.symm j) := by
    intro l β
    obtain ⟨g, hg⟩ := hKrel l
    set M : Matrix (Fin ρ) (Fin ρ) K :=
      fun i j => VK (e i) ↑(eJ.symm j) with hMdef
    set w : Fin ρ → K := fun i => VK (e i) l with hwdef
    have hMv : Matrix.mulVec M g = w := by
      funext i
      have hβ := hg (e i)
      show (∑ j, M i j * g j) = w i
      simp only [hMdef, hwdef, hVKdef]
      rw [hβ]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hCramerK : ∀ j, M.det * g j = ∑ i, M.adjugate j i * w i := by
      intro j
      have h1 : (Matrix.mulVec M.adjugate (Matrix.mulVec M g)) j
          = (Matrix.mulVec M.adjugate w) j := by rw [hMv]
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
        Matrix.one_mulVec] at h1
      simpa [Matrix.mulVec_apply_eq_sum, Pi.smul_apply, smul_eq_mul] using h1
    have hfullK : M.det * VK β l
        = ∑ j, (∑ i, M.adjugate j i * w i) * VK β ↑(eJ.symm j) := by
      have hβ' : VK β l = ∑ j, g j * VK β ↑(eJ.symm j) := by
        simpa [hVKdef] using hg β
      calc M.det * VK β l
          = M.det * ∑ j, g j * VK β ↑(eJ.symm j) := by rw [hβ']
        _ = ∑ j, (M.det * g j) * VK β ↑(eJ.symm j) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
        _ = ∑ j, (∑ i, M.adjugate j i * w i) * VK β ↑(eJ.symm j) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [hCramerK j]
    have hMK : (algebraMap A K).mapMatrix Amat = M := by
      rw [RingHom.mapMatrix_apply]
      funext i j
      show algebraMap A K (Amat i j) = M i j
      simp only [hAmatdef, hMdef, hVKdef]
    have hdetK : M.det = algebraMap A K Amat.det := by
      rw [← hMK, RingHom.map_det]
    have hAdjK : M.adjugate = Amat.adjugate.map ⇑(algebraMap A K) := by
      have h := RingHom.map_adjugate (algebraMap A K) Amat
      rw [hMK] at h
      rw [← h, RingHom.mapMatrix_apply]
    have h2 := hfullK
    rw [hdetK, hAdjK] at h2
    simp only [Matrix.map_apply, hVKdef, hwdef] at h2
    have hinj := IsFractionRing.injective A K
    apply hinj
    simp only [map_mul, map_sum]
    exact h2
  -- Part 1: rank, discriminant, and the fibre property.
  set S : ℕ := Fintype.card (bidegIndex n m s t) with hSdef
  refine ⟨S - ρ, ⟨Pmat.det, _, hPdet, hg0, ?_⟩, ?_⟩
  · -- Part 1: over `z` off the discriminant, the fibre dimension is `S - ρ`.
    intro z hzW hne
    obtain ⟨ε, hε⟩ := evalQuotientMk W z hzW
    set R : bidegIndex n m s t → NGenIdx n m s t ι sk tk → ℂ :=
      fun β l => ε (V β l) with hRdef
    have hdetε : ε Amat.det
        = MvPolynomial.eval ((Fin.cons (1 : ℂ) z : Fin (o + 1) → ℂ)) Pmat.det := by
      rw [hAdet]
      exact hε Pmat.det
    have hminor : Matrix.det (fun i j' : Fin ρ => R (e i) ↑(eJ.symm j')) ≠ 0 := by
      have hmap : Matrix.det (fun i j' : Fin ρ => R (e i) ↑(eJ.symm j'))
          = ε Amat.det := by
        have hfun : (fun i j' : Fin ρ => R (e i) ↑(eJ.symm j'))
            = (fun i j' : Fin ρ => ε (Amat i j')) := by
          funext i j'
          simp [hRdef, hAmatdef]
        have hmat : (fun i j' : Fin ρ => ε (Amat i j'))
            = ε.mapMatrix Amat := by
          funext i j'
          show ε (Amat i j') = (ε.mapMatrix Amat) i j'
          rw [RingHom.mapMatrix_apply, Matrix.map_apply]
        rw [hfun, hmat, RingHom.map_det]
      rw [hmap, hdetε]
      exact hne
    have hindep : LinearIndependent ℂ (fun j : ↥J => fun β => R β ↑j) :=
      linearIndependent_of_ne_zero_minor (fun l β => R β l) J eJ e hminor
    have hspanR : ∀ l, (fun β => R β l) ∈ Submodule.span ℂ
        (Set.range (fun j : ↥J => fun β => R β ↑j)) := by
      intro l
      have hcrε : ∀ β, ε Amat.det * R β l
          = ∑ j, (∑ i, ε (Amat.adjugate j i) * ε (V (e i) l))
            * R β ↑(eJ.symm j) := by
        intro β
        have hβ := congrArg ε (hCramer l β)
        simpa [map_mul, map_sum, ← hRdef] using hβ
      have hneε : ε Amat.det ≠ 0 := by
        rw [hdetε]
        exact hne
      have hcomb : (fun β => R β l) = ∑ j : Fin ρ,
          ((ε Amat.det)⁻¹ * (∑ i, ε (Amat.adjugate j i) * ε (V (e i) l)))
            • fun β => R β ↑(eJ.symm j) := by
        funext β
        have hβ := hcrε β
        have e1 : R β l = (ε Amat.det)⁻¹ * (ε Amat.det * R β l) := by
          rw [← mul_assoc, inv_mul_cancel₀ hneε, one_mul]
        rw [e1, hβ, Finset.mul_sum, Finset.sum_apply]
        apply Finset.sum_congr rfl
        intro j _
        rw [Pi.smul_apply, smul_eq_mul]
        ring
      rw [hcomb]
      apply Submodule.sum_mem
      intro j _
      apply Submodule.smul_mem
      apply Submodule.subset_span
      exact ⟨eJ.symm j, rfl⟩
    refine fibre_hilbert_of_relations T z G sk tk hGmem hGx hGy hGspan
      (fun l β => R β l) (fun l => ?_) J hindep hspanR
    rw [fibreSpecialize_NGenElem z T G sk tk hGmem hGx hGy l]
    show ∑ β : bidegIndex n m s t, MvPolynomial.monomial β.1 (R β l) = _
    apply Finset.sum_congr rfl
    intro β _
    congr 1
    simp only [hRdef, hVdef]
    exact hε _
  · -- Part 2: the slope estimate from the Hilbert-function sandwich.
    have hρS : ρ ≤ Fintype.card (bidegIndex n m s t) := by
      have h := hBindep.fintype_card_le_finrank
      rwa [Fintype.card_fin, Module.finrank_fintype_fun_eq_card] at h
    refine triple_slope_of_columns T W hW hTW G sk tk uk hGmem hGx hGy hGz hGspan hρS
      (fun j => ↑(eJ.symm j)) ?_ Pmat.det _ hPdet hg0 ?_
      (fun j l => ∑ i, Amat.adjugate j i * V (e i) l) ?_
    · intro a ha j
      have hK : ∑ j, (algebraMap A K (a j)) • (fun β => Bmat β j) = 0 := by
        funext β
        have h := congrFun ha β
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h ⊢
        have h' := congrArg (algebraMap A K) h
        rw [map_sum, map_zero] at h'
        rw [← h']
        apply Finset.sum_congr rfl
        intro j _
        rw [map_mul]
      have h0 := Fintype.linearIndependent_iff.mp hBindep _ hK j
      exact IsFractionRing.injective A K (by rw [h0, map_zero])
    · intro j
      exact Finset.single_le_sum (f := fun j => uk (↑(eJ.symm j) : NGenIdx n m s t ι sk tk).1)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    · intro l β
      have h := hCramer l β
      rw [hAdet] at h
      exact h

/-! ### Countable generic-point avoidance over ℂ -/

/-- A countably generated ℂ-algebra has countable rank. -/
theorem rank_adjoin_le_aleph0 {B : Type*} [CommRing B] [Algebra ℂ B] (G : Set B)
    (hG : G.Countable) : Module.rank ℂ (Algebra.adjoin ℂ G) ≤ Cardinal.aleph0 := by
  have hspan := Algebra.adjoin_eq_span ℂ G
  have hcl : (Submonoid.closure G : Set B).Countable := by
    rw [Submonoid.closure_eq_mrange]
    haveI : Countable G := hG.to_subtype
    exact Set.countable_range _
  have h1 : Module.rank ℂ (Submodule.span ℂ (Submonoid.closure G : Set B)) ≤
      Cardinal.aleph0 :=
    (rank_span_le _).trans (Cardinal.mk_le_aleph0_iff.mpr hcl.to_subtype)
  rw [← hspan] at h1
  exact h1

/-- A field of countable dimension over ℂ is ℂ (uncountable-dimensionality of ℂ(t)). -/
theorem algebraMap_surjective_of_rank_le {L : Type} [Field L] [Algebra ℂ L]
    (h : Module.rank ℂ L ≤ Cardinal.aleph0) : Function.Surjective (algebraMap ℂ L) := by
  have halg : Algebra.IsAlgebraic ℂ L := by
    constructor
    intro x
    by_contra hx
    have hli := (Transcendental.linearIndependent_sub_inv (F := ℂ) hx).cardinal_lift_le_rank
    simp only [Cardinal.lift_id, Cardinal.mk_complex] at hli
    exact absurd (hli.trans h) (not_le.mpr Cardinal.aleph0_lt_continuum)
  haveI : Algebra.IsIntegral ℂ L := ⟨fun x => (halg.isAlgebraic x).isIntegral⟩
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral.2

/-- A nonzero ℂ-algebra of countable dimension has a ℂ-point. -/
theorem exists_algHom_of_rank_le {B : Type} [CommRing B] [Nontrivial B] [Algebra ℂ B]
    (h : Module.rank ℂ B ≤ Cardinal.aleph0) : Nonempty (B →ₐ[ℂ] ℂ) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  let _ : Field (B ⧸ m) := Ideal.Quotient.field m
  have hL : Module.rank ℂ (B ⧸ m) ≤ Cardinal.aleph0 :=
    (LinearMap.rank_le_of_surjective (Ideal.Quotient.mkₐ ℂ m).toLinearMap
      Ideal.Quotient.mk_surjective).trans h
  have hsurj := algebraMap_surjective_of_rank_le hL
  let e : ℂ ≃ₐ[ℂ] B ⧸ m := AlgEquiv.ofBijective (Algebra.ofId ℂ (B ⧸ m))
    ⟨(algebraMap ℂ (B ⧸ m)).injective, hsurj⟩
  exact ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ m)⟩

/-- L-avoid. Over ℂ, countably many functions not vanishing identically on an irreducible
variety have a common non-vanishing point on it (localize at all of them; the resulting
countably generated ℂ-algebra has a ℂ-point by the Nullstellensatz for countable rank). -/
theorem exists_point_avoiding {n : ℕ} (V : AffineVariety n) (hV : V.IsIrreducible)
    (g : ℕ → Poly n) (hg : ∀ i, g i ∉ V.ideal) :
    ∃ z ∈ V.points, ∀ i, MvPolynomial.aeval z (g i) ≠ 0 := by
  classical
  haveI : V.ideal.IsPrime := hV
  set A := Poly n ⧸ V.ideal with hA
  set q : Poly n →ₐ[ℂ] A := Ideal.Quotient.mkₐ ℂ V.ideal with hq
  set Ms : Submonoid A := Submonoid.closure (Set.range fun i => q (g i)) with hMs_def
  have hMs : Ms ≤ nonZeroDivisors A := by
    apply Submonoid.closure_le.mpr
    rintro _ ⟨i, rfl⟩
    apply mem_nonZeroDivisors_of_ne_zero
    intro h
    exact hg i (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hdom : IsDomain (Localization Ms) := IsLocalization.isDomain_localization hMs
  set φB : A →ₐ[ℂ] Localization Ms := IsScalarTower.toAlgHom ℂ A (Localization Ms) with hφB_def
  set G : Set (Localization Ms) := Set.range (fun i : Fin n => φB (q (MvPolynomial.X i))) ∪
    Set.range (fun i : ℕ => IsLocalization.mk' (Localization Ms) (1 : A)
      (⟨q (g i), Submonoid.subset_closure ⟨i, rfl⟩⟩ : Ms)) with hG_def
  have hGc : G.Countable := (Set.countable_range _).union (Set.countable_range _)
  have hφB : ∀ f : Poly n, φB (q f) ∈ Algebra.adjoin ℂ G := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C c => simpa using (Algebra.adjoin ℂ G).algebraMap_mem c
    | add f1 f2 h1 h2 => simpa using Subalgebra.add_mem _ h1 h2
    | mul_X f i h1 =>
      simpa using Subalgebra.mul_mem _ h1 (Algebra.subset_adjoin (Or.inl ⟨i, rfl⟩))
  have hinv : ∀ s : Ms, IsLocalization.mk' (Localization Ms) (1 : A) s ∈
      Algebra.adjoin ℂ G := by
    rintro ⟨s, hs⟩
    induction hs using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩)
    | one => simpa using (Algebra.adjoin ℂ G).one_mem
    | mul x y hx hy ihx ihy =>
      have he : IsLocalization.mk' (Localization Ms) (1 : A)
          (⟨x * y, Submonoid.mul_mem _ hx hy⟩ : Ms) =
          IsLocalization.mk' (Localization Ms) (1 : A) (⟨x, hx⟩ : Ms) *
            IsLocalization.mk' (Localization Ms) (1 : A) (⟨y, hy⟩ : Ms) := by
        rw [← IsLocalization.mk'_mul, mul_one]
        rfl
      rw [he]
      exact Subalgebra.mul_mem _ ihx ihy
  have htop : Algebra.adjoin ℂ G = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective Ms x
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
    show IsLocalization.mk' (Localization Ms) (Ideal.Quotient.mk V.ideal f) s ∈ _
    have hsplit : IsLocalization.mk' (Localization Ms) (Ideal.Quotient.mk V.ideal f) s =
        φB (q f) * IsLocalization.mk' (Localization Ms) (1 : A) s := by
      rw [IsLocalization.mk'_eq_mul_mk'_one]
      rfl
    rw [hsplit]
    exact Subalgebra.mul_mem _ (hφB f) (hinv s)
  have hrankB : @Module.rank ℂ (Localization Ms) _ _ Algebra.toModule ≤ Cardinal.aleph0 := by
    have h := rank_adjoin_le_aleph0 G hGc
    rw [htop] at h
    have he : Module.rank ℂ (⊤ : Subalgebra ℂ (Localization Ms)) =
        @Module.rank ℂ (Localization Ms) _ _ Algebra.toModule :=
      (Subalgebra.topEquiv : (⊤ : Subalgebra ℂ (Localization Ms)) ≃ₐ[ℂ] _).toLinearEquiv.rank_eq
    rw [he] at h
    exact h
  obtain ⟨χ⟩ := exists_algHom_of_rank_le (B := Localization Ms) hrankB
  let z : Point n := fun i => χ (φB (q (MvPolynomial.X i)))
  have hψ : ∀ f : Poly n, χ (φB (q f)) = MvPolynomial.aeval z f := by
    intro f
    have hh : (χ.comp φB).comp q = MvPolynomial.aeval z := by
      apply MvPolynomial.algHom_ext
      intro i
      simp [z]
    exact congrArg (fun F : Poly n →ₐ[ℂ] ℂ => F f) hh
  refine ⟨z, ?_, ?_⟩
  · intro f hf
    rw [← hψ]
    have h0 : q f = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hf
    rw [h0, map_zero, map_zero]
  · intro i hi
    have hunit : IsUnit (φB (q (g i))) :=
      IsLocalization.map_units (Localization Ms) (⟨q (g i), Submonoid.subset_closure ⟨i, rfl⟩⟩ : Ms)
    have hL := hunit.map χ
    rw [hψ, hi] at hL
    exact not_isUnit_zero hL

end
end DistinctDistances.TrackB.PointIntegral
