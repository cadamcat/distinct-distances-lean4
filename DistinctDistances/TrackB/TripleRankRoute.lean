import DistinctDistances.TrackB.TripleRankInfra
import DistinctDistances.TrackB.TripleRankTrunc
import DistinctDistances.TrackB.TripleRankKernelRanks

/-!
B13 redesign (lane m-b-hilb, 2026-10-10): a TRUE decomposition of
`DistinctDistances.TrackB.triple_rank_identity`.

The incidence `Z` is the projective bundle `P(L)` over the base `B`, with
`L_b = {(x0, z) : (x0, ι_d z) ∈ ℂ·(t, y)}`.  Two rank recursions compute its
section ranks:

* Euler (P1, exact): multiplication by the fiber coordinate `c`
  (`(x0, ι_d z) = c (t, y)` on `Z`) realised by the tridegree-`(1,0,1)`
  generators `π = (x0 d_i, (ι_d z)_k)` (`π_k = c p_k` on `Z`) gives
  `triple(s+1,t,u+1) = triple(s,t+1,u) + rank(I_Z + (π))(s+1,t,u+1)`.
* Kernel (P2, P3): up to `d`-torsion `I_Z + (π)` is the kernel-bundle ideal
  `J_K = I_B S + (x0) + (ι_d z)`, whose ranks satisfy the `(2,0,1)`
  recursion with the complete-intersection rank of `e` deformed forms
  `h_k = (ι_d z)_k - x0 c_k q`, `q = Σ c_k d_k` a non-zero-divisor on `B`
  (`Σ d_k h_k = - x0 q²`).

Every regularity statement is "up to `d`-torsion" (rank equality for large
direction degree `s`); no global regular sequences are claimed (they fail on
non-Cohen–Macaulay bases).  The arithmetic assembly (P5) and the `m ≥ e`
truncation (P4) are pure combinatorics.  See the lane NOTES for the
mathematics and the sanity checks (`e = 1`, `e = 2`).
-/

namespace DistinctDistances.TrackB
namespace TripleRankRoute

set_option autoImplicit false
noncomputable section
open scoped BigOperators

attribute [local instance] MvPolynomial.weightedGradedAlgebra

section Parts

variable {e : ℕ} (C : SkewCoordinates e) (Γ : AffineVariety (skewDim e + e))
  (H : Poly (skewDim e))

/-- `tripleHilbert` is the section rank of the incidence vanishing ideal. -/
theorem tripleHilbert_eq_secRank (s t u : ℕ) :
    tripleHilbert (incidenceTriples C Γ H) s t u = secRank (incIdeal C Γ H) s t u := by
  exact tripleHilbert_eq_secRank' C Γ H s t u

/-- (P0) Point degree zero: every base point has a nonzero fiber vector
(`(v_i, e_i^* ∧ y)` with `d_i ≠ 0`), so degree-`(s,t,0)` incidence sections are
base sections. -/
theorem triple_degree_zero (hres : ResolutionBase C Γ H) (s t : ℕ) :
    tripleHilbert (incidenceTriples C Γ H) s t 0 = secRank (baseIdeal C Γ H) s t 0 := by
  exact triple_degree_zero' C Γ H hres s t

/-- (P1) Euler step (exact).  `g ↦ Σ π_k g_k` for `g = Σ p_k g_k` equals `c · g` on the
incidence, is injective (fiber density: move `x` along `(v_i, e_i^* ∧ y)`, which changes
`c` by `d_i ≠ 0`) and has image the `π`-part. -/
theorem euler_step (s t u : ℕ) :
    secRank (eulerIdeal C Γ H) (s + 1) t (u + 1) +
        tripleHilbert (incidenceTriples C Γ H) s (t + 1) u =
      tripleHilbert (incidenceTriples C Γ H) (s + 1) t (u + 1) := by
  exact euler_step' C Γ H s t u

/-- (P2) The Euler cokernel ideal agrees with the kernel-bundle ideal up to direction
torsion.  `d_i · kernelIdeal ⊆ eulerIdeal`; and for `f ∈ I_Z` of point degree `u`,
`d_i^u f ∈ kernelIdeal` via `x0 ↦ 0`, `z ↦ ρ_i z = d_i z − e_i^* ∧ ι_d z` (`ι_d ρ_i z = 0`).
Finite generation turns elementwise torsion into rank equality for large `s`. -/
theorem euler_kernel_compare (hres : ResolutionBase C Γ H) :
    ∃ N : ℕ, ∀ s t u : ℕ, N ≤ s →
      secRank (eulerIdeal C Γ H) s t u = secRank (kernelIdeal C Γ H) s t u := by
  exact euler_kernel_compare' C Γ H hres

/-- (P3₀) Point degree zero of the kernel-bundle ideal. -/
theorem kernel_degree_zero (s t : ℕ) :
    secRank (kernelIdeal C Γ H) s t 0 = secRank (baseIdeal C Γ H) s t 0 := by
  exact kernel_degree_zero' C Γ H s t

/-- (P3) Kernel recursion via the `x0`-deformation `h_k = (ι_d z)_k − x0 c_k q`
(`q = Σ c_k d_k` a non-zero-divisor modulo the base, `Σ d_k h_k = −x0 q²`):
with `ZK = rank(kernelIdeal)` and `G = rank(I_B S + (h))` (complete intersection up to
torsion), `ZK(ν) − ZK(ν − (2,0,1)) = G(ν) − G(ν − (0,0,1))`, i.e. the stated
recursion.  Chart model: `I_B S + (w_k, k ≠ i) + (x0 q²)` via substitutions `α, β`
with `β ∘ α = α ∘ β = d_i`-scaling of the point variables. -/
theorem kernel_recursion :
    ∃ N : ℕ, ∀ s t u : ℕ, N ≤ s →
      (secRank (kernelIdeal C Γ H) (s + 2) t (u + 1) : ℤ) =
        secRank (kernelIdeal C Γ H) s t u +
          ∑ k ∈ Finset.range (e + 1), (-1 : ℤ) ^ k * (e.choose k : ℤ) *
            (baseRankZ C Γ H (s + 2 - k) t ((u : ℤ) + 1 - k) -
              baseRankZ C Γ H (s + 2 - k) t ((u : ℤ) - k)) := by
  obtain ⟨c, hc⟩ := exists_generic_q (liftedParameterBase C Γ H)
  exact kernel_recursion_complete C Γ H c hc

end Parts

/-- (P4) Truncation of the Koszul sum above the rank: for a base polynomial of total
degree `< e`, the inner `m`-bracket of `triple_rank_identity` vanishes for `m ≥ e`.
(Generating function `(1−z)^{e−1}(1+aw)^e/((1+(2a−a²)w)(1+bw))`, `w = z/(1−z)`, with
nilpotent difference operators `a, b`.) -/
theorem koszul_truncation (e : ℕ) (P : BaseHilbertPolynomial) (hP : P.totalDegree + 1 ≤ e)
    (m : ℕ) (hm : e ≤ m) (s t : ℚ) :
    (∑ δ ∈ Finset.range 2, ∑ k ∈ Finset.range (e + 1),
      ∑ l ∈ Finset.range (m + 1), ∑ β ∈ Finset.range (m + 1),
        if δ + k + l + β = m then
          ((-1 : ℚ) ^ (l + β) * (e.choose k : ℚ)) *
            MvPolynomial.eval (Fin.cons (s - k - 2 * l - β) (fun _ : Fin 1 => t + β)) P
        else 0) = 0 :=
  TripleRankTrunc.truncation e P hP m hm s t

/-- Zero extension of `P(s,t) · C(u+n, n)` to negative point degree. -/
def zext (P : ℕ → ℕ → ℤ) (n s t : ℕ) (u : ℤ) : ℤ :=
  if u < 0 then 0 else P s t * (((u.toNat + n).choose n : ℕ) : ℤ)

/-- `β = 0` bracket. -/
def kz (e : ℕ) (P : ℕ → ℕ → ℤ) (m s t : ℕ) : ℤ :=
  ∑ δ ∈ Finset.range 2, ∑ k ∈ Finset.range (e + 1), ∑ l ∈ Finset.range (m + 1),
    if δ + k + l = m then ((-1 : ℤ) ^ l * (e.choose k : ℤ)) * P (s - k - 2 * l) t else 0

/-- `l = β = 0` bracket. -/
def kz0 (e : ℕ) (P : ℕ → ℕ → ℤ) (m s t : ℕ) : ℤ :=
  ∑ δ ∈ Finset.range 2, ∑ k ∈ Finset.range (e + 1),
    if δ + k = m then (e.choose k : ℤ) * P (s - k) t else 0

/-- Full bracket (frozen shape). -/
def kf (e : ℕ) (P : ℕ → ℕ → ℤ) (m s t : ℕ) : ℤ :=
  ∑ δ ∈ Finset.range 2, ∑ k ∈ Finset.range (e + 1),
    ∑ l ∈ Finset.range (m + 1), ∑ β ∈ Finset.range (m + 1),
      if δ + k + l + β = m then
        ((-1 : ℤ) ^ (l + β) * (e.choose k : ℤ)) * P (s - k - 2 * l - β) (t + β)
      else 0

theorem kz_zero (e : ℕ) (P : ℕ → ℕ → ℤ) (s t : ℕ) : kz e P 0 s t = P s t := by
  rcases Nat.eq_zero_or_pos e with he | he
  · subst he; simp [kz, Finset.sum_range_succ]
  · simp [kz, Finset.sum_range_succ, he, Nat.pos_iff_ne_zero.mp he]

theorem kz0_zero (e : ℕ) (P : ℕ → ℕ → ℤ) (s t : ℕ) : kz0 e P 0 s t = P s t := by
  rcases Nat.eq_zero_or_pos e with he | he
  · subst he; simp [kz0, Finset.sum_range_succ]
  · simp [kz0, Finset.sum_range_succ, he, Nat.pos_iff_ne_zero.mp he]

/-- Peel off `l = 0`. -/
theorem kz_succ (e : ℕ) (P : ℕ → ℕ → ℤ) (m s t : ℕ) :
    kz e P (m + 1) (s + 2) t = kz0 e P (m + 1) (s + 2) t - kz e P m s t := by
  unfold kz kz0
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro δ _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_range_succ']
  have h0 : (if δ + k + 0 = m + 1 then ((-1 : ℤ) ^ 0 * (e.choose k : ℤ)) * P (s + 2 - k - 2 * 0) t
      else 0) = if δ + k = m + 1 then (e.choose k : ℤ) * P (s + 2 - k) t else 0 := by
    simp
  have h1 : (∑ l ∈ Finset.range (m + 1), if δ + k + (l + 1) = m + 1 then
      ((-1 : ℤ) ^ (l + 1) * (e.choose k : ℤ)) * P (s + 2 - k - 2 * (l + 1)) t else 0) =
      -∑ l ∈ Finset.range (m + 1), if δ + k + l = m then
        ((-1 : ℤ) ^ l * (e.choose k : ℤ)) * P (s - k - 2 * l) t else 0 := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro l _
    have harg : s + 2 - k - 2 * (l + 1) = s - k - 2 * l := by omega
    rw [harg]
    by_cases h : δ + k + l = m
    · rw [if_pos (by omega), if_pos h]; ring
    · rw [if_neg (by omega), if_neg h]; ring
  rw [h0, h1]
  ring

/-- Recombination of the `(2,0,1)` step. -/
theorem kz_step (e n : ℕ) (P : ℕ → ℕ → ℤ) (u s t : ℕ) :
    ∑ m ∈ Finset.range (u + 2), (-1 : ℤ) ^ m * kz e P m (s + 2) t *
        (((u + 1 - m + n).choose n : ℕ) : ℤ) =
      ∑ m ∈ Finset.range (u + 2), (-1 : ℤ) ^ m * kz0 e P m (s + 2) t *
        (((u + 1 - m + n).choose n : ℕ) : ℤ) +
      ∑ m ∈ Finset.range (u + 1), (-1 : ℤ) ^ m * kz e P m s t *
        (((u - m + n).choose n : ℕ) : ℤ) := by
  rw [Finset.sum_range_succ' _ (u + 1), Finset.sum_range_succ' _ (u + 1)]
  simp only [kz_zero, kz0_zero, kz_succ]
  have h : ∀ m ∈ Finset.range (u + 1),
      (-1 : ℤ) ^ (m + 1) * (kz0 e P (m + 1) (s + 2) t - kz e P m s t) *
          (((u + 1 - (m + 1) + n).choose n : ℕ) : ℤ) =
        (-1 : ℤ) ^ (m + 1) * kz0 e P (m + 1) (s + 2) t *
          (((u + 1 - (m + 1) + n).choose n : ℕ) : ℤ) +
        (-1 : ℤ) ^ m * kz e P m s t * (((u - m + n).choose n : ℕ) : ℤ) := by
    intro m _
    have : u + 1 - (m + 1) = u - m := by omega
    rw [this]; ring
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib]
  ring

/-- The `l = β = 0` sum is the zero-extended Koszul difference. -/
theorem kz0_sum (e n : ℕ) (P : ℕ → ℕ → ℤ) (u s t : ℕ) :
    ∑ m ∈ Finset.range (u + 2), (-1 : ℤ) ^ m * kz0 e P m (s + 2) t *
        (((u + 1 - m + n).choose n : ℕ) : ℤ) =
      ∑ k ∈ Finset.range (e + 1), (-1 : ℤ) ^ k * (e.choose k : ℤ) *
        (zext P n (s + 2 - k) t ((u : ℤ) + 1 - k) - zext P n (s + 2 - k) t ((u : ℤ) - k)) := by
  unfold kz0
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  rw [Finset.sum_comm]
  conv_lhs => enter [2]; rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  simp only [mul_ite, ite_mul, mul_zero, zero_mul]
  rw [Finset.sum_ite_eq, Finset.sum_ite_eq]
  simp only [Finset.mem_range]
  unfold zext
  by_cases h1 : k ≤ u
  · have hA : ¬ ((u : ℤ) + 1 - k < 0) := by omega
    have hB : ¬ ((u : ℤ) - k < 0) := by omega
    rw [if_pos (by omega), if_pos (by omega), if_neg hA, if_neg hB]
    have e1 : ((u : ℤ) + 1 - k).toNat = u + 1 - (0 + k) := by omega
    have e2 : ((u : ℤ) - k).toNat = u + 1 - (1 + k) := by omega
    rw [e1, e2]
    simp only [zero_add, pow_add, pow_one]
    ring
  · by_cases h2 : k = u + 1
    · subst h2
      have hA : ¬ ((u : ℤ) + 1 - ↑(u + 1) < 0) := by push_cast; omega
      have hB : ((u : ℤ) - ↑(u + 1) < 0) := by push_cast; omega
      rw [if_pos (by omega), if_neg (by omega), if_neg hA, if_pos hB]
      have e1 : ((u : ℤ) + 1 - ↑(u + 1)).toNat = u + 1 - (0 + (u + 1)) := by push_cast; omega
      rw [e1]
      simp only [zero_add]
      ring
    · have hA : ((u : ℤ) + 1 - k < 0) := by omega
      have hB : ((u : ℤ) - k < 0) := by omega
      rw [if_neg (by omega), if_neg (by omega), if_pos hA, if_pos hB]
      ring

/-- Closed form of the kernel ranks. -/
theorem zk_closed (e n N : ℕ) (ZK : ℕ → ℕ → ℕ → ℤ) (P : ℕ → ℕ → ℤ)
    (hZ0 : ∀ s t, ZK s t 0 = P s t)
    (hZ : ∀ s t u, N ≤ s → ZK (s + 2) t (u + 1) = ZK s t u +
      ∑ k ∈ Finset.range (e + 1), (-1 : ℤ) ^ k * (e.choose k : ℤ) *
        (zext P n (s + 2 - k) t ((u : ℤ) + 1 - k) - zext P n (s + 2 - k) t ((u : ℤ) - k))) :
    ∀ u s t : ℕ, N + 2 * u ≤ s →
      ZK s t u = ∑ m ∈ Finset.range (u + 1), (-1 : ℤ) ^ m * kz e P m s t *
        (((u - m + n).choose n : ℕ) : ℤ) := by
  intro u
  induction u with
  | zero =>
    intro s t _
    simp [hZ0, kz_zero]
  | succ u ih =>
    intro s t hs
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 2 := ⟨s - 2, by omega⟩
    rw [hZ s' t u (by omega), ih s' t (by omega), kz_step, kz0_sum]
    ring

/-- Triple ranks as a diagonal sum of kernel ranks. -/
theorem tr_diag (N : ℕ) (Tr ZK : ℕ → ℕ → ℕ → ℤ) (P : ℕ → ℕ → ℤ)
    (hT0 : ∀ s t, Tr s t 0 = P s t)
    (hT : ∀ s t u, N ≤ s → Tr (s + 1) t (u + 1) = Tr s (t + 1) u + ZK (s + 1) t (u + 1))
    (hZ0 : ∀ s t, ZK s t 0 = P s t) :
    ∀ u s t : ℕ, N + u ≤ s →
      Tr s t u = ∑ β ∈ Finset.range (u + 1), ZK (s - β) (t + β) (u - β) := by
  intro u
  induction u with
  | zero =>
    intro s t _
    simp [hT0, hZ0]
  | succ u ih =>
    intro s t hs
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    rw [hT s' t u (by omega), ih s' (t + 1) (by omega), Finset.sum_range_succ' _ (u + 1)]
    simp only [Nat.sub_zero, add_zero]
    have hsum : ∑ β ∈ Finset.range (u + 1), ZK (s' - β) (t + 1 + β) (u - β) =
        ∑ β ∈ Finset.range (u + 1), ZK (s' + 1 - (β + 1)) (t + (β + 1)) (u + 1 - (β + 1)) := by
      apply Finset.sum_congr rfl
      intro β _
      have h1 : s' + 1 - (β + 1) = s' - β := by omega
      have h2 : t + 1 + β = t + (β + 1) := by omega
      have h3 : u + 1 - (β + 1) = u - β := by omega
      rw [h1, h2, h3]
    rw [hsum]

/-- The full bracket is the alternating diagonal sum of `β = 0` brackets. -/
theorem kf_eq (e : ℕ) (P : ℕ → ℕ → ℤ) (m s t : ℕ) :
    kf e P m s t = ∑ β ∈ Finset.range (m + 1), (-1 : ℤ) ^ β * kz e P (m - β) (s - β) (t + β) := by
  unfold kf kz
  -- step A: inner `l`-sums over the full range
  have hA : ∀ β ∈ Finset.range (m + 1), ∀ δ k : ℕ,
      (∑ l ∈ Finset.range (m - β + 1), (-1 : ℤ) ^ β *
        (if δ + k + l = m - β then ((-1 : ℤ) ^ l * (e.choose k : ℤ)) *
          P (s - β - k - 2 * l) (t + β) else 0)) =
      ∑ l ∈ Finset.range (m + 1), (if δ + k + l + β = m then
        ((-1 : ℤ) ^ (l + β) * (e.choose k : ℤ)) * P (s - k - 2 * l - β) (t + β) else 0) := by
    intro β hβ δ k
    have hβm : β ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hβ)
    rw [← Finset.sum_subset (Finset.range_subset_range.mpr (by omega : m - β + 1 ≤ m + 1))]
    · apply Finset.sum_congr rfl
      intro l _
      have harg : s - β - k - 2 * l = s - k - 2 * l - β := by omega
      rw [harg]
      by_cases h : δ + k + l = m - β
      · rw [if_pos h, if_pos (by omega)]; ring
      · rw [if_neg h, if_neg (by omega)]; ring
    · intro l _ hl
      have : ¬ (δ + k + l + β = m) := by
        intro h; apply hl; rw [Finset.mem_range]; omega
      rw [if_neg this]
  symm
  simp only [Finset.mul_sum]
  calc ∑ β ∈ Finset.range (m + 1), ∑ δ ∈ Finset.range 2, ∑ k ∈ Finset.range (e + 1),
        ∑ l ∈ Finset.range (m - β + 1), (-1 : ℤ) ^ β *
          (if δ + k + l = m - β then ((-1 : ℤ) ^ l * (e.choose k : ℤ)) *
            P (s - β - k - 2 * l) (t + β) else 0)
      = ∑ β ∈ Finset.range (m + 1), ∑ δ ∈ Finset.range 2, ∑ k ∈ Finset.range (e + 1),
        ∑ l ∈ Finset.range (m + 1), (if δ + k + l + β = m then
          ((-1 : ℤ) ^ (l + β) * (e.choose k : ℤ)) * P (s - k - 2 * l - β) (t + β) else 0) := by
        apply Finset.sum_congr rfl
        intro β hβ
        apply Finset.sum_congr rfl
        intro δ _
        apply Finset.sum_congr rfl
        intro k _
        exact hA β hβ δ k
    _ = ∑ δ ∈ Finset.range 2, ∑ k ∈ Finset.range (e + 1),
        ∑ l ∈ Finset.range (m + 1), ∑ β ∈ Finset.range (m + 1), (if δ + k + l + β = m then
          ((-1 : ℤ) ^ (l + β) * (e.choose k : ℤ)) * P (s - k - 2 * l - β) (t + β) else 0) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro δ _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.sum_comm]

/-- (P5a) Arithmetic assembly of the two recursions (zero-extended below point degree 0). -/
theorem assembly_core (e n N : ℕ) (Tr ZK : ℕ → ℕ → ℕ → ℤ) (P : ℕ → ℕ → ℤ)
    (hT0 : ∀ s t, Tr s t 0 = P s t)
    (hT : ∀ s t u, N ≤ s → Tr (s + 1) t (u + 1) = Tr s (t + 1) u + ZK (s + 1) t (u + 1))
    (hZ0 : ∀ s t, ZK s t 0 = P s t)
    (hZ : ∀ s t u, N ≤ s → ZK (s + 2) t (u + 1) = ZK s t u +
      ∑ k ∈ Finset.range (e + 1), (-1 : ℤ) ^ k * (e.choose k : ℤ) *
        (zext P n (s + 2 - k) t ((u : ℤ) + 1 - k) - zext P n (s + 2 - k) t ((u : ℤ) - k))) :
    ∀ u s t : ℕ, N + 3 * u + 2 * e + 2 ≤ s →
      Tr s t u = ∑ m ∈ Finset.range (u + 1), (-1 : ℤ) ^ m *
        (∑ δ ∈ Finset.range 2, ∑ k ∈ Finset.range (e + 1),
          ∑ l ∈ Finset.range (m + 1), ∑ β ∈ Finset.range (m + 1),
            if δ + k + l + β = m then
              ((-1 : ℤ) ^ (l + β) * (e.choose k : ℤ)) * P (s - k - 2 * l - β) (t + β)
            else 0) *
        (((u - m + n).choose n : ℕ) : ℤ) := by
  intro u s t hs
  rw [tr_diag N Tr ZK P hT0 hT hZ0 u s t (by omega)]
  have hZc : ∀ β ∈ Finset.range (u + 1), ZK (s - β) (t + β) (u - β) =
      ∑ m' ∈ Finset.range (u - β + 1), (-1 : ℤ) ^ m' * kz e P m' (s - β) (t + β) *
        (((u - β - m' + n).choose n : ℕ) : ℤ) := by
    intro β hβ
    have hβu : β ≤ u := Nat.lt_succ_iff.mp (Finset.mem_range.mp hβ)
    exact zk_closed e n N ZK P hZ0 hZ (u - β) (s - β) (t + β) (by omega)
  rw [Finset.sum_congr rfl hZc]
  have hflip := Finset.sum_range_diag_flip (u + 1) (fun β m' => (-1 : ℤ) ^ m' *
    kz e P m' (s - β) (t + β) * (((u - β - m' + n).choose n : ℕ) : ℤ))
  have hrange : ∀ β ∈ Finset.range (u + 1), u - β + 1 = u + 1 - β := by
    intro β hβ
    have := Finset.mem_range.mp hβ
    omega
  rw [Finset.sum_congr rfl (fun β hβ => by rw [hrange β hβ]), ← hflip]
  apply Finset.sum_congr rfl
  intro m hm
  have hmu : m ≤ u := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  change _ = (-1 : ℤ) ^ m * kf e P m s t * _
  rw [kf_eq, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro β hβ
  have hβm : β ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hβ)
  have h1 : u - β - (m - β) = u - m := by omega
  rw [h1]
  have h2 : (-1 : ℤ) ^ m = (-1 : ℤ) ^ (m - β) * (-1 : ℤ) ^ β := by
    rw [← pow_add, Nat.sub_add_cancel hβm]
  have h3 : (-1 : ℤ) ^ β * (-1 : ℤ) ^ β = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  rw [h2]
  linear_combination (-((-1 : ℤ) ^ (m - β) * kz e P (m - β) (s - β) (t + β) *
    (((u - m + n).choose n : ℕ) : ℤ))) * h3

open MvPolynomial in
/-- (P5b) Two trivariate polynomials agreeing on a cone region
`{u ≥ U, s ≥ a + b u, t ≥ c}` are equal. -/
theorem polynomial_eq_of_cone (F G : MvPolynomial (Fin 3) ℚ) (U a b c : ℕ)
    (h : ∀ s t u : ℕ, U ≤ u → a + b * u ≤ s → c ≤ t →
      MvPolynomial.eval (Fin.cons (s : ℚ) (Fin.cons (t : ℚ) (fun _ : Fin 1 => (u : ℚ)))) F =
        MvPolynomial.eval (Fin.cons (s : ℚ) (Fin.cons (t : ℚ) (fun _ : Fin 1 => (u : ℚ)))) G) :
    F = G := by
  classical
  let φ : Fin 3 → MvPolynomial (Fin 3) ℚ := ![C ((a : ℚ) + b * U) + C (b : ℚ) * X 2 + X 0,
    C (c : ℚ) + X 1, C (U : ℚ) + X 2]
  let ψ : Fin 3 → MvPolynomial (Fin 3) ℚ := ![X 0 - C (b : ℚ) * X 2 - C (a : ℚ),
    X 1 - C (c : ℚ), X 2 - C (U : ℚ)]
  have hinv : ∀ P : MvPolynomial (Fin 3) ℚ, bind₁ ψ (bind₁ φ P) = P := by
    intro P
    rw [bind₁_bind₁]
    have hid : (fun i => bind₁ ψ (φ i)) = (X : Fin 3 → MvPolynomial (Fin 3) ℚ) := by
      funext i
      fin_cases i <;> simp [φ, ψ] <;> ring
    rw [hid, bind₁_X_left]
    rfl
  have hφ : bind₁ φ F = bind₁ φ G := by
    let S : Set ℚ := Set.range (fun n : ℕ => (n : ℚ))
    have hS : S.Infinite := Set.infinite_range_of_injective Nat.cast_injective
    apply MvPolynomial.funext_set (fun _ : Fin 3 => S) (fun _ => hS)
    intro x hx
    have hex (i : Fin 3) : ∃ n : ℕ, (n : ℚ) = x i := hx i (Set.mem_univ i)
    choose d hd using hex
    have key := h (a + b * U + b * d 2 + d 0) (c + d 1) (U + d 2) (Nat.le_add_right _ _)
      (by nlinarith) (Nat.le_add_right _ _)
    have hev : ∀ P : MvPolynomial (Fin 3) ℚ, eval x (bind₁ φ P) =
        eval (Fin.cons (((a + b * U + b * d 2 + d 0 : ℕ)) : ℚ)
          (Fin.cons ((c + d 1 : ℕ) : ℚ) (fun _ : Fin 1 => ((U + d 2 : ℕ) : ℚ)))) P := by
      intro P
      have h1 := MvPolynomial.aeval_bind₁ (R := ℚ) (S := ℚ) x φ P
      simp only [MvPolynomial.aeval_eq_eval] at h1
      rw [h1]
      have hpt : (fun i => eval x (φ i)) = (Fin.cons (((a + b * U + b * d 2 + d 0 : ℕ)) : ℚ)
          (Fin.cons ((c + d 1 : ℕ) : ℚ) (fun _ : Fin 1 => ((U + d 2 : ℕ) : ℚ))) : Fin 3 → ℚ) := by
        funext i
        fin_cases i
        · simp [φ, ← hd]
        · simp [φ, ← hd]
        · simp [φ, ← hd]; rfl
      rw [hpt]
    rw [hev, hev]
    exact key
  rw [← hinv F, ← hinv G, hφ]



/-- The frozen right-hand side of `triple_rank_identity`. -/
def frozenRHS {e : ℕ} (C : SkewCoordinates e) (Γ : AffineVariety (skewDim e + e))
    (H : Poly (skewDim e)) (s t u : ℕ) : ℚ :=
  ∑ m ∈ Finset.range e, (-1 : ℚ) ^ m *
    (∑ delta ∈ Finset.range 2, ∑ k ∈ Finset.range (e + 1),
      ∑ l ∈ Finset.range (m + 1), ∑ beta ∈ Finset.range (m + 1),
        if delta + k + l + beta = m then
          ((-1 : ℚ) ^ (l + beta) * (e.choose k : ℚ)) *
            ((pairHilbert (liftedParameterBase C Γ H) (s - k - 2 * l - beta) (t + beta) : ℕ) : ℚ)
        else 0) *
    ((Nat.choose (u - m + e.choose 2) (e.choose 2) : ℕ) : ℚ)

/-- (P5) `triple_rank_identity` from the parts.  External inputs: the base degree bound
(`parameterBaseHilbert_degree` with `j ≤ 1`), the pullback product ranks
(`FiberEquations.pairPullback_section_product`) and the Koszul evaluation
(`KoszulEval.koszul_eval_eq_pair_ranks`). -/
theorem triple_rank_of_parts {e : ℕ} (C : SkewCoordinates e)
    (Γ : AffineVariety (skewDim e + e)) (H : Poly (skewDim e))
    (hdeg : (parameterBaseHilbert C Γ H).totalDegree + 1 ≤ e)
    (hres : ResolutionBase C Γ H)
    (hpull : ∀ s t u : ℕ, secRank (baseIdeal C Γ H) s t u =
      pairHilbert (liftedParameterBase C Γ H) s t * (skewDim e + 1).multichoose u)
    (hkos : ∀ NP : ℕ, (∀ a b : ℕ, NP ≤ a → NP ≤ b →
        MvPolynomial.eval (Fin.cons (a : ℚ) (fun _ : Fin 1 => (b : ℚ)))
          (parameterBaseHilbert C Γ H) = ((pairHilbert (liftedParameterBase C Γ H) a b : ℕ) : ℚ)) →
      ∀ s t u : ℕ, NP + 2 * e ≤ s → NP ≤ t → e ≤ u →
        MvPolynomial.eval (Fin.cons (s : ℚ) (Fin.cons (t : ℚ) (fun _ : Fin 1 => (u : ℚ))))
          (koszulIncidenceHilbert e (parameterBaseHilbert C Γ H)) = frozenRHS C Γ H s t u) :
    ∃ N : ℕ, ∀ s t u : ℕ, N ≤ s → N ≤ t → N ≤ u →
      ((tripleHilbert (incidenceTriples C Γ H) s t u : ℕ) : ℚ) = frozenRHS C Γ H s t u := by
  classical
  obtain ⟨NP, hP⟩ := (parameterBaseHilbert_eventually_polynomial C Γ H).choose_spec
  obtain ⟨NC, hC0⟩ := (compactIncidenceHilbert_eventually_polynomial C Γ H).choose_spec
  have hC : ∀ s t u : ℕ, NC ≤ s → NC ≤ t → NC ≤ u →
      MvPolynomial.eval (Fin.cons (s : ℚ) (Fin.cons (t : ℚ) (fun _ : Fin 1 => (u : ℚ))))
        (compactIncidenceHilbert C Γ H) = (tripleHilbert (incidenceTriples C Γ H) s t u : ℚ) :=
    hC0
  obtain ⟨N2, h2⟩ := euler_kernel_compare C Γ H hres
  obtain ⟨N3, h3⟩ := kernel_recursion C Γ H
  have hPq : ∀ a b : ℕ, NP ≤ a → NP ≤ b →
      MvPolynomial.eval (Fin.cons (a : ℚ) (fun _ : Fin 1 => (b : ℚ)))
        (parameterBaseHilbert C Γ H) = ((pairHilbert (liftedParameterBase C Γ H) a b : ℕ) : ℚ) :=
    fun a b ha hb => hP a b ha hb
  let n := skewDim e
  let P : ℕ → ℕ → ℤ := fun s t => (pairHilbert (liftedParameterBase C Γ H) s t : ℤ)
  let Tr : ℕ → ℕ → ℕ → ℤ := fun s t u => (tripleHilbert (incidenceTriples C Γ H) s t u : ℤ)
  let ZK : ℕ → ℕ → ℕ → ℤ := fun s t u => (secRank (kernelIdeal C Γ H) s t u : ℤ)
  have hmc : ∀ u : ℕ, (n + 1).multichoose u = (u + n).choose n := by
    intro u
    rw [Nat.multichoose_eq, show n + 1 + u - 1 = u + n by omega]
    exact Nat.choose_symm_add
  have hbaseZ : ∀ (s t : ℕ) (u : ℤ), baseRankZ C Γ H s t u = zext P n s t u := by
    intro s t u
    unfold baseRankZ zext
    split_ifs with hu
    · rfl
    · rw [hpull, hmc]
      push_cast
      rfl
  have hT0 : ∀ s t, Tr s t 0 = P s t := by
    intro s t
    simp only [Tr, P]
    rw [triple_degree_zero C Γ H hres, hpull]
    simp
  have hT : ∀ s t u, max N2 N3 ≤ s →
      Tr (s + 1) t (u + 1) = Tr s (t + 1) u + ZK (s + 1) t (u + 1) := by
    intro s t u hs
    have e1 := euler_step C Γ H s t u
    have e2 := h2 (s + 1) t (u + 1) (by omega)
    simp only [Tr, ZK]
    rw [← e1, e2]
    push_cast
    ring
  have hZ0 : ∀ s t, ZK s t 0 = P s t := by
    intro s t
    simp only [ZK, P]
    rw [kernel_degree_zero, hpull]
    simp
  have hZ : ∀ s t u, max N2 N3 ≤ s → ZK (s + 2) t (u + 1) = ZK s t u +
      ∑ k ∈ Finset.range (e + 1), (-1 : ℤ) ^ k * (e.choose k : ℤ) *
        (zext P n (s + 2 - k) t ((u : ℤ) + 1 - k) - zext P n (s + 2 - k) t ((u : ℤ) - k)) := by
    intro s t u hs
    have := h3 s t u (by omega)
    simp only [hbaseZ] at this
    exact this
  have hcore := assembly_core e n (max N2 N3) Tr ZK P hT0 hT hZ0 hZ
  -- the region where the triple ranks equal the Koszul evaluation
  let A := max N2 N3 + 2 * e + 2 + NP + e + NC
  have hregion : ∀ s t u : ℕ, max e NC ≤ u → A + 3 * u ≤ s → max NP NC ≤ t →
      MvPolynomial.eval (Fin.cons (s : ℚ) (Fin.cons (t : ℚ) (fun _ : Fin 1 => (u : ℚ))))
          (compactIncidenceHilbert C Γ H) =
        MvPolynomial.eval (Fin.cons (s : ℚ) (Fin.cons (t : ℚ) (fun _ : Fin 1 => (u : ℚ))))
          (koszulIncidenceHilbert e (parameterBaseHilbert C Γ H)) := by
    intro s t u hu hs ht
    have hue : e ≤ u := le_trans (le_max_left _ _) hu
    rw [hC s t u (by omega) (by omega) (le_trans (le_max_right _ _) hu),
      hkos NP hPq s t u (by omega) (le_trans (le_max_left _ _) ht) hue]
    have h1 := hcore u s t (by omega)
    have h1q : ((tripleHilbert (incidenceTriples C Γ H) s t u : ℕ) : ℚ) =
        ((∑ m ∈ Finset.range (u + 1), (-1 : ℤ) ^ m * kf e P m s t *
          (((u - m + n).choose n : ℕ) : ℤ) : ℤ) : ℚ) := by
      have : (Tr s t u : ℚ) = _ := congrArg (Int.cast : ℤ → ℚ) h1
      simpa [Tr, kf] using this
    rw [h1q, ← Finset.sum_range_add_sum_Ico _ (show e ≤ u + 1 by omega)]
    have hzero : ∀ m ∈ Finset.Ico e (u + 1), kf e P m s t = 0 := by
      intro m hm
      obtain ⟨hem, hmu⟩ := Finset.mem_Ico.mp hm
      have hq := koszul_truncation e (parameterBaseHilbert C Γ H) hdeg m hem (s : ℚ) (t : ℚ)
      have hcast : (kf e P m s t : ℚ) = 0 := by
        rw [← hq]
        unfold kf
        push_cast
        apply Finset.sum_congr rfl; intro δ _
        apply Finset.sum_congr rfl; intro k hk
        apply Finset.sum_congr rfl; intro l hl
        apply Finset.sum_congr rfl; intro β hβ
        have hk' : k ≤ e := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        have hl' : l ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
        have hβ' : β ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hβ)
        split_ifs with hc
        · congr 1
          have hle : k + 2 * l + β ≤ s := by omega
          have hval := hPq (s - k - 2 * l - β) (t + β) (by omega) (by omega)
          simp only [P]
          push_cast
          rw [← hval]
          have hpt : (Fin.cons (((s - k - 2 * l - β : ℕ)) : ℚ)
              (fun _ : Fin 1 => ((t + β : ℕ) : ℚ)) : Fin 2 → ℚ) =
              Fin.cons ((s : ℚ) - k - 2 * l - β) (fun _ : Fin 1 => (t : ℚ) + β) := by
            funext i
            refine Fin.cases ?_ (fun j => ?_) i
            · simp only [Fin.cons_zero]
              rw [show s - k - 2 * l - β = s - (k + 2 * l + β) by omega, Nat.cast_sub hle]
              push_cast
              ring
            · simp only [Fin.cons_succ]
              push_cast
              ring
          rw [hpt]
        · rfl
      exact_mod_cast hcast
    rw [Finset.sum_eq_zero (s := Finset.Ico e (u + 1)) (fun m hm => by rw [hzero m hm]; ring),
      add_zero]
    unfold frozenRHS
    push_cast
    apply Finset.sum_congr rfl
    intro m _
    simp only [kf, P, n, skewDim]
    push_cast
    rfl
  have hpoly := polynomial_eq_of_cone (compactIncidenceHilbert C Γ H)
    (koszulIncidenceHilbert e (parameterBaseHilbert C Γ H)) (max e NC) A 3 (max NP NC)
    (fun s t u hu hs ht => hregion s t u hu (by omega) ht)
  refine ⟨max NC (NP + 2 * e) + e, ?_⟩
  intro s t u hs ht hu
  rw [← hC s t u (by omega) (by omega) (by omega), hpoly]
  exact hkos NP hPq s t u (by omega) (by omega) (by omega)

end
end TripleRankRoute
end DistinctDistances.TrackB
