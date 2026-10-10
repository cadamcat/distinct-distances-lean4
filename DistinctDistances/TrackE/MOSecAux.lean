import DistinctDistances.TrackE.CommonImageInputs
import DistinctDistances.TrackD.SecantsLabelAlgebra
import DistinctDistances.TrackD.ProductGeometry
import DistinctDistances.TrackD.RationalImages
import DistinctDistances.TrackE.CommonIsolation
import DistinctDistances.TrackE.CommonMixedInputs
import DistinctDistances.TrackE.CommonSourceSections
import DistinctDistances.TrackE.CommonPointLifting
import DistinctDistances.TrackE.CommonSectionInputs
import DistinctDistances.TrackE.CommonNormalizationTangents
import DistinctDistances.TrackA.Hilbert
import DistinctDistances.TrackA.PoolingSupport
import DistinctDistances.TrackA.ADepthAux

/-! Cleared secant pullbacks of affine-linear section equations
(`sc:retained-products.depth`, sparse-cones.tex:143-156).

For a fixed chart `i₀`, secant numerators `f` (degree ≤2) and denominator
`g` (degree ≤1), the cleared pullback of an affine-linear target equation
`L(z) = ∑ aᵢ zᵢ + c` is `N(p) = ∑ aᵢ fᵢ(p) + c g(p)` (degree ≤2).
At a chart preimage (`g(p) ≠ 0`, `q = φ(p)`), `N(p) = g(p) L(q)`.
-/

namespace DistinctDistances.SparseCones
open scoped BigOperators Classical
noncomputable section
variable {d : ℕ}

/-- Local secant denominator bound (copy of `MODegAux.secantDenominator_degree_le`,
kept here to avoid an import cycle: `MODegAux` will import this file). -/
theorem secantDenominator_degree_le_aux (i₀ : Fin d) :
    (TrackD.secantChartDenominator (d := d) i₀).totalDegree ≤ 1 := by
  unfold TrackD.secantChartDenominator
  calc (MvPolynomial.X (finSumFinEquiv (Sum.inr i₀)) -
        MvPolynomial.X (finSumFinEquiv (Sum.inl i₀)) : Poly (d + d)).totalDegree
      ≤ max (MvPolynomial.X (finSumFinEquiv (Sum.inr i₀)) : Poly (d + d)).totalDegree
        (MvPolynomial.X (finSumFinEquiv (Sum.inl i₀)) : Poly (d + d)).totalDegree :=
        MvPolynomial.totalDegree_sub _ _
    _ ≤ 1 := by
        apply max_le <;> simp [MvPolynomial.totalDegree_X]

/-- Local secant numerator bound (copy of `MODegAux.secantNumerator_degree_le`). -/
theorem secantNumerator_degree_le_aux (i₀ : Fin d) (j : Fin (d + d)) :
    (TrackD.secantChartNumerator (d := d) i₀ j).totalDegree ≤ 2 := by
  obtain ⟨q, rfl⟩ := finSumFinEquiv.surjective j
  unfold TrackD.secantChartNumerator
  rw [Equiv.symm_apply_apply]
  cases q with
  | inl k =>
    simp only [Sum.elim_inl]
    calc (MvPolynomial.X (finSumFinEquiv (Sum.inl k)) *
          TrackD.secantChartDenominator i₀ : Poly (d + d)).totalDegree
        ≤ (MvPolynomial.X (finSumFinEquiv (Sum.inl k)) : Poly (d + d)).totalDegree +
          (TrackD.secantChartDenominator i₀).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
      _ ≤ 1 + 1 := by
          apply Nat.add_le_add _ (secantDenominator_degree_le_aux i₀)
          simp [MvPolynomial.totalDegree_X]
      _ = 2 := rfl
  | inr k =>
    simp only [Sum.elim_inr]
    calc (MvPolynomial.X (finSumFinEquiv (Sum.inr k)) -
        MvPolynomial.X (finSumFinEquiv (Sum.inl k)) : Poly (d + d)).totalDegree
        ≤ max (MvPolynomial.X (finSumFinEquiv (Sum.inr k)) : Poly (d + d)).totalDegree
          (MvPolynomial.X (finSumFinEquiv (Sum.inl k)) : Poly (d + d)).totalDegree :=
          MvPolynomial.totalDegree_sub _ _
      _ ≤ 2 := by
          apply max_le <;> (calc _ ≤ (1 : ℕ) := by simp [MvPolynomial.totalDegree_X]
            _ ≤ 2 := by omega)

/-- Cleared pullback of one normalization fiber equation through the fixed
secant chart: `∑ aᵢ fᵢ + c g` with `f` secant numerators, `g` denominator. -/
def clearedPullback (i₀ : Fin d) {e : ℕ} (φZ : AffineProjection (d + d) e)
    (t : Point e) (j : Fin e) : Poly (d + d) :=
  (∑ i : Fin (d + d), MvPolynomial.C (φZ.linear (Pi.single i 1) j) *
    TrackD.secantChartNumerator i₀ i) +
    MvPolynomial.C (φZ.offset j - t j) * TrackD.secantChartDenominator i₀

theorem clearedPullback_degree_le (i₀ : Fin d) {e : ℕ}
    (φZ : AffineProjection (d + d) e) (t : Point e) (j : Fin e) :
    (clearedPullback i₀ φZ t j).totalDegree ≤ 2 := by
  classical
  unfold clearedPullback
  have hf : ∀ i : Fin (d + d),
      (MvPolynomial.C (φZ.linear (Pi.single i 1) j) *
        TrackD.secantChartNumerator i₀ i : Poly (d + d)).totalDegree ≤ 2 := by
    intro i
    have hmul := MvPolynomial.totalDegree_mul
      (MvPolynomial.C (φZ.linear (Pi.single i 1) j) : Poly (d + d))
      (TrackD.secantChartNumerator i₀ i)
    have hC : (MvPolynomial.C (φZ.linear (Pi.single i 1) j) : Poly (d + d)).totalDegree ≤ 0 := by
      rw [MvPolynomial.totalDegree_C]
    have hn := secantNumerator_degree_le_aux (d := d) i₀ i
    omega
  have hsum : (∑ i : Fin (d + d), MvPolynomial.C (φZ.linear (Pi.single i 1) j) *
      TrackD.secantChartNumerator i₀ i : Poly (d + d)).totalDegree ≤ 2 := by
    apply MvPolynomial.totalDegree_finsetSum_le
    intro i _
    exact hf i
  have hg : (MvPolynomial.C (φZ.offset j - t j) *
      TrackD.secantChartDenominator i₀ : Poly (d + d)).totalDegree ≤ 2 := by
    have hmul := MvPolynomial.totalDegree_mul
      (MvPolynomial.C (φZ.offset j - t j) : Poly (d + d))
      (TrackD.secantChartDenominator i₀)
    have hC : (MvPolynomial.C (φZ.offset j - t j) : Poly (d + d)).totalDegree ≤ 0 := by
      rw [MvPolynomial.totalDegree_C]
    have hn := secantDenominator_degree_le_aux (d := d) i₀
    omega
  calc ((∑ i : Fin (d + d), MvPolynomial.C (φZ.linear (Pi.single i 1) j) *
        TrackD.secantChartNumerator i₀ i : Poly (d + d)) +
      MvPolynomial.C (φZ.offset j - t j) * TrackD.secantChartDenominator i₀).totalDegree
      ≤ max ((∑ i : Fin (d + d), MvPolynomial.C (φZ.linear (Pi.single i 1) j) *
        TrackD.secantChartNumerator i₀ i : Poly (d + d)).totalDegree)
        ((MvPolynomial.C (φZ.offset j - t j) *
          TrackD.secantChartDenominator i₀ : Poly (d + d)).totalDegree) :=
        MvPolynomial.totalDegree_add _ _
    _ ≤ 2 := max_le hsum hg

/-- Linear maps expand in the standard basis (used for pullback evaluation). -/
theorem linear_apply_sum {m : ℕ} (φ : AffineProjection (d + d) m)
    (q : Point (d + d)) (j : Fin m) :
    φ.linear q j = ∑ i : Fin (d + d), φ.linear (Pi.single i 1) j * q i := by
  have hq : q = ∑ i : Fin (d + d), q i • (Pi.single i (1 : ℂ) : Point (d + d)) := by
    simpa using ((Pi.basisFun ℂ (Fin (d + d))).sum_repr q).symm
  have hlin : φ.linear q j = ∑ i : Fin (d + d), q i * φ.linear (Pi.single i 1) j := by
    have h := congrFun (congrArg φ.linear hq) j
    rw [map_sum] at h
    simpa [map_smul, Pi.smul_apply, smul_eq_mul] using h
  calc φ.linear q j = ∑ i : Fin (d + d), q i * φ.linear (Pi.single i 1) j := hlin
    _ = ∑ i : Fin (d + d), φ.linear (Pi.single i 1) j * q i := by
        apply Finset.sum_congr rfl
        intro i _
        ring

/-- Pullback of the normalization linear part evaluates as the linear form. -/
theorem pullback_fiber_eval {e : ℕ}
    (φZ : AffineProjection (d + d) e) (t : Point e) (j : Fin e)
    (q : Point (d + d)) :
    MvPolynomial.eval q (φZ.pullback (MvPolynomial.X j) - MvPolynomial.C (t j)) =
      (∑ i : Fin (d + d), φZ.linear (Pi.single i 1) j * q i) +
        (φZ.offset j - t j) := by
  have hpull : MvPolynomial.eval q (φZ.pullback (MvPolynomial.X j)) =
      (∑ i : Fin (d + d), φZ.linear (Pi.single i 1) j * q i) + φZ.offset j := by
    have h := φZ.eval_pullback q (MvPolynomial.X j)
    simp only [MvPolynomial.aeval_X, MvPolynomial.aeval_eq_eval] at h
    rw [h]
    simp only [AffineProjection.apply, Pi.add_apply]
    congr 1
    exact linear_apply_sum φZ q j
  simp only [map_sub, MvPolynomial.eval_C, hpull]
  ring

/-- Evaluation: at a chart point (`g(p) ≠ 0`) with `q = φ(p)`,
`Nⱼ(p) = g(p) Lⱼ(q)`. Hence `Nⱼ(p) = 0 ↔ Lⱼ(q) = 0`. -/
theorem clearedPullback_eval_ne (i₀ : Fin d) {e : ℕ}
    (φZ : AffineProjection (d + d) e) (t : Point e) (j : Fin e)
    (p : Point (d + d))
    (hg : MvPolynomial.eval p (TrackD.secantChartDenominator i₀) ≠ 0) :
    MvPolynomial.eval p (clearedPullback i₀ φZ t j) =
      MvPolynomial.eval p (TrackD.secantChartDenominator i₀) *
        MvPolynomial.eval (TrackD.rationalPoint
          (TrackD.secantChartNumerator i₀)
          (TrackD.secantChartDenominator i₀) p)
          (φZ.pullback (MvPolynomial.X j) - MvPolynomial.C (t j)) := by
  classical
  unfold clearedPullback
  simp only [map_add, map_sum, map_mul, MvPolynomial.eval_C]
  have hq : ∀ i : Fin (d + d),
      MvPolynomial.eval p (TrackD.secantChartNumerator i₀ i) =
        MvPolynomial.eval p (TrackD.secantChartDenominator i₀) *
          (TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
            (TrackD.secantChartDenominator i₀) p i) := by
    intro i
    simp only [TrackD.rationalPoint]
    rw [mul_comm]
    exact (div_mul_cancel₀ _ hg).symm
  have hLq := pullback_fiber_eval (d := d) φZ t j
    (TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
      (TrackD.secantChartDenominator i₀) p)
  rw [hLq]
  have hsum : (∑ i : Fin (d + d), φZ.linear (Pi.single i 1) j *
      MvPolynomial.eval p (TrackD.secantChartNumerator i₀ i)) =
      MvPolynomial.eval p (TrackD.secantChartDenominator i₀) *
        (∑ i : Fin (d + d), φZ.linear (Pi.single i 1) j *
          (TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
            (TrackD.secantChartDenominator i₀) p i)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hq i]
    ring
  rw [hsum]
  ring

theorem clearedPullback_zero_iff (i₀ : Fin d) {e : ℕ}
    (φZ : AffineProjection (d + d) e) (t : Point e) (j : Fin e)
    (p : Point (d + d))
    (hg : MvPolynomial.eval p (TrackD.secantChartDenominator i₀) ≠ 0) :
    MvPolynomial.eval p (clearedPullback i₀ φZ t j) = 0 ↔
      MvPolynomial.eval (TrackD.rationalPoint
        (TrackD.secantChartNumerator i₀)
        (TrackD.secantChartDenominator i₀) p)
        (φZ.pullback (MvPolynomial.X j) - MvPolynomial.C (t j)) = 0 := by
  rw [clearedPullback_eval_ne i₀ φZ t j p hg]
  exact ⟨fun h => (mul_eq_zero.mp h).resolve_left hg,
    fun h => by rw [h, mul_zero]⟩

/-- Differential of a constant multiple: `d(C(c) f) = c • df`
(via Leibniz + `d(C(c)) = 0`). -/
theorem differential_C_mul {n : ℕ} (c : ℂ) (f : Poly n) (x : Point n) :
    differential (MvPolynomial.C c * f) x = c • differential f x := by
  have hmul := TrackD.differential_mul (MvPolynomial.C c) f x
  have hC : differential (MvPolynomial.C c : Poly n) x = 0 :=
    TrackD.differential_C c x
  have heval : MvPolynomial.eval x (MvPolynomial.C c : Poly n) = c := by
    simp [MvPolynomial.eval_C]
  rw [hmul, hC, heval]
  simp [add_comm]

/-- Differential of a finset sum is the sum of differentials. -/
theorem differential_finsetSum {n : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → Poly n) (x : Point n) :
    differential (∑ i ∈ s, f i) x = ∑ i ∈ s, differential (f i) x := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    have h0 : (0 : Poly n) = MvPolynomial.C (0 : ℂ) := by simp
    rw [h0]
    exact TrackD.differential_C 0 x
  | insert a s has ih =>
    rw [Finset.sum_insert has, Finset.sum_insert has]
    rw [TrackD.differential_add _ _ x, ih]

/-- Differential of the cleared pullback at `p`:
`dNⱼ = ∑ aᵢ dfᵢ + c dg` with the same coefficients as `Lⱼ`. -/
theorem clearedPullback_differential (i₀ : Fin d) {e : ℕ}
    (φZ : AffineProjection (d + d) e) (t : Point e) (j : Fin e)
    (p : Point (d + d)) :
    differential (clearedPullback i₀ φZ t j) p =
      (∑ i : Fin (d + d), (φZ.linear (Pi.single i 1) j) •
        differential (TrackD.secantChartNumerator i₀ i) p) +
        (φZ.offset j - t j) • differential (TrackD.secantChartDenominator i₀) p := by
  classical
  unfold clearedPullback
  rw [TrackD.differential_add]
  congr 1
  · rw [differential_finsetSum]
    apply Finset.sum_congr rfl
    intro i _
    exact differential_C_mul _ _ _
  · exact differential_C_mul _ _ _

/-- Differential of a normalization fiber equation at any point:
`dLⱼ = ∑ aᵢ dXᵢ` (constant, independent of the base point). -/
theorem pullback_fiber_differential {e : ℕ}
    (φZ : AffineProjection (d + d) e) (t : Point e) (j : Fin e)
    (q : Point (d + d)) :
    differential (φZ.pullback (MvPolynomial.X j) - MvPolynomial.C (t j)) q =
      ∑ i : Fin (d + d), (φZ.linear (Pi.single i 1) j) •
        differential (MvPolynomial.X i : Poly (d + d)) q := by
  classical
  have hsub := TrackD.differential_sub (φZ.pullback (MvPolynomial.X j))
    (MvPolynomial.C (t j)) q
  have hC : differential (MvPolynomial.C (t j) : Poly (d + d)) q = 0 :=
    TrackD.differential_C _ _
  rw [hsub, hC, sub_zero]
  have hpull : differential (φZ.pullback (MvPolynomial.X j)) q =
      ∑ i : Fin (d + d), (φZ.linear (Pi.single i 1) j) •
        differential (MvPolynomial.X i : Poly (d + d)) q := by
    have hbase : ∀ v : Point (d + d),
        differential (φZ.pullback (MvPolynomial.X j)) q v =
          ∑ i : Fin (d + d), φZ.linear (Pi.single i 1) j * v i := by
      intro v
      have hrat := common_affine_projection_rational_differential φZ q
      have hpi : TrackD.rationalDifferential
          (fun i => φZ.pullback (MvPolynomial.X i)) 1 q =
          LinearMap.pi (fun i => differential (φZ.pullback (MvPolynomial.X i)) q) := by
        unfold TrackD.rationalDifferential
        have heval1 : MvPolynomial.eval q (1 : Poly (d + d)) = 1 := by simp
        have hdiff1 : differential (1 : Poly (d + d)) q = 0 := by
          have h1 : (1 : Poly (d + d)) = MvPolynomial.C (1 : ℂ) := (map_one _).symm
          rw [h1]
          exact TrackD.differential_C 1 q
        simp [heval1, hdiff1]
      have hpiEq : LinearMap.pi (fun i => differential (φZ.pullback (MvPolynomial.X i)) q) =
          φZ.linear := by
        rw [← hpi]
        exact hrat
      have hcongr := LinearMap.congr_fun hpiEq v
      have hj := congrFun hcongr j
      simp only [LinearMap.pi_apply] at hj
      rw [hj]
      exact linear_apply_sum φZ v j
    apply LinearMap.ext
    intro v
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [hbase v]
    simp only [TrackD.differential_X, LinearMap.proj_apply]
  rw [hpull]

/-- Pointwise quotient-rule relation at a fiber preimage:
`dNⱼ(v) = g(p) * dLⱼ(dφ(v))`, using `Lⱼ(q) = 0`.
Stated pointwise (plain `*`, no linear-map `•`) so every rewrite matches
syntactically; per-term field identities use `g≠0`, sums handled by
unconditional `Finset` lemmas, closing by pure-ring `linear_combination`. -/
theorem clearedPullback_pointwise (i₀ : Fin d) {e : ℕ}
    (φZ : AffineProjection (d + d) e) (t : Point e) (j : Fin e)
    (p v : Point (d + d))
    (hg : MvPolynomial.eval p (TrackD.secantChartDenominator i₀) ≠ 0)
    (hQvan : MvPolynomial.eval (TrackD.rationalPoint
      (TrackD.secantChartNumerator i₀)
      (TrackD.secantChartDenominator i₀) p)
      (φZ.pullback (MvPolynomial.X j) - MvPolynomial.C (t j)) = 0) :
    differential (clearedPullback i₀ φZ t j) p v =
      MvPolynomial.eval p (TrackD.secantChartDenominator i₀) *
        (((differential (φZ.pullback (MvPolynomial.X j) - MvPolynomial.C (t j))
          (TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
            (TrackD.secantChartDenominator i₀) p)).comp
          (TrackD.rationalDifferential (TrackD.secantChartNumerator i₀)
            (TrackD.secantChartDenominator i₀) p)) v) := by
  classical
  have hN := clearedPullback_differential i₀ φZ t j p
  have hL := pullback_fiber_differential (d := d) φZ t j
    (TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
      (TrackD.secantChartDenominator i₀) p)
  have hQdiv : (∑ i : Fin (d + d), φZ.linear (Pi.single i 1) j *
      (MvPolynomial.eval p (TrackD.secantChartNumerator i₀ i) /
        MvPolynomial.eval p (TrackD.secantChartDenominator i₀))) +
      (φZ.offset j - t j) = 0 := by
    have h := pullback_fiber_eval (d := d) φZ t j
      (TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
        (TrackD.secantChartDenominator i₀) p)
    rw [hQvan] at h
    simp only [TrackD.rationalPoint] at h
    exact h.symm
  have hNv : differential (clearedPullback i₀ φZ t j) p v =
      (∑ i : Fin (d + d), φZ.linear (Pi.single i 1) j *
        differential (TrackD.secantChartNumerator i₀ i) p v) +
        (φZ.offset j - t j) *
          differential (TrackD.secantChartDenominator i₀) p v := by
    simp only [hN, LinearMap.add_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul]
  have hLv : ∀ w : Point (d + d),
      differential (φZ.pullback (MvPolynomial.X j) - MvPolynomial.C (t j))
        (TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
          (TrackD.secantChartDenominator i₀) p) w =
        ∑ i : Fin (d + d), φZ.linear (Pi.single i 1) j * w i := by
    intro w
    simp only [hL, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      TrackD.differential_X, LinearMap.proj_apply]
  have hphiv : ∀ i : Fin (d + d),
      TrackD.rationalDifferential (TrackD.secantChartNumerator i₀)
        (TrackD.secantChartDenominator i₀) p v i =
        differential (TrackD.secantChartNumerator i₀ i) p v /
          MvPolynomial.eval p (TrackD.secantChartDenominator i₀) -
        (MvPolynomial.eval p (TrackD.secantChartNumerator i₀ i) /
          MvPolynomial.eval p (TrackD.secantChartDenominator i₀) ^ 2) *
          differential (TrackD.secantChartDenominator i₀) p v := by
    intro i
    simp only [TrackD.rationalDifferential, LinearMap.pi_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul, inv_mul_eq_div]
  have hcomp : ((differential (φZ.pullback (MvPolynomial.X j) - MvPolynomial.C (t j))
      (TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
        (TrackD.secantChartDenominator i₀) p)).comp
      (TrackD.rationalDifferential (TrackD.secantChartNumerator i₀)
        (TrackD.secantChartDenominator i₀) p)) v =
      ∑ i : Fin (d + d), φZ.linear (Pi.single i 1) j *
        (differential (TrackD.secantChartNumerator i₀ i) p v /
          MvPolynomial.eval p (TrackD.secantChartDenominator i₀) -
        (MvPolynomial.eval p (TrackD.secantChartNumerator i₀ i) /
          MvPolynomial.eval p (TrackD.secantChartDenominator i₀) ^ 2) *
          differential (TrackD.secantChartDenominator i₀) p v) := by
    simp only [LinearMap.comp_apply, hLv, hphiv]
  have hper : ∀ i : Fin (d + d),
      MvPolynomial.eval p (TrackD.secantChartDenominator i₀) *
        (φZ.linear (Pi.single i 1) j *
          (differential (TrackD.secantChartNumerator i₀ i) p v /
            MvPolynomial.eval p (TrackD.secantChartDenominator i₀) -
          (MvPolynomial.eval p (TrackD.secantChartNumerator i₀ i) /
            MvPolynomial.eval p (TrackD.secantChartDenominator i₀) ^ 2) *
            differential (TrackD.secantChartDenominator i₀) p v)) =
        φZ.linear (Pi.single i 1) j *
          differential (TrackD.secantChartNumerator i₀ i) p v -
        φZ.linear (Pi.single i 1) j *
          (MvPolynomial.eval p (TrackD.secantChartNumerator i₀ i) /
            MvPolynomial.eval p (TrackD.secantChartDenominator i₀)) *
          differential (TrackD.secantChartDenominator i₀) p v := by
    intro i
    field_simp
  rw [hNv, hcomp, Finset.mul_sum]
  simp only [hper, Finset.sum_sub_distrib, ←Finset.sum_mul]
  linear_combination (differential (TrackD.secantChartDenominator i₀) p v) * hQdiv

/-- Linear-map form of the quotient rule: at a fiber preimage (`Lⱼ(q) = 0`),
`dNⱼ = g(p) • (dLⱼ ∘ dφ)`. -/
theorem clearedPullback_linear_comp (i₀ : Fin d) {e : ℕ}
    (φZ : AffineProjection (d + d) e) (t : Point e) (j : Fin e)
    (p : Point (d + d))
    (hg : MvPolynomial.eval p (TrackD.secantChartDenominator i₀) ≠ 0)
    (hQvan : MvPolynomial.eval (TrackD.rationalPoint
      (TrackD.secantChartNumerator i₀)
      (TrackD.secantChartDenominator i₀) p)
      (φZ.pullback (MvPolynomial.X j) - MvPolynomial.C (t j)) = 0) :
    differential (clearedPullback i₀ φZ t j) p =
      MvPolynomial.eval p (TrackD.secantChartDenominator i₀) •
        ((differential (φZ.pullback (MvPolynomial.X j) - MvPolynomial.C (t j))
          (TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
            (TrackD.secantChartDenominator i₀) p)).comp
          (TrackD.rationalDifferential (TrackD.secantChartNumerator i₀)
            (TrackD.secantChartDenominator i₀) p)) := by
  apply LinearMap.ext
  intro v
  rw [LinearMap.smul_apply, smul_eq_mul]
  exact clearedPullback_pointwise i₀ φZ t j p v hg hQvan

/-- Transverse propagation: if the secant differential is injective on the
source tangent, maps the source tangent into the image tangent, and the
target fiber differentials are injective on the image tangent, then the
cleared pullbacks are injective on the source tangent
(`dN = g • dL ∘ dφ` with `g ≠ 0`, proved by elements to avoid
`domRestrict`/`comp` algebra). -/
theorem transverse_clearedPullback_injective (i₀ : Fin d) {m : ℕ}
    (S Z : AffineVariety (d + d))
    (φZ : AffineProjection (d + d) m) (t : Point m)
    (p : Point (d + d))
    (hg : MvPolynomial.eval p (TrackD.secantChartDenominator i₀) ≠ 0)
    (hvan : ∀ j, MvPolynomial.eval (TrackD.rationalPoint
      (TrackD.secantChartNumerator i₀)
      (TrackD.secantChartDenominator i₀) p)
      (φZ.pullback (MvPolynomial.X j) - MvPolynomial.C (t j)) = 0)
    (hDmap : ∀ v ∈ S.tangentSpace p,
      TrackD.rationalDifferential (TrackD.secantChartNumerator i₀)
        (TrackD.secantChartDenominator i₀) p v ∈
        Z.tangentSpace (TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
          (TrackD.secantChartDenominator i₀) p))
    (hDinj : Function.Injective
      ((TrackD.rationalDifferential (TrackD.secantChartNumerator i₀)
        (TrackD.secantChartDenominator i₀) p).domRestrict (S.tangentSpace p)))
    (hLinj : Function.Injective
      ((LinearMap.pi (fun j => differential (φZ.pullback (MvPolynomial.X j) -
        MvPolynomial.C (t j)) (TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
          (TrackD.secantChartDenominator i₀) p))).domRestrict
        (Z.tangentSpace (TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
          (TrackD.secantChartDenominator i₀) p)))) :
    Function.Injective
      ((LinearMap.pi (fun j => differential (clearedPullback i₀ φZ t j) p)).domRestrict
        (S.tangentSpace p)) := by
  classical
  have hN : ∀ j, differential (clearedPullback i₀ φZ t j) p =
      MvPolynomial.eval p (TrackD.secantChartDenominator i₀) •
        ((differential (φZ.pullback (MvPolynomial.X j) - MvPolynomial.C (t j))
          (TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
            (TrackD.secantChartDenominator i₀) p)).comp
          (TrackD.rationalDifferential (TrackD.secantChartNumerator i₀)
            (TrackD.secantChartDenominator i₀) p)) :=
    fun j => clearedPullback_linear_comp i₀ φZ t j p hg (hvan j)
  intro a b hab
  have hcoord : ∀ j, differential (φZ.pullback (MvPolynomial.X j) -
      MvPolynomial.C (t j)) (TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
        (TrackD.secantChartDenominator i₀) p)
        (TrackD.rationalDifferential (TrackD.secantChartNumerator i₀)
          (TrackD.secantChartDenominator i₀) p a.val) =
      differential (φZ.pullback (MvPolynomial.X j) - MvPolynomial.C (t j))
        (TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
          (TrackD.secantChartDenominator i₀) p)
        (TrackD.rationalDifferential (TrackD.secantChartNumerator i₀)
          (TrackD.secantChartDenominator i₀) p b.val) := by
    intro j
    have haj : (LinearMap.pi (fun j => differential (clearedPullback i₀ φZ t j) p)) a.val j =
        (LinearMap.pi (fun j => differential (clearedPullback i₀ φZ t j) p)) b.val j :=
      congrFun hab j
    simp only [LinearMap.pi_apply, hN, LinearMap.smul_apply, smul_eq_mul,
      LinearMap.comp_apply] at haj
    exact mul_left_cancel₀ hg haj
  have hF : (LinearMap.pi (fun j => differential (φZ.pullback (MvPolynomial.X j) -
      MvPolynomial.C (t j)) (TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
        (TrackD.secantChartDenominator i₀) p)))
        (TrackD.rationalDifferential (TrackD.secantChartNumerator i₀)
          (TrackD.secantChartDenominator i₀) p a.val) =
      (LinearMap.pi (fun j => differential (φZ.pullback (MvPolynomial.X j) -
      MvPolynomial.C (t j)) (TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
        (TrackD.secantChartDenominator i₀) p)))
        (TrackD.rationalDifferential (TrackD.secantChartNumerator i₀)
          (TrackD.secantChartDenominator i₀) p b.val) := by
    funext j
    simp only [LinearMap.pi_apply]
    exact hcoord j
  have haT := hDmap a.val a.property
  have hbT := hDmap b.val b.property
  have hsub : ((LinearMap.pi (fun j => differential (φZ.pullback (MvPolynomial.X j) -
      MvPolynomial.C (t j)) (TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
        (TrackD.secantChartDenominator i₀) p))).domRestrict
      (Z.tangentSpace (TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
        (TrackD.secantChartDenominator i₀) p)))
      ⟨TrackD.rationalDifferential (TrackD.secantChartNumerator i₀)
        (TrackD.secantChartDenominator i₀) p a.val, haT⟩ =
      ((LinearMap.pi (fun j => differential (φZ.pullback (MvPolynomial.X j) -
      MvPolynomial.C (t j)) (TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
        (TrackD.secantChartDenominator i₀) p))).domRestrict
      (Z.tangentSpace (TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
        (TrackD.secantChartDenominator i₀) p)))
      ⟨TrackD.rationalDifferential (TrackD.secantChartNumerator i₀)
        (TrackD.secantChartDenominator i₀) p b.val, hbT⟩ :=
    hF
  have hDeq := hLinj hsub
  have hDval : TrackD.rationalDifferential (TrackD.secantChartNumerator i₀)
      (TrackD.secantChartDenominator i₀) p a.val =
      TrackD.rationalDifferential (TrackD.secantChartNumerator i₀)
        (TrackD.secantChartDenominator i₀) p b.val :=
    congrArg Subtype.val hDeq
  have hDrest : (TrackD.rationalDifferential (TrackD.secantChartNumerator i₀)
      (TrackD.secantChartDenominator i₀) p).domRestrict (S.tangentSpace p) a =
      (TrackD.rationalDifferential (TrackD.secantChartNumerator i₀)
        (TrackD.secantChartDenominator i₀) p).domRestrict (S.tangentSpace p) b :=
    hDval
  exact hDinj hDrest

/-- Conditional assembly for the full-dimensional case (`dim Z = 2k`, so the
normalization target is `2k`-dimensional and the cleared pullbacks give `2k`
equations): transverse section data on `Z` (a degree-computing fiber `Q` over
`t`, transverse at every point) plus a lifted transverse preimage set `P` on
`S` (in the denominator chart, mapping into `Q` with a section `σ`, tangent
preserved and transverse) yield the good-section package. The hard remaining
inputs are the existence of transverse `Q` (Chevalley image-openness plus the
étale locus of the `Z` normalization) and of transverse lifts (generic
transversality pruning). -/
theorem mo_good_section_of_transverse_lift (i₀ : Fin d) (k : ℕ) (X Y : AffineVariety d)
    (hX : X.IsIrreducible) (hY : Y.IsIrreducible)
    (φZ : AffineProjection (d + d) (2 * k)) (t : Point (2 * k))
    (Q : Finset (Point (d + d)))
    (hQcard : (Q.card : ℚ) = (commonProductImage i₀ X Y).degree)
    (hQfib : ∀ z ∈ Q, φZ.apply z = t)
    (hQtrans : ∀ z ∈ Q, Function.Injective
      ((LinearMap.pi (fun j => differential (φZ.pullback (MvPolynomial.X j) -
        MvPolynomial.C (t j)) z)).domRestrict
        ((commonProductImage i₀ X Y).tangentSpace z)))
    (P : Finset (Point (d + d)))
    (hPmem : ∀ p ∈ P, p ∈ (TrackD.productVariety X Y).points)
    (hg : ∀ p ∈ P, MvPolynomial.eval p (TrackD.secantChartDenominator i₀) ≠ 0)
    (hPmap : ∀ p ∈ P, TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
      (TrackD.secantChartDenominator i₀) p ∈ Q)
    (σ : ↥Q → ↥P)
    (hσ : ∀ q : ↥Q, TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
      (TrackD.secantChartDenominator i₀) (σ q).val = q.val)
    (hDmap : ∀ p ∈ P, ∀ v ∈ (TrackD.productVariety X Y).tangentSpace p,
      TrackD.rationalDifferential (TrackD.secantChartNumerator i₀)
        (TrackD.secantChartDenominator i₀) p v ∈
        (commonProductImage i₀ X Y).tangentSpace
          (TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
            (TrackD.secantChartDenominator i₀) p))
    (hDinj : ∀ p ∈ P, Function.Injective
      ((TrackD.rationalDifferential (TrackD.secantChartNumerator i₀)
        (TrackD.secantChartDenominator i₀) p).domRestrict
        ((TrackD.productVariety X Y).tangentSpace p))) :
    ∃ (Q' : Finset (Point (d + d))) (P' : Finset (Point (d + d)))
      (E : Finset (Poly (d + d))),
      ((Q'.card : ℚ) = (commonProductImage i₀ X Y).degree) ∧
      (Q'.card ≤ P'.card) ∧
      (∀ f ∈ E, f.totalDegree ≤ 2) ∧
      (∀ p ∈ P', pointIdeal p ∈
        ((TrackD.productVariety X Y).ideal ⊔
          Ideal.span (↑E : Set (Poly (d + d)))).minimalPrimes) := by
  classical
  have hS : (TrackD.productVariety X Y).IsIrreducible :=
    TrackD.productVariety_irreducible X Y hX hY
  have hQvan : ∀ (z : Point (d + d)), z ∈ Q → ∀ j : Fin (2 * k),
      MvPolynomial.eval z (φZ.pullback (MvPolynomial.X j) - MvPolynomial.C (t j)) = 0 := by
    intro z hz j
    have hfib := hQfib z hz
    have h := φZ.eval_pullback z (MvPolynomial.X j)
    simp only [MvPolynomial.aeval_X, MvPolynomial.aeval_eq_eval] at h
    rw [hfib] at h
    simp only [map_sub, MvPolynomial.eval_C, h, sub_self]
  have hPvan : ∀ (p : Point (d + d)), p ∈ P → ∀ j : Fin (2 * k),
      MvPolynomial.eval p (clearedPullback i₀ φZ t j) = 0 := by
    intro p hp j
    rw [clearedPullback_zero_iff i₀ φZ t j p (hg p hp)]
    exact hQvan _ (hPmap p hp) j
  have hσinj : Function.Injective σ := by
    intro a b hab
    have ha := hσ a
    have hb := hσ b
    rw [hab] at ha
    have hval : (a : Point (d + d)) = (b : Point (d + d)) := ha.symm.trans hb
    exact Subtype.ext hval
  have hcard : Q.card ≤ P.card := by
    have h := Fintype.card_le_of_injective σ hσinj
    simpa [Fintype.card_coe] using h
  refine ⟨Q, P, Finset.image (fun j => clearedPullback i₀ φZ t j) Finset.univ,
    hQcard, hcard, ?_, ?_⟩
  · intro f hf
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hf
    exact clearedPullback_degree_le i₀ φZ t j
  · intro p hp
    have hinj := transverse_clearedPullback_injective i₀
      (TrackD.productVariety X Y) (commonProductImage i₀ X Y) φZ t p
      (hg p hp) (fun j => hQvan _ (hPmap p hp) j)
      (hDmap p hp) (hDinj p hp) (hQtrans _ (hPmap p hp))
    have hiso := common_quadratic_section_isolated (TrackD.productVariety X Y) hS
      (fun j => clearedPullback i₀ φZ t j)
      (fun a => clearedPullback_degree_le i₀ φZ t a)
      p (hPmem p hp) (fun a => hPvan p hp a) hinj
    have hspan : (↑(Finset.image (fun j => clearedPullback i₀ φZ t j) Finset.univ) :
        Set (Poly (d + d))) = Set.range (fun j => clearedPullback i₀ φZ t j) := by
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    rw [← hspan] at hiso
    exact hiso

/-- The normalization fiber differentials coincide with the projection linear
part (from `pullback_fiber_differential` + `linear_apply_sum`). -/
theorem fiberDifferential_eq_linear {e : ℕ}
    (φZ : AffineProjection (d + d) e) (t : Point e) (q : Point (d + d)) :
    LinearMap.pi (fun j => differential (φZ.pullback (MvPolynomial.X j) -
      MvPolynomial.C (t j)) q) = φZ.linear := by
  apply LinearMap.ext
  intro v
  funext j
  simp only [LinearMap.pi_apply]
  have hLv : differential (φZ.pullback (MvPolynomial.X j) - MvPolynomial.C (t j)) q v =
      ∑ i : Fin (d + d), φZ.linear (Pi.single i 1) j * v i := by
    rw [pullback_fiber_differential]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      TrackD.differential_X, LinearMap.proj_apply]
  exact hLv.trans (linear_apply_sum φZ v j).symm

/-- Z-side transverse fiber: from normalization data plus a transverse
principal open (`gT`) and a Chevalley image open (`hC`), one
`section_in_open` call yields a degree-computing fiber inside both opens,
hence transverse with all points in the secant image. -/
theorem zTransverse_fiber (i₀ : Fin d) (X Y : AffineVariety d) (e : ℕ)
    (φZ : AffineProjection (d + d) e) (hφsurj : Function.Surjective φZ.linear)
    (hφfin : TrackA.FiniteAffineProjection φZ (commonProductImage i₀ X Y))
    (r : ℕ) (hr : φZ.GenericallyFiniteOfDegree (commonProductImage i₀ X Y) r)
    (hdegree : (r : ℚ) = (commonProductImage i₀ X Y).degree)
    (hZirr : (commonProductImage i₀ X Y).IsIrreducible)
    (hZdim : (commonProductImage i₀ X Y).dimension = e)
    (gT : Poly (d + d)) (hgT : gT ∉ (commonProductImage i₀ X Y).ideal)
    (hTinj : ∀ z ∈ (commonProductImage i₀ X Y).points, MvPolynomial.eval z gT ≠ 0 →
      Function.Injective (φZ.linear.domRestrict ((commonProductImage i₀ X Y).tangentSpace z)))
    (hC : Poly (d + d)) (hhC : hC ∉ (commonProductImage i₀ X Y).ideal)
    (hClift : ∀ z ∈ (commonProductImage i₀ X Y).points, MvPolynomial.eval z hC ≠ 0 →
      ∃ p ∈ (TrackD.productVariety X Y).points,
        MvPolynomial.eval p (TrackD.secantChartDenominator i₀) ≠ 0 ∧
        TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
          (TrackD.secantChartDenominator i₀) p = z) :
    ∃ (t : Point e) (Q : Finset (Point (d + d))),
      ((Q.card : ℚ) = (commonProductImage i₀ X Y).degree) ∧
      (∀ z ∈ Q, z ∈ (commonProductImage i₀ X Y).points ∧ φZ.apply z = t) ∧
      (∀ z ∈ Q, Function.Injective
        ((LinearMap.pi (fun j => differential (φZ.pullback (MvPolynomial.X j) -
          MvPolynomial.C (t j)) z)).domRestrict
          ((commonProductImage i₀ X Y).tangentSpace z))) ∧
      (∀ z ∈ Q, ∃ p ∈ (TrackD.productVariety X Y).points,
        MvPolynomial.eval p (TrackD.secantChartDenominator i₀) ≠ 0 ∧
        TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
          (TrackD.secantChartDenominator i₀) p = z) ∧
      (∀ z ∈ Q, MvPolynomial.eval z (gT * hC) ≠ 0) := by
  classical
  have hg' : gT * hC ∉ (commonProductImage i₀ X Y).ideal := by
    intro hm
    exact (hZirr.mem_or_mem hm).elim hgT hhC
  obtain ⟨t, -, S, hcard, hfib, hgOpen⟩ :=
    common_normalization_section_in_open (commonProductImage i₀ X Y) hZirr hZdim
      φZ hφsurj hφfin r hr hdegree (gT * hC) hg'
  refine ⟨t, S, hcard, ?_, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨hzm, hft⟩ := (hfib z).mp hz
    exact ⟨hzm, hft⟩
  · intro z hz
    have hgne : MvPolynomial.eval z (gT * hC) ≠ 0 := hgOpen z hz
    rw [map_mul, mul_ne_zero_iff] at hgne
    have htinj := hTinj z ((hfib z).mp hz).1 hgne.1
    rw [fiberDifferential_eq_linear φZ t z]
    exact htinj
  · intro z hz
    have hgne : MvPolynomial.eval z (gT * hC) ≠ 0 := hgOpen z hz
    rw [map_mul, mul_ne_zero_iff] at hgne
    exact hClift z ((hfib z).mp hz).1 hgne.2
  · exact fun z hz => hgOpen z hz

/-- Full Z-side existence (full-dimensional case): normalization + transverse
locus + a caller-supplied avoidance/image open combined. The caller folds the
Chevalley open and the bad-image avoidance into `hAv`. -/
theorem zGoodFiber_of_chart (i₀ : Fin d) (k : ℕ) (X Y : AffineVariety d)
    (hZirr : (commonProductImage i₀ X Y).IsIrreducible)
    (hZdim : (commonProductImage i₀ X Y).dimension = 2 * k)
    (hAv : Poly (d + d)) (hhAv : hAv ∉ (commonProductImage i₀ X Y).ideal)
    (hAvlift : ∀ z ∈ (commonProductImage i₀ X Y).points, MvPolynomial.eval z hAv ≠ 0 →
      ∃ p ∈ (TrackD.productVariety X Y).points,
        MvPolynomial.eval p (TrackD.secantChartDenominator i₀) ≠ 0 ∧
        TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
          (TrackD.secantChartDenominator i₀) p = z) :
    ∃ (φZ : AffineProjection (d + d) (2 * k)) (t : Point (2 * k))
      (Q : Finset (Point (d + d))),
      ((Q.card : ℚ) = (commonProductImage i₀ X Y).degree) ∧
      (∀ z ∈ Q, z ∈ (commonProductImage i₀ X Y).points ∧ φZ.apply z = t) ∧
      (∀ z ∈ Q, Function.Injective
        ((LinearMap.pi (fun j => differential (φZ.pullback (MvPolynomial.X j) -
          MvPolynomial.C (t j)) z)).domRestrict
          ((commonProductImage i₀ X Y).tangentSpace z))) ∧
      (∀ z ∈ Q, ∃ p ∈ (TrackD.productVariety X Y).points,
        MvPolynomial.eval p (TrackD.secantChartDenominator i₀) ≠ 0 ∧
        TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
          (TrackD.secantChartDenominator i₀) p = z) ∧
      (∀ z ∈ Q, MvPolynomial.eval z hAv ≠ 0) := by
  classical
  have hkle : 2 * k ≤ d + d := by
    have hle := TrackA.pooling_dimension_le_ambient (commonProductImage i₀ X Y) hZirr
    omega
  have hPure : AffineFamily.IsPure
      ({commonProductImage i₀ X Y} : AffineFamily.Family (d + d)) (2 * k) := by
    intro W hW
    rw [Finset.mem_singleton.mp hW]
    exact ⟨hZirr, hZdim⟩
  obtain ⟨φZ, hsurj, hnorm⟩ := TrackA.poly_hilbert_normalization
    ({commonProductImage i₀ X Y} : AffineFamily.Family (d + d)) (2 * k) hkle hPure
  obtain ⟨hfin, r, hrdeg, hr⟩ := hnorm _ (Finset.mem_singleton_self _)
  have hTgen : TrackD.ForGeneralPoint (commonProductImage i₀ X Y)
      (fun z => Function.Injective
        (φZ.linear.domRestrict ((commonProductImage i₀ X Y).tangentSpace z))) :=
    common_normalization_general_tangent_injective
      (commonProductImage i₀ X Y) hZirr hZdim φZ hfin
  obtain ⟨gT, hgTmem, hgTimp⟩ :=
    common_principal_open_of_general (commonProductImage i₀ X Y) _ hTgen
  obtain ⟨t, Q, hQcard, hQfib, hQtrans, hQlift, hAvoid⟩ :=
    zTransverse_fiber i₀ X Y (2 * k) φZ hsurj hfin r hr hrdeg hZirr hZdim
      gT hgTmem (fun z hzm hne => hgTimp z hzm hne) hAv hhAv hAvlift
  refine ⟨φZ, t, Q, hQcard, hQfib, hQtrans, hQlift, ?_⟩
  intro z hz
  have hne := hAvoid z hz
  rw [map_mul, mul_ne_zero_iff] at hne
  exact hne.2

/-- S-side transverse locus (full-dimensional case): at a general source
point the secant differential is injective on the tangent and maps it onto
the image tangent. Needs `dim Z = 2k` (so generic rank is full); no
pair-transversality hypothesis. -/
theorem secantTransverse_general (i₀ : Fin d) (k : ℕ) (X Y : AffineVariety d)
    (hX : X.IsIrreducible) (hY : Y.IsIrreducible)
    (hXd : X.dimension = k) (hYd : Y.dimension = k)
    (hchart : ∃ x ∈ X, ∃ y ∈ Y, (y - x) i₀ ≠ 0)
    (hZdim : (commonProductImage i₀ X Y).dimension = 2 * k) :
    TrackD.ForGeneralPoint (TrackD.productVariety X Y) (fun p =>
      MvPolynomial.eval p (TrackD.secantChartDenominator i₀) ≠ 0 ∧
      ((TrackD.productVariety X Y).tangentSpace p).map
          (TrackD.rationalDifferential (TrackD.secantChartNumerator i₀)
            (TrackD.secantChartDenominator i₀) p) =
          (commonProductImage i₀ X Y).tangentSpace
            (TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
              (TrackD.secantChartDenominator i₀) p) ∧
      Function.Injective
        ((TrackD.rationalDifferential (TrackD.secantChartNumerator i₀)
          (TrackD.secantChartDenominator i₀) p).domRestrict
          ((TrackD.productVariety X Y).tangentSpace p))) := by
  classical
  have hS : (TrackD.productVariety X Y).IsIrreducible :=
    TrackD.productVariety_irreducible X Y hX hY
  have hg : TrackD.secantChartDenominator i₀ ∉ (TrackD.productVariety X Y).ideal :=
    common_image_domain_not_mem i₀ X Y hchart
  obtain ⟨-, hgen⟩ := TrackD.request_rational_image_generic_tangent
    (TrackD.productVariety X Y) hS
    (TrackD.secantChartNumerator i₀) (TrackD.secantChartDenominator i₀) hg
  have hfinrank := TrackD.general_tangent_finrank (TrackD.productVariety X Y) hS
  have hSdim : (TrackD.productVariety X Y).dimension = 2 * k := by
    rw [TrackD.product_dimension X Y hX hY, hXd, hYd, two_mul]
  have hdimbridge : (TrackD.rationalImage (TrackD.productVariety X Y)
      (TrackD.secantChartNumerator i₀)
      (TrackD.secantChartDenominator i₀)).dimension =
      (commonProductImage i₀ X Y).dimension := rfl
  apply (hgen.and hS hfinrank).mono
  intro p hp h
  obtain ⟨⟨hg0, hmap, hfrank⟩, hdom⟩ := h
  rw [hdimbridge, hZdim] at hfrank
  refine ⟨hg0, hmap, ?_⟩
  have hdom2k : Module.finrank ℂ ((TrackD.productVariety X Y).tangentSpace p) = 2 * k := by
    rw [hdom, hSdim]
  have hrange2k : Module.finrank ℂ (LinearMap.range
      ((TrackD.rationalDifferential (TrackD.secantChartNumerator i₀)
        (TrackD.secantChartDenominator i₀) p).domRestrict
        ((TrackD.productVariety X Y).tangentSpace p))) = 2 * k := by
    rw [LinearMap.range_domRestrict, hmap, hfrank]
  have hker0 : Module.finrank ℂ (LinearMap.ker
      ((TrackD.rationalDifferential (TrackD.secantChartNumerator i₀)
        (TrackD.secantChartDenominator i₀) p).domRestrict
        ((TrackD.productVariety X Y).tangentSpace p))) = 0 := by
    have hrn := LinearMap.finrank_range_add_finrank_ker
      ((TrackD.rationalDifferential (TrackD.secantChartNumerator i₀)
        (TrackD.secantChartDenominator i₀) p).domRestrict
        ((TrackD.productVariety X Y).tangentSpace p))
    omega
  have hkerbot := Submodule.finrank_eq_zero.mp hker0
  exact LinearMap.ker_eq_bot.mp hkerbot

/-- Bad-image avoidance: a general `Z`-section point whose preimage exists
must have that preimage in the transverse locus. Precisely, there is
`hW ∉ Z.ideal` such that any `q ∈ Z` off `V(hW)` forces every denominator-chart
preimage into `D(gS)`. Proof: over each minimal prime of the bad closed set,
either the denominator vanishes identically (dead factor `1`) or the
component has dimension `< 2k` (proper cut), so its secant-image closure is a
proper closed subset of `Z` (generic-rank bound), contributing a separating
equation; the product avoids all of them at once. -/
theorem badImage_avoid (i₀ : Fin d) (k : ℕ) (X Y : AffineVariety d)
    (hX : X.IsIrreducible) (hY : Y.IsIrreducible)
    (hk : 1 ≤ k)
    (hSdim : (TrackD.productVariety X Y).dimension = 2 * k)
    (gS : Poly (d + d)) (hgS : gS ∉ (TrackD.productVariety X Y).ideal)
    (hZirr : (commonProductImage i₀ X Y).IsIrreducible)
    (hZdim : (commonProductImage i₀ X Y).dimension = 2 * k)
    (hZne : (commonProductImage i₀ X Y).points.Nonempty) :
    ∃ hW : Poly (d + d), hW ∉ (commonProductImage i₀ X Y).ideal ∧
      ∀ q ∈ (commonProductImage i₀ X Y).points, MvPolynomial.eval q hW ≠ 0 →
        ∀ p ∈ (TrackD.productVariety X Y).points,
          MvPolynomial.eval p (TrackD.secantChartDenominator i₀) ≠ 0 →
          TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
            (TrackD.secantChartDenominator i₀) p = q →
          MvPolynomial.eval p gS ≠ 0 := by
  classical
  have hS : (TrackD.productVariety X Y).IsIrreducible :=
    TrackD.productVariety_irreducible X Y hX hY
  letI hZprime : (commonProductImage i₀ X Y).ideal.IsPrime := hZirr
  have h1ne : (1 : Poly (d + d)) ∉ (commonProductImage i₀ X Y).ideal := by
    intro hm
    obtain ⟨z, hz⟩ := hZne
    have he := (TrackD.mem_ideal_iff_eval_zero (commonProductImage i₀ X Y) 1).mp hm z hz
    simpa using he
  have hfin : ((TrackD.productVariety X Y).ideal ⊔ Ideal.span {gS}).minimalPrimes.Finite :=
    Ideal.finite_minimalPrimes_of_isNoetherianRing _ _
  -- per-factor equations, uniform statement (dead components contribute nothing)
  have perFactor : ∀ 𝔭 : Ideal (Poly (d + d)), ∃ h : Poly (d + d),
      h ∉ (commonProductImage i₀ X Y).ideal ∧
      (𝔭 ∈ hfin.toFinset →
        ∀ p ∈ (TrackD.productVariety X Y).points, (∀ F ∈ 𝔭, MvPolynomial.eval p F = 0) →
          MvPolynomial.eval p (TrackD.secantChartDenominator i₀) ≠ 0 →
          ∀ q, TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
            (TrackD.secantChartDenominator i₀) p = q →
          MvPolynomial.eval q h = 0) := by
    intro 𝔭
    by_cases hmem : 𝔭 ∈ hfin.toFinset
    · have hmemSet : 𝔭 ∈ ((TrackD.productVariety X Y).ideal ⊔ Ideal.span {gS}).minimalPrimes :=
        (Set.Finite.mem_toFinset _).mp hmem
      have hPprime : 𝔭.IsPrime := hmemSet.isPrime
      have hWirr : (⟨𝔭, hPprime.isRadical⟩ : AffineVariety (d + d)).IsIrreducible := hPprime
      by_cases hg𝔭 : TrackD.secantChartDenominator i₀ ∈ 𝔭
      · refine ⟨1, h1ne, ?_⟩
        intro _ p _ hpointwise hgp _ _
        exact absurd (hpointwise _ hg𝔭) hgp
      · have hWcomp : (⟨𝔭, hPprime.isRadical⟩ : AffineVariety (d + d)).IsComponentOf
            ((TrackD.productVariety X Y).ideal ⊔ Ideal.span {gS}) := hmemSet
        have hWdim : (⟨𝔭, hPprime.isRadical⟩ : AffineVariety (d + d)).dimension
            = 2 * k - 1 := by
          have hSdim' : (TrackD.productVariety X Y).dimension = (2 * k - 1) + 1 := by omega
          exact TrackA.fa_bezout_proper_dimension _ _ hS gS hgS hWcomp (2 * k - 1) hSdim'
        have hgimg : TrackD.secantChartDenominator i₀ ∉
            (⟨𝔭, hPprime.isRadical⟩ : AffineVariety (d + d)).ideal := hg𝔭
        obtain ⟨-, hgenimg⟩ := TrackD.request_rational_image_generic_tangent
          (⟨𝔭, hPprime.isRadical⟩ : AffineVariety (d + d)) hWirr
          (TrackD.secantChartNumerator i₀) (TrackD.secantChartDenominator i₀) hgimg
        have hZimgdim : (TrackD.rationalImage
            (⟨𝔭, hPprime.isRadical⟩ : AffineVariety (d + d))
            (TrackD.secantChartNumerator i₀)
            (TrackD.secantChartDenominator i₀)).dimension ≤ 2 * k - 1 :=
          calc _ ≤ (⟨𝔭, hPprime.isRadical⟩ : AffineVariety (d + d)).dimension :=
                TrackD.rational_image_dimension_le_of_generic_rank _ hWirr _ _ hgenimg
            _ = 2 * k - 1 := hWdim
        -- the component image closure is a proper closed subset of Z
        have hsub : (TrackD.rationalImage
            (⟨𝔭, hPprime.isRadical⟩ : AffineVariety (d + d))
            (TrackD.secantChartNumerator i₀)
            (TrackD.secantChartDenominator i₀)).points ⊆
            (commonProductImage i₀ X Y).points := by
          have hleS : (TrackD.productVariety X Y).ideal ≤ 𝔭 :=
            le_sup_left.trans hmemSet.le
          have himg : {y | ∃ x ∈ (⟨𝔭, hPprime.isRadical⟩ : AffineVariety (d + d)),
              MvPolynomial.eval x (TrackD.secantChartDenominator i₀) ≠ 0 ∧
              TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
                (TrackD.secantChartDenominator i₀) x = y} ⊆
              {y | ∃ x ∈ (TrackD.productVariety X Y),
              MvPolynomial.eval x (TrackD.secantChartDenominator i₀) ≠ 0 ∧
              TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
                (TrackD.secantChartDenominator i₀) x = y} := by
            rintro y ⟨x, hxW, hxg, rfl⟩
            have hxWp : x ∈ (⟨𝔭, hPprime.isRadical⟩ : AffineVariety (d + d)).points := hxW
            have hxSp : x ∈ (TrackD.productVariety X Y).points := by
              simpa only [AffineVariety.points, MvPolynomial.mem_zeroLocus_iff] using
                (fun F hF => (MvPolynomial.mem_zeroLocus_iff.mp hxWp F
                  (show F ∈ (⟨𝔭, hPprime.isRadical⟩ : AffineVariety (d + d)).ideal from hleS hF)))
            exact ⟨x, hxSp, hxg, rfl⟩
          intro z hz f hf
          have hf' : ∀ y ∈ {y | ∃ x ∈ (⟨𝔭, hPprime.isRadical⟩ : AffineVariety (d + d)),
              MvPolynomial.eval x (TrackD.secantChartDenominator i₀) ≠ 0 ∧
              TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
                (TrackD.secantChartDenominator i₀) x = y},
              MvPolynomial.eval y f = 0 := fun y hy => hf y (himg hy)
          have hfm : f ∈ MvPolynomial.vanishingIdeal ℂ {y |
              ∃ x ∈ (⟨𝔭, hPprime.isRadical⟩ : AffineVariety (d + d)),
              MvPolynomial.eval x (TrackD.secantChartDenominator i₀) ≠ 0 ∧
              TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
                (TrackD.secantChartDenominator i₀) x = y} :=
            (MvPolynomial.mem_vanishingIdeal_iff).mpr hf'
          exact (MvPolynomial.mem_zeroLocus_iff.mp hz f hfm)
        have hne : (TrackD.rationalImage
            (⟨𝔭, hPprime.isRadical⟩ : AffineVariety (d + d))
            (TrackD.secantChartNumerator i₀)
            (TrackD.secantChartDenominator i₀)).points ≠
            (commonProductImage i₀ X Y).points := by
          intro heq
          have e1 : (TrackD.rationalImage
              (⟨𝔭, hPprime.isRadical⟩ : AffineVariety (d + d))
              (TrackD.secantChartNumerator i₀)
              (TrackD.secantChartDenominator i₀)).ideal =
              (commonProductImage i₀ X Y).ideal := by
            rw [← AffineVariety.vanishingIdeal_points,
              ← AffineVariety.vanishingIdeal_points, heq]
          have hdimEq : (TrackD.rationalImage
              (⟨𝔭, hPprime.isRadical⟩ : AffineVariety (d + d))
              (TrackD.secantChartNumerator i₀)
              (TrackD.secantChartDenominator i₀)).dimension =
              (commonProductImage i₀ X Y).dimension := by
            show OAI.QuarticPowerFree.affineDimension _ =
              OAI.QuarticPowerFree.affineDimension _
            rw [e1]
          omega
        obtain ⟨z, hzz, hznot⟩ : ∃ z ∈ (commonProductImage i₀ X Y).points,
            z ∉ (TrackD.rationalImage
              (⟨𝔭, hPprime.isRadical⟩ : AffineVariety (d + d))
              (TrackD.secantChartNumerator i₀)
              (TrackD.secantChartDenominator i₀)).points := by
          by_contra hcon
          push_neg at hcon
          exact hne (Set.Subset.antisymm hsub hcon)
        have hex : ∃ h ∈ (TrackD.rationalImage
            (⟨𝔭, hPprime.isRadical⟩ : AffineVariety (d + d))
            (TrackD.secantChartNumerator i₀)
            (TrackD.secantChartDenominator i₀)).ideal,
            MvPolynomial.eval z h ≠ 0 := by
          by_contra hcon
          push_neg at hcon
          exact hznot ((MvPolynomial.mem_zeroLocus_iff).mpr
            (by simpa only [← MvPolynomial.aeval_eq_eval] using hcon))
        obtain ⟨h, hhZimg, hhz⟩ := hex
        have hhZ : h ∉ (commonProductImage i₀ X Y).ideal := by
          intro hm
          exact hhz ((TrackD.mem_ideal_iff_eval_zero _ _).mp hm z hzz)
        refine ⟨h, hhZ, ?_⟩
        intro _ p hp hpointwise hgp q hq
        have hpW : p ∈ (⟨𝔭, hPprime.isRadical⟩ : AffineVariety (d + d)).points :=
          (MvPolynomial.mem_zeroLocus_iff).mpr
            (by simpa only [← MvPolynomial.aeval_eq_eval] using hpointwise)
        have hqmem : TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
            (TrackD.secantChartDenominator i₀) p ∈
            (TrackD.rationalImage (⟨𝔭, hPprime.isRadical⟩ : AffineVariety (d + d))
              (TrackD.secantChartNumerator i₀)
              (TrackD.secantChartDenominator i₀)).points :=
          TrackD.rationalPoint_mem_image _ _ _ _ hpW hgp
        rw [hq] at hqmem
        exact (TrackD.mem_ideal_iff_eval_zero _ _).mp hhZimg q hqmem
    · exact ⟨1, h1ne, fun hcon => False.elim (hmem hcon)⟩
  choose hfun hprop using perFactor
  refine ⟨∏ 𝔭 ∈ hfin.toFinset, hfun 𝔭, ?_, ?_⟩
  · intro hm
    obtain ⟨𝔭, h𝔭mem, h𝔭0⟩ := Ideal.IsPrime.prod_mem_iff.mp hm
    exact ((hprop 𝔭).1) h𝔭0
  · intro q hq hqh p hp hgp hqp
    by_contra hgS0
    -- point-ideal membership is evaluation-vanishing (bridge used below)
    have hPtmem : ∀ F : Poly (d + d), F ∈ pointIdeal p ↔ MvPolynomial.eval p F = 0 := by
      intro F
      constructor
      · intro hF
        have hF' : F ∈ MvPolynomial.vanishingIdeal ℂ {p} := hF
        have hae := (MvPolynomial.mem_vanishingIdeal_singleton_iff p F).mp hF'
        simpa only [← MvPolynomial.aeval_eq_eval] using hae
      · intro hF
        have hF' : MvPolynomial.aeval p F = 0 := hF
        exact (MvPolynomial.mem_vanishingIdeal_singleton_iff p F).mpr hF'
    -- the bad preimage lies over some minimal prime
    have hJle : (TrackD.productVariety X Y).ideal ⊔ Ideal.span {gS} ≤ pointIdeal p := by
      apply sup_le
      · intro F hF
        exact (hPtmem F).mpr ((TrackD.mem_ideal_iff_eval_zero _ _).mp hF p hp)
      · apply Ideal.span_le.mpr
        intro F hF
        rw [Set.mem_singleton_iff.mp hF]
        exact (hPtmem gS).mpr hgS0
    letI hPprimePt : (pointIdeal p).IsPrime := (pointIdeal_isMaximal p).isPrime
    obtain ⟨P, hPmin, hPpoint⟩ := Ideal.exists_minimalPrimes_le hJle
    have hPmem : P ∈ hfin.toFinset := (Set.Finite.mem_toFinset _).mpr hPmin
    have hpointwise : ∀ F ∈ P, MvPolynomial.eval p F = 0 :=
      fun F hF => (hPtmem F).mp (hPpoint hF)
    have hfac0 : MvPolynomial.eval q (hfun P) = 0 :=
      (hprop P).2 hPmem p hp hpointwise hgp q hqp
    have hq0 : MvPolynomial.eval q (∏ 𝔭 ∈ hfin.toFinset, hfun 𝔭) = 0 := by
      simp only [← MvPolynomial.aeval_eq_eval, map_prod]
      exact Finset.prod_eq_zero hPmem (by simpa only [MvPolynomial.aeval_eq_eval] using hfac0)
    exact hqh hq0

/-- Transverse lifts: every `Q` point has a Chevalley preimage, and the
avoidance open forces that preimage into the transverse locus, giving all
source-side assembly inputs (`σ`, tangent preservation/injection). -/
theorem transverse_lift (i₀ : Fin d) (k : ℕ) (X Y : AffineVariety d)
    (φZ : AffineProjection (d + d) (2 * k)) (t : Point (2 * k))
    (Q : Finset (Point (d + d)))
    (hQfib : ∀ z ∈ Q, z ∈ (commonProductImage i₀ X Y).points ∧ φZ.apply z = t)
    (hQlift : ∀ z ∈ Q, ∃ p ∈ (TrackD.productVariety X Y).points,
      MvPolynomial.eval p (TrackD.secantChartDenominator i₀) ≠ 0 ∧
      TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
        (TrackD.secantChartDenominator i₀) p = z)
    (gS : Poly (d + d))
    (hgStrans : ∀ p ∈ (TrackD.productVariety X Y).points, MvPolynomial.eval p gS ≠ 0 →
      MvPolynomial.eval p (TrackD.secantChartDenominator i₀) ≠ 0 ∧
      ((TrackD.productVariety X Y).tangentSpace p).map
        (TrackD.rationalDifferential (TrackD.secantChartNumerator i₀)
          (TrackD.secantChartDenominator i₀) p) =
        (commonProductImage i₀ X Y).tangentSpace
          (TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
            (TrackD.secantChartDenominator i₀) p) ∧
      Function.Injective
        ((TrackD.rationalDifferential (TrackD.secantChartNumerator i₀)
          (TrackD.secantChartDenominator i₀) p).domRestrict
          ((TrackD.productVariety X Y).tangentSpace p)))
    (hW : Poly (d + d))
    (hWavoid : ∀ q ∈ (commonProductImage i₀ X Y).points, MvPolynomial.eval q hW ≠ 0 →
      ∀ p ∈ (TrackD.productVariety X Y).points,
        MvPolynomial.eval p (TrackD.secantChartDenominator i₀) ≠ 0 →
        TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
          (TrackD.secantChartDenominator i₀) p = q →
        MvPolynomial.eval p gS ≠ 0)
    (hWQ : ∀ z ∈ Q, MvPolynomial.eval z hW ≠ 0) :
    ∃ (P : Finset (Point (d + d))) (σ : ↥Q → ↥P),
      (∀ p ∈ P, p ∈ (TrackD.productVariety X Y).points) ∧
      (∀ p ∈ P, MvPolynomial.eval p (TrackD.secantChartDenominator i₀) ≠ 0) ∧
      (∀ p ∈ P, TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
        (TrackD.secantChartDenominator i₀) p ∈ Q) ∧
      (∀ q : ↥Q, TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
        (TrackD.secantChartDenominator i₀) (σ q).val = q.val) ∧
      (∀ p ∈ P, ∀ v ∈ (TrackD.productVariety X Y).tangentSpace p,
        TrackD.rationalDifferential (TrackD.secantChartNumerator i₀)
          (TrackD.secantChartDenominator i₀) p v ∈
          (commonProductImage i₀ X Y).tangentSpace
            (TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
              (TrackD.secantChartDenominator i₀) p)) ∧
      (∀ p ∈ P, Function.Injective
        ((TrackD.rationalDifferential (TrackD.secantChartNumerator i₀)
          (TrackD.secantChartDenominator i₀) p).domRestrict
          ((TrackD.productVariety X Y).tangentSpace p))) := by
  classical
  have perQ : ∀ q : ↥Q, ∃ p : Point (d + d),
      p ∈ (TrackD.productVariety X Y).points ∧
      MvPolynomial.eval p (TrackD.secantChartDenominator i₀) ≠ 0 ∧
      TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
        (TrackD.secantChartDenominator i₀) p = q.val ∧
      (∀ v ∈ (TrackD.productVariety X Y).tangentSpace p,
        TrackD.rationalDifferential (TrackD.secantChartNumerator i₀)
          (TrackD.secantChartDenominator i₀) p v ∈
          (commonProductImage i₀ X Y).tangentSpace
            (TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
              (TrackD.secantChartDenominator i₀) p)) ∧
      Function.Injective
        ((TrackD.rationalDifferential (TrackD.secantChartNumerator i₀)
          (TrackD.secantChartDenominator i₀) p).domRestrict
          ((TrackD.productVariety X Y).tangentSpace p)) := by
    intro q
    obtain ⟨p₀, hp₀mem, hp₀g, hp₀fib⟩ := hQlift q.val q.property
    have hqmem : q.val ∈ (commonProductImage i₀ X Y).points :=
      (hQfib q.val q.property).1
    have hgS0 : MvPolynomial.eval p₀ gS ≠ 0 :=
      hWavoid q.val hqmem (hWQ q.val q.property) p₀ hp₀mem hp₀g hp₀fib
    obtain ⟨-, hmap, hinj⟩ := hgStrans p₀ hp₀mem hgS0
    refine ⟨p₀, hp₀mem, hp₀g, hp₀fib, ?_, hinj⟩
    intro v hv
    rw [← hmap]
    exact Submodule.mem_map.mpr ⟨v, hv, rfl⟩
  choose σ' hσ' using perQ
  refine ⟨Finset.univ.image σ',
    fun q => ⟨σ' q, Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hp
    exact (hσ' q).1
  · intro p hp
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hp
    exact (hσ' q).2.1
  · intro p hp
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hp
    have hfib := (hσ' q).2.2.1
    rw [hfib]
    exact q.property
  · intro q
    exact (hσ' q).2.2.1
  · intro p hp
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hp
    exact (hσ' q).2.2.2.1
  · intro p hp
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hp
    exact (hσ' q).2.2.2.2

/-- Full-dimensional package (`dim Z = 2k`, `1 ≤ k`): Z-side transverse fiber
inside the combined Chevalley/bad-avoidance open, lifted to transverse
preimages, fed to the conditional assembly. -/
theorem fulldim_package (i₀ : Fin d) (k : ℕ) (X Y : AffineVariety d)
    (hX : X.IsIrreducible) (hY : Y.IsIrreducible)
    (hXd : X.dimension = k) (hYd : Y.dimension = k)
    (hchart : ∃ x ∈ X, ∃ y ∈ Y, (y - x) i₀ ≠ 0)
    (hk : 1 ≤ k)
    (hZirr : (commonProductImage i₀ X Y).IsIrreducible)
    (hZdim : (commonProductImage i₀ X Y).dimension = 2 * k) :
    ∃ (Q : Finset (Point (d + d))) (P : Finset (Point (d + d)))
      (E : Finset (Poly (d + d))),
      ((Q.card : ℚ) = (commonProductImage i₀ X Y).degree) ∧
      (Q.card ≤ P.card) ∧
      (∀ f ∈ E, f.totalDegree ≤ 2) ∧
      (∀ p ∈ P, pointIdeal p ∈
        ((TrackD.productVariety X Y).ideal ⊔
          Ideal.span (↑E : Set (Poly (d + d)))).minimalPrimes) := by
  classical
  have hSdim : (TrackD.productVariety X Y).dimension = 2 * k := by
    rw [TrackD.product_dimension X Y hX hY, hXd, hYd, two_mul]
  have hSgen := secantTransverse_general i₀ k X Y hX hY hXd hYd hchart hZdim
  obtain ⟨gS, hgS, hgStrans⟩ :=
    common_principal_open_of_general (TrackD.productVariety X Y) _ hSgen
  have hZne : (commonProductImage i₀ X Y).points.Nonempty := by
    obtain ⟨x₀, hx₀, y₀, hy₀, hi₀⟩ := hchart
    have hp₀ : TrackD.productPoint x₀ y₀ ∈ (TrackD.productVariety X Y).points :=
      AffineVariety.subset_closure _ ⟨x₀, hx₀, y₀, hy₀, rfl⟩
    have hg₀ : MvPolynomial.eval (TrackD.productPoint x₀ y₀)
        (TrackD.secantChartDenominator i₀) ≠ 0 := by
      simpa only [TrackD.eval_secantChartDenominator] using hi₀
    exact ⟨_, TrackD.rationalPoint_mem_image _ _ _ _ hp₀ hg₀⟩
  obtain ⟨hW, hhW, hWavoid⟩ :=
    badImage_avoid i₀ k X Y hX hY hk hSdim gS hgS hZirr hZdim hZne
  obtain ⟨hC, hhC, hClift0⟩ := common_product_image_contains_open i₀ X Y hX hY hchart
  have hClift : ∀ z ∈ (commonProductImage i₀ X Y).points, MvPolynomial.eval z hC ≠ 0 →
      ∃ p ∈ (TrackD.productVariety X Y).points,
        MvPolynomial.eval p (TrackD.secantChartDenominator i₀) ≠ 0 ∧
        TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
          (TrackD.secantChartDenominator i₀) p = z := by
    intro z hz hzh
    obtain ⟨x, hx, y, hy, hi, hlab⟩ := hClift0 z hz hzh
    refine ⟨TrackD.productPoint x y,
      AffineVariety.subset_closure _ ⟨x, hx, y, hy, rfl⟩, ?_, ?_⟩
    · simpa only [TrackD.eval_secantChartDenominator] using hi
    · rw [TrackD.rational_secant_label i₀ x y hi]
      exact hlab
  have hhAv : hC * hW ∉ (commonProductImage i₀ X Y).ideal := by
    intro hm
    exact (hZirr.mem_or_mem hm).elim hhC hhW
  have hAvlift : ∀ z ∈ (commonProductImage i₀ X Y).points,
      MvPolynomial.eval z (hC * hW) ≠ 0 →
      ∃ p ∈ (TrackD.productVariety X Y).points,
        MvPolynomial.eval p (TrackD.secantChartDenominator i₀) ≠ 0 ∧
        TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
          (TrackD.secantChartDenominator i₀) p = z := by
    intro z hz hne
    rw [map_mul, mul_ne_zero_iff] at hne
    exact hClift z hz hne.1
  obtain ⟨φZ, t, Q, hQcard, hQfibQ, hQtrans, hQliftQ, hAvQ⟩ :=
    zGoodFiber_of_chart i₀ k X Y hZirr hZdim (hC * hW) hhAv hAvlift
  have hWQ : ∀ z ∈ Q, MvPolynomial.eval z hW ≠ 0 := by
    intro z hz
    have hne := hAvQ z hz
    rw [map_mul, mul_ne_zero_iff] at hne
    obtain ⟨-, hne2⟩ := hne
    exact hne2
  obtain ⟨P, σ, hPmem, hgP, hPmap, hσsec, hDmap, hDinj⟩ := transverse_lift i₀ k X Y
    φZ t Q hQfibQ hQliftQ gS hgStrans hW hWavoid hWQ
  exact mo_good_section_of_transverse_lift i₀ k X Y hX hY φZ t Q hQcard
    (fun z hz => (hQfibQ z hz).2) hQtrans P hPmem hgP hPmap σ hσsec hDmap hDinj

/-- Zero-dimensional package (`k = 0`): both source and image are points, so
`Q = {z₀}`, `P = {s₀}`, `E = ∅` works with isolation from maximality. -/
theorem zerodim_package (i₀ : Fin d) (X Y : AffineVariety d)
    (hX : X.IsIrreducible) (hY : Y.IsIrreducible)
    (hXd : X.dimension = 0) (hYd : Y.dimension = 0)
    (hchart : ∃ x ∈ X, ∃ y ∈ Y, (y - x) i₀ ≠ 0) :
    ∃ (Q : Finset (Point (d + d))) (P : Finset (Point (d + d)))
      (E : Finset (Poly (d + d))),
      ((Q.card : ℚ) = (commonProductImage i₀ X Y).degree) ∧
      (Q.card ≤ P.card) ∧
      (∀ f ∈ E, f.totalDegree ≤ 2) ∧
      (∀ p ∈ P, pointIdeal p ∈
        ((TrackD.productVariety X Y).ideal ⊔
          Ideal.span (↑E : Set (Poly (d + d)))).minimalPrimes) := by
  classical
  have hS : (TrackD.productVariety X Y).IsIrreducible :=
    TrackD.productVariety_irreducible X Y hX hY
  have hSdim : (TrackD.productVariety X Y).dimension = 0 := by
    rw [TrackD.product_dimension X Y hX hY, hXd, hYd]
  -- image dimension vanishes too
  have hZdim0 : (commonProductImage i₀ X Y).dimension = 0 := by
    have hg := common_image_domain_not_mem i₀ X Y hchart
    obtain ⟨-, hgen⟩ := TrackD.request_rational_image_generic_tangent
      (TrackD.productVariety X Y) hS
      (TrackD.secantChartNumerator i₀) (TrackD.secantChartDenominator i₀) hg
    have hle := TrackD.rational_image_dimension_le_of_generic_rank
      (TrackD.productVariety X Y) hS
      (TrackD.secantChartNumerator i₀) (TrackD.secantChartDenominator i₀) hgen
    have hleZ : (commonProductImage i₀ X Y).dimension ≤
        (TrackD.productVariety X Y).dimension := hle
    omega
  have hZirr : (commonProductImage i₀ X Y).IsIrreducible := by
    have hg := common_image_domain_not_mem i₀ X Y hchart
    exact TrackD.rational_image_irreducible _ hS _ _ hg
  -- both are reduced points by zero-dimensional maximality
  obtain ⟨s₀, hs₀⟩ := TrackD.irreducible_points_nonempty _ hS
  haveI hSprime : (TrackD.productVariety X Y).ideal.IsPrime := hS
  have hSdim0 : OAI.QuarticPowerFree.affineDimension (TrackD.productVariety X Y).ideal = 0 :=
    hSdim
  have hSmax : (TrackD.productVariety X Y).ideal.IsMaximal :=
    OAI.QuarticPowerFree.zeroDim_isMaximal _ hSdim0
  have hSideal : (TrackD.productVariety X Y).ideal = pointIdeal s₀ :=
    hSmax.eq_of_le (pointIdeal_isMaximal s₀).ne_top (by
      intro F hF
      have he : MvPolynomial.eval s₀ F = 0 :=
        (TrackD.mem_ideal_iff_eval_zero _ _).mp hF s₀ hs₀
      simpa only [pointIdeal, MvPolynomial.mem_vanishingIdeal_singleton_iff,
        ← MvPolynomial.aeval_eq_eval] using he)
  obtain ⟨x₀, hx₀, y₀, hy₀, hi₀⟩ := hchart
  have hp₀ : TrackD.productPoint x₀ y₀ ∈ (TrackD.productVariety X Y).points :=
    AffineVariety.subset_closure _ ⟨x₀, hx₀, y₀, hy₀, rfl⟩
  have hg₀ : MvPolynomial.eval (TrackD.productPoint x₀ y₀)
      (TrackD.secantChartDenominator i₀) ≠ 0 := by
    simpa only [TrackD.eval_secantChartDenominator] using hi₀
  have hZne : (commonProductImage i₀ X Y).points.Nonempty :=
    ⟨_, TrackD.rationalPoint_mem_image _ _ _ _ hp₀ hg₀⟩
  obtain ⟨z₀, hz₀⟩ := hZne
  haveI hZprime : (commonProductImage i₀ X Y).ideal.IsPrime := hZirr
  have hZdim0' : OAI.QuarticPowerFree.affineDimension (commonProductImage i₀ X Y).ideal = 0 :=
    hZdim0
  have hZmax : (commonProductImage i₀ X Y).ideal.IsMaximal :=
    OAI.QuarticPowerFree.zeroDim_isMaximal _ hZdim0'
  have hZideal : (commonProductImage i₀ X Y).ideal = pointIdeal z₀ :=
    hZmax.eq_of_le (pointIdeal_isMaximal z₀).ne_top (by
      intro F hF
      have he : MvPolynomial.eval z₀ F = 0 :=
        (TrackD.mem_ideal_iff_eval_zero _ _).mp hF z₀ hz₀
      simpa only [pointIdeal, MvPolynomial.mem_vanishingIdeal_singleton_iff,
        ← MvPolynomial.aeval_eq_eval] using he)
  have hZdeg : (commonProductImage i₀ X Y).degree = 1 := by
    show OAI.QuarticPowerFree.affineDegree _ = 1
    rw [hZideal]
    exact TrackA.affine_point_degree_one z₀
  refine ⟨{z₀}, {s₀}, ∅, ?_, ?_, ?_, ?_⟩
  · simp only [Finset.card_singleton, Nat.cast_one]
    exact hZdeg.symm
  · simp
  · intro f hf
    exact Finset.notMem_empty f hf |>.elim
  · intro p hp
    rw [Finset.mem_singleton.mp hp]
    haveI : (pointIdeal s₀).IsPrime := (pointIdeal_isMaximal s₀).isPrime
    have hspan : Ideal.span (↑(∅ : Finset (Poly (d + d))) : Set (Poly (d + d))) = ⊥ := by
      simp
    rw [hspan, sup_bot_eq, hSideal]
    simpa only [Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff]

end
end DistinctDistances.SparseCones
