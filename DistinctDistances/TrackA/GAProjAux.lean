import DistinctDistances.TrackA.Definitions
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Block

namespace DistinctDistances.TrackA

open scoped BigOperators Classical

def polyDegreeLE (n : ℕ) (F : Type*) [CommRing F] (q : ℕ) : Submodule F (FieldPoly n F) where
  carrier := {g | g.totalDegree ≤ q}
  zero_mem' := by simp
  add_mem' {a b} ha hb := (MvPolynomial.totalDegree_add a b).trans (max_le ha hb)
  smul_mem' c x hx := (MvPolynomial.totalDegree_smul_le c x).trans hx

theorem poly_compression_failed_separation_proof {n : ℕ} {F : Type*} [Field F]
    (S : Finset (FieldPoint n F)) (x : FieldPoint n F) (q : ℕ)
    (hfailure : ∀ g : FieldPoly n F, g.totalDegree ≤ q →
      (∀ z ∈ S, MvPolynomial.eval z g = 0) → MvPolynomial.eval x g = 0) :
    ∃ weights : S → F, ∀ g : FieldPoly n F, g.totalDegree ≤ q →
      MvPolynomial.eval x g = ∑ z : S, weights z * MvPolynomial.eval z.val g := by
  let E := polyDegreeLE n F q
  let L : S → E →ₗ[F] F := fun z =>
    ((MvPolynomial.aeval z.val).toLinearMap).comp E.subtype
  let K : E →ₗ[F] F :=
    ((MvPolynomial.aeval x).toLinearMap).comp E.subtype
  have hker : (⨅ z : S, LinearMap.ker (L z)) ≤ LinearMap.ker K := by
    intro g hg
    rw [Submodule.mem_iInf] at hg
    rw [LinearMap.mem_ker]
    change MvPolynomial.aeval x g.val = 0
    rw [MvPolynomial.aeval_eq_eval]
    apply hfailure g.val g.property
    intro z hz
    have hz' : g ∈ LinearMap.ker (L ⟨z, hz⟩) := hg ⟨z, hz⟩
    rw [LinearMap.mem_ker] at hz'
    change MvPolynomial.aeval z g.val = 0 at hz'
    rwa [MvPolynomial.aeval_eq_eval] at hz'
  have hspan := mem_span_of_iInf_ker_le_ker hker
  obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hspan
  refine ⟨w, ?_⟩
  intro g hg
  let gE : E := ⟨g, hg⟩
  have hval := LinearMap.congr_fun hw gE
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul] at hval
  have hK : K gE = MvPolynomial.eval x g := by
    change MvPolynomial.aeval x g = _
    rw [MvPolynomial.aeval_eq_eval]
  have hL : ∀ z : S, L z gE = MvPolynomial.eval z.val g := by
    intro z
    change MvPolynomial.aeval z.val g = _
    rw [MvPolynomial.aeval_eq_eval]
  rw [hK] at hval
  simp_rw [hL] at hval
  exact hval.symm

lemma choose_le_pow_two_mul_choose (D q : ℕ) (h2q : 2 * q ≤ D) (k : ℕ) :
    (D + k).choose k ≤ 2^k * (D - q + k).choose k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : (D + k + 1) * (D + k).choose k = (D + k + 1).choose (k + 1) * (k + 1) :=
      Nat.add_one_mul_choose_eq (D + k) k
    have h2 : (D - q + k + 1) * (D - q + k).choose k = (D - q + k + 1).choose (k + 1) * (k + 1) :=
      Nat.add_one_mul_choose_eq (D - q + k) k
    have hstep : D + k + 1 ≤ 2 * (D - q + k + 1) := by omega
    have hmul : (D + k + 1) * (D + k).choose k ≤ 2 * (D - q + k + 1) * (2^k * (D - q + k).choose k) :=
      Nat.mul_le_mul hstep ih
    rw [h1] at hmul
    have hrew : 2 * (D - q + k + 1) * (2^k * (D - q + k).choose k) =
        (2^(k + 1) * (D - q + k + 1).choose (k + 1)) * (k + 1) := by
      calc
        2 * (D - q + k + 1) * (2^k * (D - q + k).choose k)
        _ = 2^(k + 1) * ((D - q + k + 1) * (D - q + k).choose k) := by ring
        _ = 2^(k + 1) * ((D - q + k + 1).choose (k + 1) * (k + 1)) := by rw [h2]
        _ = (2^(k + 1) * (D - q + k + 1).choose (k + 1)) * (k + 1) := by ring
    rw [hrew] at hmul
    exact Nat.le_of_mul_le_mul_right hmul (Nat.succ_pos k)

lemma choose_sub_choose_le_mul (D : ℕ) (k : ℕ) (hk : 0 < k) (q : ℕ) (hq : q ≤ D) :
    (D + k).choose k - (D - q + k).choose k ≤ q * (D + k - 1).choose (k - 1) := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hqD : q ≤ D := by omega
    have ih' := ih hqD
    have hsplit : (D + k).choose k - (D - (q + 1) + k).choose k =
        ((D + k).choose k - (D - q + k).choose k) +
        ((D - q + k).choose k - (D - (q + 1) + k).choose k) := by
      have hle1 : (D - (q + 1) + k).choose k ≤ (D - q + k).choose k := by
        apply Nat.choose_le_choose
        omega
      have hle2 : (D - q + k).choose k ≤ (D + k).choose k := by
        apply Nat.choose_le_choose
        omega
      omega
    have hstep : (D - q + k).choose k - (D - (q + 1) + k).choose k ≤ (D + k - 1).choose (k - 1) := by
      have hM : D - q + k = (D - (q + 1) + k) + 1 := by omega
      have hsucc : ((D - (q + 1) + k) + 1).choose k =
          (D - (q + 1) + k).choose (k - 1) + (D - (q + 1) + k).choose k :=
        Nat.choose_succ_left (D - (q + 1) + k) k hk
      have hdiff : (D - q + k).choose k - (D - (q + 1) + k).choose k = (D - (q + 1) + k).choose (k - 1) := by
        rw [hM, hsucc]
        omega
      rw [hdiff]
      apply Nat.choose_le_choose
      omega
    rw [hsplit]
    calc
      ((D + k).choose k - (D - q + k).choose k) + ((D - q + k).choose k - (D - (q + 1) + k).choose k)
      _ ≤ q * (D + k - 1).choose (k - 1) + (D + k - 1).choose (k - 1) := Nat.add_le_add ih' hstep
      _ = (q + 1) * (D + k - 1).choose (k - 1) := by ring

lemma choose_diff_bound (n D q k : ℕ) (hk : k ≤ n) (hkpos : 0 < k) (hD : 1 ≤ D) (h2q : 2 * q ≤ D) :
    D * ((D + k).choose k - (D - q + k).choose k) ≤ (n * 2^n) * q * (D - q + k).choose k := by
  have hqD : q ≤ D := by omega
  have hsub := choose_sub_choose_le_mul D k hkpos q hqD
  have hmulD : D * ((D + k).choose k - (D - q + k).choose k) ≤ D * (q * (D + k - 1).choose (k - 1)) :=
    Nat.mul_le_mul_left D hsub
  have hchoose_eq : (D + k) * (D + k - 1).choose (k - 1) = k * (D + k).choose k := by
    have h1 := Nat.add_one_mul_choose_eq (D + k - 1) (k - 1)
    have hpred1 : D + k - 1 + 1 = D + k := by omega
    have hpred2 : k - 1 + 1 = k := by omega
    rw [hpred1, hpred2] at h1
    rw [h1]
    ring
  have hD_le : D * (D + k - 1).choose (k - 1) ≤ (D + k) * (D + k - 1).choose (k - 1) := by
    apply Nat.mul_le_mul_right
    omega
  rw [hchoose_eq] at hD_le
  have h2k := choose_le_pow_two_mul_choose D q h2q k
  have hkle : k * (D + k).choose k ≤ (k * 2^k) * (D - q + k).choose k := by
    calc
      k * (D + k).choose k ≤ k * (2^k * (D - q + k).choose k) := Nat.mul_le_mul_left k h2k
      _ = (k * 2^k) * (D - q + k).choose k := by ring
  have hkn : k * 2^k ≤ n * 2^n := by
    have hpow : 2^k ≤ 2^n := Nat.pow_le_pow_right (by decide) hk
    exact Nat.mul_le_mul hk hpow
  have hkle' : k * (D + k).choose k ≤ (n * 2^n) * (D - q + k).choose k :=
    hkle.trans (Nat.mul_le_mul_right _ hkn)
  have hD_le' : D * (D + k - 1).choose (k - 1) ≤ (n * 2^n) * (D - q + k).choose k :=
    hD_le.trans hkle'
  calc
    D * ((D + k).choose k - (D - q + k).choose k)
    _ ≤ D * (q * (D + k - 1).choose (k - 1)) := hmulD
    _ = q * (D * (D + k - 1).choose (k - 1)) := by ring
    _ ≤ q * ((n * 2^n) * (D - q + k).choose k) := Nat.mul_le_mul_left q hD_le'
    _ = (n * 2^n) * q * (D - q + k).choose k := by ring

theorem poly_regularity_binomial_loss_proof (n : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ (k q D : ℕ) (a b : ℚ), k ≤ n → 1 ≤ D → 2*q ≤ D →
      0 ≤ a → 0 ≤ b →
      (a+b) * ((D-q+k).choose k : ℚ) ≤ a * ((D+k).choose k : ℚ) →
      b ≤ (C : ℚ) * a * (q : ℚ) / (D : ℚ) := by
  refine ⟨n * 2^n + 1, by omega, ?_⟩
  intro k q D a b hk hD h2q ha hb hle
  by_cases hkzero : k = 0
  · subst hkzero
    simp only [Nat.choose_zero_right, Nat.cast_one, mul_one] at hle
    have hb0 : b ≤ 0 := by linarith
    have hbzero : b = 0 := by linarith
    subst hbzero
    have hCpos : 0 ≤ ((n * 2^n + 1 : ℕ) : ℚ) * a * (q : ℚ) / (D : ℚ) := by
      apply div_nonneg
      · apply mul_nonneg
        · apply mul_nonneg (by positivity) ha
        · positivity
      · positivity
    linarith
  have hkpos : 0 < k := by omega
  by_cases ha0 : a = 0
  · subst ha0
    simp only [zero_add] at hle
    have hpos : 0 < ((D - q + k).choose k : ℚ) := by
      have : 0 < (D - q + k).choose k := Nat.choose_pos (by omega)
      positivity
    have hb0 : b ≤ 0 := by
      nlinarith
    have hbzero : b = 0 := by linarith
    subst hbzero
    have hCpos : 0 ≤ ((n * 2^n + 1 : ℕ) : ℚ) * 0 * (q : ℚ) / (D : ℚ) := by positivity
    linarith
  have hchoose_pos : 0 < (D - q + k).choose k := Nat.choose_pos (by omega)
  have hchoose_qpos : 0 < ((D - q + k).choose k : ℚ) := by positivity
  have hD_qpos : 0 < (D : ℚ) := by positivity
  have hdiff_nat := choose_diff_bound n D q k hk hkpos hD h2q
  have hdiff_q : (D : ℚ) * (((D + k).choose k : ℚ) - ((D - q + k).choose k : ℚ)) ≤
      ((n * 2^n + 1 : ℕ) : ℚ) * (q : ℚ) * ((D - q + k).choose k : ℚ) := by
    have hdiff_cast : ((D * ((D + k).choose k - (D - q + k).choose k) : ℕ) : ℚ) ≤
        (((n * 2^n + 1) * q * (D - q + k).choose k : ℕ) : ℚ) := by
      have hle' : (n * 2^n) * q * (D - q + k).choose k ≤ (n * 2^n + 1) * q * (D - q + k).choose k := by
        apply Nat.mul_le_mul_right
        apply Nat.mul_le_mul_right
        omega
      exact_mod_cast hdiff_nat.trans hle'
    have hnat_sub : (((D + k).choose k - (D - q + k).choose k : ℕ) : ℚ) =
        ((D + k).choose k : ℚ) - ((D - q + k).choose k : ℚ) :=
      Nat.cast_sub (R := ℚ) (Nat.choose_le_choose k (by omega))
    calc
      (D : ℚ) * (((D + k).choose k : ℚ) - ((D - q + k).choose k : ℚ))
      _ = (D : ℚ) * (((D + k).choose k - (D - q + k).choose k : ℕ) : ℚ) := by rw [hnat_sub]
      _ = ((D * ((D + k).choose k - (D - q + k).choose k) : ℕ) : ℚ) := by push_cast; rfl
      _ ≤ (((n * 2^n + 1) * q * (D - q + k).choose k : ℕ) : ℚ) := hdiff_cast
      _ = ((n * 2^n + 1 : ℕ) : ℚ) * (q : ℚ) * ((D - q + k).choose k : ℚ) := by push_cast; ring
  have hble : b * ((D - q + k).choose k : ℚ) ≤ a * (((D + k).choose k : ℚ) - ((D - q + k).choose k : ℚ)) := by
    linarith
  have hmulD : (D : ℚ) * (b * ((D - q + k).choose k : ℚ)) ≤
      a * ((D : ℚ) * (((D + k).choose k : ℚ) - ((D - q + k).choose k : ℚ))) := by
    calc
      (D : ℚ) * (b * ((D - q + k).choose k : ℚ))
      _ = (D : ℚ) * (b * ((D - q + k).choose k : ℚ)) := rfl
      _ ≤ (D : ℚ) * (a * (((D + k).choose k : ℚ) - ((D - q + k).choose k : ℚ))) := by
        nlinarith
      _ = a * ((D : ℚ) * (((D + k).choose k : ℚ) - ((D - q + k).choose k : ℚ))) := by ring
  have hfinal : (D : ℚ) * (b * ((D - q + k).choose k : ℚ)) ≤
      a * (((n * 2^n + 1 : ℕ) : ℚ) * (q : ℚ) * ((D - q + k).choose k : ℚ)) := by
    apply hmulD.trans
    have := mul_le_mul_of_nonneg_left hdiff_q (by positivity : 0 ≤ a)
    exact this
  have hdiv : b ≤ ((n * 2^n + 1 : ℕ) : ℚ) * a * (q : ℚ) / (D : ℚ) := by
    have h1 : b * ((D : ℚ) * ((D - q + k).choose k : ℚ)) ≤
        (((n * 2^n + 1 : ℕ) : ℚ) * a * (q : ℚ) / (D : ℚ)) * ((D : ℚ) * ((D - q + k).choose k : ℚ)) := by
      calc
        b * ((D : ℚ) * ((D - q + k).choose k : ℚ))
        _ = (D : ℚ) * (b * ((D - q + k).choose k : ℚ)) := by ring
        _ ≤ a * (((n * 2^n + 1 : ℕ) : ℚ) * (q : ℚ) * ((D - q + k).choose k : ℚ)) := hfinal
        _ = (((n * 2^n + 1 : ℕ) : ℚ) * a * (q : ℚ) / (D : ℚ)) * ((D : ℚ) * ((D - q + k).choose k : ℚ)) := by
          have hDne : (D : ℚ) ≠ 0 := by positivity
          calc
            a * (((n * 2^n + 1 : ℕ) : ℚ) * (q : ℚ) * ((D - q + k).choose k : ℚ))
            _ = (((n * 2^n + 1 : ℕ) : ℚ) * a * (q : ℚ) / (D : ℚ) * (D : ℚ)) * ((D - q + k).choose k : ℚ) := by
              rw [div_mul_cancel₀ _ hDne]
              ring
            _ = (((n * 2^n + 1 : ℕ) : ℚ) * a * (q : ℚ) / (D : ℚ)) * ((D : ℚ) * ((D - q + k).choose k : ℚ)) := by ring
    have hprod_pos : 0 < (D : ℚ) * ((D - q + k).choose k : ℚ) := by positivity
    exact le_of_mul_le_mul_right h1 hprod_pos
  exact hdiv

lemma mem_pointIdealOver_iff {n : ℕ} {F : Type*} [Field F] (p : FieldPoint n F) (g : FieldPoly n F) :
    g ∈ pointIdealOver p ↔ MvPolynomial.eval p g = 0 := by
  dsimp [pointIdealOver]
  rw [MvPolynomial.mem_vanishingIdeal_iff]
  simp only [Set.mem_singleton_iff, forall_eq, MvPolynomial.aeval_eq_eval]

lemma finset_prod_mem_ideal_pow {R : Type*} [CommRing R] (I : Ideal R) {ι : Type*}
    (s : Finset ι) (f : ι → R) (hf : ∀ i ∈ s, f i ∈ I) :
    ∏ i ∈ s, f i ∈ I ^ s.card := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.prod_empty, Finset.card_empty, pow_zero, Ideal.one_eq_top, Submodule.mem_top]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ, mul_comm (f a)]
    exact Ideal.mul_mem_mul (ih (fun i hi => hf _ (Finset.mem_insert_of_mem hi))) (hf _ (Finset.mem_insert_self _ _))

lemma matrix_det_mem_pow_of_rows_mem {R : Type*} [CommRing R] (I : Ideal R)
    {m : Type*} [Fintype m] [DecidableEq m] (N : Matrix m m R)
    (S : Finset m) (hS : ∀ i ∈ S, ∀ j : m, N i j ∈ I)
    (h : ℕ) (hhS : h ≤ S.card) :
    N.det ∈ I ^ h := by
  rw [Matrix.det_apply]
  apply Ideal.sum_mem
  intro σ _
  let T : Finset m := S.image σ.symm
  have hT_card : T.card = S.card := Finset.card_image_of_injective S σ.symm.injective
  have hT_sub : T ⊆ Finset.univ := Finset.subset_univ T
  have hprod : (∏ i, N (σ i) i) = (∏ i ∈ T, N (σ i) i) * (∏ i ∈ (Finset.univ \ T), N (σ i) i) := by
    rw [← Finset.prod_sdiff hT_sub, mul_comm]
  rw [hprod]
  have hT_mem : ∏ i ∈ T, N (σ i) i ∈ I ^ T.card := by
    apply finset_prod_mem_ideal_pow
    intro i hi
    rcases Finset.mem_image.mp hi with ⟨k, hkS, rfl⟩
    rw [Equiv.apply_symm_apply]
    exact hS k hkS _
  have hT_le : I ^ T.card ≤ I ^ h := by
    rw [hT_card]
    exact Ideal.pow_le_pow_right hhS
  have h1 : ∏ i ∈ T, N (σ i) i ∈ I ^ h := hT_le hT_mem
  have h2 : (∏ i ∈ T, N (σ i) i) * (∏ i ∈ (Finset.univ \ T), N (σ i) i) ∈ I ^ h :=
    Ideal.mul_mem_right _ _ h1
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hsign | hsign
  · rw [hsign, one_smul]
    exact h2
  · rw [hsign, Units.neg_smul, one_smul]
    exact Submodule.neg_mem (I ^ h) h2

theorem poly_matrix_multiplicity_proof {n a b q h : ℕ}
    (A : Matrix (Fin a) (Fin b) (Poly n)) (p : Point n)
    (rows : Fin q ↪ Fin a) (cols : Fin q ↪ Fin b) (hhq : h ≤ q)
    (hrank : Matrix.rank (fun i j => MvPolynomial.eval p (A i j)) ≤ q-h) :
    OrderAtLeast (Matrix.det (A.submatrix rows cols)) p h := by
  by_cases hh : h = 0
  · subst hh
    change Matrix.det (A.submatrix rows cols) ∈ (pointIdealOver p) ^ 0
    rw [pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  have hpos : 1 ≤ h := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hh)
  have hqpos : 1 ≤ q := hpos.trans hhq
  let M := A.submatrix rows cols
  let Ap : Matrix (Fin a) (Fin b) ℂ := fun i j => MvPolynomial.eval p (A i j)
  let Mp : Matrix (Fin q) (Fin q) ℂ := fun i j => MvPolynomial.eval p (M i j)
  have hMp_sub : Mp = Ap.submatrix rows cols := by
    ext i j
    rfl
  have hMp_rank : Mp.rank ≤ q - h := by
    rw [hMp_sub]
    exact (Matrix.rank_submatrix_le Ap rows cols).trans hrank
  obtain ⟨V, U, e, hV, hU, heq⟩ := Matrix.exists_rank_normal_form Mp
  have hVdet : IsUnit V.det := (Matrix.isUnit_iff_isUnit_det (A := V)).1 hV
  have hUdet : IsUnit U.det := (Matrix.isUnit_iff_isUnit_det (A := U)).1 hU
  let c : ℂ := V.det * U.det
  have hc : IsUnit c := IsUnit.mul hVdet hUdet
  have hcne : c ≠ 0 := hc.ne_zero
  let VP : Matrix (Fin q) (Fin q) (Poly n) := V.map MvPolynomial.C
  let UP : Matrix (Fin q) (Fin q) (Poly n) := U.map MvPolynomial.C
  let N : Matrix (Fin q) (Fin q) (Poly n) := VP * M * UP
  let S : Finset (Fin q) :=
    Finset.image (fun k : Fin (Fintype.card (Fin q) - Mp.rank) => e.symm (Sum.inr k)) Finset.univ
  have hS_card : S.card = q - Mp.rank := by
    have hinj : Function.Injective (fun k : Fin (Fintype.card (Fin q) - Mp.rank) => e.symm (Sum.inr k)) := by
      intro k1 k2 hk
      have h1 := e.symm.injective hk
      exact Sum.inr.inj h1
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin, Fintype.card_fin]
  have hhS : h ≤ S.card := by
    rw [hS_card]
    omega
  have hN_eval : ∀ i j, MvPolynomial.eval p (N i j) = (V * Mp * U) i j := by
    intro i j
    have hNmap : N.map (MvPolynomial.eval p) = V * Mp * U := by
      dsimp [N, VP, UP]
      rw [Matrix.map_mul, Matrix.map_mul]
      have hVP : VP.map (MvPolynomial.eval p) = V := by
        ext i1 j1
        change MvPolynomial.eval p (MvPolynomial.C (V i1 j1)) = V i1 j1
        exact MvPolynomial.eval_C (V i1 j1)
      have hUP : UP.map (MvPolynomial.eval p) = U := by
        ext i1 j1
        change MvPolynomial.eval p (MvPolynomial.C (U i1 j1)) = U i1 j1
        exact MvPolynomial.eval_C (U i1 j1)
      have hMmap : M.map (MvPolynomial.eval p) = Mp := by
        ext i1 j1
        rfl
      rw [hVP, hUP, hMmap]
    have := congr_fun (congr_fun hNmap i) j
    exact this
  have hN_rows : ∀ i ∈ S, ∀ j, N i j ∈ pointIdealOver p := by
    intro i hi j
    rw [mem_pointIdealOver_iff, hN_eval, heq]
    rcases Finset.mem_image.mp hi with ⟨k, _, rfl⟩
    simp only [Matrix.submatrix_apply, Equiv.apply_symm_apply]
    cases h : e j with
    | inl j1 =>
      rw [Matrix.fromBlocks_apply₂₁]
      rfl
    | inr j2 =>
      rw [Matrix.fromBlocks_apply₂₂]
      rfl
  have hNdet_mem : N.det ∈ pointIdealOver p ^ h :=
    matrix_det_mem_pow_of_rows_mem (pointIdealOver p) N S hN_rows h hhS
  have hNdet_eq : N.det = MvPolynomial.C c * M.det := by
    have h1 : N.det = VP.det * M.det * UP.det := by
      dsimp [N]
      rw [Matrix.det_mul, Matrix.det_mul]
    have hVPdet : VP.det = MvPolynomial.C V.det := (RingHom.map_det MvPolynomial.C V).symm
    have hUPdet : UP.det = MvPolynomial.C U.det := (RingHom.map_det MvPolynomial.C U).symm
    rw [h1, hVPdet, hUPdet]
    dsimp [c]
    rw [map_mul]
    ring
  have hMdet : M.det = MvPolynomial.C c⁻¹ * N.det := by
    rw [hNdet_eq, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hcne, map_one, one_mul]
  rw [hMdet]
  exact Ideal.mul_mem_left (pointIdealOver p ^ h) (MvPolynomial.C c⁻¹) hNdet_mem

end DistinctDistances.TrackA
