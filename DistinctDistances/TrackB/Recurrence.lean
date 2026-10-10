import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
Finite real recurrence interfaces for concentration.tex:1128–1174. These are
independent of the shared geometry and do not assume uniform bounds for the sample.
-/

namespace DistinctDistances.TrackB

set_option autoImplicit false

open scoped BigOperators

/-- B35's finite maximum principle. The source of each affine transition is one
available index; the half-barrier condition includes its nonnegative intercept. -/
theorem finite_affine_maximum_principle {ι : Type*} [DecidableEq ι]
    (indices interior : Finset ι) (R B : ι → ℝ)
    (transitions : ι → Finset ι) (a q : ι → ι → ℝ)
    (hsub : interior ⊆ indices)
    (hB : ∀ i ∈ indices, 0 < B i)
    (hR : ∀ i ∈ indices, 0 ≤ R i)
    (hend : ∀ i ∈ indices, i ∉ interior → R i ≤ B i)
    (htarget : ∀ i ∈ interior, transitions i ⊆ indices)
    (ha : ∀ i ∈ interior, ∀ j ∈ transitions i, 0 ≤ a i j)
    (hq : ∀ i ∈ interior, ∀ j ∈ transitions i, 0 ≤ q i j)
    (hbarrier : ∀ i ∈ interior, ∀ j ∈ transitions i,
      a i j + q i j * B j ≤ B i / 2)
    (hrec : ∀ i ∈ interior, ∃ j ∈ transitions i,
      R i ≤ a i j + q i j * R j) :
    ∀ i ∈ indices, R i ≤ B i := by
  intro i hi
  by_contra hbad
  have hi_gt : B i < R i := lt_of_not_ge hbad
  obtain ⟨m, hm, hmax⟩ :=
    Finset.exists_max_image indices (fun j => R j / B j) ⟨i, hi⟩
  let T := R m / B m
  have hT : 1 < T :=
    lt_of_lt_of_le ((lt_div_iff₀ (hB i hi)).mpr (by simpa using hi_gt)) (hmax i hi)
  have hm_gt : B m < R m := by
    have := (lt_div_iff₀ (hB m hm)).mp hT
    simpa using this
  have hm_int : m ∈ interior := by
    by_contra hm_out
    exact (not_le_of_gt hm_gt) (hend m hm hm_out)
  obtain ⟨j, hj, hstep⟩ := hrec m hm_int
  have hj_indices := htarget m hm_int hj
  have hj_bound : R j ≤ T * B j :=
    (div_le_iff₀ (hB j hj_indices)).mp (hmax j hj_indices)
  have hTpos : 0 < T := lt_trans (by norm_num) hT
  have hintercept : a m j ≤ T * a m j := by
    nlinarith [ha m hm_int j hj]
  have hlinear : q m j * R j ≤ T * (q m j * B j) := by
    have := mul_le_mul_of_nonneg_left hj_bound (hq m hm_int j hj)
    nlinarith
  have hbar := mul_le_mul_of_nonneg_left (hbarrier m hm_int j hj) hTpos.le
  have hRm : R m = T * B m := by
    exact (div_mul_cancel₀ (R m) (hB m hm).ne').symm
  nlinarith [hB m hm]

/-- B34's proof-friendly half-barriers; both specifications use these same constants.
The optional ambient endpoint has `B r = B 0`. concentration.tex:1141–1166. -/
theorem uniform_barriers_exist (r : ℕ) (hr : 2 ≤ r)
    (C C0 : ℝ) (hC : 1 ≤ C) (hC0 : 1 ≤ C0) :
    ∃ K B : ℕ → ℝ,
      (∀ h ≤ r, 0 < B h) ∧ 1 ≤ B 0 ∧ C0 ≤ B 0 ∧ B r = B 0 ∧
      (∀ h, 1 ≤ h → h < r → C0 < K h) ∧
      (∀ h i, 1 ≤ h → h < i → i < r → K i < K h) ∧
      (∀ h, 1 ≤ h → h < r → C * (1 + K h * B (h - 1)) ≤ B h / 2) ∧
      (∀ h i, 1 ≤ h → h < r → h < i → i ≤ r →
        C * B i / K h ^ (i - h) ≤ B h / 2) := by
  classical
  let c1 : ℝ := 4 * C + 4
  let κ : ℝ := 4 * C * c1 + 4
  let b0 : ℝ := C0 + 1
  let K : ℕ → ℝ := fun h => b0 * κ ^ (r - h)
  let B : ℕ → ℝ := fun h =>
    if h = r then b0 else b0 * ∏ j ∈ Finset.range h, (c1 * K (j + 1))
  have hb0 : 1 ≤ b0 := by dsimp [b0]; linarith
  have hb0pos : 0 < b0 := lt_of_lt_of_le (by norm_num) hb0
  have hCpos : 0 < C := by linarith
  have hc1 : 4 * C ≤ c1 := by dsimp [c1]; linarith
  have hc1pos : 0 < c1 := by dsimp [c1]; linarith
  have hc1one : 1 ≤ c1 := by dsimp [c1]; linarith
  have hκgt : 1 < κ := by dsimp [κ, c1]; nlinarith [hC]
  have hκpos : 0 < κ := lt_trans (by norm_num) hκgt
  have hκone : 1 ≤ κ := hκgt.le
  have hκtwice : 2 * C * c1 ≤ κ := by
    dsimp [κ]
    nlinarith [mul_nonneg (show 0 ≤ C by linarith) (show 0 ≤ c1 by linarith)]
  have hκc1 : c1 ≤ κ := by
    dsimp [κ]
    nlinarith [hC, hc1pos]
  have hKpos (h : ℕ) : 0 < K h := by
    dsimp [K, b0]
    exact mul_pos (by linarith) (pow_pos hκpos _)
  have hKge1 (h : ℕ) : 1 ≤ K h := by
    have hp : 1 ≤ κ ^ (r - h) := one_le_pow₀ hκone
    have hmul := mul_le_mul_of_nonneg_left hp hb0pos.le
    calc
      1 ≤ b0 := hb0
      _ = b0 * 1 := by simp
      _ ≤ b0 * κ ^ (r - h) := hmul
  have hKbase (h : ℕ) : b0 ≤ K h := by
    have hp : 1 ≤ κ ^ (r - h) := one_le_pow₀ hκone
    change b0 ≤ b0 * κ ^ (r - h)
    calc
      b0 = b0 * 1 := by simp
      _ ≤ b0 * κ ^ (r - h) := mul_le_mul_of_nonneg_left hp hb0pos.le
  have hKstep (h : ℕ) (hh : h < r) : K h = κ * K (h + 1) := by
    have hexp : r - h = (r - (h + 1)) + 1 := by omega
    simp only [K]
    rw [hexp, pow_succ]
    nlinarith
  have hKdec (h : ℕ) (hh : h < r) : K (h + 1) < K h := by
    have hmul := mul_lt_mul_of_pos_right hκgt (hKpos (h + 1))
    calc
      K (h + 1) = 1 * K (h + 1) := by simp
      _ < κ * K (h + 1) := by simpa using hmul
      _ = K h := (hKstep h hh).symm
  have hKmono (h i : ℕ) (hhi : h < i) (hir : i < r) : K i < K h := by
    have hbound : ∀ n, h + 1 ≤ n → n < r → K n ≤ K (h + 1) := by
      intro n hle
      induction n, hle using Nat.le_induction with
      | base => intro _; exact le_rfl
      | succ n hle ih =>
          intro hn
          exact (hKdec n (by omega)).le.trans (ih (by omega))
    have hstart : h + 1 ≤ i := by omega
    exact (hbound i hstart hir).trans_lt (hKdec h (by omega))
  have hKratio (h j : ℕ) (hhj : h < j) (hj : j < r) :
      κ * K j ≤ K h := by
    have hstep := hKstep h (by omega)
    have hmono : K j ≤ K (h + 1) := by
      by_cases heq : j = h + 1
      · simpa [heq]
      · have hlt' : h + 1 < j := by omega
        exact (hKmono (h + 1) j hlt' hj).le
    calc
      κ * K j ≤ κ * K (h + 1) := mul_le_mul_of_nonneg_left hmono hκpos.le
      _ = K h := hstep.symm
  have hBend : B r = b0 := by simp [B]
  have hBformula (h : ℕ) (hh : h < r) :
      B h = b0 * ∏ j ∈ Finset.range h, (c1 * K (j + 1)) := by
    simp [B, ne_of_lt hh]
  have hBzero : B 0 = b0 := by
    simp [B, show 0 ≠ r by omega]
  have hBrec (h : ℕ) (hh : 1 ≤ h) (hhr : h < r) :
      B h = c1 * K h * B (h - 1) := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : h ≠ 0)
    simp [B, show n + 1 ≠ r by omega, show n ≠ r by omega,
      Nat.succ_sub_one, Finset.prod_range_succ, mul_assoc, mul_comm, mul_left_comm]
  have prod_range_pos (n : ℕ) (f : ℕ → ℝ)
      (hf : ∀ j, j < n → 0 < f j) : 0 < ∏ j ∈ Finset.range n, f j := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.prod_range_succ]
        exact mul_pos (ih (fun j hj => hf j (by omega))) (hf n (by omega))
  have hfactorpos (j : ℕ) : 0 < c1 * K (j + 1) :=
    mul_pos hc1pos (hKpos (j + 1))
  have hBpos (h : ℕ) (hh : h < r) : 0 < B h := by
    rw [hBformula h hh]
    apply mul_pos hb0pos
    exact prod_range_pos h (fun j => c1 * K (j + 1)) (fun j hj => hfactorpos j)
  have hfactorge (j : ℕ) : 1 ≤ c1 * K j := by
    have hmul := mul_le_mul_of_nonneg_left (hKge1 j) hc1pos.le
    calc
      1 ≤ c1 := hc1one
      _ = c1 * 1 := by simp
      _ ≤ c1 * K j := hmul
  have hBbase : ∀ h, h < r → b0 ≤ B h := by
    intro h
    induction h with
    | zero =>
        intro hh
        rw [hBzero]
    | succ n ih =>
        intro hh
        rw [hBrec (n + 1) (by omega) hh]
        have hprev := ih (by omega)
        have hgrow : B n ≤ c1 * K (n + 1) * B n := by
          calc
            B n = 1 * B n := by simp
            _ ≤ (c1 * K (n + 1)) * B n :=
              mul_le_mul_of_nonneg_right (hfactorge (n + 1)) (hBpos n (by omega)).le
        exact hprev.trans hgrow
  have hBge1 (h : ℕ) (hh : h < r) : 1 ≤ B h :=
    le_trans hb0 (hBbase h hh)
  have hlow (h : ℕ) (hh : 1 ≤ h) (hhr : h < r) :
      C * (1 + K h * B (h - 1)) ≤ B h / 2 := by
    have hrec := hBrec h hh hhr
    have hprev : 1 ≤ B (h - 1) := hBge1 (h - 1) (by omega)
    have hKh : 1 ≤ K h := hKge1 h
    have hX : 1 ≤ K h * B (h - 1) := by
      calc
        1 ≤ K h := hKh
        _ = K h * 1 := by simp
        _ ≤ K h * B (h - 1) := by
          exact mul_le_mul_of_nonneg_left hprev (hKpos h).le
    have hcoeff := mul_le_mul_of_nonneg_right (show 2 * C ≤ c1 by linarith)
      (show 0 ≤ K h * B (h - 1) by positivity)
    have hrec' : B h = c1 * (K h * B (h - 1)) := by rw [hrec]; nlinarith
    nlinarith [hX, hcoeff, hrec']
  have hBhighDiff (h : ℕ) : ∀ d, 1 ≤ d → h + d < r →
      C * B (h + d) ≤ B h / 2 * K h ^ d := by
    intro d hd
    induction d with
    | zero => omega
    | succ d ih =>
        intro hsum
        by_cases hd0 : d = 0
        · subst d
          have hrec := hBrec (h + 1) (by omega) hsum
          have hrecNorm : B (h + 1) = c1 * K (h + 1) * B h := by
            simpa using hrec
          have hratio := hKratio h (h + 1) (by omega) hsum
          have hscaled := mul_le_mul_of_nonneg_right hκtwice (hKpos (h + 1)).le
          have hcoeff : C * (c1 * K (h + 1)) ≤ K h / 2 := by
            nlinarith [hscaled, hratio]
          have hbase : C * B (h + 1) ≤ B h / 2 * K h := by
            calc
              C * B (h + 1) = (C * (c1 * K (h + 1))) * B h := by
                rw [hrecNorm]
                nlinarith
              _ ≤ (K h / 2) * B h :=
                mul_le_mul_of_nonneg_right hcoeff (hBpos h (by omega)).le
              _ = B h / 2 * K h := by nlinarith
          have hexp : 0 + 1 = (1 : ℕ) := rfl
          rw [hexp, pow_one]
          exact hbase
        · have hdpos : 1 ≤ d := by omega
          have hprev := ih hdpos (by omega)
          have hrec := hBrec (h + (d + 1)) (by omega) hsum
          have hrecNorm : B (h + (d + 1)) =
              c1 * K (h + (d + 1)) * B (h + d) := by
            have hsub : h + (d + 1) - 1 = h + d := by omega
            simpa [hsub] using hrec
          have hratio := hKratio h (h + (d + 1)) (by omega) hsum
          have hfactor : c1 * K (h + (d + 1)) ≤ K h := by
            calc
              c1 * K (h + (d + 1)) ≤ κ * K (h + (d + 1)) :=
                mul_le_mul_of_nonneg_right hκc1 (hKpos _).le
              _ ≤ K h := hratio
          have hterm : 0 ≤ B h / 2 * K h ^ d :=
            mul_nonneg (div_nonneg (hBpos h (by omega)).le (by norm_num))
              (pow_pos (hKpos h) _).le
          calc
            C * B (h + (d + 1)) =
                (c1 * K (h + (d + 1))) * (C * B (h + d)) := by
              rw [hrecNorm]
              nlinarith
            _ ≤ (c1 * K (h + (d + 1))) * (B h / 2 * K h ^ d) :=
              mul_le_mul_of_nonneg_left hprev (mul_pos hc1pos (hKpos _)).le
            _ ≤ K h * (B h / 2 * K h ^ d) :=
              mul_le_mul_of_nonneg_right hfactor hterm
            _ = B h / 2 * K h ^ (d + 1) := by rw [pow_succ]; nlinarith
  have hBhigh (h i : ℕ) (hhi : h < i) (hir : i < r) :
      C * B i ≤ B h / 2 * K h ^ (i - h) := by
    have hdiff : i = h + (i - h) := by omega
    have hpos : 1 ≤ i - h := by omega
    have hsum : h + (i - h) < r := by omega
    rw [hdiff]
    rw [show (h + (i - h)) - h = i - h by omega]
    exact hBhighDiff h (i - h) hpos hsum
  have hambientHigh (h : ℕ) (hh : 1 ≤ h) (hhr : h < r) :
      C * B r ≤ B h / 2 * K h ^ (r - h) := by
    have hrec := hBrec h hh hhr
    have hprev : b0 ≤ B (h - 1) := hBbase (h - 1) (by omega)
    have hKh : 1 ≤ K h := hKge1 h
    have hc1Kh : 2 * C ≤ c1 * K h := by
      have hc1' : 2 * C ≤ c1 := by dsimp [c1]; linarith
      calc
        2 * C ≤ c1 := hc1'
        _ = c1 * 1 := by simp
        _ ≤ c1 * K h := mul_le_mul_of_nonneg_left hKh hc1pos.le
    have hdouble : 2 * C * b0 ≤ B h := by
      calc
        2 * C * b0 ≤ (c1 * K h) * b0 :=
          mul_le_mul_of_nonneg_right hc1Kh hb0pos.le
        _ ≤ (c1 * K h) * B (h - 1) :=
          mul_le_mul_of_nonneg_left hprev (mul_pos hc1pos (hKpos h)).le
        _ = B h := by rw [hrec]
    have hhalf : C * b0 ≤ B h / 2 := by linarith
    have hpow : 1 ≤ K h ^ (r - h) := one_le_pow₀ hKh
    calc
      C * B r = C * b0 := by rw [hBend]
      _ ≤ B h / 2 := hhalf
      _ = B h / 2 * 1 := by simp
      _ ≤ B h / 2 * K h ^ (r - h) :=
        mul_le_mul_of_nonneg_left hpow
          (div_nonneg (hBpos h hhr).le (by norm_num))
  refine ⟨K, B, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h hh
    by_cases heq : h = r
    · subst h
      rw [hBend]
      exact hb0pos
    · exact hBpos h (by omega)
  · simpa [B, b0, show 0 ≠ r by omega] using hb0
  · have hc0b0 : C0 ≤ b0 := by dsimp [b0]; linarith
    simpa [B, show 0 ≠ r by omega] using hc0b0
  · calc
      B r = b0 := hBend
      _ = B 0 := hBzero.symm
  · intro h hh hhr
    have hC0ltb0 : C0 < b0 := by dsimp [b0]; linarith
    exact hC0ltb0.trans_le (hKbase h)
  · intro h i hh hhi hir
    exact hKmono h i hhi hir
  · exact hlow
  · intro h i hh hhr hhi hir
    have hbound : C * B i ≤ B h / 2 * K h ^ (i - h) := by
      rcases lt_or_eq_of_le hir with hi | hi
      · exact hBhigh h i hhi hi
      · subst i
        exact hambientHigh h hh hhr
    exact (div_le_iff₀ (pow_pos (hKpos h) _)).2 hbound

/-- B33/B35: close the paper's finite system, omitting the ambient endpoint in case (b).
No maximum over an empty high-transition set is used in the statement. -/
theorem concentration_recurrence_bound (r : ℕ) (hr : 2 ≤ r)
    (C C0 : ℝ) (hC : 1 ≤ C) (hC0 : 1 ≤ C0) :
    ∃ K B : ℕ → ℝ,
      (∀ h ≤ r, 0 < B h) ∧
      (∀ h, 1 ≤ h → h < r → C0 < K h) ∧
      ∀ (ambient : Bool) (R : ℕ → ℝ),
        (∀ h ≤ r, 0 ≤ R h) → R 0 ≤ 1 →
        (ambient = true → R r ≤ C0) →
        (∀ h, 1 ≤ h → h < r →
          R h ≤ C * (1 + K h * R (h - 1)) ∨
          ∃ i, h < i ∧ (i < r ∨ (ambient = true ∧ i = r)) ∧
            R h ≤ C * R i / K h ^ (i - h)) →
        ∀ h, (h < r ∨ (ambient = true ∧ h = r)) → R h ≤ B h := by
  classical
  obtain ⟨K, B, hB, hB0, hC0B, hBr, hK, _, hlow, hhigh⟩ :=
    uniform_barriers_exist r hr C C0 hC hC0
  refine ⟨K, B, hB, hK, ?_⟩
  intro ambient R hR hR0 hRr hrec
  let indices := Finset.range r ∪ if ambient = true then {r} else ∅
  let interior := (Finset.range r).erase 0
  let transitions : ℕ → Finset ℕ := fun h => indices.filter (fun j => j = h - 1 ∨ h < j)
  let a : ℕ → ℕ → ℝ := fun h j => if j = h - 1 then C else 0
  let q : ℕ → ℕ → ℝ := fun h j =>
    if j = h - 1 then C * K h else C / K h ^ (j - h)
  have hindices (j : ℕ) : j ∈ indices ↔ j < r ∨ (ambient = true ∧ j = r) := by
    by_cases hamb : ambient = true <;> simp [indices, hamb, or_comm]
  have hinterior (j : ℕ) : j ∈ interior ↔ 1 ≤ j ∧ j < r := by
    simp only [interior, Finset.mem_erase, Finset.mem_range]
    omega
  have hKpos (h : ℕ) (hh : h ∈ interior) : 0 < K h := by
    have hi := (hinterior h).mp hh
    linarith [hK h hi.1 hi.2]
  have hCnonneg : 0 ≤ C := by linarith
  have hmax := finite_affine_maximum_principle indices interior R B transitions a q
    (by
      intro h hh
      exact (hindices h).mpr (Or.inl ((hinterior h).mp hh).2))
    (by
      intro h hh
      exact hB h (by have := (hindices h).mp hh; omega))
    (by
      intro h hh
      exact hR h (by have := (hindices h).mp hh; omega))
    (by
      intro h hh hnot
      rcases (hindices h).mp hh with hh | ⟨hamb, rfl⟩
      · have hz : h = 0 := by
          have hn := mt (hinterior h).mpr hnot
          omega
        simpa [hz] using hR0.trans hB0
      · exact (hRr hamb).trans (hBr.symm ▸ hC0B))
    (by intro h hh; exact Finset.filter_subset _ _)
    (by
      intro h hh j hj
      dsimp [a]
      split
      · exact hCnonneg
      · exact le_rfl)
    (by
      intro h hh j hj
      dsimp [q]
      split
      · exact mul_nonneg hCnonneg (hKpos h hh).le
      · exact div_nonneg hCnonneg (pow_pos (hKpos h hh) _).le)
    (by
      intro h hh j hj
      obtain ⟨hjmem, hj⟩ := Finset.mem_filter.mp hj
      have hi := (hinterior h).mp hh
      by_cases hjlow : j = h - 1
      · subst j
        simpa [a, q, mul_add, mul_assoc] using hlow h hi.1 hi.2
      · have hlt : h < j := hj.resolve_left hjlow
        have hjle : j ≤ r := by have := (hindices j).mp hjmem; omega
        simpa [a, q, hjlow, div_mul_eq_mul_div] using hhigh h j hi.1 hi.2 hlt hjle)
    (by
      intro h hh
      have hi := (hinterior h).mp hh
      rcases hrec h hi.1 hi.2 with hstep | ⟨j, hj, hjavail, hstep⟩
      · refine ⟨h - 1, ?_, ?_⟩
        · exact Finset.mem_filter.mpr
            ⟨(hindices (h - 1)).mpr (Or.inl (by omega)), Or.inl rfl⟩
        · simpa [a, q, mul_add, mul_assoc] using hstep
      · have hjlow : j ≠ h - 1 := by omega
        refine ⟨j, Finset.mem_filter.mpr ⟨(hindices j).mpr hjavail, Or.inr hj⟩, ?_⟩
        simpa [a, q, hjlow, div_mul_eq_mul_div] using hstep)
  intro h hh
  exact hmax h ((hindices h).mpr hh)


#print axioms finite_affine_maximum_principle
#print axioms concentration_recurrence_bound

end DistinctDistances.TrackB
