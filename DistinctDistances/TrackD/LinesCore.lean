import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Real-analytic and counting lemmas for `geo:terminal.lines-core`

The line case of terminal deletion (`secants.tex:254–331`) is proved here in an abstract form:
lines and planes are arbitrary types with an incidence relation satisfying a
Szemerédi–Trotter-type bound. The proof replaces the paper's dyadic decompositions by layer-cake
sums, and its Hölder step by `holder_layer`.
-/

namespace DistinctDistances
namespace TrackD
namespace LinesCore

open Finset

/-- One step of the integral comparison for `x ↦ x^{1-α}` (Bernoulli's inequality). -/
lemma rpow_step (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1) (x : ℝ) (hx : 0 ≤ x) :
    x ^ (1 - α) + (1 - α) * (x + 1) ^ (-α) ≤ (x + 1) ^ (1 - α) := by
  have hx1 : 0 < x + 1 := by linarith
  have hs : (-1 : ℝ) ≤ -1 / (x + 1) := by
    rw [neg_div, neg_le_neg_iff, div_le_one hx1]; linarith
  have hb := rpow_one_add_le_one_add_mul_self hs (by linarith : (0 : ℝ) ≤ 1 - α)
    (by linarith : 1 - α ≤ 1)
  have e1 : (1 : ℝ) + -1 / (x + 1) = x / (x + 1) := by field_simp; ring
  rw [e1, Real.div_rpow hx hx1.le] at hb
  have hpos : 0 < (x + 1) ^ (1 - α) := Real.rpow_pos_of_pos hx1 _
  rw [div_le_iff₀ hpos] at hb
  have hy : (x + 1) ^ (1 - α) = (x + 1) ^ (-α) * (x + 1) := by
    rw [show (1 : ℝ) - α = -α + 1 by ring, Real.rpow_add hx1, Real.rpow_one]
  rw [hy] at hb ⊢
  have e2 : (1 + (1 - α) * (-1 / (x + 1))) * ((x + 1) ^ (-α) * (x + 1)) =
      (x + 1) ^ (-α) * (x + 1) - (1 - α) * (x + 1) ^ (-α) := by
    field_simp; ring
  rw [e2] at hb
  linarith

/-- `Σ_{j<J} (j+1)^{-α} ≤ J^{1-α}/(1-α)` for `0 ≤ α < 1`. -/
lemma sum_rpow_neg_le (α : ℝ) (h0 : 0 ≤ α) (h1 : α < 1) (J : ℕ) :
    ∑ j ∈ range J, ((j : ℝ) + 1) ^ (-α) ≤ (J : ℝ) ^ (1 - α) / (1 - α) := by
  have hα : 0 < 1 - α := by linarith
  induction J with
  | zero => simp [Real.zero_rpow hα.ne']
  | succ J ih =>
    rw [sum_range_succ]
    have hstep := rpow_step α h0 h1 (J : ℝ) (Nat.cast_nonneg J)
    push_cast
    rw [le_div_iff₀ hα] at ih ⊢
    rw [add_mul]
    nlinarith

/-- Integer powers of real powers, for nonnegative bases. -/
lemma rpow_pow_eq (x r : ℝ) (hx : 0 ≤ x) (n : ℕ) : (x ^ r) ^ n = x ^ (r * n) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]

/-- The Hölder step of the layer cake: for `a_j ≥ 0`,
`(Σ_{j<J} a_j^{2/3})^3 ≤ 16 J^{1/2} Σ_{j<J} (j+1)^{3/2} a_j^2`. -/
lemma holder_layer (J : ℕ) (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) :
    (∑ j ∈ range J, a j ^ ((2 : ℝ) / 3)) ^ 3 ≤
      16 * (J : ℝ) ^ ((1 : ℝ) / 2) * ∑ j ∈ range J, ((j : ℝ) + 1) ^ ((3 : ℝ) / 2) * a j ^ 2 := by
  have hj : ∀ j : ℕ, (0 : ℝ) < (j : ℝ) + 1 := fun j => by positivity
  set f : ℕ → ℝ := fun j => a j ^ ((2 : ℝ) / 3) * ((j : ℝ) + 1) ^ ((1 : ℝ) / 2)
  set g : ℕ → ℝ := fun j => ((j : ℝ) + 1) ^ (-((1 : ℝ) / 2))
  have hfg : ∀ j, a j ^ ((2 : ℝ) / 3) = f j * g j := by
    intro j
    simp only [f, g, mul_assoc, ← Real.rpow_add (hj j)]
    norm_num
  have hpq : Real.HolderConjugate 3 (3 / 2) := Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hH := Real.inner_le_Lp_mul_Lq_of_nonneg (range J) hpq
    (f := f) (g := g) (fun j _ => mul_nonneg (Real.rpow_nonneg (ha j) _)
      (Real.rpow_nonneg (hj j).le _)) (fun j _ => Real.rpow_nonneg (hj j).le _)
  have hf3 : ∀ j, f j ^ (3 : ℝ) = ((j : ℝ) + 1) ^ ((3 : ℝ) / 2) * a j ^ 2 := by
    intro j
    simp only [f]
    rw [Real.mul_rpow (Real.rpow_nonneg (ha j) _) (Real.rpow_nonneg (hj j).le _),
      ← Real.rpow_mul (ha j),
      ← Real.rpow_mul (hj j).le]
    norm_num
    ring
  have hg3 : ∀ j, g j ^ ((3 : ℝ) / 2) = ((j : ℝ) + 1) ^ (-(3 / 4 : ℝ)) := by
    intro j
    simp only [g]
    rw [← Real.rpow_mul (hj j).le]
    norm_num
  simp only [hf3, hg3] at hH
  have hS2 := sum_rpow_neg_le (3 / 4) (by norm_num) (by norm_num) J
  rw [show (1 : ℝ) - 3 / 4 = 1 / 4 by norm_num] at hS2
  set S1 := ∑ j ∈ range J, ((j : ℝ) + 1) ^ ((3 : ℝ) / 2) * a j ^ 2
  set S2 := ∑ j ∈ range J, ((j : ℝ) + 1) ^ (-(3 / 4 : ℝ))
  have hS1 : 0 ≤ S1 := sum_nonneg fun j _ => by positivity
  have hS2n : 0 ≤ S2 := sum_nonneg fun j _ => by positivity
  have hsum : ∑ j ∈ range J, a j ^ ((2 : ℝ) / 3) = ∑ j ∈ range J, f j * g j :=
    sum_congr rfl fun j _ => hfg j
  have hT0 : 0 ≤ ∑ j ∈ range J, a j ^ ((2 : ℝ) / 3) :=
    sum_nonneg fun j _ => Real.rpow_nonneg (ha j) _
  rw [hsum] at hT0 ⊢
  have hcube := pow_le_pow_left₀ hT0 hH 3
  rw [mul_pow, rpow_pow_eq _ _ hS1, rpow_pow_eq _ _ hS2n] at hcube
  norm_num at hcube
  have hS2sq : S2 ^ 2 ≤ (4 * (J : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 := by
    apply pow_le_pow_left₀ hS2n
    have : (J : ℝ) ^ ((1 : ℝ) / 4) / (1 / 4) = 4 * (J : ℝ) ^ ((1 : ℝ) / 4) := by ring
    linarith
  have hJ : (4 * (J : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 = 16 * (J : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [mul_pow, rpow_pow_eq _ _ (Nat.cast_nonneg J)]
    norm_num
  calc (∑ j ∈ range J, f j * g j) ^ 3 ≤ S1 * S2 ^ 2 := hcube
    _ ≤ S1 * (16 * (J : ℝ) ^ ((1 : ℝ) / 2)) := by
        rw [← hJ]; exact mul_le_mul_of_nonneg_left hS2sq hS1
    _ = 16 * (J : ℝ) ^ ((1 : ℝ) / 2) * S1 := by ring

/-- For a non-increasing nonnegative sequence, `Σ_{j<J} (j+1) a_j^2 ≤ (Σ_{j<J} a_j)^2`. -/
lemma sum_succ_mul_sq_le (J : ℕ) (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hanti : ∀ i j, i ≤ j → a j ≤ a i) :
    ∑ j ∈ range J, ((j : ℝ) + 1) * a j ^ 2 ≤ (∑ j ∈ range J, a j) ^ 2 := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [sum_range_succ, sum_range_succ]
    have hlow : (J : ℝ) * a J ≤ ∑ j ∈ range J, a j := by
      have : ∑ _j ∈ range J, a J ≤ ∑ j ∈ range J, a j :=
        sum_le_sum fun j hj => hanti j J (mem_range.mp hj).le
      simpa using this
    have haJ := ha J
    nlinarith

/-- Absorption: `X ≤ 2C (X/A)^{2/3} T + 2CN` implies `X ≤ 4CN + 64 C^3 T^3 / A^2`. -/
lemma absorb (X A T N C : ℝ) (hX : 0 ≤ X) (hA : 0 < A) (hT : 0 ≤ T) (hN : 0 ≤ N)
    (hC : 0 ≤ C) (h : X ≤ 2 * C * (X / A) ^ ((2 : ℝ) / 3) * T + 2 * C * N) :
    X ≤ 4 * C * N + 64 * C ^ 3 * T ^ 3 / A ^ 2 := by
  have hT3 : 0 ≤ 64 * C ^ 3 * T ^ 3 / A ^ 2 := by positivity
  by_cases h4 : X ≤ 4 * C * N
  · linarith
  push Not at h4
  set y := (X / A) ^ ((1 : ℝ) / 3) with hy
  have hXA : 0 ≤ X / A := div_nonneg hX hA.le
  have hy0 : 0 ≤ y := Real.rpow_nonneg hXA _
  have hy3 : y ^ 3 = X / A := by
    rw [hy, rpow_pow_eq _ _ hXA]; norm_num
  have hy2 : (X / A) ^ ((2 : ℝ) / 3) = y ^ 2 := by
    rw [hy, rpow_pow_eq _ _ hXA]; norm_num
  rw [hy2] at h
  have hXeq : X = A * y ^ 3 := by rw [hy3]; field_simp
  -- `X < 4 C y^2 T`, hence `A y < 4 C T`
  have hlt : A * y ^ 3 < 4 * C * y ^ 2 * T := by nlinarith
  have hypos : 0 < y := by
    rcases hy0.lt_or_eq with h' | h'
    · exact h'
    · rw [← h'] at hlt; simp at hlt
  have hAy : A * y < 4 * C * T := by
    have hy2pos : 0 < y ^ 2 := by positivity
    nlinarith
  have hy_le : y ≤ 4 * C * T / A := by rw [le_div_iff₀ hA]; linarith
  have hcube : y ^ 3 ≤ (4 * C * T / A) ^ 3 := pow_le_pow_left₀ hy0 hy_le 3
  rw [hXeq]
  calc A * y ^ 3 ≤ A * (4 * C * T / A) ^ 3 := mul_le_mul_of_nonneg_left hcube hA.le
    _ = 64 * C ^ 3 * T ^ 3 / A ^ 2 := by field_simp; ring
    _ ≤ 4 * C * N + 64 * C ^ 3 * T ^ 3 / A ^ 2 := by nlinarith


/-! ### Abstract weighted line–plane sums

Lines `ι`, planes `κ`, an incidence relation `R` (here `ℓ ⊆ H`), integer line weights `n` (the
assigned masses `|S_ℓ|`) and plane occupancies `h` (`|P ∩ H|`). -/

section Abstract

open scoped Classical

variable {ι κ : Type*}

/-- `σ(H) = Σ_{ℓ ⊆ H} n_ℓ`. -/
noncomputable def sig (R : ι → κ → Prop) (L : Finset ι) (n : ι → ℕ) (H : κ) : ℝ :=
  ∑ ℓ ∈ L.filter (fun ℓ => R ℓ H), (n ℓ : ℝ)

/-- The layer `a_j = #{ℓ : n_ℓ > j}`. -/
noncomputable def layer (L : Finset ι) (n : ι → ℕ) (j : ℕ) : ℝ :=
  ((L.filter (fun ℓ => j < n ℓ)).card : ℝ)

lemma layer_nonneg (L : Finset ι) (n : ι → ℕ) (j : ℕ) : 0 ≤ layer L n j := Nat.cast_nonneg _

lemma layer_anti (L : Finset ι) (n : ι → ℕ) (i j : ℕ) (hij : i ≤ j) :
    layer L n j ≤ layer L n i := by
  unfold layer
  exact_mod_cast card_le_card (fun ℓ hℓ => by
    simp only [mem_filter] at hℓ ⊢; exact ⟨hℓ.1, lt_of_le_of_lt hij hℓ.2⟩)

lemma count_lt (m J : ℕ) (h : m ≤ J) :
    ∑ j ∈ range J, (if j < m then 1 else 0 : ℕ) = m := by
  rw [← card_filter]
  have : (range J).filter (fun j => j < m) = range m := by
    ext j; simp only [mem_filter, mem_range]; constructor
    · exact fun h' => h'.2
    · exact fun h' => ⟨lt_of_lt_of_le h' h, h'⟩
  rw [this, card_range]

lemma count_lt_le (m J : ℕ) : ∑ j ∈ range J, (if j < m then 1 else 0 : ℕ) ≤ m := by
  rw [← card_filter]
  calc ((range J).filter (fun j => j < m)).card ≤ (range m).card := by
        apply card_le_card; intro j; simp only [mem_filter, mem_range]; exact fun h' => h'.2
    _ = m := card_range m

/-- `Σ_{j<J} a_j ≤ Σ_ℓ n_ℓ`. -/
lemma sum_layer_le (L : Finset ι) (n : ι → ℕ) (J : ℕ) :
    ∑ j ∈ range J, layer L n j ≤ ∑ ℓ ∈ L, (n ℓ : ℝ) := by
  unfold layer
  have hnat : ∑ j ∈ range J, (L.filter (fun ℓ => j < n ℓ)).card ≤ ∑ ℓ ∈ L, n ℓ := by
    simp only [card_filter]
    rw [sum_comm]
    exact sum_le_sum fun ℓ _ => count_lt_le (n ℓ) J
  exact_mod_cast hnat

/-- Layer cake for a plane family: `Σ_{H ∈ G} σ(H) ≤ Σ_{j<J} I(L_{>j}, G)` when every line in a
plane of `G` has weight at most `J`. -/
lemma sum_sig_le_layers (R : ι → κ → Prop) (L : Finset ι) (G : Finset κ) (n : ι → ℕ) (J : ℕ)
    (hJ : ∀ ℓ ∈ L, ∀ H ∈ G, R ℓ H → n ℓ ≤ J) :
    ∑ H ∈ G, sig R L n H ≤
      ∑ j ∈ range J,
        ((((L.filter (fun ℓ => j < n ℓ)) ×ˢ G).filter (fun x => R x.1 x.2)).card : ℝ) := by
  unfold sig
  have hnat : ∑ H ∈ G, ∑ ℓ ∈ L.filter (fun ℓ => R ℓ H), n ℓ ≤
      ∑ j ∈ range J, (((L.filter (fun ℓ => j < n ℓ)) ×ˢ G).filter (fun x => R x.1 x.2)).card := by
    simp only [card_filter, sum_product, sum_filter]
    rw [sum_comm]
    calc ∑ ℓ ∈ L, ∑ H ∈ G, (if R ℓ H then n ℓ else 0)
        ≤ ∑ ℓ ∈ L, ∑ H ∈ G, ∑ j ∈ range J, (if j < n ℓ then (if R ℓ H then 1 else 0) else 0) := by
          apply sum_le_sum; intro ℓ hℓ; apply sum_le_sum; intro H hH
          by_cases hR : R ℓ H
          · simp only [hR, ite_true]
            exact le_of_eq (count_lt (n ℓ) J (hJ ℓ hℓ H hH hR)).symm
          · simp [hR]
      _ = ∑ ℓ ∈ L, ∑ j ∈ range J, ∑ H ∈ G,
            (if j < n ℓ then (if R ℓ H then 1 else 0) else 0) := by
          apply sum_congr rfl; intro ℓ _; exact sum_comm
      _ = ∑ j ∈ range J, ∑ ℓ ∈ L, ∑ H ∈ G,
            (if j < n ℓ then (if R ℓ H then 1 else 0) else 0) := sum_comm
      _ = ∑ j ∈ range J, ∑ ℓ ∈ L, (if j < n ℓ then ∑ H ∈ G, (if R ℓ H then 1 else 0) else 0) := by
          apply sum_congr rfl; intro j _; apply sum_congr rfl; intro ℓ _
          split_ifs <;> simp
  exact_mod_cast (by simpa only [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero] using hnat)

/-- One plane family: `Σ_{H∈G} σ(H) ≤ 4C₁N + 64 C₁³ T³ / A²` with `T = Σ_{j<J} a_j^{2/3}`, when
every plane has `σ(H) ≥ A`, lines in its planes have weight at most `J`, and `C₁ J ≤ A/2`. -/
lemma group_bound (R : ι → κ → Prop) (L : Finset ι) (G : Finset κ) (n : ι → ℕ)
    (C₁ N A : ℝ) (J : ℕ) (hC₁ : 0 < C₁) (hA : 0 < A) (hN : 0 ≤ N)
    (hinc : ∀ L' ⊆ L, ((((L' ×ˢ G).filter (fun x => R x.1 x.2)).card : ℝ) ≤
      C₁ * (((L'.card : ℝ) * G.card) ^ ((2 : ℝ) / 3) + L'.card + G.card)))
    (hmass : ∑ ℓ ∈ L, (n ℓ : ℝ) ≤ N)
    (hσ : ∀ H ∈ G, A ≤ sig R L n H)
    (hJ : ∀ ℓ ∈ L, ∀ H ∈ G, R ℓ H → n ℓ ≤ J)
    (hCJ : C₁ * J ≤ A / 2) :
    ∑ H ∈ G, sig R L n H ≤
      4 * C₁ * N + 64 * C₁ ^ 3 * (∑ j ∈ range J, layer L n j ^ ((2 : ℝ) / 3)) ^ 3 / A ^ 2 := by
  set X := ∑ H ∈ G, sig R L n H with hXdef
  set T := ∑ j ∈ range J, layer L n j ^ ((2 : ℝ) / 3) with hTdef
  set F : ℝ := (G.card : ℝ) with hFdef
  have hsig0 : ∀ H, 0 ≤ sig R L n H := fun H => sum_nonneg fun ℓ _ => Nat.cast_nonneg _
  have hX0 : 0 ≤ X := sum_nonneg fun H _ => hsig0 H
  have hT0 : 0 ≤ T := sum_nonneg fun j _ => Real.rpow_nonneg (layer_nonneg L n j) _
  have hF0 : 0 ≤ F := Nat.cast_nonneg _
  have hAF : A * F ≤ X := by
    have h' : ∑ _H ∈ G, A ≤ X := sum_le_sum hσ
    rw [sum_const, nsmul_eq_mul] at h'
    linarith [h']
  have hFX : F ≤ X / A := by rw [le_div_iff₀ hA]; linarith
  have h1 := sum_sig_le_layers R L G n J hJ
  have h2 : ∑ j ∈ range J,
      ((((L.filter (fun ℓ => j < n ℓ)) ×ˢ G).filter (fun x => R x.1 x.2)).card : ℝ) ≤
      ∑ j ∈ range J, C₁ * (layer L n j ^ ((2 : ℝ) / 3) * F ^ ((2 : ℝ) / 3) + layer L n j + F) := by
    apply sum_le_sum; intro j _
    have h' := hinc (L.filter (fun ℓ => j < n ℓ)) (filter_subset _ _)
    rw [Real.mul_rpow (Nat.cast_nonneg _) hF0] at h'
    exact h'
  have h3 : ∑ j ∈ range J, C₁ * (layer L n j ^ ((2 : ℝ) / 3) * F ^ ((2 : ℝ) / 3) + layer L n j + F)
      = C₁ * (F ^ ((2 : ℝ) / 3) * T + ∑ j ∈ range J, layer L n j + J * F) := by
    rw [← mul_sum, sum_add_distrib, sum_add_distrib, ← sum_mul, sum_const, card_range,
      nsmul_eq_mul, hTdef]
    ring
  have hlay := (sum_layer_le L n J).trans hmass
  have hFr : F ^ ((2 : ℝ) / 3) ≤ (X / A) ^ ((2 : ℝ) / 3) :=
    Real.rpow_le_rpow hF0 hFX (by norm_num)
  have hJF : C₁ * ((J : ℝ) * F) ≤ X / 2 := by
    have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
    calc C₁ * ((J : ℝ) * F) = (C₁ * J) * F := by ring
      _ ≤ (A / 2) * (X / A) := mul_le_mul hCJ hFX hF0 (by positivity)
      _ = X / 2 := by field_simp
  have hmain : X ≤ 2 * C₁ * (X / A) ^ ((2 : ℝ) / 3) * T + 2 * C₁ * N := by
    have hle : X ≤ C₁ * (F ^ ((2 : ℝ) / 3) * T + ∑ j ∈ range J, layer L n j + J * F) := by
      rw [← h3]; exact h1.trans h2
    have hstep : C₁ * (F ^ ((2 : ℝ) / 3) * T) ≤ C₁ * ((X / A) ^ ((2 : ℝ) / 3) * T) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hFr hT0) hC₁.le
    nlinarith
  exact absorb X A T N C₁ hX0 hA hT0 hN hC₁.le hmain

lemma sum_range_eq_ite (m J : ℕ) (h : m ≤ J) (c : ℕ → ℝ) :
    ∑ j ∈ range m, c j = ∑ j ∈ range J, (if j < m then c j else 0) := by
  rw [← sum_filter]
  congr 1
  ext j; simp only [mem_filter, mem_range]; constructor
  · exact fun h' => ⟨lt_of_lt_of_le h' h, h'⟩
  · exact fun h' => h'.2

lemma sum_ite_lt_le (U m : ℕ) (g : ℕ → ℝ) (hg : ∀ u, 0 ≤ g u) :
    ∑ u ∈ range U, (if u < m then g u else 0) ≤ ∑ u ∈ range m, g u := by
  rw [← sum_filter]
  apply sum_le_sum_of_subset_of_nonneg
  · intro u; simp only [mem_filter, mem_range]; exact fun h' => h'.2
  · exact fun u _ _ => hg u

/-- Per-layer bound used in the `u`-sum: for `j < J_u`,
`J_u^{1/2} ≤ W^{1/2} (u+1)^{-1/2}` and `u + 1 ≤ ⌊W/(j+1)⌋`. -/
lemma layer_u_bound (W : ℝ) (hW : 0 ≤ W) (u j Ju : ℕ) (hJu : (Ju : ℝ) ≤ W / ((u : ℝ) + 1))
    (hj : j < Ju) :
    (Ju : ℝ) ^ ((1 : ℝ) / 2) ≤ W ^ ((1 : ℝ) / 2) * ((u : ℝ) + 1) ^ (-((1 : ℝ) / 2)) ∧
      u < ⌊W / ((j : ℝ) + 1)⌋₊ := by
  have hu1 : (0 : ℝ) < (u : ℝ) + 1 := by positivity
  have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  constructor
  · calc (Ju : ℝ) ^ ((1 : ℝ) / 2) ≤ (W / ((u : ℝ) + 1)) ^ ((1 : ℝ) / 2) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hJu (by norm_num)
      _ = W ^ ((1 : ℝ) / 2) * ((u : ℝ) + 1) ^ (-((1 : ℝ) / 2)) := by
          rw [Real.div_rpow hW hu1.le, Real.rpow_neg hu1.le, div_eq_mul_inv]
  · have hj' : ((j : ℝ) + 1) ≤ Ju := by exact_mod_cast hj
    have h1 : ((j : ℝ) + 1) * ((u : ℝ) + 1) ≤ W := by
      have := hj'.trans hJu
      rw [le_div_iff₀ hu1] at this; linarith
    have h2 : ((u + 1 : ℕ) : ℝ) ≤ W / ((j : ℝ) + 1) := by
      rw [le_div_iff₀ hj1]; push_cast; linarith
    have h3 := Nat.le_floor h2
    omega

/-- **Abstract core of `geo:terminal.lines-core`.** Lines with integer weights `n` (total mass
`≤ N`), planes `G` with occupancies `h ≤ U`, an incidence relation obeying a
Szemerédi–Trotter bound with constant `C₁`, the occupancy product bound
`n_ℓ h_H ≤ C₀ M²` for incident pairs, and `A ≤ σ(H) ≤ h_H` on every plane, with
`2 C₁ C₀ M² ≤ A²`. Then `Σ_H h_H σ(H) ≤ 4 C₁ N U + 2048 C₀ C₁³ M² N² / A²`. -/
theorem planes_weighted_sum (R : ι → κ → Prop) (L : Finset ι) (G : Finset κ) (n : ι → ℕ)
    (h : κ → ℕ) (C₀ C₁ M N A : ℝ) (U : ℕ) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) (hA : 0 < A)
    (hN : 0 ≤ N)
    (hinc : ∀ L' ⊆ L, ∀ G' ⊆ G, ((((L' ×ˢ G').filter (fun x => R x.1 x.2)).card : ℝ) ≤
      C₁ * (((L'.card : ℝ) * G'.card) ^ ((2 : ℝ) / 3) + L'.card + G'.card)))
    (hocc : ∀ ℓ ∈ L, ∀ H ∈ G, R ℓ H → (n ℓ : ℝ) * h H ≤ C₀ * M ^ 2)
    (hmass : ∑ ℓ ∈ L, (n ℓ : ℝ) ≤ N)
    (hσ : ∀ H ∈ G, A ≤ sig R L n H)
    (hσh : ∀ H ∈ G, sig R L n H ≤ h H)
    (hU : ∀ H ∈ G, h H ≤ U)
    (habs : 2 * C₁ * C₀ * M ^ 2 ≤ A ^ 2) :
    ∑ H ∈ G, (h H : ℝ) * sig R L n H ≤
      4 * C₁ * N * U + 2048 * C₀ * C₁ ^ 3 * M ^ 2 * N ^ 2 / A ^ 2 := by
  set W := C₀ * M ^ 2 with hWdef
  have hW : 0 ≤ W := by positivity
  set Jstar := ⌊W / A⌋₊ with hJstar
  let Ju : ℕ → ℕ := fun u => min ⌊W / ((u : ℝ) + 1)⌋₊ Jstar
  have hJu_le : ∀ u, Ju u ≤ Jstar := fun u => min_le_right _ _
  have hJu_W : ∀ u : ℕ, (Ju u : ℝ) ≤ W / ((u : ℝ) + 1) := fun u =>
    (Nat.cast_le.mpr (min_le_left _ _)).trans (Nat.floor_le (by positivity))
  have hJstar_W : (Jstar : ℝ) ≤ W / A := Nat.floor_le (div_nonneg hW hA.le)
  set a : ℕ → ℝ := layer L n with hadef
  set T : ℕ → ℝ := fun u => ∑ j ∈ range (Ju u), a j ^ ((2 : ℝ) / 3) with hTdef
  -- Step b: layer cake in the occupancy.
  have hb : ∑ H ∈ G, (h H : ℝ) * sig R L n H =
      ∑ u ∈ range U, ∑ H ∈ G.filter (fun H => u < h H), sig R L n H := by
    have : ∀ H ∈ G, (h H : ℝ) * sig R L n H =
        ∑ u ∈ range U, (if u < h H then sig R L n H else 0) := by
      intro H hH
      have hc := count_lt (h H) U (hU H hH)
      have hc' : (h H : ℝ) = ∑ u ∈ range U, (if u < h H then (1 : ℝ) else 0) := by
        exact_mod_cast hc.symm
      rw [hc', sum_mul]
      apply sum_congr rfl; intro u _; split_ifs <;> simp
    rw [sum_congr rfl this, sum_comm]
    apply sum_congr rfl; intro u _
    rw [sum_filter]
  -- Group bound for each `u`.
  have hgroup : ∀ u ∈ range U, ∑ H ∈ G.filter (fun H => u < h H), sig R L n H ≤
      4 * C₁ * N + 64 * C₁ ^ 3 * T u ^ 3 / A ^ 2 := by
    intro u _
    apply group_bound R L (G.filter (fun H => u < h H)) n C₁ N A (Ju u) hC₁ hA hN
    · intro L' hL'; exact hinc L' hL' _ (filter_subset _ _)
    · exact hmass
    · intro H hH; exact hσ H (mem_filter.mp hH).1
    · intro ℓ hℓ H hH hR
      obtain ⟨hHG, huH⟩ := mem_filter.mp hH
      have hocc' := hocc ℓ hℓ H hHG hR
      have hn0 : (0 : ℝ) ≤ n ℓ := Nat.cast_nonneg _
      have hhu : ((u : ℝ) + 1) ≤ h H := by exact_mod_cast huH
      have hhA : A ≤ h H := (hσ H hHG).trans (hσh H hHG)
      apply le_min
      · apply Nat.le_floor
        rw [le_div_iff₀ (by positivity)]
        nlinarith
      · apply Nat.le_floor
        rw [le_div_iff₀ hA]
        nlinarith
    · have : (C₁ : ℝ) * Ju u ≤ C₁ * (W / A) :=
        mul_le_mul_of_nonneg_left ((Nat.cast_le.mpr (hJu_le u)).trans hJstar_W) hC₁.le
      have h2 : C₁ * (W / A) ≤ A / 2 := by
        rw [mul_div_assoc', div_le_div_iff₀ hA (by norm_num)]
        nlinarith
      linarith
  -- Step c: the sum of `T_u^3`.
  have ha0 : ∀ j, 0 ≤ a j := fun j => layer_nonneg L n j
  have hasum : ∑ j ∈ range Jstar, a j ≤ N := (sum_layer_le L n Jstar).trans hmass
  have hasum0 : 0 ≤ ∑ j ∈ range Jstar, a j := sum_nonneg fun j _ => ha0 j
  set c : ℕ → ℝ := fun j => ((j : ℝ) + 1) ^ ((3 : ℝ) / 2) * a j ^ 2 with hcdef
  have hc0 : ∀ j, 0 ≤ c j := fun j => by positivity
  have hT3 : ∀ u, T u ^ 3 ≤
      16 * ∑ j ∈ range Jstar, c j * (if j < Ju u then (Ju u : ℝ) ^ ((1 : ℝ) / 2) else 0) := by
    intro u
    have hh := holder_layer (Ju u) a ha0
    show (∑ j ∈ range (Ju u), a j ^ ((2 : ℝ) / 3)) ^ 3 ≤ _
    refine hh.trans (le_of_eq ?_)
    rw [sum_range_eq_ite (Ju u) Jstar (hJu_le u), mul_assoc, mul_sum]
    congr 1
    apply sum_congr rfl; intro j _
    split_ifs with hj
    · simp only [c]; ring
    · simp
  have hinner : ∀ j, ∑ u ∈ range U, (if j < Ju u then (Ju u : ℝ) ^ ((1 : ℝ) / 2) else 0) ≤
      2 * W * ((j : ℝ) + 1) ^ (-((1 : ℝ) / 2)) := by
    intro j
    have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    set m := ⌊W / ((j : ℝ) + 1)⌋₊
    have hpt : ∀ u ∈ range U, (if j < Ju u then (Ju u : ℝ) ^ ((1 : ℝ) / 2) else 0) ≤
        (if u < m then W ^ ((1 : ℝ) / 2) * ((u : ℝ) + 1) ^ (-((1 : ℝ) / 2)) else 0) := by
      intro u _
      by_cases hj : j < Ju u
      · obtain ⟨h1, h2⟩ := layer_u_bound W hW u j (Ju u) (hJu_W u) hj
        have h2' : u < m := h2
        rw [if_pos hj, if_pos h2']; exact h1
      · rw [if_neg hj]; split_ifs <;> positivity
    refine (sum_le_sum hpt).trans ?_
    refine (sum_ite_lt_le U m _ (fun u => by positivity)).trans ?_
    rw [← mul_sum]
    have hs := sum_rpow_neg_le (1 / 2) (by norm_num) (by norm_num) m
    have hm : (m : ℝ) ≤ W / ((j : ℝ) + 1) := Nat.floor_le (by positivity)
    have hm2 : (m : ℝ) ^ (1 - (1 : ℝ) / 2) ≤ W ^ ((1 : ℝ) / 2) * ((j : ℝ) + 1) ^ (-((1 : ℝ) / 2)) := by
      rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
      calc (m : ℝ) ^ ((1 : ℝ) / 2) ≤ (W / ((j : ℝ) + 1)) ^ ((1 : ℝ) / 2) :=
            Real.rpow_le_rpow (Nat.cast_nonneg _) hm (by norm_num)
        _ = _ := by rw [Real.div_rpow hW hj1.le, Real.rpow_neg hj1.le, div_eq_mul_inv]
    have hWW : W ^ ((1 : ℝ) / 2) * W ^ ((1 : ℝ) / 2) = W := by
      rw [← Real.rpow_add' hW (by norm_num)]; norm_num
    calc W ^ ((1 : ℝ) / 2) * ∑ u ∈ range m, ((u : ℝ) + 1) ^ (-((1 : ℝ) / 2))
        ≤ W ^ ((1 : ℝ) / 2) * ((m : ℝ) ^ (1 - (1 : ℝ) / 2) / (1 - 1 / 2)) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
      _ ≤ W ^ ((1 : ℝ) / 2) *
            ((W ^ ((1 : ℝ) / 2) * ((j : ℝ) + 1) ^ (-((1 : ℝ) / 2))) / (1 - 1 / 2)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact div_le_div_of_nonneg_right hm2 (by norm_num)
      _ = 2 * (W ^ ((1 : ℝ) / 2) * W ^ ((1 : ℝ) / 2)) * ((j : ℝ) + 1) ^ (-((1 : ℝ) / 2)) := by
          ring
      _ = 2 * W * ((j : ℝ) + 1) ^ (-((1 : ℝ) / 2)) := by rw [hWW]
  have hsumT : ∑ u ∈ range U, T u ^ 3 ≤ 32 * W * N ^ 2 := by
    calc ∑ u ∈ range U, T u ^ 3
        ≤ ∑ u ∈ range U, 16 * ∑ j ∈ range Jstar,
            c j * (if j < Ju u then (Ju u : ℝ) ^ ((1 : ℝ) / 2) else 0) := sum_le_sum fun u _ => hT3 u
      _ = 16 * ∑ j ∈ range Jstar, c j *
            ∑ u ∈ range U, (if j < Ju u then (Ju u : ℝ) ^ ((1 : ℝ) / 2) else 0) := by
          rw [← mul_sum, sum_comm]
          congr 1; apply sum_congr rfl; intro j _; rw [mul_sum]
      _ ≤ 16 * ∑ j ∈ range Jstar, c j * (2 * W * ((j : ℝ) + 1) ^ (-((1 : ℝ) / 2))) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hinner j) (hc0 j)
      _ = 32 * W * ∑ j ∈ range Jstar, ((j : ℝ) + 1) * a j ^ 2 := by
          rw [mul_sum, mul_sum]
          apply sum_congr rfl; intro j _
          have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
          have hpow : ((j : ℝ) + 1) ^ ((3 : ℝ) / 2) * ((j : ℝ) + 1) ^ (-((1 : ℝ) / 2)) =
              (j : ℝ) + 1 := by
            rw [← Real.rpow_add hj1]; norm_num
          simp only [c]
          calc 16 * (((j : ℝ) + 1) ^ ((3 : ℝ) / 2) * a j ^ 2 *
                (2 * W * ((j : ℝ) + 1) ^ (-((1 : ℝ) / 2))))
              = 32 * W * ((((j : ℝ) + 1) ^ ((3 : ℝ) / 2) * ((j : ℝ) + 1) ^ (-((1 : ℝ) / 2))) *
                  a j ^ 2) := by ring
            _ = 32 * W * (((j : ℝ) + 1) * a j ^ 2) := by rw [hpow]
      _ ≤ 32 * W * (∑ j ∈ range Jstar, a j) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact sum_succ_mul_sq_le Jstar a ha0 (fun i j hij => layer_anti L n i j hij)
      _ ≤ 32 * W * N ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact pow_le_pow_left₀ hasum0 hasum 2
  -- Assemble.
  rw [hb]
  calc ∑ u ∈ range U, ∑ H ∈ G.filter (fun H => u < h H), sig R L n H
      ≤ ∑ u ∈ range U, (4 * C₁ * N + 64 * C₁ ^ 3 * T u ^ 3 / A ^ 2) := sum_le_sum hgroup
    _ = 4 * C₁ * N * U + 64 * C₁ ^ 3 / A ^ 2 * ∑ u ∈ range U, T u ^ 3 := by
        rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, mul_sum]
        congr 1
        · ring
        · apply sum_congr rfl; intro u _; ring
    _ ≤ 4 * C₁ * N * U + 64 * C₁ ^ 3 / A ^ 2 * (32 * W * N ^ 2) := by
        exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hsumT (by positivity))
    _ = 4 * C₁ * N * U + 2048 * C₀ * C₁ ^ 3 * M ^ 2 * N ^ 2 / A ^ 2 := by
        rw [hWdef]; ring

end Abstract

end LinesCore
end TrackD
end DistinctDistances
