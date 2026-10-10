import DistinctDistances.TrackD.Profiles.Defs

/-!
# Quantitative rank propagation (`profiles.tex:283–312`)

The profile calculation below is independent of the algebraic envelope construction. It
records the loss when a Hilbert comparison starts just before a cluster of cuts. The algebraic
comparison must hold uniformly for every dense subset, including the subset selected by the
envelope argument. No Hilbert estimate is assumed implicitly in these lemmas.
-/

namespace DistinctDistances.TrackD.RankCore

open scoped BigOperators

variable {d : ℕ}

theorem testDeg_pos {B : ℝ} (hB : 0 < B) (s b : ℝ) : 0 < testDeg B s b :=
  mul_pos hB (Real.exp_pos _)

theorem testDeg_mono {B s a b : ℝ} (hB : 0 ≤ B) (hs : 0 ≤ s) (hab : a ≤ b) :
    testDeg B s a ≤ testDeg B s b := by
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hab hs)) hB

theorem testDeg_shift (B s a b : ℝ) :
    testDeg B s b = testDeg B s a * Real.exp ((b - a) * s) := by
  unfold testDeg
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem sigma_nonneg {B : ℝ} (hB : 0 ≤ B) (s : ℝ) (t : Fin d → ℝ) (b : ℝ) :
    0 ≤ sigma B s t b := by
  apply Finset.prod_nonneg
  intro i hi
  exact le_min (mul_nonneg hB (Real.exp_nonneg _)) (mul_nonneg hB (Real.exp_nonneg _))

/-- Crossing an interval of length `b-a` loses at most `d (b-a) s` in logarithmic rank. -/
theorem sigma_lipschitz {B s a b : ℝ} (hB : 0 ≤ B) (hs : 0 ≤ s) (hab : a ≤ b)
    (t : Fin d → ℝ) :
    sigma B s t b ≤ sigma B s t a * Real.exp ((d : ℝ) * (b - a) * s) := by
  have hr : 1 ≤ Real.exp ((b - a) * s) :=
    Real.one_le_exp_iff.mpr (mul_nonneg (sub_nonneg.mpr hab) hs)
  have hprod : sigma B s t b ≤
      ∏ i : Fin d, min (testDeg B s a) (cutScale B s t i) * Real.exp ((b - a) * s) := by
    apply Finset.prod_le_prod₀
    · intro i hi
      exact le_min (mul_nonneg hB (Real.exp_nonneg _)) (mul_nonneg hB (Real.exp_nonneg _))
    · intro i hi
      rw [min_mul_of_nonneg _ _ (Real.exp_nonneg _), testDeg_shift B s a b]
      exact min_le_min le_rfl (le_mul_of_one_le_right (mul_nonneg hB (Real.exp_nonneg _)) hr)
  simpa only [Finset.prod_mul_distrib, sigma, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← Real.exp_nat_mul, mul_assoc] using hprod

theorem card_after (j : ℕ) (hj : j ≤ d) :
    (Finset.univ.filter (fun i : Fin d => j ≤ i.val)).card = d - j := by
  by_cases hlt : j < d
  · have heq : Finset.univ.filter (fun i : Fin d => j ≤ i.val) =
        Finset.Ici (⟨j, hlt⟩ : Fin d) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ici, Fin.le_def]
    rw [heq, Fin.card_Ici]
  · have hzero : Finset.univ.filter (fun i : Fin d => j ≤ i.val) = ∅ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp
      omega
    rw [hzero, Finset.card_empty]
    omega

/-- On one plateau, the profile grows with exactly the dimension left after the cuts. -/
theorem sigma_growth_on_plateau {B s a b : ℝ} (hB : 0 ≤ B) (hs : 0 ≤ s)
    (t : Fin d → ℝ) (j : ℕ) (hj : j ≤ d)
    (ha : OnPlateau t j 0 a) (hb : OnPlateau t j 0 b) :
    sigma B s t b = sigma B s t a * Real.exp (((d - j : ℕ) : ℝ) * (b - a) * s) := by
  have hfactor : ∀ i : Fin d,
      min (testDeg B s b) (cutScale B s t i) =
        min (testDeg B s a) (cutScale B s t i) *
          (if j ≤ i.val then Real.exp ((b - a) * s) else 1) := by
    intro i
    unfold cutScale
    by_cases hi : j ≤ i.val
    · have hait : a ≤ t i := by simpa using (ha i).2 hi
      have hbit : b ≤ t i := by simpa using (hb i).2 hi
      rw [ite_eq_left hi, min_eq_left (testDeg_mono hB hs hbit),
        min_eq_left (testDeg_mono hB hs hait)]
      exact testDeg_shift B s a b
    · have hita : t i ≤ a := by simpa using (ha i).1 (by omega)
      have hitb : t i ≤ b := by simpa using (hb i).1 (by omega)
      rw [ite_eq_right hi, min_eq_right (testDeg_mono hB hs hitb),
        min_eq_right (testDeg_mono hB hs hita), mul_one]
  unfold sigma
  simp_rw [hfactor]
  rw [Finset.prod_mul_distrib, Finset.prod_ite]
  simp only [Finset.prod_const, one_pow, mul_one, card_after j hj,
    ← Real.exp_nat_mul, mul_assoc]

/-- Eliminate the common component degree from the two Hilbert estimates
`c a T^h ≤ R` and `R' ≤ C a U^h` (`profiles.tex:290–300`). -/
theorem eliminate_degree {R R' a T U c C : ℝ} (h : ℕ)
    (hc : 0 < c) (hC : 0 < C) (hT : 0 < T) (hU : 0 < U)
    (hlower : c * a * T ^ h ≤ R) (hupper : R' ≤ C * a * U ^ h) :
    R' * ((c / C) * (T / U) ^ h) ≤ R := by
  calc
    R' * ((c / C) * (T / U) ^ h) ≤
        (C * a * U ^ h) * ((c / C) * (T / U) ^ h) :=
      mul_le_mul_of_nonneg_right hupper (by positivity)
    _ = c * a * T ^ h := by
      rw [div_pow]
      field_simp
    _ ≤ R := hlower

/-- The rounded smaller testing degree costs at most a factor `2^h` when it is at least one.
This is the fixed multiplicative loss suppressed by exponential accuracy in the paper. -/
theorem rounded_ratio {T U : ℝ} (hU : 1 ≤ U) (hT : 0 ≤ T) (h : ℕ) :
    (T / (2 * U)) ^ h ≤ (T / (U + 1)) ^ h := by
  apply pow_le_pow_left₀ (by positivity)
  exact div_le_div_of_nonneg_left hT (by positivity) (by linarith)

/-- Profile growth from a time before a cluster to a later point on its plateau. The
cluster's width `κ` is charged independently of any later choice of a dense subset. -/
theorem sigma_cluster_growth {B s a c b κ : ℝ} (hB : 0 ≤ B) (hs : 0 ≤ s)
    (hac : a ≤ c) (_hcb : c ≤ b) (hgap : c - a ≤ κ)
    (t : Fin d → ℝ) (j : ℕ) (hj : j ≤ d)
    (hc : OnPlateau t j 0 c) (hb : OnPlateau t j 0 b) :
    sigma B s t b ≤ sigma B s t a *
      Real.exp ((((d - j : ℕ) : ℝ) * (b - a) + (d : ℝ) * κ) * s) := by
  have hl : 0 ≤ ((d - j : ℕ) : ℝ) := Nat.cast_nonneg _
  have hexp : (d : ℝ) * (c - a) * s + ((d - j : ℕ) : ℝ) * (b - c) * s ≤
      (((d - j : ℕ) : ℝ) * (b - a) + (d : ℝ) * κ) * s := by
    have hdc : (d : ℝ) * (c - a) ≤ (d : ℝ) * κ :=
      mul_le_mul_of_nonneg_left hgap (Nat.cast_nonneg _)
    have hlc : 0 ≤ ((d - j : ℕ) : ℝ) * (c - a) := mul_nonneg hl (sub_nonneg.mpr hac)
    have : (d : ℝ) * (c - a) + ((d - j : ℕ) : ℝ) * (b - c) ≤
        ((d - j : ℕ) : ℝ) * (b - a) + (d : ℝ) * κ := by nlinarith
    nlinarith
  rw [sigma_growth_on_plateau hB hs t j hj hc hb]
  calc
    sigma B s t c * Real.exp (((d - j : ℕ) : ℝ) * (b - c) * s) ≤
        (sigma B s t a * Real.exp ((d : ℝ) * (c - a) * s)) *
          Real.exp (((d - j : ℕ) : ℝ) * (b - c) * s) :=
      mul_le_mul_of_nonneg_right (sigma_lipschitz hB hs hac t) (Real.exp_nonneg _)
    _ = sigma B s t a * Real.exp ((d : ℝ) * (c - a) * s +
        ((d - j : ℕ) : ℝ) * (b - c) * s) := by rw [mul_assoc, ← Real.exp_add]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (sigma_nonneg hB _ _ _)

/-- One quantitative propagation step (`profiles.tex:300–312`). The input Hilbert
comparison may use any dimension `h ≥ d-j`; the output loses exactly `μ + d κ` in
the normalized exponent. All parameters precede the ranks, so this applies to ranks of
arbitrary subsets chosen after the piece and its profile have been fixed. -/
theorem propagate_step {B s a c b κ L μ R R' : ℝ} (hB : 0 ≤ B) (hs : 0 ≤ s)
    (hac : a ≤ c) (hcb : c ≤ b) (hgap : c - a ≤ κ)
    (t : Fin d → ℝ) (j h : ℕ) (hj : j ≤ d) (hdim : d - j ≤ h)
    (hc : OnPlateau t j 0 c) (hb : OnPlateau t j 0 b)
    (hstart : sigma B s t a * Real.exp (-L * s) ≤ R')
    (hcompare : R' * Real.exp (((h : ℝ) * (b - a) - μ) * s) ≤ R) :
    sigma B s t b * Real.exp (-(L + μ + (d : ℝ) * κ) * s) ≤ R := by
  have hR' : 0 ≤ R' := (mul_nonneg (sigma_nonneg hB _ _ _) (Real.exp_nonneg _)).trans hstart
  have hab : a ≤ b := hac.trans hcb
  have hdim' : ((d - j : ℕ) : ℝ) ≤ (h : ℝ) := by exact_mod_cast hdim
  calc
    sigma B s t b * Real.exp (-(L + μ + (d : ℝ) * κ) * s) ≤
        (sigma B s t a * Real.exp ((((d - j : ℕ) : ℝ) * (b - a) + (d : ℝ) * κ) * s)) *
          Real.exp (-(L + μ + (d : ℝ) * κ) * s) :=
      mul_le_mul_of_nonneg_right
        (sigma_cluster_growth hB hs hac hcb hgap t j hj hc hb) (Real.exp_nonneg _)
    _ = (sigma B s t a * Real.exp (-L * s)) *
        Real.exp ((((d - j : ℕ) : ℝ) * (b - a) - μ) * s) := by
      rw [mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ R' * Real.exp ((((d - j : ℕ) : ℝ) * (b - a) - μ) * s) :=
      mul_le_mul_of_nonneg_right hstart (Real.exp_nonneg _)
    _ ≤ R' * Real.exp (((h : ℝ) * (b - a) - μ) * s) := by
      apply mul_le_mul_of_nonneg_left _ hR'
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right
        (sub_le_sub_right (mul_le_mul_of_nonneg_right hdim' (sub_nonneg.mpr hab)) μ) hs
    _ ≤ R := hcompare

/-- A fixed Hilbert constant can be absorbed into an arbitrarily small normalized loss;
the threshold is chosen before any configuration or subset. -/
theorem absorb_constant {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε) :
    ∃ s₀ : ℝ, ∀ s ≥ s₀, C ≤ Real.exp (ε * s) := by
  refine ⟨Real.log C / ε, ?_⟩
  intro s hs
  rw [← Real.exp_log hC]
  apply Real.exp_le_exp.mpr
  have := (div_le_iff₀ hε).mp hs
  linarith

/-- Induction uniform over the admissible subsets at each stage. The smaller subset
`S'` is chosen by the comparison argument after `S`; the induction hypothesis applies
to every such choice. With `q = d κ + μ`, each cut cluster contributes at most `q`.
The predicate `good` can record the successively smaller density thresholds. -/
theorem propagate_uniform {α : Type*} (good : ℕ → α → Prop) (R : ℕ → α → ℝ)
    (σ g : ℕ → ℝ) (s L q : ℝ)
    (hstart : ∀ S, good 0 S → σ 0 * Real.exp (-L * s) ≤ R 0 S)
    (hgrowth : ∀ i, σ (i + 1) ≤ σ i * Real.exp (g i * s))
    (hchoose : ∀ i S, good (i + 1) S → ∃ S', good i S' ∧
      R i S' * Real.exp ((g i - q) * s) ≤ R (i + 1) S) :
    ∀ n S, good n S → σ n * Real.exp (-(L + (n : ℝ) * q) * s) ≤ R n S := by
  intro n
  induction n with
  | zero => simpa using hstart
  | succ n ih =>
      intro S hS
      obtain ⟨S', hS', hcompare⟩ := hchoose n S hS
      calc
        σ (n + 1) * Real.exp (-(L + ((n + 1 : ℕ) : ℝ) * q) * s) ≤
            (σ n * Real.exp (g n * s)) *
              Real.exp (-(L + ((n + 1 : ℕ) : ℝ) * q) * s) :=
          mul_le_mul_of_nonneg_right (hgrowth n) (Real.exp_nonneg _)
        _ = (σ n * Real.exp (-(L + (n : ℝ) * q) * s)) *
            Real.exp ((g n - q) * s) := by
          rw [mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]
          congr 2
          push_cast
          ring
        _ ≤ R n S' * Real.exp ((g n - q) * s) :=
          mul_le_mul_of_nonneg_right (ih S' hS') (Real.exp_nonneg _)
        _ ≤ R (n + 1) S := hcompare

/-- At most `d` cut clusters yield the dimension-only loss `d² κ + d μ`. -/
theorem bounded_loss {σ R s L κ μ : ℝ} (hσ : 0 ≤ σ) (hs : 0 ≤ s)
    (hκ : 0 ≤ κ) (hμ : 0 ≤ μ) (n : ℕ) (hn : n ≤ d)
    (h : σ * Real.exp (-(L + (n : ℝ) * ((d : ℝ) * κ + μ)) * s) ≤ R) :
    σ * Real.exp (-(L + (d : ℝ) ^ 2 * κ + (d : ℝ) * μ) * s) ≤ R := by
  apply le_trans _ h
  apply mul_le_mul_of_nonneg_left _ hσ
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_right _ hs
  have hn' : (n : ℝ) ≤ (d : ℝ) := by exact_mod_cast hn
  have hq : 0 ≤ (d : ℝ) * κ + μ := by positivity
  have := mul_le_mul_of_nonneg_right hn' hq
  nlinarith

end DistinctDistances.TrackD.RankCore
