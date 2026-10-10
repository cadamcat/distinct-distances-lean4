import DistinctDistances.TrackD.Profiles.Budget
import DistinctDistances.TrackD.Profiles.PoolFamilies
import DistinctDistances.TrackD.Profiles.RegularityMass

namespace DistinctDistances.TrackD
open scoped BigOperators Classical
noncomputable section
variable {d : ℕ}

-- Scalar helpers for testDeg.
theorem md_testDeg_nonneg (B s b : ℝ) (hB : 0 ≤ B) : 0 ≤ testDeg B s b := by
  unfold testDeg
  exact mul_nonneg hB (Real.exp_nonneg _)

theorem md_testDeg_pos_of_pos (B s b : ℝ) (hB : 0 < B) : 0 < testDeg B s b := by
  unfold testDeg
  exact mul_pos hB (Real.exp_pos _)

theorem md_testDeg_mono_of_nonneg (B s a b : ℝ) (hB : 0 ≤ B) (hs : 0 ≤ s)
    (hab : a ≤ b) : testDeg B s a ≤ testDeg B s b := by
  unfold testDeg
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hab hs)) hB

theorem md_testDeg_shift (B s a b : ℝ) :
    testDeg B s b = testDeg B s a * Real.exp ((b - a) * s) := by
  unfold testDeg
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem md_testDeg_mul_exp (B s b e : ℝ) :
    testDeg B s b * Real.exp (e * s) = testDeg B s (b + e) := by
  unfold testDeg
  rw [mul_assoc, ← Real.exp_add, show b * s + e * s = (b + e) * s by ring]

-- Ceil / floor helpers.
theorem md_nat_ceil_ge (a : ℝ) : a ≤ (⌈a⌉₊ : ℝ) := Nat.le_ceil a

theorem md_nat_ceil_le_of_le {a : ℝ} {n : ℕ} (h : a ≤ (n : ℝ)) (_ha : 0 ≤ a) :
    ⌈a⌉₊ ≤ n := by
  rw [Nat.ceil_le]
  exact h

theorem md_nat_le_ceil_of_le {n : ℕ} {a : ℝ} (h : (n : ℝ) ≤ a) : n ≤ ⌈a⌉₊ := by
  have h2 : (n : ℝ) ≤ (⌈a⌉₊ : ℝ) := le_trans h (Nat.le_ceil a)
  exact_mod_cast h2

theorem md_ceil_mono {a b : ℝ} (h : a ≤ b) : ⌈a⌉₊ ≤ ⌈b⌉₊ := by
  rw [Nat.ceil_le]
  exact le_trans h (Nat.le_ceil b)

theorem md_floor_mono {a b : ℝ} (ha : 0 ≤ a) (h : a ≤ b) : ⌊a⌋₊ ≤ ⌊b⌋₊ := by
  apply Nat.le_floor
  calc ((⌊a⌋₊ : ℕ) : ℝ) ≤ a := Nat.floor_le ha
    _ ≤ b := h

theorem md_ceil_add_one_ge (a : ℝ) (_ha : 0 ≤ a) : a ≤ ((⌈a⌉₊ + 1 : ℕ) : ℝ) := by
  calc a ≤ (⌈a⌉₊ : ℝ) := Nat.le_ceil a
    _ ≤ (((⌈a⌉₊ + 1 : ℕ)) : ℝ) := by exact_mod_cast Nat.le_succ _

theorem md_floor_sub_one_le (a : ℝ) (_ha : 0 ≤ a) : (a - 1 : ℝ) ≤ (⌊a⌋₊ : ℝ) := by
  have hlt : a < ((⌊a⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one a
  linarith

-- Prefix family is defined in degree L when every prefix cut has degree ≤ L.
theorem md_piece_components_defined (X : Piece d) (j L : ℕ)
    (hdeg : ∀ i : Fin d, i.val < j → (X.path.cut i).totalDegree ≤ L) :
    AffineFamily.ComponentsDefinedInDegree (pieceCarrierFamily X j) L := by
  refine ⟨{f | ∃ i : Fin d, i.val < j ∧ X.path.cut i = f}, ?_, ?_⟩
  · rintro f ⟨i, hi, rfl⟩
    exact hdeg i hi
  · intro Z hZ
    have hcar : X.path.IsCarrier j Z := (mem_pieceCarrierFamily X j Z).mp hZ |>.1
    -- system j is exactly span of this set by definition
    exact hcar

theorem md_piece_from_lists (X : Piece d) (j L : ℕ) (hL : 1 ≤ L)
    (hdeg : ∀ i : Fin d, i.val < j → (X.path.cut i).totalDegree ≤ L) :
    TrackA.FromAffineLists (pieceCarrierFamily X j) L := by
  refine ⟨1, fun _ => pieceCarrierFamily X j, fun _ => L, ?_, ?_, ?_⟩
  · intro i
    exact ⟨hL, md_piece_components_defined X j L hdeg⟩
  · intro V
    constructor
    · intro hV
      exact ⟨0, hV⟩
    · rintro ⟨i, hi⟩
      -- Fin 1 has only 0
      have : i = 0 := Fin.eq_zero i
      subst this
      exact hi
  · simp

theorem md_ceil_lt_add_one (a : ℝ) (ha : 0 ≤ a) : (⌈a⌉₊ : ℝ) < a + 1 :=
  Nat.ceil_lt_add_one ha

theorem md_ceil_le_add_one (a : ℝ) (ha : 0 ≤ a) : (⌈a⌉₊ : ℝ) ≤ a + 1 :=
  le_of_lt (md_ceil_lt_add_one a ha)

theorem md_exp_ge (a C : ℝ) (ha : 0 < a) (hC : 0 < C) :
    ∃ s₀ : ℝ, ∀ s ≥ s₀, C ≤ Real.exp (a * s) := by
  obtain ⟨s₀, hs₀⟩ := regularity_exp_threshold a (1 / C) ha (by positivity)
  refine ⟨s₀, ?_⟩
  intro s hs
  have hle := hs₀ s hs
  have hpos : 0 < Real.exp (a * s) := Real.exp_pos _
  have hneg : Real.exp (-a * s) = (Real.exp (a * s))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  rw [hneg] at hle
  have hCpos : 0 < (1 / C : ℝ) := by positivity
  have hinv : (Real.exp (a * s))⁻¹ ≤ (1 / C : ℝ) := hle
  -- invert: C ≤ exp
  have h1 : C ≤ Real.exp (a * s) := by
    rw [one_div] at hinv
    -- (exp)⁻¹ ≤ C⁻¹ → C ≤ exp for positives
    exact (inv_le_inv₀ hpos hC).mp hinv
  exact h1

theorem md_cfgB_nonneg (P : Finset (Pt d)) : 0 ≤ cfgB P := by
  unfold cfgB
  positivity

theorem md_eScale_nonneg (B s : ℝ) (t : Fin d → ℝ) (j : ℕ) (hB : 0 ≤ B) :
    0 ≤ eScale B s t j := by
  unfold eScale cutScale testDeg
  apply Finset.prod_nonneg
  intro i _
  exact mul_nonneg hB (Real.exp_nonneg _)

theorem md_piece_pure (P : Finset (Pt d)) (X : Piece d) (θ ξ K : ℝ)
    (hX : PieceGood P θ ξ K X) (j : ℕ) (hj : j ≤ d) :
    AffineFamily.IsPure (pieceCarrierFamily X j) (d - j) := by
  have hpool := poolCarrierFamily_pure P {X} θ ξ K
    (by intro Y hY; have : Y = X := Finset.mem_singleton.mp hY; subst this; exact hX)
    j hj
  -- pool {X} = piece X
  have heq : poolCarrierFamily {X} j = pieceCarrierFamily X j := by
    simp [poolCarrierFamily]
  rw [heq] at hpool
  exact hpool

theorem md_const_le_large (C : ℝ) (hC : 0 ≤ C) :
    3 * C * (C + 1) ≤ 100 * (C + 2) ^ 2 + 100 := by
  nlinarith [sq_nonneg C, hC]

theorem md_const_le_large2 (C : ℝ) (hC : 0 ≤ C) :
    (C : ℝ) + 1 ≤ 100 * (C + 2) ^ 2 + 100 := by
  nlinarith [sq_nonneg C, hC]

theorem md_const_le_large3 (C : ℝ) (hC : 0 ≤ C) :
    6 * C * (C + 1) ≤ 100 * (C + 2) ^ 2 + 100 := by
  nlinarith [sq_nonneg C, hC]

theorem md_const_2C1_le (C : ℝ) (hC : 0 ≤ C) :
    2 * (C + 1) ≤ 100 * (C + 2) ^ 2 + 100 := by
  nlinarith [sq_nonneg C, hC]

end
end DistinctDistances.TrackD
