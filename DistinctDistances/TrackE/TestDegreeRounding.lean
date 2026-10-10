import DistinctDistances.TrackE.ProjectedMass
import Mathlib.Algebra.Order.Floor.Semiring

/-! Integer testing degrees for `sc:u-final-curve.regularity`
(`sparse-cones.tex:803–810, 870–880`). -/

namespace DistinctDistances.SparseCones

open Filter
open scoped Topology

/-- Round the envelope degree up and the regularity degree down. The ratio
loses at most a factor four, and the regularity threshold is preserved. -/
theorem rounded_test_degrees (C : ℕ) (T₀ T₁ : ℝ) (h₀ : 1 ≤ T₀) (h₁ : 2 ≤ T₁)
    (hgap : 4 * (C : ℝ) * T₀ ≤ T₁) :
    1 ≤ ⌈T₀⌉₊ ∧ C * ⌈T₀⌉₊ ≤ ⌊T₁⌋₊ ∧
      (⌈T₀⌉₊ : ℝ) / (⌊T₁⌋₊ : ℝ) ≤ 4 * (T₀ / T₁) := by
  have hL : (⌈T₀⌉₊ : ℝ) ≤ 2 * T₀ := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ T₀ by linarith)
    linarith
  have hD : T₁ / 2 ≤ (⌊T₁⌋₊ : ℝ) := by
    have h := Nat.lt_floor_add_one T₁
    linarith
  have hT₁ : 0 < T₁ := by linarith
  have hDpos : 0 < (⌊T₁⌋₊ : ℝ) := by linarith
  refine ⟨Nat.one_le_ceil_iff.mpr (by linarith), ?_, ?_⟩
  · have hmul := mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg C : (0 : ℝ) ≤ C)
    have hbound : (C : ℝ) * (⌈T₀⌉₊ : ℝ) ≤ (⌊T₁⌋₊ : ℝ) := by nlinarith
    exact_mod_cast hbound
  · apply (div_le_iff₀ hDpos).mpr
    have hmul := mul_le_mul_of_nonneg_left hD
      (show 0 ≤ 4 * (T₀ / T₁) by positivity)
    have heq : 4 * (T₀ / T₁) * (T₁ / 2) = 2 * T₀ := by
      field_simp
      <;> ring
    rw [heq] at hmul
    exact hL.trans hmul

/-- The two fixed interior times have a positive gap `η`. Their exponential
ratio absorbs the rounding loss and every fixed regularity constant, uniformly
before any center or envelope is chosen. -/
theorem eventually_rounded_test_degrees (C : ℕ) (s T₀ T₁ : ℕ → ℝ) (η : ℝ)
    (hs : Tendsto s atTop atTop) (hη : 0 < η)
    (h₀ : ∀ᶠ i in atTop, 1 ≤ T₀ i)
    (hratio : ∀ i, T₁ i = T₀ i * Real.exp (η * s i)) :
    ∀ᶠ i in atTop,
      1 ≤ ⌈T₀ i⌉₊ ∧ C * ⌈T₀ i⌉₊ ≤ ⌊T₁ i⌋₊ ∧
        (⌈T₀ i⌉₊ : ℝ) / (⌊T₁ i⌋₊ : ℝ) ≤ 4 * Real.exp (-η * s i) := by
  have hgrowth : ∀ᶠ i in atTop, 4 * (C : ℝ) + 2 < Real.exp (η * s i) := by
    filter_upwards [eventually_exponential_gap s hs (4 * (C : ℝ) + 2) 0 η
      (by positivity) hη] with i hi
    have hi' : (4 * (C : ℝ) + 2) * Real.exp (-η * s i) < 1 := by
      simpa using hi
    have hcancel : Real.exp (-η * s i) * Real.exp (η * s i) = 1 := by
      rw [← Real.exp_add, show -η * s i + η * s i = 0 by ring, Real.exp_zero]
    have hm := mul_lt_mul_of_pos_right hi' (Real.exp_pos (η * s i))
    simpa only [mul_assoc, hcancel, mul_one, one_mul] using hm
  filter_upwards [h₀, hgrowth] with i hi hg
  have hT₀ : 0 < T₀ i := by linarith
  have he : 2 ≤ Real.exp (η * s i) := by
    have hC : (0 : ℝ) ≤ C := Nat.cast_nonneg C
    linarith
  have hT₁ : 2 ≤ T₁ i := by
    rw [hratio i]
    have hm := mul_le_mul hi he (by norm_num : (0 : ℝ) ≤ 2) hT₀.le
    simpa using hm
  have hgap : 4 * (C : ℝ) * T₀ i ≤ T₁ i := by
    rw [hratio i]
    have hm := mul_le_mul_of_nonneg_right
      (show 4 * (C : ℝ) ≤ Real.exp (η * s i) by linarith) hT₀.le
    simpa only [mul_comm] using hm
  obtain ⟨hL, hthreshold, hrounded⟩ := rounded_test_degrees C (T₀ i) (T₁ i) hi hT₁ hgap
  refine ⟨hL, hthreshold, hrounded.trans_eq ?_⟩
  have hinv : T₀ i / T₁ i = Real.exp (-η * s i) := by
    rw [hratio i, show -η * s i = -(η * s i) by ring, Real.exp_neg]
    field_simp
  rw [hinv]

end DistinctDistances.SparseCones
