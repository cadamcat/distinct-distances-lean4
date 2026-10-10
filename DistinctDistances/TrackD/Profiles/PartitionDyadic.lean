import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace DistinctDistances.TrackD

open scoped BigOperators
noncomputable section

/-- The final halving window lies in [t,2t), with all previous windows
at least 2t. No constant depends on the number of windows. -/
theorem partition_dyadic_stop (b t : ℝ) (ht : 0 < t) (hbt : t ≤ b) :
    ∃ a : ℕ, t ≤ b / 2 ^ a ∧ b / 2 ^ a < 2 * t ∧
      ∀ k < a, 2 * t ≤ b / 2 ^ k := by
  have hratio : (1 : ℝ) ≤ b / t := (le_div_iff₀ ht).mpr (by simpa using hbt)
  obtain ⟨a, hlow, hhigh⟩ := exists_nat_pow_near hratio (by norm_num : (1 : ℝ) < 2)
  have hp : (0 : ℝ) < 2 ^ a := by positivity
  have hlower := (le_div_iff₀ ht).mp hlow
  have hupper := (div_lt_iff₀ ht).mp hhigh
  refine ⟨a, (le_div_iff₀ hp).mpr (by nlinarith), ?_, ?_⟩
  · apply (div_lt_iff₀ hp).mpr
    rw [pow_succ] at hupper
    nlinarith
  · intro k hk
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ k)).mpr
    have hpow : (2 : ℝ) ^ (k + 1) ≤ 2 ^ a := pow_le_pow_right₀ (by norm_num) (by omega)
    have hmul := mul_le_mul_of_nonneg_right hpow ht.le
    rw [pow_succ] at hmul
    nlinarith

/-- Reverse the finite halving windows and compare their losses to the
infinite dyadic sum at the actual smallest width. -/
theorem partition_dyadic_sum_le (f : ℝ → ℝ) (b u : ℝ) (a : ℕ)
    (hu : u = b / 2 ^ a) (hpos : ∀ n : ℕ, 0 ≤ f (2 ^ n * u))
    (hsum : Summable (fun n : ℕ => f (2 ^ n * u))) :
    (∑ k ∈ Finset.range a, f (b / 2 ^ k)) ≤ ∑' n : ℕ, f (2 ^ n * u) := by
  have hscale : ∀ k < a, b / 2 ^ k = 2 ^ (a - k) * u := by
    intro k hk
    have hpow : (2 : ℝ) ^ a = 2 ^ (a - k) * 2 ^ k := by
      rw [← pow_add]
      congr 1
      omega
    rw [hu, hpow]
    field_simp
  have heq : (∑ k ∈ Finset.range a, f (b / 2 ^ k)) =
      ∑ n ∈ Finset.Icc 1 a, f (2 ^ n * u) := by
    apply Finset.sum_bij (fun k hk => a - k)
    · intro k hk
      simp only [Finset.mem_range] at hk
      simp only [Finset.mem_Icc]
      omega
    · intro k₁ hk₁ k₂ hk₂ h
      simp only [Finset.mem_range] at hk₁ hk₂
      omega
    · intro n hn
      simp only [Finset.mem_Icc] at hn
      refine ⟨a - n, by simp only [Finset.mem_range]; omega, ?_⟩
      omega
    · intro k hk
      rw [hscale k (Finset.mem_range.mp hk)]
  rw [heq]
  exact hsum.sum_le_tsum (Finset.Icc 1 a) (fun n hn => hpos n)

/-- The per-window loss ledger telescopes. Its total loss is a sum of
fractions, not the window count times a worst-case fraction. -/
theorem partition_window_mass_ledger (n : ℕ) (remaining emitted error : ℕ → ℝ)
    (hstep : ∀ i < n, remaining i - remaining (i + 1) - emitted i ≤ error i) :
    remaining 0 - remaining n - (∑ i ∈ Finset.range n, emitted i) ≤
      ∑ i ∈ Finset.range n, error i := by
  have main : ∀ k ≤ n,
      remaining 0 - remaining k - (∑ i ∈ Finset.range k, emitted i) ≤
        ∑ i ∈ Finset.range k, error i := by
    intro k
    induction k with
    | zero => intro hk; simp
    | succ k ih =>
        intro hk
        have hprev := ih (by omega)
        have hnext := hstep k (by omega)
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        linarith
  exact main n le_rfl

end
end DistinctDistances.TrackD
