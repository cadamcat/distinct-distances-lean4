import DistinctDistances.TrackD.Profiles.PartitionRemainder
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace DistinctDistances.TrackD

open Filter
open scoped BigOperators Classical Topology
noncomputable section

/-- A fixed coefficient multiplying a lower power is absorbed by any fixed
positive fraction of a larger power. -/
theorem partition_scaled_rpow_eventually (p q C ε : ℝ) (hpq : p < q) (hε : 0 < ε) :
    ∀ᶠ s : ℝ in atTop, C * s ^ p < ε * s ^ q := by
  have ht : Tendsto (fun s : ℝ => C * s ^ (p - q)) atTop (𝓝 0) := by
    simpa only [neg_sub, mul_zero] using
      (tendsto_rpow_neg_atTop (show 0 < q - p by linarith)).const_mul C
  have hsmall := ht.eventually (eventually_lt_nhds hε)
  filter_upwards [hsmall, eventually_gt_atTop (0 : ℝ)] with s hsmall hs
  rw [Real.rpow_sub hs, ← mul_div_assoc] at hsmall
  exact (div_lt_iff₀ (Real.rpow_pos_of_pos hs q)).mp hsmall

/-- One width threshold handles both the external piece size and the
remainder's strict comparison with the greedy extraction threshold. -/
theorem partition_growth_budgets_eventually (C θ : ℝ) (hθ : 0 < θ) :
    ∀ᶠ s : ℝ in atTop, 1 ≤ s ∧
      Real.sqrt s + C * s ^ ((1 : ℝ) / 10) ≤ θ * s ∧
      s ^ ((1 : ℝ) / 3) + C * s ^ ((1 : ℝ) / 10) < Real.sqrt s := by
  have hθhalf : 0 < θ / 2 := by positivity
  have h1 := partition_scaled_rpow_eventually ((1 : ℝ) / 2) 1 1 (θ / 2)
    (by norm_num) hθhalf
  have h2 := partition_scaled_rpow_eventually ((1 : ℝ) / 10) 1 C (θ / 2)
    (by norm_num) hθhalf
  have h3 := partition_scaled_rpow_eventually ((1 : ℝ) / 3) ((1 : ℝ) / 2) 1 (1 / 2)
    (by norm_num) (by norm_num)
  have h4 := partition_scaled_rpow_eventually ((1 : ℝ) / 10) ((1 : ℝ) / 2) C (1 / 2)
    (by norm_num) (by norm_num)
  filter_upwards [h1, h2, h3, h4, eventually_ge_atTop (1 : ℝ)] with s h1 h2 h3 h4 hs
  simp only [one_mul, Real.rpow_one, ← Real.sqrt_eq_rpow] at h1 h2 h3 h4
  exact ⟨hs, by linarith, by linarith⟩

theorem partition_capture_error_eventually (θ : ℝ) (hθ : 0 < θ) :
    ∀ᶠ s : ℝ in atTop, Real.exp (-7 * s ^ ((1 : ℝ) / 10) / 18) ≤ θ := by
  have ht := tendsto_rpow_atTop (show (0 : ℝ) < 1 / 10 by norm_num)
  have hb := ht.eventually (eventually_ge_atTop (-18 / 7 * Real.log θ))
  filter_upwards [hb] with s hs
  rw [← Real.exp_log hθ]
  apply Real.exp_le_exp.mpr
  linarith

end
end DistinctDistances.TrackD
