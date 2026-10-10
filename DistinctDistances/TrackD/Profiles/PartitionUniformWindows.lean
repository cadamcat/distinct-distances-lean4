import DistinctDistances.TrackD.Profiles.PartitionGridParameters
import DistinctDistances.TrackD.Profiles.PartitionWidthControls
import DistinctDistances.TrackD.Profiles.PartitionCarryover

namespace DistinctDistances.TrackD

open Filter
open scoped BigOperators Classical Topology
noncomputable section

/-- One fixed grid and one width threshold precede the sample, the window
index and every batch. The two extra scalar gaps preserve the next entry. -/
theorem partition_uniform_window_parameters (d : ℕ) (θ ξ K : ℝ)
    (hθ : 0 < θ) (hξ : 0 < ξ) :
    ∃ G : ℕ, ∃ hG : 0 < G, ∃ grid : Fin G → ℝ, ∃ s₁ : ℝ,
      1 ≤ s₁ ∧ StrictMono grid ∧ grid ⟨0, hG⟩ = -1 ∧
      1 + θ / 2 ≤ grid ⟨G - 1, by omega⟩ ∧
      grid ⟨G - 1, by omega⟩ ≤ 1 + θ ∧
      (∀ k : Fin G, ∀ hk : k.val + 1 < G,
        grid ⟨k.val + 1, hk⟩ - grid k ≤ min (θ / 8) (ξ / 4)) ∧
      ∀ s ≥ s₁, ∃ a : Fin (G * d) → ℝ,
        PartitionWidthControls d G θ ξ K s a ∧
        Real.sqrt s + Real.log (d + 1 : ℝ) ≤ θ * s / 4 ∧
        Real.log K ≤ ξ / 4 * (s / 2) := by
  obtain ⟨G, hG, grid, hmono, hfirst, hlast, hupper, hmesh⟩ :=
    partition_fixed_grid θ ξ hθ hξ
  obtain ⟨S, hSone, hcontrols⟩ := partition_width_controls d G θ ξ K hθ hξ
  have hroot := partition_scaled_rpow_eventually ((1 : ℝ) / 2) 1 1 (θ / 8)
    (by norm_num) (by positivity)
  have hconstant := partition_scaled_rpow_eventually 0 1 (Real.log (d + 1 : ℝ)) (θ / 8)
    (by norm_num) (by positivity)
  have hmult := partition_scaled_rpow_eventually 0 1 (Real.log K) (ξ / 8)
    (by norm_num) (by positivity)
  have hevent : ∀ᶠ s : ℝ in atTop,
      Real.sqrt s + Real.log (d + 1 : ℝ) ≤ θ * s / 4 ∧
        Real.log K ≤ ξ / 4 * (s / 2) := by
    filter_upwards [hroot, hconstant, hmult] with s hr hc hm
    simp only [one_mul, Real.rpow_one, Real.rpow_zero, mul_one, ← Real.sqrt_eq_rpow] at hr hc hm
    constructor <;> nlinarith
  obtain ⟨T, hT⟩ := eventually_atTop.mp hevent
  refine ⟨G, hG, grid, max S T, hSone.trans (le_max_left _ _),
    hmono, hfirst, hlast, hupper, hmesh, ?_⟩
  intro s hs
  obtain ⟨a, ha⟩ := hcontrols s ((le_max_left _ _).trans hs)
  exact ⟨a, ha, hT s ((le_max_right _ _).trans hs)⟩

/-- The terminal width bound converts entry isolation into the single
core-degree bound used with the delta threshold. -/
theorem partition_final_core_degree (B s t θ L : ℝ) (hB : 0 ≤ B)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hstop : s ≤ 2 * t) (hθ : θ ≤ 1 / 2)
    (hdegree : L ≤ testDeg B s (1 + θ / 2)) :
    L ≤ B * Real.exp (3 * t) := by
  apply hdegree.trans
  unfold testDeg
  apply mul_le_mul_of_nonneg_left _ hB
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul_of_nonneg_right
    (show 1 + θ / 2 ≤ (3 : ℝ) / 2 by linarith) hs
  nlinarith

end
end DistinctDistances.TrackD
