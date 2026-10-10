import DistinctDistances.TrackD.Profiles.PartitionGrowth

namespace DistinctDistances.TrackD

open Filter
open scoped BigOperators Classical Topology
noncomputable section

/-- A grid event just after -1/2 is available for every first-type batch. -/
theorem partition_grid_after_half {G : ℕ} (hG : 0 < G) (grid : Fin G → ℝ)
    (η : ℝ) (hη : 0 < η) (hηsmall : η ≤ 1 / 2)
    (hfirst : grid ⟨0, hG⟩ = -1) (hlast : 1 ≤ grid ⟨G - 1, by omega⟩)
    (hmesh : ∀ k : Fin G, ∀ hk : k.val + 1 < G,
      grid ⟨k.val + 1, hk⟩ - grid k ≤ η) :
    ∃ k : Fin G, -1 / 2 ≤ grid k ∧ grid k < -1 / 2 + η := by
  let last : Fin G := ⟨G - 1, by omega⟩
  let t : Fin 1 → ℝ := fun _ => grid last
  let b : ℝ := -1 / 2 - η
  have hp : OnPlateau t 0 (4 * η) b := by
    intro i
    constructor
    · intro hi; omega
    · intro hi
      dsimp [t, b]
      linarith
  have hm : ∀ k : Fin G, ∀ hk : k.val + 1 < G,
      grid ⟨k.val + 1, hk⟩ - grid k ≤ 4 * η / 4 := by
    intro k hk
    have h := hmesh k hk
    linarith
  rcases partition_grid_interior hG grid (4 * η) (by positivity) hm t
      (fun i => ⟨last, rfl⟩) 0 (by norm_num) b hp with hlow | ⟨k, hl, hu, hplateau⟩
  · rw [hfirst] at hlow
    dsimp [b] at hlow
    linarith
  · refine ⟨k, ?_, ?_⟩ <;> dsimp [b] at hl hu <;> linarith

/-- An inherited global boundary estimate is divided by the descendant's
original batch-size estimate without changing its carrier assignment. -/
theorem partition_boundary_mass_ratio (N n c v w θ : ℝ) (hn : 0 ≤ n)
    (hsize : N * Real.exp (-w) ≤ n) (hcapture : c ≤ N * Real.exp (-v))
    (hratio : Real.exp (w - v) ≤ θ) : c ≤ θ * n := by
  have h := mul_le_mul_of_nonneg_right hsize (Real.exp_nonneg (w - v))
  have heq : N * Real.exp (-w) * Real.exp (w - v) = N * Real.exp (-v) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [heq] at h
  calc
    c ≤ n * Real.exp (w - v) := hcapture.trans h
    _ ≤ n * θ := mul_le_mul_of_nonneg_left hratio hn
    _ = θ * n := mul_comm _ _

/-- The inherited exp(-sqrt(2s)) boundary is negligible relative to the
smallest regularized batch, uniformly for every sufficiently large width. -/
theorem partition_inherited_boundary_eventually (C θ : ℝ) (hθ : 0 < θ) :
    ∀ᶠ s : ℝ in atTop,
      Real.exp (-Real.sqrt (2 * s) + Real.sqrt s + C * s ^ ((1 : ℝ) / 10)) ≤ θ := by
  have htwo : 1 < Real.sqrt 2 := by
    have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hnonneg := Real.sqrt_nonneg (2 : ℝ)
    nlinarith
  let c : ℝ := (Real.sqrt 2 - 1) / 2
  have hc : 0 < c := by dsimp [c]; linarith
  have hslow := partition_scaled_rpow_eventually ((1 : ℝ) / 10) ((1 : ℝ) / 2) C c
    (by norm_num) hc
  have hlim := tendsto_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)
  have hlarge := hlim.eventually (eventually_ge_atTop (-Real.log θ / c))
  filter_upwards [hslow, hlarge] with s hslow hlarge
  rw [← Real.sqrt_eq_rpow] at hslow hlarge
  have hlog := (div_le_iff₀ hc).mp hlarge
  rw [← Real.exp_log hθ]
  apply Real.exp_le_exp.mpr
  calc
    _ = -Real.sqrt 2 * Real.sqrt s + Real.sqrt s + C * s ^ ((1 : ℝ) / 10) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    _ ≤ -Real.sqrt 2 * Real.sqrt s + Real.sqrt s + c * Real.sqrt s := by linarith
    _ = -c * Real.sqrt s := by dsimp [c]; ring
    _ ≤ Real.log θ := by linarith

end
end DistinctDistances.TrackD
