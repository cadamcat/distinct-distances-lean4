import DistinctDistances.TrackD.Profiles.PartitionBoundary

namespace DistinctDistances.TrackD

open Filter
open scoped BigOperators Classical Topology
noncomputable section

structure PartitionWidthControls (d G : ℕ) (θ ξ K s : ℝ)
    (a : Fin (G * d) → ℝ) : Prop where
  width : 1 ≤ s
  positive : 0 < s ^ ((1 : ℝ) / 10)
  weights : ∀ i, s ^ ((1 : ℝ) / 10) ≤ a i
  tail : ∀ i, (∑ k ∈ Finset.univ.filter (fun k : Fin (G * d) => i < k), a k) ≤ a i / 9
  total : (∑ i, a i) ≤ (10 : ℝ) ^ (G * d) * s ^ ((1 : ℝ) / 10)
  size : Real.sqrt s + partitionEventTail a 0 ≤ θ * s
  remainder : s ^ ((1 : ℝ) / 3) + partitionEventTail a 0 < Real.sqrt s
  capture : Real.exp (-7 * s ^ ((1 : ℝ) / 10) / 18) ≤ θ
  boundary : Real.exp (-Real.sqrt (2 * s) + Real.sqrt s + partitionEventTail a 0) ≤ θ
  multiplier : Real.log K < ξ / 4 * s

/-- The analytic threshold precedes the sample. At each width one hierarchy
is chosen before any greedy batch or tree of that width. -/
theorem partition_width_controls (d G : ℕ) (θ ξ K : ℝ) (hθ : 0 < θ) (hξ : 0 < ξ) :
    ∃ s₁ : ℝ, 1 ≤ s₁ ∧ ∀ s ≥ s₁, ∃ a : Fin (G * d) → ℝ,
      PartitionWidthControls d G θ ξ K s a := by
  let C : ℝ := (10 : ℝ) ^ (G * d)
  have hgrowth := partition_growth_budgets_eventually C θ hθ
  have hbound := partition_inherited_boundary_eventually C θ hθ
  have hcap := partition_capture_error_eventually θ hθ
  have hmult := partition_scaled_rpow_eventually 0 1 (Real.log K) (ξ / 4)
    (by norm_num) (by positivity)
  have hall : ∀ᶠ s : ℝ in atTop, 1 ≤ s ∧
      Real.sqrt s + C * s ^ ((1 : ℝ) / 10) ≤ θ * s ∧
      s ^ ((1 : ℝ) / 3) + C * s ^ ((1 : ℝ) / 10) < Real.sqrt s ∧
      Real.exp (-7 * s ^ ((1 : ℝ) / 10) / 18) ≤ θ ∧
      Real.exp (-Real.sqrt (2 * s) + Real.sqrt s + C * s ^ ((1 : ℝ) / 10)) ≤ θ ∧
      Real.log K < ξ / 4 * s := by
    filter_upwards [hgrowth, hbound, hcap, hmult] with s hg hb hc hm
    simp only [Real.rpow_zero, mul_one, Real.rpow_one] at hm
    exact ⟨hg.1, hg.2.1, hg.2.2, hc, hb, hm⟩
  obtain ⟨S, hS⟩ := eventually_atTop.mp hall
  refine ⟨max S 1, le_max_right _ _, ?_⟩
  intro s hs
  obtain ⟨hsone, hsize, hrem, hcap, hboundary, hmult⟩ := hS s ((le_max_left _ _).trans hs)
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hsone
  have hupos : 0 < s ^ ((1 : ℝ) / 10) := Real.rpow_pos_of_pos hspos _
  obtain ⟨a, ha, htail, htotal⟩ := partition_threshold_hierarchy (G * d) (s ^ ((1 : ℝ) / 10)) hupos
  have htail0 : partitionEventTail a 0 ≤ C * s ^ ((1 : ℝ) / 10) := by
    simpa [partitionEventTail, C, mul_comm] using htotal
  refine ⟨a, ⟨hsone, hupos, ha, htail, ?_, ?_, ?_, hcap, ?_, hmult⟩⟩
  · simpa [C, mul_comm] using htotal
  · linarith
  · linarith
  · exact (Real.exp_le_exp.mpr (by linarith :
        -Real.sqrt (2 * s) + Real.sqrt s + partitionEventTail a 0 ≤
          -Real.sqrt (2 * s) + Real.sqrt s + C * s ^ ((1 : ℝ) / 10))).trans hboundary

theorem partition_event_error_bound {K : ℕ} (a : Fin K → ℝ) (u : ℝ)
    (ha : ∀ i, u ≤ a i) :
    partitionEventTail (fun i => Real.exp (-a i / 2)) 0 ≤ (K : ℝ) * Real.exp (-u / 2) := by
  simp only [partitionEventTail, Nat.zero_le, Finset.filter_true]
  calc
    (∑ i : Fin K, Real.exp (-a i / 2)) ≤ ∑ i : Fin K, Real.exp (-u / 2) := by
      apply Finset.sum_le_sum
      intro i hi
      exact Real.exp_le_exp.mpr (by have h := ha i; linarith)
    _ = (K : ℝ) * Real.exp (-u / 2) := by simp

end
end DistinctDistances.TrackD
