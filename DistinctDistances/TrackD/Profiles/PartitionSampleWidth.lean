import DistinctDistances.TrackD.Profiles.Defs

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section

/-- Choose the sample threshold before the configuration so that its
outer dyadic width dominates the fixed terminal width. -/
theorem partition_sample_width (d : ℕ) (hd : 0 < d) (t : ℝ) (ht : 0 < t) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ P : Finset (Pt d), N₀ ≤ P.card →
      0 < cfgN P ∧ 1 < cfgB P ∧ 4 * t ≤ Real.log (cfgB P) := by
  let N₀ : ℕ := max 2 ⌈Real.exp ((d : ℝ) * (4 * t))⌉₊
  refine ⟨N₀, le_max_left _ _, ?_⟩
  intro P hP
  have hcard : 2 ≤ P.card := (le_max_left _ _).trans hP
  have hN : 0 < cfgN P := by unfold cfgN; exact_mod_cast (by omega : 0 < P.card)
  have hNP : (0 : ℝ) < P.card := hN
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hlarge : Real.exp ((d : ℝ) * (4 * t)) ≤ (P.card : ℝ) := by
    apply (Nat.le_ceil _).trans
    exact_mod_cast ((le_max_right _ _).trans hP : ⌈Real.exp ((d : ℝ) * (4 * t))⌉₊ ≤ P.card)
  have hlog : (d : ℝ) * (4 * t) ≤ Real.log (P.card : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos _) hlarge
    simpa only [Real.log_exp] using h
  have hwidth : 4 * t ≤ Real.log (cfgB P) := by
    unfold cfgB
    rw [Real.log_rpow hNP]
    have hdivide : 4 * t ≤ Real.log (P.card : ℝ) / (d : ℝ) :=
      (le_div_iff₀ hdR).mpr (by nlinarith)
    simpa only [one_div_mul_eq_div] using hdivide
  have hBpos : 0 < cfgB P := by unfold cfgB; exact Real.rpow_pos_of_pos hNP _
  have hB : 1 < cfgB P := (Real.log_pos_iff hBpos.le).mp (by linarith)
  exact ⟨hN, hB, hwidth⟩

end
end DistinctDistances.TrackD
