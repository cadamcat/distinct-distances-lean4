import DistinctDistances.TrackE.OuterPool

/-! Supporting lemmas for 190 `outer_smooth_subfamily` (lane m-o-r190).

Plateau-agnostic helpers only (no `OuterRegularity` types, to avoid a
dependency loop, since `OuterRegularity.lean` loads this file). The main
helper lemma with the missing plateau hypotheses lives directly above 190
in `OuterRegularity.lean`. No frozen declaration is proved here. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- A time strictly inside `(lo, hi)` avoiding all `d` cut times. -/
theorem exists_time_avoiding_cuts (b : Fin d → ℝ) (lo hi : ℝ) (h : lo < hi) :
    ∃ τ : ℝ, lo < τ ∧ τ < hi ∧ ∀ a : Fin d, b a ≠ τ := by
  classical
  -- `d+1` evenly spaced points in `(lo, hi)`; one avoids the `d` cuts.
  let pts : Finset ℝ := (Finset.range (d + 1)).image
    (fun k : ℕ => lo + (hi - lo) * ((k : ℝ) + 1) / ((d : ℝ) + 2))
  have hpts_card : pts.card = d + 1 := by
    rw [Finset.card_image_of_injective]
    · rw [Finset.card_range]
    · intro k l hkl
      simp only at hkl
      have hne : ((hi - lo) / ((d : ℝ) + 2)) ≠ 0 := by
        have hpos : (0 : ℝ) < (hi - lo) / ((d : ℝ) + 2) := by
          apply div_pos (by linarith) (by positivity)
        exact ne_of_gt hpos
      have hsub : (hi - lo) * ((k : ℝ) + 1) / ((d : ℝ) + 2) =
          (hi - lo) * ((l : ℝ) + 1) / ((d : ℝ) + 2) := by
        have h' : lo + (hi - lo) * ((k : ℝ) + 1) / ((d : ℝ) + 2) =
            lo + (hi - lo) * ((l : ℝ) + 1) / ((d : ℝ) + 2) := hkl
        exact add_left_cancel h'
      have hmul : ((k : ℝ) + 1) = ((l : ℝ) + 1) := by
        have hDpos : (0 : ℝ) < (d : ℝ) + 2 := by positivity
        field_simp at hsub ⊢
        have h2 : (hi - lo) * ((k : ℝ) + 1) = (hi - lo) * ((l : ℝ) + 1) := by
          linarith [hsub]
        have hhl : hi - lo ≠ 0 := ne_of_gt (by linarith)
        exact mul_left_cancel₀ hhl h2
      have hkl2 : (k : ℝ) = (l : ℝ) := by linarith
      exact_mod_cast hkl2
  let cuts : Finset ℝ := Finset.image b Finset.univ
  have hcuts_card : cuts.card ≤ d := by
    calc cuts.card ≤ Finset.univ.card := Finset.card_image_le
      _ = d := by rw [Finset.card_univ, Fintype.card_fin]
  have hnotsub : ¬ pts ⊆ cuts := by
    intro hsub
    have hle := Finset.card_le_card hsub
    omega
  rw [Finset.not_subset] at hnotsub
  obtain ⟨τ, hτpts, hτnot⟩ := hnotsub
  rw [Finset.mem_image] at hτpts
  obtain ⟨k, hkrange, rfl⟩ := hτpts
  have hkmem : k ≤ d :=
    Nat.le_of_lt_succ (Finset.mem_range.mp hkrange)
  have hkR : (k : ℝ) ≤ (d : ℝ) := by exact_mod_cast hkmem
  have hDpos : (0 : ℝ) < (d : ℝ) + 2 := by positivity
  have hfrac_pos : (0 : ℝ) < ((k : ℝ) + 1) / ((d : ℝ) + 2) := by positivity
  have hfrac_lt : ((k : ℝ) + 1) / ((d : ℝ) + 2) < 1 := by
    rw [div_lt_one hDpos]
    linarith
  have hgap : (0 : ℝ) < hi - lo := by linarith
  have hprod_pos : (0 : ℝ) < (hi - lo) * ((k : ℝ) + 1) / ((d : ℝ) + 2) :=
    div_pos (mul_pos hgap (by positivity)) (by positivity)
  have hprod_lt : (hi - lo) * ((k : ℝ) + 1) / ((d : ℝ) + 2) < hi - lo := by
    have h1 : (hi - lo) * (((k : ℝ) + 1) / ((d : ℝ) + 2)) < (hi - lo) * 1 :=
      mul_lt_mul_of_pos_left hfrac_lt hgap
    calc (hi - lo) * ((k : ℝ) + 1) / ((d : ℝ) + 2)
        = (hi - lo) * (((k : ℝ) + 1) / ((d : ℝ) + 2)) := by
          rw [mul_div_assoc]
      _ < (hi - lo) * 1 := h1
      _ = hi - lo := mul_one _
  refine ⟨lo + (hi - lo) * ((k : ℝ) + 1) / ((d : ℝ) + 2), by linarith, by linarith, ?_⟩
  intro a ha
  apply hτnot
  show lo + (hi - lo) * ((k : ℝ) + 1) / ((d : ℝ) + 2) ∈ cuts
  unfold cuts
  rw [Finset.mem_image]
  exact ⟨a, Finset.mem_univ a, ha⟩

/-- Field cancellation for the exceptional-mass assembly: collapse `e²`
(used with `e = eScale`, `X = exp(εs)`). Pure real identity, kept here so
`field_simp` runs in a small context. -/
theorem cancel_escale_sq (X Wp e C Rp E01 : ℝ) (he : e ≠ 0) :
    X * (Wp / e ^ 2) * (C * ((Rp * e ^ 2 * X)) * (2 * E01)) =
      2 * C * Rp * Wp * (X * X * E01) := by
  field_simp

/-- Final-budget cancellation for the `g`-zero (and any `θg`-scaled) mass
estimate: with `θg = (ρ'/3)·(1-ρ)²`, the pool-to-`S` conversion leaves
exactly `(ρ'/3)·|S|²`. Kept here so `field_simp` runs in a small context. -/
theorem cancel_theta_sq (S Rm Rho : ℝ) (hRm : Rm ≠ 0) :
    ((Rho / 3) * Rm ^ 2) * ((S / Rm) * (S / Rm)) = (Rho / 3) * S ^ 2 := by
  field_simp

end
end DistinctDistances.SparseCones
