import DistinctDistances.TrackD.Profiles.RankInduction

namespace DistinctDistances.TrackD

noncomputable section

set_option maxHeartbeats 1000000 in
theorem budget_rank_real (d : ℕ) (hd : 3 ≤ d) :
    ∃ Cd : ℝ, 0 < Cd ∧ ∀ θ > 0, ∀ (α₀ : ℝ), 0 < α₀ → ∃ θ₁ > 0, ∃ s₁ : ℝ,
      ∀ (P : Finset (Pt d)) (X : Piece d) (ξ K : ℝ), 0 < ξ → 1 ≤ K →
        PieceGood P θ₁ ξ K X → s₁ ≤ X.width →
        ∀ j : ℕ, j ≤ d → ∀ b : ℝ, OnPlateau X.path.time j ξ b →
          1 ≤ testDeg (cfgB P) X.width b →
          ∀ S ⊆ X.pts, α₀ * (X.pts.card : ℝ) ≤ (S.card : ℝ) →
            sigma (cfgB P) X.width X.path.time b * Real.exp (-(Cd*ξ+θ)*X.width) ≤
              hilbertOfSet (toC '' (S : Set (Pt d))) ⌊testDeg (cfgB P) X.width b⌋₊ := by
  obtain ⟨c, hc, hcomparison⟩ := piece_rank_comparison d
  let Cd : ℝ := 2*(d : ℝ)^3+1
  refine ⟨Cd, by dsimp [Cd]; positivity, ?_⟩
  intro θ hθ α hα
  let μ := θ/(d+1 : ℝ)
  have hμ : 0 < μ := by dsimp [μ]; positivity
  let θ₁ := RankCore.density α d 0 / 2
  have hθ₁ : 0 < θ₁ := div_pos (RankCore.density_pos hα d 0) (by norm_num)
  obtain ⟨s₀, hs₀⟩ := RankCore.lower_constant hc hμ
  refine ⟨θ₁, hθ₁, max 1 s₀, ?_⟩
  intro P X ξ K hξ hK hX hs j hj b hb hT S hS hSdense
  have hs1 : 1 ≤ X.width := (le_max_left 1 s₀).trans hs
  have hs0 : s₀ ≤ X.width := (le_max_right 1 s₀).trans hs
  have hsmall := hs₀ X.width hs0
  have hcomp := hcomparison P X θ₁ ξ K hθ₁.le hK hX
  have hmain := RankCore.rank_induction d (by omega) P X α μ ξ K c hα hμ hξ hK hX
    hs1 hsmall hcomp j hj b hb hT S hS
  have hn : 0 ≤ (X.pts.card : ℝ) := Nat.cast_nonneg _
  have hSβ : RankCore.density α d j * X.pts.card ≤ (S.card : ℝ) :=
    (mul_le_mul_of_nonneg_right (RankCore.density_le_initial hα.le d j) hn).trans hSdense
  have hbound := hmain hSβ
  have hμsum : (d+1 : ℝ)*μ = θ := by
    dsimp [μ]
    field_simp
  have hq : 0 ≤ 2*(d : ℝ)^2*ξ+μ := by positivity
  have hjR : (j : ℝ) ≤ d := by exact_mod_cast hj
  have hloss : (j : ℝ)*(2*(d : ℝ)^2*ξ+μ)+μ ≤ Cd*ξ+θ := by
    have hstep := mul_le_mul_of_nonneg_right hjR hq
    dsimp [Cd]
    nlinarith
  have hspos : 0 ≤ X.width := by linarith
  have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hloss) hspos)
  exact (mul_le_mul_of_nonneg_left he (RankCore.sigma_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) _ _ _)).trans hbound

/-- Preserve the frozen natural-density signature while supplying the
paper's stronger real-density form above. -/
theorem budget_rank_proof (d : ℕ) (hd : 3 ≤ d) :
    ∃ Cd : ℝ, 0 < Cd ∧ ∀ θ > 0, ∀ α₀ > 0, ∃ θ₁ > 0, ∃ s₁ : ℝ,
      ∀ (P : Finset (Pt d)) (X : Piece d) (ξ K : ℝ), 0 < ξ → 1 ≤ K →
        PieceGood P θ₁ ξ K X → s₁ ≤ X.width →
        ∀ j : ℕ, j ≤ d → ∀ b : ℝ, OnPlateau X.path.time j ξ b →
          1 ≤ testDeg (cfgB P) X.width b →
          ∀ S ⊆ X.pts, α₀ * X.pts.card ≤ S.card →
            sigma (cfgB P) X.width X.path.time b * Real.exp (-(Cd*ξ+θ)*X.width) ≤
              hilbertOfSet (toC '' (S : Set (Pt d))) ⌊testDeg (cfgB P) X.width b⌋₊ := by
  obtain ⟨Cd, hCd, hreal⟩ := budget_rank_real d hd
  refine ⟨Cd, hCd, ?_⟩
  intro θ hθ α hα
  obtain ⟨θ₁, hθ₁, s₁, hbound⟩ := hreal θ hθ (α : ℝ) (by exact_mod_cast hα)
  refine ⟨θ₁, hθ₁, s₁, ?_⟩
  intro P X ξ K hξ hK hX hs j hj b hb hT S hS hdensity
  exact hbound P X ξ K hξ hK hX hs j hj b hb hT S hS (by exact_mod_cast hdensity)

end
end DistinctDistances.TrackD
