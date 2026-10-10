import DistinctDistances.TrackE.CommonRankAlternative
import DistinctDistances.TrackE.CommonRankNumerics
import DistinctDistances.TrackE.CommonRankInitial

/-! The common label rank, sparse-cones.tex:216–316, assembled downstream of
the retained-product infrastructure. Its statement uses the definitions of CommonRank.lean. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- One plateau step: the alternative, then the scalar propagation. -/
theorem common_rank_plateau_step {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (M : CommonPoolProfile T)
    (j : ℕ) (hj : j + 1 < d)
    (hprev : ∀ τ' : ℝ, τ' < M.b ⟨j, by omega⟩ → (∀ a : Fin d, M.b a ≠ τ') →
      ∀ θ : ℝ, 0 < θ → CommonRankAt M τ' θ)
    (τ : ℝ) (hτ₁ : M.b ⟨j, by omega⟩ < τ) (hτ₂ : τ < M.b ⟨j + 1, hj⟩) :
    ∀ θ : ℝ, 0 < θ → CommonRankAt M τ θ :=
  common_rank_step_of_alternative T M j hj hprev τ ⟨hτ₁, hτ₂⟩
    (common_rank_envelope_alternative T M j hj τ ⟨hτ₁, hτ₂⟩)

/-- sc:common-rank, with the statement of `common_label_rank`. -/
theorem common_label_rank_proved {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (M : CommonPoolProfile T)
    (τ : ℝ) (_hτ₀ : -1 < τ) (hτ : τ < commonLastTime M)
    (hcut : ∀ a : Fin d, M.b a ≠ τ) :
    ∀ θ : ℝ, 0 < θ → ∀ ρ : ℝ, 0 < ρ → ∀ᶠ i in atTop,
      ∀ (i₀ : Fin d) (Γ : Finset (RPoint d × RPoint d)),
        Γ ⊆ TrackD.poolPts (T.sources i) ×ˢ TrackD.poolPts (T.targets i) →
        (∀ pq ∈ Γ, (TrackD.toC pq.2 - TrackD.toC pq.1) i₀ ≠ 0) →
        ρ * ((TrackD.poolPts (T.sources i)).card : ℝ) *
          (TrackD.poolPts (T.targets i)).card ≤ Γ.card →
        commonRankTarget M i τ * Real.exp (-θ * M.s i) ≤
          commonLabelRank i₀ Γ ⌊TrackD.testDeg (regime.B i) (M.s i) τ⌋₊ :=
  common_label_rank_of_steps T M (common_rank_initial T M)
    (fun j hj hprev τ h₁ h₂ => common_rank_plateau_step T M j hj hprev τ h₁ h₂) τ hτ hcut

end
end DistinctDistances.SparseCones
