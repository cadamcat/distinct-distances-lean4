import DistinctDistances.TrackE.Directional
import DistinctDistances.TrackE.OuterRoots
import DistinctDistances.TrackE.FinalCurveMass
import DistinctDistances.TrackE.RegularityBudget
import DistinctDistances.TrackE.FinalCurveRegularity
import DistinctDistances.TrackE.TestDegreeRounding
import DistinctDistances.TrackE.MixedFiber
import DistinctDistances.TrackE.DepthAssembly
import DistinctDistances.TrackE.WideCarriers
import DistinctDistances.TrackE.SelectionSequence
import DistinctDistances.TrackE.CommonProfiles
import DistinctDistances.TrackE.CommonEndpoint
import DistinctDistances.TrackE.WindowBranches
import DistinctDistances.TrackE.ProfileBranches
import DistinctDistances.TrackE.TerminalDepth
import DistinctDistances.TrackE.DepthBatch
import DistinctDistances.TrackE.ProfileBatchGraph
import DistinctDistances.TrackE.DirectionEnvelope
import DistinctDistances.TrackE.DirectionRank
import DistinctDistances.TrackE.StrictMargins
import DistinctDistances.TrackE.StrictRankInduction
import DistinctDistances.TrackE.SeparatedEndpoint
import DistinctDistances.TrackE.CoveringEnvelope
import DistinctDistances.TrackE.FinalCurvePlacement
import DistinctDistances.TrackE.FinalNarrowRegularity
import DistinctDistances.TrackE.FinalMinorCuts
import DistinctDistances.TrackE.FinalCurveContradiction
import DistinctDistances.TrackE.OuterEndpoint

/-!
# `sc:theorem`: the sparse-cones theorem (`sparse-cones.tex:10-19, 930-941`)

The paper states it along a contradiction sequence: no families `C_p` with
`deg C_p ≤ δN/A`, `δ → 0`, cover `1 - o(1)` of the pairs in one orientation or the other. The
finitary form below (the convention of track D, `lead-d` `TrackD/Basic.lean`) is equivalent by a
diagonal argument: with `δ₀, ε₀ → 0` and `N₀ → ∞` a failure of it produces such a sequence.
It is the form `red:directions` consumes.

The proof assembles `prof:pair-selection` (track D) with the four endpoint contradictions of
`sparse-cones.tex` (`sc:u-common-contra`, `sc:u-outer-lift`, `sc:u-separated-contra`,
`sc:u-final-curve`); their Lean statements are fixed once track D's piece and profile
statements are fixed.
-/

namespace DistinctDistances

open Filter
open scoped BigOperators

noncomputable section

namespace SparseCones

variable {d : ℕ}

/-- The three literal window branches of one selected profile sequence are
each impossible (sparse-cones.tex:930–941). -/
theorem selected_profile_contradiction {regime : Regime d}
    {F : ConeCoverageSequence regime} (T : SelectedProfileSequence F) : False := by
  obtain ⟨φ, hφ, hbranch⟩ := selected_window_branch T
  rcases hbranch with hcom | hsep | hout
  · obtain ⟨ψ, hψ, M, hcom'⟩ :=
      selected_common_profile (T.comp φ hφ) (Frequently.of_forall hcom)
    exact common_profile_contradiction _ M hcom'
  · obtain ⟨ψ, hψ, S, hS⟩ :=
      selected_separated_sequence (T.comp φ hφ) (Frequently.of_forall hsep)
    obtain ⟨χ, hχ, L, hL⟩ := separated_profile_limits S
    letI : Fintype (ProfilePlateau L) := by
      unfold ProfilePlateau
      infer_instance
    refine separated_profile_contradiction (((T.comp φ hφ).comp ψ hψ).comp χ hχ) L
      (fun i => ?_) (fun i => ?_)
    · rw [hL]
      exact (hS (χ i)).1
    · rw [hL]
      exact (hS (χ i)).2
  · obtain ⟨ψ, hψ, M, hout', hs⟩ :=
      selected_outer_profile (T.comp φ hφ) (Frequently.of_forall hout)
    exact outer_profile_contradiction _ M hout' hs

/-- sc:theorem (`sparse-cones.tex:10-19`), finitary form. In dimension `d ≥ 3` under IH(d) there
are `η, δ₀, ε₀ > 0` and `N₀` such that for every `P` with `|P| ≥ N₀` and `M ≤ ε₀ A`, and all
directional families `C_p` (`p ∈ P`) of total degree at most `δ₀ N/A`, at least `η N^2` ordered
pairs of distinct points are covered in neither orientation. -/
theorem sparse_cones (hd : 3 ≤ d) (hIH : IH d) :
    ∃ η δ₀ ε₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧ 0 < ε₀ ∧ ∃ N₀ : ℕ,
      ∀ P : Finset (RPoint d), N₀ ≤ P.card → Mcount P ≤ ε₀ * Ascale d P.card →
      ∀ C : RPoint d → ProjectiveFamily.Family d,
        (∀ p ∈ P, IsDirectionalFamily (C p)) →
        (∀ p ∈ P, (ProjectiveFamily.degree (C p) : ℝ) ≤ δ₀ * P.card / Ascale d P.card) →
        η * (P.card : ℝ) ^ 2 ≤ (uncoveredPairs P C).card := by
  by_contra hfail
  obtain ⟨regime, ⟨F⟩⟩ := cone_sequence_of_failure hd hIH hfail
  obtain ⟨φ, hφ, ⟨T⟩⟩ := select_profile_sequence F
  exact selected_profile_contradiction T

end SparseCones

end

end DistinctDistances
