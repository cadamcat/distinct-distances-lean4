import DistinctDistances.TrackE.WindowBranches

/-! Route the three literal selected-window cases to their limiting profiles
(`sc:selection.branches`, sparse-cones.tex:21–25, 44–49, 340–350, 658–666;
profiles.tex:525–538, 570–618). Every returned selection is a reindexing of
the original physical pools, cones, graph and global terminal assignment. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- The separated limiting profile remains indexed by the exact selected
singleton pools, without exchanging the source and target roles. -/
structure SeparatedPoolProfile {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) where
  profile : LimitingSeparatedProfile regime
  source : ∀ i, T.sources i = {profile.sequence.source i}
  target : ∀ i, T.targets i = {profile.sequence.target i}

/-- `sc:selection.separated-profile`: compose the width-orientation and profile
subsequences, retaining their literal singleton identities in one record. -/
theorem selected_separated_profile {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (hsep : ∃ᶠ i in atTop, T.IsSeparated i) :
    ∃ (φ : ℕ → ℕ) (hφ : StrictMono φ),
      Nonempty (SeparatedPoolProfile (T.comp φ hφ)) := by
  obtain ⟨φ₀, hφ₀, S, hS⟩ := selected_separated_sequence T hsep
  obtain ⟨φ₁, hφ₁, L, hL⟩ := separated_profile_limits S
  refine ⟨φ₀ ∘ φ₁, hφ₀.comp hφ₁, ⟨{
    profile := L
    source := ?_
    target := ?_ }⟩⟩
  · intro i
    rw [hL]
    exact (hS (φ₁ i)).1
  · intro i
    rw [hL]
    exact (hS (φ₁ i)).2

/-- `sc:selection.branches`: one subsequence has a common singleton profile,
a separated singleton profile, or the same outer pool in both roles with the
original square-root-delta mass and its exact logarithmic width. -/
theorem selected_profile_alternative {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) :
    ∃ (φ : ℕ → ℕ) (hφ : StrictMono φ),
      (∃ M : CommonPoolProfile (T.comp φ hφ),
        ∀ i, (T.comp φ hφ).IsCommon i) ∨
      Nonempty (SeparatedPoolProfile (T.comp φ hφ)) ∨
      (∃ M : CommonPoolProfile (T.comp φ hφ),
        (∀ i, (T.comp φ hφ).IsOuter i) ∧
        (∀ i, M.s i = Real.log (regime.B (φ i)))) := by
  obtain ⟨φ₀, hφ₀, hbranch⟩ := selected_window_branch T
  let T₀ := T.comp φ₀ hφ₀
  rcases hbranch with hcommon | hsep | houter
  · obtain ⟨φ₁, hφ₁, M, hM⟩ := selected_common_profile T₀
      (Filter.Frequently.of_forall hcommon)
    exact ⟨φ₀ ∘ φ₁, hφ₀.comp hφ₁, Or.inl ⟨M, hM⟩⟩
  · obtain ⟨φ₁, hφ₁, M⟩ := selected_separated_profile T₀
      (Filter.Frequently.of_forall hsep)
    exact ⟨φ₀ ∘ φ₁, hφ₀.comp hφ₁, Or.inr (Or.inl M)⟩
  · obtain ⟨φ₁, hφ₁, M, hM, hs⟩ := selected_outer_profile T₀
      (Filter.Frequently.of_forall houter)
    exact ⟨φ₀ ∘ φ₁, hφ₀.comp hφ₁, Or.inr (Or.inr ⟨M, hM, hs⟩)⟩

end
end DistinctDistances.SparseCones
