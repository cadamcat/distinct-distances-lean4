import DistinctDistances.TrackE.CommonProfiles

/-! Literal branches of `prof:pair-selection` (`profiles.tex:525–538, 570–618`). -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

namespace SelectedProfileSequence

/-- The two physical singleton pools in a common window, without role exchange. -/
def IsCommon {F : ConeCoverageSequence regime} (T : SelectedProfileSequence F)
    (i : ℕ) : Prop :=
  ∃ X Y : TrackD.Piece d, T.sources i = {X} ∧ T.targets i = {Y} ∧
    X.width = Y.width ∧ X.width < Real.log (regime.B i)

/-- The outermost pool used in both roles, with its literal lower mass bound. -/
def IsOuter {F : ConeCoverageSequence regime} (T : SelectedProfileSequence F)
    (i : ℕ) : Prop :=
  T.sources i = T.targets i ∧
    (∀ X ∈ T.sources i, X.width = Real.log (regime.B i)) ∧
    regime.N i * Real.sqrt (F.delta i) ≤ (TrackD.poolPts (T.sources i)).card

end SelectedProfileSequence

/-- Stabilize one literal window branch, retaining every selection field. -/
theorem selected_window_branch {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) :
    ∃ (φ : ℕ → ℕ) (hφ : StrictMono φ),
      (∀ i, (T.comp φ hφ).IsCommon i) ∨
      (∀ i, (T.comp φ hφ).IsSeparated i) ∨
      (∀ i, (T.comp φ hφ).IsOuter i) := by
  have halternative (i : ℕ) : T.IsCommon i ∨ T.IsSeparated i ∨ T.IsOuter i := by
    have hwin := (T.certificate i).window
    have hB : TrackD.cfgB (regime.P i) = regime.B i := rfl
    have hN : TrackD.cfgN (regime.P i) = regime.N i := rfl
    rcases hwin with hcommon | hseparated | houter
    · left
      rcases hcommon with ⟨X, Y, hX, hY, hw, hbound⟩
      rw [hB] at hbound
      exact ⟨X, Y, hX, hY, hw, hbound⟩
    · right; left
      rcases hseparated with ⟨X, Y, hX, hY, hw, hboundX, hboundY⟩
      rw [hB] at hboundX hboundY
      exact ⟨X, Y, hX, hY, hw, hboundX, hboundY⟩
    · right; right
      rcases houter with ⟨hXY, hwidth, hcard⟩
      rw [hB] at hwidth
      rw [hN] at hcard
      exact ⟨hXY, hwidth, hcard⟩
  have hfreq : (∃ᶠ i in atTop, T.IsCommon i) ∨
      (∃ᶠ i in atTop, T.IsSeparated i) ∨
      (∃ᶠ i in atTop, T.IsOuter i) := by
    have hevt : ∀ᶠ i in atTop, T.IsCommon i ∨ T.IsSeparated i ∨ T.IsOuter i :=
      Eventually.of_forall halternative
    have hf := hevt.frequently
    rwa [frequently_or_distrib, frequently_or_distrib] at hf
  rcases hfreq with hcom | hsep | hout
  · obtain ⟨φ, hφ, h⟩ := Filter.extraction_of_frequently_atTop hcom
    exact ⟨φ, hφ, Or.inl h⟩
  · obtain ⟨φ, hφ, h⟩ := Filter.extraction_of_frequently_atTop hsep
    exact ⟨φ, hφ, Or.inr (Or.inl h)⟩
  · obtain ⟨φ, hφ, h⟩ := Filter.extraction_of_frequently_atTop hout
    exact ⟨φ, hφ, Or.inr (Or.inr h)⟩

/-- The common singleton branch carries the shared limiting profile record. -/
theorem selected_common_profile {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (hcommon : ∃ᶠ i in atTop, T.IsCommon i) :
    ∃ (φ : ℕ → ℕ) (hφ : StrictMono φ)
      (M : CommonPoolProfile (T.comp φ hφ)),
      ∀ i, (T.comp φ hφ).IsCommon i := by
  obtain ⟨ψ, hψ, hψcom⟩ := Filter.extraction_of_frequently_atTop hcommon
  let T' := T.comp ψ hψ
  have hwidth (i : ℕ) : ∃ s : ℝ, ∀ Z ∈ T'.sources i ∪ T'.targets i, Z.width = s := by
    obtain ⟨X, Y, hX, hY, hXYw, _⟩ := hψcom i
    refine ⟨X.width, ?_⟩
    intro Z hZ
    have hZ' : Z ∈ T.sources (ψ i) ∪ T.targets (ψ i) := hZ
    rw [hX, hY, Finset.mem_union, Finset.mem_singleton, Finset.mem_singleton] at hZ'
    rcases hZ' with rfl | rfl
    · rfl
    · exact hXYw.symm
  obtain ⟨θ, hθ, ⟨M⟩⟩ := selected_common_pool_profile T' hwidth
  let φ := ψ ∘ θ
  have hφ : StrictMono φ := hψ.comp hθ
  have hcompEq : T'.comp θ hθ = T.comp φ hφ := rfl
  rw [hcompEq] at M
  refine ⟨φ, hφ, M, fun i => hψcom (θ i)⟩

/-- The outer branch retains equal physical roles, s=log B and N sqrt(delta). -/
theorem selected_outer_profile {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (houter : ∃ᶠ i in atTop, T.IsOuter i) :
    ∃ (φ : ℕ → ℕ) (hφ : StrictMono φ)
      (M : CommonPoolProfile (T.comp φ hφ)),
      (∀ i, (T.comp φ hφ).IsOuter i) ∧
      (∀ i, M.s i = Real.log (regime.B (φ i))) := by
  obtain ⟨ψ, hψ, hψout⟩ := Filter.extraction_of_frequently_atTop houter
  let T' := T.comp ψ hψ
  have hwidth (i : ℕ) : ∃ s : ℝ, ∀ Z ∈ T'.sources i ∪ T'.targets i, Z.width = s := by
    obtain ⟨hXY, hwidth, _⟩ := hψout i
    refine ⟨Real.log (regime.B (ψ i)), ?_⟩
    intro Z hZ
    have hZ' : Z ∈ T.sources (ψ i) ∨ Z ∈ T.targets (ψ i) := Finset.mem_union.mp hZ
    rcases hZ' with h | h
    · exact hwidth Z h
    · rw [← hXY] at h
      exact hwidth Z h
  obtain ⟨θ, hθ, ⟨M⟩⟩ := selected_common_pool_profile T' hwidth
  let φ := ψ ∘ θ
  have hφ : StrictMono φ := hψ.comp hθ
  have hcompEq : T'.comp θ hθ = T.comp φ hφ := rfl
  rw [hcompEq] at M
  have hM_s (i : ℕ) : M.s i = Real.log (regime.B (φ i)) := by
    obtain ⟨X, hX⟩ := (T.comp φ hφ).certificate i |>.sources_nonempty
    have hXmem : X ∈ (T.comp φ hφ).sources i ∪ (T.comp φ hφ).targets i :=
      Finset.mem_union_left _ hX
    have h1 := M.width i X hXmem
    have h2 := (hψout (θ i)).2.1 X hX
    rw [← h1, h2]
    rfl
  exact ⟨φ, hφ, M, fun i => hψout (θ i), hM_s⟩

end
end DistinctDistances.SparseCones
