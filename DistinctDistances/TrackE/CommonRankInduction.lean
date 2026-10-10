import DistinctDistances.TrackE.CommonEndpointInputs

/-! Propagation of the common label rank through the finitely many cut
times, sparse-cones.tex:229–316. The initial interval and one plateau step
are the only inputs. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- sc:label-rank at one testing time `τ` with logarithmic tolerance `θ`,
for every later dense physical graph in every chart containing its pairs. -/
def CommonRankAt {F : ConeCoverageSequence regime} {T : SelectedProfileSequence F}
    (M : CommonPoolProfile T) (τ θ : ℝ) : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ∀ᶠ i in atTop,
    ∀ (i₀ : Fin d) (Γ : Finset (RPoint d × RPoint d)),
      Γ ⊆ TrackD.poolPts (T.sources i) ×ˢ TrackD.poolPts (T.targets i) →
      (∀ pq ∈ Γ, (TrackD.toC pq.2 - TrackD.toC pq.1) i₀ ≠ 0) →
      ρ * ((TrackD.poolPts (T.sources i)).card : ℝ) *
        (TrackD.poolPts (T.targets i)).card ≤ Γ.card →
      commonRankTarget M i τ * Real.exp (-θ * M.s i) ≤
        commonLabelRank i₀ Γ ⌊TrackD.testDeg (regime.B i) (M.s i) τ⌋₊

/-- The induction over cut times: the initial interval before the first cut,
and one step for the open plateau between the zero-based cuts `j` and `j+1`
given the rank at every earlier time off the cuts, give the rank at every time
off the cuts before the last cut. Times below `-1` are allowed: there the
testing degree may be below one, which is the paper's rank-one convention. -/
theorem common_label_rank_of_steps {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (M : CommonPoolProfile T)
    (hinit : ∀ τ : ℝ, τ < M.b ⟨0, by have := regime.dimension_ge_three; omega⟩ →
      ∀ θ : ℝ, 0 < θ → CommonRankAt M τ θ)
    (hstep : ∀ (j : ℕ) (hj : j + 1 < d),
      (∀ τ' : ℝ, τ' < M.b ⟨j, by omega⟩ → (∀ a : Fin d, M.b a ≠ τ') →
        ∀ θ : ℝ, 0 < θ → CommonRankAt M τ' θ) →
      ∀ τ : ℝ, M.b ⟨j, by omega⟩ < τ → τ < M.b ⟨j + 1, hj⟩ →
        ∀ θ : ℝ, 0 < θ → CommonRankAt M τ θ)
    (τ : ℝ) (hτ : τ < commonLastTime M)
    (hcut : ∀ a : Fin d, M.b a ≠ τ) :
    ∀ θ : ℝ, 0 < θ → CommonRankAt M τ θ := by
  have hd := regime.dimension_ge_three
  -- `Q j`: the rank at every admissible time below all cuts of index at least `j`.
  have key : ∀ j : ℕ, j < d → ∀ τ : ℝ, (∀ a : Fin d, M.b a ≠ τ) →
      (∀ a : Fin d, j ≤ a.val → τ < M.b a) → ∀ θ : ℝ, 0 < θ → CommonRankAt M τ θ := by
    intro j
    induction j with
    | zero =>
      intro _ τ _ hbelow
      exact hinit τ (hbelow _ (Nat.zero_le _))
    | succ j ih =>
      intro hj τ hcut hbelow
      rcases lt_or_gt_of_ne (hcut ⟨j, by omega⟩).symm with hlt | hgt
      · apply ih (by omega) τ hcut
        intro a ha
        rcases Nat.lt_or_ge j a.val with hja | hja
        · exact hbelow a hja
        · have hEq : a = ⟨j, by omega⟩ := Fin.ext (by show a.val = j; omega)
          rw [hEq]
          exact hlt
      · apply hstep j hj ?_ τ hgt (hbelow ⟨j + 1, hj⟩ le_rfl)
        intro τ' hτ' hcut'
        apply ih (by omega) τ' hcut'
        intro a ha
        exact lt_of_lt_of_le hτ' (M.sorted (show (⟨j, by omega⟩ : Fin d) ≤ a from ha))
  apply key (d - 1) (by omega) τ hcut
  intro a ha
  have hEq : a = ⟨d - 1, by omega⟩ := Fin.ext (by show a.val = d - 1; have := a.isLt; omega)
  rw [hEq]
  exact hτ

end
end DistinctDistances.SparseCones
