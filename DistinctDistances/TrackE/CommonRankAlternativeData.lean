import DistinctDistances.TrackE.CommonRankInduction

/-! The equal-dimension / borrowing alternative of one common plateau,
sparse-cones.tex:239–306, stated before its proof. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- The equal-dimension degree lower bound on the plateau after the zero-based
cut `j`: `D_1` on the first plateau (`k = d-1`, sparse-cones.tex:282–295) and
`e_{j+1}^2` on later plateaux (`k < d-1`, sparse-cones.tex:297–306). -/
def commonEqualDimLower {F : ConeCoverageSequence regime} {T : SelectedProfileSequence F}
    (M : CommonPoolProfile T) (i j : ℕ) : ℝ :=
  if j = 0 then
    TrackD.cutScale (regime.B i) (M.s i) M.b ⟨0, by have := regime.dimension_ge_three; omega⟩
  else (TrackD.eScale (regime.B i) (M.s i) M.b (j + 1)) ^ 2

/-- sc:common-rank.plateau alternative at a testing time `τ` on the plateau
after the zero-based cut `j` (`k = d - (j+1)`). For every later dense graph in
every chart, some envelope dimension group `h ≥ 2k` carries a dense subgraph
`Γ'`. Either `h = 2k` and the rank at `τ` has the equal-dimension degree lower
bound, or `h > 2k` and the rank at `τ` dominates every rank of `Γ'` with
exponent `h` (the upper Hilbert bound of the group at all degrees `E` against
its lower bound at the defining degree). -/
def CommonRankAlternative {F : ConeCoverageSequence regime} {T : SelectedProfileSequence F}
    (M : CommonPoolProfile T) (j : ℕ) (τ : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ θ : ℝ, 0 < θ → ∀ ρ : ℝ, 0 < ρ → ∀ᶠ i in atTop,
    ∀ (i₀ : Fin d) (Γ : Finset (RPoint d × RPoint d)),
      Γ ⊆ TrackD.poolPts (T.sources i) ×ˢ TrackD.poolPts (T.targets i) →
      (∀ pq ∈ Γ, (TrackD.toC pq.2 - TrackD.toC pq.1) i₀ ≠ 0) →
      ρ * ((TrackD.poolPts (T.sources i)).card : ℝ) *
        (TrackD.poolPts (T.targets i)).card ≤ Γ.card →
      ∃ h : ℕ, 2 * (d - (j + 1)) ≤ h ∧ h ≤ 2 * d ∧
        ∃ Γ' : Finset (RPoint d × RPoint d), Γ' ⊆ Γ ∧
          (ρ / (2 * (2 * d + 1 : ℝ))) * ((TrackD.poolPts (T.sources i)).card : ℝ) *
            (TrackD.poolPts (T.targets i)).card ≤ Γ'.card ∧
          ((h = 2 * (d - (j + 1)) ∧
            c * commonEqualDimLower M i j * Real.exp (-θ * M.s i) *
              (⌊TrackD.testDeg (regime.B i) (M.s i) τ⌋₊ : ℝ) ^ h ≤
              commonLabelRank i₀ Γ ⌊TrackD.testDeg (regime.B i) (M.s i) τ⌋₊) ∨
          (2 * (d - (j + 1)) < h ∧ ∀ E : ℕ,
            c * (commonLabelRank i₀ Γ' E : ℝ) *
              (⌊TrackD.testDeg (regime.B i) (M.s i) τ⌋₊ : ℝ) ^ h ≤
              (commonLabelRank i₀ Γ ⌊TrackD.testDeg (regime.B i) (M.s i) τ⌋₊ : ℝ) *
                ((E + h).choose h : ℝ)))

end
end DistinctDistances.SparseCones
