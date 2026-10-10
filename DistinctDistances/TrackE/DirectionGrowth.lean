import DistinctDistances.TrackE.DirectionInitialRank

/-! Convert complete-component rank bounds to actual testing-degree growth,
with constants chosen before centers, rows and densities (sc:separated-rank). -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- `sc:separated-rank.power-alternative`: the same dense physical subrow
now borrows at every earlier testing time with its complete component dimension
as growth exponent. One constant absorbs all finite floor/binomial costs. -/
theorem dense_direction_rank_power_alternative {α : Type*} [Fintype α]
    {F : ConeCoverageSequence regime} {T : SelectedProfileSequence F}
    (S : LimitingSeparatedProfile regime)
    {plateau : α → ProfilePlateau S} {kind : α → DepthRateKind} {ε : α → ℝ}
    (H : ProfileDepthBatchData T S plateau kind ε) (a : α) (τ : ℝ)
    (hτ : S.b ⟨(plateau a).val.val - 1, by have := (plateau a).val.isLt; omega⟩ < τ ∧
      τ < S.b (plateau a).val) :
    ∃ c : ℝ, 0 < c ∧ ∀ ρ : ℝ, 0 < ρ → ∀ᶠ i in atTop,
      ∀ p ∈ (S.sequence.source i).pts.image TrackD.toC, p ∉ H.batch.badCenters i →
      ∀ Q : Finset (RPoint d), Q ⊆ (S.sequence.target i).pts →
        (∀ q ∈ Q, TrackD.toC q ≠ p) →
        (∀ q ∈ Q, TrackD.toC q ∉ batchBadTargets (fun a => H.data (plateau a))
          (fun i => (S.sequence.target i).pts.image TrackD.toC) H.batch.bad i p) →
        ρ * (((S.sequence.target i).pts.image TrackD.toC).card : ℝ) ≤ Q.card →
        ∃ h : ℕ, d - (plateau a).val.val ≤ h ∧ h ≤ d ∧
          ∃ Q' : Finset (RPoint d), Q' ⊆ Q ∧
            (ρ / (2 * (d + 1 : ℝ))) *
              (((S.sequence.target i).pts.image TrackD.toC).card : ℝ) ≤ Q'.card ∧
            let x := TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ;
            (h = d - (plateau a).val.val ∧
              c * ((H.data (plateau a)).degreeBudget i /
                profileDepthRate S (plateau a).val.val (kind a) i *
                Real.exp (-ε a * (H.data (plateau a)).s i)) * x^h ≤
                  rowDirectionRank p Q ⌊x⌋₊) ∨
            (d - (plateau a).val.val < h ∧ ∀ t : ℝ,
              let y := TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width t;
              1 ≤ y → c * (rowDirectionRank p Q' ⌊y⌋₊ : ℝ) * (x / y)^h ≤
                rowDirectionRank p Q ⌊x⌋₊) := by
  classical
  obtain ⟨c, hc, hAlt⟩ := dense_direction_envelope_rank_alternative S H a τ hτ
  have hden : 0 < (4 : ℝ)^d := by positivity
  refine ⟨c / (4 : ℝ)^d, div_pos hc hden, ?_⟩
  intro ρ hρ
  filter_upwards [hAlt ρ hρ, target_test_degree S τ] with i hAlt_i htest
  intro p hp htypical Q hQ hneq hsurvives hdense
  obtain ⟨h, hlh, hhd, Q', hQ'Q, hQ'mass, hchoice⟩ :=
    hAlt_i p hp htypical Q hQ hneq hsurvives hdense
  let x := TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ
  let D := H.data (plateau a)
  let U := D.degreeBudget i / profileDepthRate S (plateau a).val.val (kind a) i *
    Real.exp (-ε a * D.s i)
  refine ⟨h, hlh, hhd, Q', hQ'Q, hQ'mass, ?_⟩
  change (h = d - (plateau a).val.val ∧
    (c / (4 : ℝ)^d) * U * x^h ≤ rowDirectionRank p Q ⌊x⌋₊) ∨
    (d - (plateau a).val.val < h ∧ ∀ t : ℝ,
      let y := TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width t;
      1 ≤ y → (c / (4 : ℝ)^d) * (rowDirectionRank p Q' ⌊y⌋₊ : ℝ) * (x / y)^h ≤
        rowDirectionRank p Q ⌊x⌋₊)
  rcases hchoice with ⟨heq, hsame⟩ | ⟨hlt, hborrow⟩
  · refine Or.inl ⟨heq, ?_⟩
    have hB : 0 < regime.B i := regime.B_pos i
    have hbudget : 0 ≤ D.degreeBudget i := by
      unfold TrackA.SeparatedDepthData.degreeBudget TrackA.SeparatedDepthData.cutDegree
      exact Finset.prod_nonneg (fun _ _ => mul_nonneg hB.le (Real.exp_nonneg _))
    have hrate : 0 < profileDepthRate S (plateau a).val.val (kind a) i := by
      cases hk : kind a <;> simp only [profileDepthRate, hk] <;> positivity
    have hU : 0 ≤ U := mul_nonneg (div_nonneg hbudget hrate.le) (Real.exp_nonneg _)
    exact same_dimension_floor_growth d h hhd c U (rowDirectionRank p Q ⌊x⌋₊) x
      hc.le hU htest hsame
  · refine Or.inr ⟨hlt, ?_⟩
    intro t y hy
    have hb := hborrow ⌊y⌋₊
    exact borrowed_floor_growth d h hhd c (rowDirectionRank p Q' ⌊y⌋₊)
      (rowDirectionRank p Q ⌊x⌋₊) x y hc.le (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      htest hy hb

end
end DistinctDistances.SparseCones
