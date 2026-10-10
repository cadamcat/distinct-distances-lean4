import DistinctDistances.TrackE.DirectionPropagationInputs

/-! Initial rank and strict margin for actual radial directions of arbitrary
dense physical target rows, sparse-cones.tex:711–718. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- `sc:separated-rank.initial-full`: the initial no-capture plateau forces
every dense row's direction envelope to have the full homogeneous rank.
The polynomial, complex center and physical row can all be chosen later. -/
theorem initial_direction_rank_full (S : LimitingSeparatedProfile regime) (τ : ℝ)
    (hτ : τ < S.b ⟨0, by have := regime.dimension_ge_three; omega⟩) :
    ∀ ρ : ℝ, 0 < ρ → ∀ᶠ i in atTop,
      ∀ p : Point d, ∀ Q : Finset (RPoint d), Q ⊆ (S.sequence.target i).pts →
        (∀ q ∈ Q, TrackD.toC q ≠ p) →
        ρ * ((S.sequence.target i).pts.card : ℝ) ≤ Q.card →
        rowDirectionRank p Q
          ⌊TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ⌋₊ =
            (⌊TrackD.testDeg (TrackD.cfgB (regime.P i))
              (S.sequence.target i).width τ⌋₊ + (d - 1)).choose (d - 1) := by
  classical
  obtain ⟨ξ, hξ, hplateau⟩ := target_initial_plateau_margin S τ hτ
  intro ρ hρ
  have hhalf : 0 < ρ / 2 := by positivity
  filter_upwards [S.sequence.good (ρ / 2) hhalf ξ hξ 1 le_rfl,
    hplateau, target_test_degree S τ] with i hgood hplateaui htest
  intro p Q hQ hneq hdense
  let L : ℕ := ⌊TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ⌋₊
  apply row_direction_rank_full (by have := regime.dimension_ge_three; omega) p Q L
  intro f hf hfV
  by_contra hfnz
  obtain ⟨g, hgdeg, hgnz, hgeval⟩ := nonzero_direction_pullback p f hf hfnz
  have henvspec := (Bridges.projective_envelope d (rowDirections p Q) L).choose_spec
  have hfzero := (henvspec.2.1 f hf).mp hfV
  have hvanish : ∀ q ∈ Q, MvPolynomial.eval (TrackD.toC q - p) f = 0 := by
    intro q hq
    apply hfzero (TrackD.toC q - p)
    refine ⟨sub_ne_zero.mpr (hneq q hq), ?_⟩
    exact ⟨q, hq, hneq q hq, rfl⟩
  have hdegree : (g.totalDegree : ℝ) ≤
      1 * TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ := by
    have hg : (g.totalDegree : ℝ) ≤ (L : ℝ) := by exact_mod_cast hgdeg
    have hfloor : (L : ℝ) ≤ TrackD.testDeg (TrackD.cfgB (regime.P i))
        (S.sequence.target i).width τ := Nat.floor_le (by linarith)
    simpa only [one_mul] using hg.trans hfloor
  have hcapture := hgood.2.noCapture 0 (by have := regime.dimension_ge_three; omega)
    τ hplateaui htest g hdegree
  have hsub : Q ⊆ (S.sequence.target i).path.captured 0 (S.sequence.target i).pts g := by
    intro q hq
    refine Finset.mem_filter.mpr ⟨hQ hq, ?_, ?_⟩
    · rw [hgeval]
      exact hvanish q hq
    · intro Z hZ
      rw [initial_carrier_ideal _ Z hZ.1]
      simpa only [Ideal.mem_bot] using hgnz
  have hcard : (Q.card : ℝ) ≤
      (((S.sequence.target i).path.captured 0 (S.sequence.target i).pts g).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hN : 0 < TrackD.cfgN (regime.P i) := by
    simpa only [TrackD.cfgN, Regime.N] using regime.N_pos i
  have hmass : 0 < ((S.sequence.target i).pts.card : ℝ) :=
    (mul_pos hN (Real.exp_pos _)).trans_le (S.sequence.base_good i).2.size
  have hpos := mul_pos hρ hmass
  have hbound := hcard.trans hcapture
  nlinarith

/-- `sc:separated-rank.initial`: a fixed positive strict-rank margin on the
initial interval, uniform over all later dense rows and complex centers. -/
theorem initial_direction_rank_margin (S : LimitingSeparatedProfile regime) (τ : ℝ)
    (hτ : τ < S.b ⟨0, by have := regime.dimension_ge_three; omega⟩) :
    ∃ c : ℝ, 0 < c ∧ ∀ ρ : ℝ, 0 < ρ → ∀ᶠ i in atTop,
      ∀ p : Point d, ∀ Q : Finset (RPoint d), Q ⊆ (S.sequence.target i).pts →
        (∀ q ∈ Q, TrackD.toC q ≠ p) →
        ρ * ((S.sequence.target i).pts.card : ℝ) ≤ Q.card →
        profileDirectionRankTarget S i τ * Real.exp (c * (S.sequence.target i).width) ≤
          rowDirectionRank p Q
            ⌊TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ⌋₊ := by
  obtain ⟨κ, hκ, hb₀, _, _⟩ := S.balance
  have hτneg : τ < 0 := by linarith
  refine ⟨-τ, by linarith, ?_⟩
  intro ρ hρ
  filter_upwards [initial_direction_rank_full S τ hτ ρ hρ,
    initial_profile_rank_margin S τ hτ] with i hfull hmargin
  intro p Q hQ hneq hdense
  rw [hfull p Q hQ hneq hdense]
  exact hmargin

end
end DistinctDistances.SparseCones
