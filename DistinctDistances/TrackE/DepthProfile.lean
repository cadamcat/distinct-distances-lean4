import DistinctDistances.TrackD.Profiles.PairSelection
import DistinctDistances.TrackA.Depth

/-!
Sequence inputs for the separated-window branch (`depth.tex:4–16`;
`profiles.tex:525–535, 570–618`). The finitary precision parameters have
already been chosen by a slow diagonal. These are recorded pieces and paths,
not the hypotheses of the actual-center depth theorem.
-/

namespace DistinctDistances.SparseCones

open Filter
open scoped Topology BigOperators Classical

noncomputable section

/-- Two actual pieces in separated windows, before passage to a limiting profile.
The initial-index conditions can be obtained by dropping a finite prefix. -/
structure SeparatedProfileSequence {d : ℕ} (regime : Regime d) where
  source : ℕ → TrackD.Piece d
  target : ℕ → TrackD.Piece d
  base_good : ∀ i, TrackD.PieceGood (regime.P i) 1 1 1 (source i) ∧
    TrackD.PieceGood (regime.P i) 1 1 1 (target i)
  good : ∀ θ : ℝ, 0 < θ → ∀ ξ : ℝ, 0 < ξ → ∀ K : ℝ, 1 ≤ K →
    ∀ᶠ i in atTop, TrackD.PieceGood (regime.P i) θ ξ K (source i) ∧
      TrackD.PieceGood (regime.P i) θ ξ K (target i)
  width_pos : ∀ i, 0 < (source i).width ∧ 0 < (target i).width
  source_grows : Tendsto (fun i => (source i).width) atTop atTop
  target_grows : Tendsto (fun i => (target i).width) atTop atTop
  source_small : Framework.LittleO (fun i => (source i).width)
    (fun i => Real.log (regime.B i))
  target_small : Framework.LittleO (fun i => (target i).width)
    (fun i => Real.log (regime.B i))
  separated : Tendsto (fun i => (source i).width / (target i).width) atTop (𝓝 0) ∨
    Tendsto (fun i => (target i).width / (source i).width) atTop (𝓝 0)
  times_close : ∀ t, Tendsto (fun i => (source i).path.time t - (target i).path.time t)
    atTop (𝓝 0)

namespace SeparatedProfileSequence

/-- Reindex the actual pieces together with the underlying contradiction sequence. -/
def comp {d : ℕ} {regime : Regime d} (S : SeparatedProfileSequence regime)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) : SeparatedProfileSequence (regime.comp φ hφ) := by
  refine {
    source := fun i => S.source (φ i)
    target := fun i => S.target (φ i)
    base_good := fun i => S.base_good (φ i)
    good := ?_
    width_pos := fun i => S.width_pos (φ i)
    source_grows := S.source_grows.comp hφ.tendsto_atTop
    target_grows := S.target_grows.comp hφ.tendsto_atTop
    source_small := S.source_small.comp_tendsto hφ.tendsto_atTop
    target_small := S.target_small.comp_tendsto hφ.tendsto_atTop
    separated := ?_
    times_close := fun t => (S.times_close t).comp hφ.tendsto_atTop }
  · intro θ hθ ξ hξ K hK
    exact hφ.tendsto_atTop.eventually (S.good θ hθ ξ hξ K hK)
  · rcases S.separated with h | h
    · exact Or.inl (h.comp hφ.tendsto_atTop)
    · exact Or.inr (h.comp hφ.tendsto_atTop)

end SeparatedProfileSequence

/-- A single limiting profile, shared by the source and target, with the
balance margins consumed at the separated endpoints. -/
structure LimitingSeparatedProfile {d : ℕ} (regime : Regime d) where
  sequence : SeparatedProfileSequence regime
  b : Fin d → ℝ
  source_limit : Framework.ProfileConverges (fun i => (sequence.source i).path.time) b
  target_limit : Framework.ProfileConverges (fun i => (sequence.target i).path.time) b
  sorted : Monotone b
  sum_zero : ∑ t, b t = 0
  balance : ∃ c : ℝ, 0 < c ∧
    b ⟨0, by have := regime.dimension_ge_three; omega⟩ ≤ -c ∧
    c ≤ b ⟨d - 1, by have := regime.dimension_ge_three; omega⟩ ∧
    b ⟨0, by have := regime.dimension_ge_three; omega⟩ +
      b ⟨1, by have := regime.dimension_ge_three; omega⟩ ≤ -c

/-- `G5.profile-limits`: compactness and the profile budget give an honest
limiting profile, retaining both actual piece sequences on the same subsequence. -/
theorem separated_profile_limits {d : ℕ} {regime : Regime d}
    (S : SeparatedProfileSequence regime) :
    ∃ (φ : ℕ → ℕ) (hφ : StrictMono φ)
      (T : LimitingSeparatedProfile (regime.comp φ hφ)),
      T.sequence = S.comp φ hφ := by
  have hd := regime.dimension_ge_three
  have hbounded : ∀ᶠ i in atTop, ∀ t, -1 ≤ (S.target i).path.time t ∧
      (S.target i).path.time t ≤ 2 := Eventually.of_forall fun i t => by
    have h := (S.base_good i).2.time_range t
    exact ⟨h.1, by linarith [h.2]⟩
  obtain ⟨φ, hφ, b, htarget⟩ := Framework.exists_profile_subsequence
    (fun i => (S.target i).path.time) (-1) 2 hbounded
  have hsource : Framework.ProfileConverges (fun i => (S.source (φ i)).path.time) b := by
    intro t
    have h := ((S.times_close t).comp hφ.tendsto_atTop).add (htarget t)
    simpa only [Function.comp_apply, sub_add_cancel, zero_add] using h
  have hmono : Monotone b := by
    intro t u htu
    exact le_of_tendsto_of_tendsto (htarget t) (htarget u)
      (Eventually.of_forall fun i => (S.base_good (φ i)).2.mono htu)
  have hsum : Tendsto (fun i => ∑ t, (S.target (φ i)).path.time t) atTop (𝓝 (∑ t, b t)) :=
    tendsto_finsetSum Finset.univ (fun t _ => htarget t)
  have hsumBound : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ i in atTop, |∑ t, (S.target (φ i)).path.time t| ≤ ε := by
    intro ε hε
    obtain ⟨θ, hθ, ξ₀, hξ₀, s₀, hbudget⟩ := TrackD.prof_budget_sum d hd ε hε
    have hξ : 0 < ξ₀ / 2 := by positivity
    have heventual : ∀ᶠ i in atTop, |∑ t, (S.target i).path.time t| ≤ ε := by
      filter_upwards [S.good θ hθ (ξ₀ / 2) hξ 1 le_rfl,
        S.target_grows.eventually_ge_atTop s₀] with i hi hwidth
      exact hbudget (regime.P i) (S.target i) (ξ₀ / 2) 1 hξ (by linarith)
        le_rfl hi.2 hwidth
    exact hφ.tendsto_atTop.eventually heventual
  have hsumZero : ∑ t, b t = 0 := by
    by_contra hne
    have hpos : 0 < |∑ t, b t| := abs_pos.mpr hne
    have h := le_of_tendsto hsum.abs (hsumBound (|∑ t, b t| / 2) (by positivity))
    linarith
  obtain ⟨c, Cd, hc, hCd, hbudgets⟩ := TrackD.prof_budget d hd
  obtain ⟨θ, hθ, ξ₀, hξ₀, s₀, hbudget⟩ := hbudgets 1 (by norm_num) 1 (by norm_num)
  have hξ : 0 < ξ₀ / 2 := by positivity
  let t₀ : Fin d := ⟨0, by omega⟩
  let t₁ : Fin d := ⟨1, by omega⟩
  let tlast : Fin d := ⟨d - 1, by omega⟩
  have hmargins : ∀ᶠ i in atTop,
      (S.target (φ i)).path.time t₀ ≤ -c ∧ c ≤ (S.target (φ i)).path.time tlast ∧
        (S.target (φ i)).path.time t₀ + (S.target (φ i)).path.time t₁ ≤ -c := by
    have heventual : ∀ᶠ i in atTop,
        (S.target i).path.time t₀ ≤ -c ∧ c ≤ (S.target i).path.time tlast ∧
          (S.target i).path.time t₀ + (S.target i).path.time t₁ ≤ -c := by
      filter_upwards [S.good θ hθ (ξ₀ / 2) hξ 1 le_rfl,
        S.target_grows.eventually_ge_atTop s₀] with i hi hwidth
      have h := hbudget (regime.P i) (S.target i) (ξ₀ / 2) 1 hξ (by linarith)
        le_rfl hi.2 hwidth
      exact ⟨h.1.2.1, h.1.2.2.1, h.1.2.2.2⟩
    exact hφ.tendsto_atTop.eventually heventual
  have hfirst : b t₀ ≤ -c :=
    le_of_tendsto (htarget t₀) (hmargins.mono fun i hi => hi.1)
  have hlast : c ≤ b tlast :=
    ge_of_tendsto (htarget tlast) (hmargins.mono fun i hi => hi.2.1)
  have hpair : b t₀ + b t₁ ≤ -c :=
    le_of_tendsto ((htarget t₀).add (htarget t₁)) (hmargins.mono fun i hi => hi.2.2)
  let T : LimitingSeparatedProfile (regime.comp φ hφ) := {
    sequence := S.comp φ hφ
    b := b
    source_limit := hsource
    target_limit := htarget
    sorted := hmono
    sum_zero := hsumZero
    balance := ⟨c, hc, hfirst, hlast, hpair⟩ }
  exact ⟨φ, hφ, T, rfl⟩

end

end DistinctDistances.SparseCones
