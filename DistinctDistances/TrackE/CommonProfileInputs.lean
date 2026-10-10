import DistinctDistances.TrackE.SelectionSequence

/-! Elementary inputs for literal common-window and outer-pool sequences
(`profiles.tex:570–618`; `sparse-cones.tex:44–52, 340–350`). -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- Disjoint equal-width pieces inherit the pool count bound from their
individual size lower bounds. No separate pool-count assumption is needed. -/
theorem pool_good_of_partition (P : Finset (RPoint d)) (Q : TrackD.Partition d)
    (δ θ ξ K s₀ ρ s : ℝ) (t : Fin d → ℝ)
    (hN : 0 < TrackD.cfgN P) (hQ : Q.Good P δ θ ξ K s₀)
    (pl : Finset (TrackD.Piece d)) (hsub : pl ⊆ Q.pieces)
    (hwidth : ∀ X ∈ pl, X.width = s)
    (hclose : ∀ X ∈ pl, ∀ a, |X.path.time a - t a| ≤ ρ) :
    TrackD.PoolGood P θ ξ K ρ pl s t := by
  refine ⟨?_, hwidth, hclose, ?_, ?_⟩
  · intro X hX
    exact (hQ.pieces_good X (hsub hX)).1
  · have hdisjoint : (pl : Set (TrackD.Piece d)).PairwiseDisjoint TrackD.Piece.pts :=
      hQ.pieces_disjoint.subset (Finset.coe_subset.mpr hsub)
    have hbiUnion : (pl.biUnion TrackD.Piece.pts).card = ∑ X ∈ pl, X.pts.card :=
      Finset.card_biUnion (fun X hX Y hY hne => hdisjoint (Finset.mem_coe.mpr hX) (Finset.mem_coe.mpr hY) hne)
    have hsubP : pl.biUnion TrackD.Piece.pts ⊆ P := by
      intro x hx
      obtain ⟨X, hX, hxX⟩ := Finset.mem_biUnion.mp hx
      exact (hQ.pieces_good X (hsub hX)).1.subset hxX
    have hcardLe : ((pl.biUnion TrackD.Piece.pts).card : ℝ) ≤ TrackD.cfgN P := by
      have := Finset.card_le_card hsubP
      dsimp [TrackD.cfgN]
      exact_mod_cast this
    have hsumLe : (pl.card : ℝ) * (TrackD.cfgN P * Real.exp (-θ * s)) ≤ ∑ X ∈ pl, (X.pts.card : ℝ) := by
      calc
        (pl.card : ℝ) * (TrackD.cfgN P * Real.exp (-θ * s)) = ∑ X ∈ pl, (TrackD.cfgN P * Real.exp (-θ * s)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ X ∈ pl, (X.pts.card : ℝ) := by
          apply Finset.sum_le_sum
          intro X hX
          have hpg := (hQ.pieces_good X (hsub hX)).1
          have hw := hwidth X hX
          have hsize := hpg.size
          rw [hw] at hsize
          exact hsize
    rw [← Nat.cast_sum, ← hbiUnion] at hsumLe
    have hcomb : (pl.card : ℝ) * Real.exp (-θ * s) * TrackD.cfgN P ≤ 1 * TrackD.cfgN P := by
      calc
        (pl.card : ℝ) * Real.exp (-θ * s) * TrackD.cfgN P = (pl.card : ℝ) * (TrackD.cfgN P * Real.exp (-θ * s)) := by ring
        _ ≤ ((pl.biUnion TrackD.Piece.pts).card : ℝ) := hsumLe
        _ ≤ TrackD.cfgN P := hcardLe
        _ = 1 * TrackD.cfgN P := by ring
    have hle1 : (pl.card : ℝ) * Real.exp (-θ * s) ≤ 1 := by
      nlinarith [hcomb, hN]
    have hexppos : 0 < Real.exp (θ * s) := Real.exp_pos _
    calc
      (pl.card : ℝ) = (pl.card : ℝ) * (Real.exp (-θ * s) * Real.exp (θ * s)) := by
        rw [← Real.exp_add]
        have : -θ * s + θ * s = 0 := by ring
        rw [this, Real.exp_zero, mul_one]
      _ = ((pl.card : ℝ) * Real.exp (-θ * s)) * Real.exp (θ * s) := by ring
      _ ≤ 1 * Real.exp (θ * s) := mul_le_mul_of_nonneg_right hle1 hexppos.le
      _ = Real.exp (θ * s) := one_mul _
  · exact hQ.pieces_disjoint.subset (Finset.coe_subset.mpr hsub)

/-- Budget limits for any actual selected piece sequence. The argument uses
growth and uniform good-piece bounds and requires no separation of widths. -/
theorem selected_piece_budget_limits {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (X : ℕ → TrackD.Piece d)
    (hX : ∀ i, X i ∈ T.sources i ∪ T.targets i) (b : Fin d → ℝ)
    (hlim : Framework.ProfileConverges (fun i => (X i).path.time) b) :
    Monotone b ∧ (∑ a, b a) = 0 ∧
      ∃ c : ℝ, 0 < c ∧
        b ⟨0, by have := regime.dimension_ge_three; omega⟩ ≤ -c ∧
        c ≤ b ⟨d - 1, by have := regime.dimension_ge_three; omega⟩ ∧
        b ⟨0, by have := regime.dimension_ge_three; omega⟩ +
          b ⟨1, by have := regime.dimension_ge_three; omega⟩ ≤ -c := by
  have hd := regime.dimension_ge_three
  have hmono : Monotone b := by
    intro t u htu
    apply le_of_tendsto_of_tendsto (hlim t) (hlim u)
    filter_upwards [selected_piece_good_eventually T 1 zero_lt_one 1 zero_lt_one 1 le_rfl] with i hi
    exact (hi (X i) (hX i)).mono htu
  have hsum : Tendsto (fun i => ∑ t, (X i).path.time t) atTop (𝓝 (∑ t, b t)) :=
    tendsto_finsetSum Finset.univ (fun t _ => hlim t)
  have hsumBound : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ i in atTop, |∑ t, (X i).path.time t| ≤ ε := by
    intro ε hε
    obtain ⟨θ, hθ, ξ₀, hξ₀, s₀, hbudget⟩ := TrackD.prof_budget_sum d hd ε hε
    have hξ : 0 < ξ₀ / 2 := by positivity
    have hwidth_ge : ∀ᶠ i in atTop, s₀ ≤ (X i).width := by
      have hcast : Tendsto (fun i => (T.precision i : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop.comp T.precision_grows
      have hscale : Tendsto (fun i => selectionScale (T.precision i)) atTop atTop := by
        simpa [selectionScale] using tendsto_atTop_add_const_right atTop 2 hcast
      filter_upwards [hscale.eventually (eventually_ge_atTop s₀)] with i hi
      have hq := (T.certificate i).good
      have hpiece_good : (X i) ∈ (T.partition i).pieces := by
        have hcases := Finset.mem_union.mp (hX i)
        rcases hcases with hx | hx
        · exact (T.certificate i).sources_subset hx
        · exact (T.certificate i).targets_subset hx
      exact hi.trans (hq.pieces_good (X i) hpiece_good).2
    filter_upwards [selected_piece_good_eventually T θ hθ (ξ₀ / 2) hξ 1 le_rfl, hwidth_ge] with i hi hwidth
    exact hbudget (regime.P i) (X i) (ξ₀ / 2) 1 hξ (by linarith) le_rfl (hi (X i) (hX i)) hwidth
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
  have hwidth_ge : ∀ᶠ i in atTop, s₀ ≤ (X i).width := by
    have hcast : Tendsto (fun i => (T.precision i : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp T.precision_grows
    have hscale : Tendsto (fun i => selectionScale (T.precision i)) atTop atTop := by
      simpa [selectionScale] using tendsto_atTop_add_const_right atTop 2 hcast
    filter_upwards [hscale.eventually (eventually_ge_atTop s₀)] with i hi
    have hq := (T.certificate i).good
    have hpiece_good : (X i) ∈ (T.partition i).pieces := by
      have hcases := Finset.mem_union.mp (hX i)
      rcases hcases with hx | hx
      · exact (T.certificate i).sources_subset hx
      · exact (T.certificate i).targets_subset hx
    exact hi.trans (hq.pieces_good (X i) hpiece_good).2
  have hmargins : ∀ᶠ i in atTop,
      (X i).path.time t₀ ≤ -c ∧ c ≤ (X i).path.time tlast ∧
        (X i).path.time t₀ + (X i).path.time t₁ ≤ -c := by
    filter_upwards [selected_piece_good_eventually T θ hθ (ξ₀ / 2) hξ 1 le_rfl, hwidth_ge] with i hi hwidth
    have h := hbudget (regime.P i) (X i) (ξ₀ / 2) 1 hξ (by linarith) le_rfl (hi (X i) (hX i)) hwidth
    exact ⟨h.1.2.1, h.1.2.2.1, h.1.2.2.2⟩
  have hfirst : b t₀ ≤ -c :=
    le_of_tendsto (hlim t₀) (hmargins.mono fun i hi => hi.1)
  have hlast : c ≤ b tlast :=
    ge_of_tendsto (hlim tlast) (hmargins.mono fun i hi => hi.2.1)
  have hpair : b t₀ + b t₁ ≤ -c :=
    le_of_tendsto ((hlim t₀).add (hlim t₁)) (hmargins.mono fun i hi => hi.2.2)
  exact ⟨hmono, hsumZero, c, hc, hfirst, hlast, hpair⟩

/-- A representative's profile limit controls every member of both actual
pools, uniformly. Both recorded profiles are close to the same reference. -/
theorem selected_uniform_profile_limit {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (X : ℕ → TrackD.Piece d)
    (hX : ∀ i, X i ∈ T.sources i ∪ T.targets i) (b : Fin d → ℝ)
    (hlim : Framework.ProfileConverges (fun i => (X i).path.time) b) :
    ∀ ρ : ℝ, 0 < ρ → ∀ᶠ i in atTop,
      ∀ Y ∈ T.sources i ∪ T.targets i, ∀ a, |Y.path.time a - b a| ≤ ρ := by
  intro ρ hρ
  have htol := selection_tolerance_tendsto_zero T.precision T.precision_grows
  have htol_small : ∀ᶠ i in atTop, 2 * selectionTolerance (T.precision i) ≤ ρ / 2 := by
    have hlim2 : Tendsto (fun i => 2 * selectionTolerance (T.precision i)) atTop (𝓝 (2 * 0)) :=
      htol.const_mul 2
    rw [mul_zero] at hlim2
    have hpos : 0 < ρ / 2 := by linarith
    exact (hlim2.eventually (Iio_mem_nhds hpos)).mono fun i hi => hi.le
  have hcoord : ∀ a : Fin d, ∀ᶠ i in atTop, |(X i).path.time a - b a| ≤ ρ / 2 := by
    intro a
    have ha := hlim a
    have hpos : 0 < ρ / 2 := by linarith
    exact (Metric.tendsto_nhds.mp ha (ρ / 2) hpos).mono fun i hi => by
      rw [Real.dist_eq] at hi
      exact hi.le
  have hcoords : ∀ᶠ i in atTop, ∀ a : Fin d, |(X i).path.time a - b a| ≤ ρ / 2 := by
    have hfin := (eventually_all_finset Finset.univ).mpr (fun a _ => hcoord a)
    exact hfin.mono fun i hi a => hi a (Finset.mem_univ a)
  filter_upwards [htol_small, hcoords] with i htol_i hcoords_i Y hY a
  have hYclose : |Y.path.time a - (T.reference i) a| ≤ selectionTolerance (T.precision i) :=
    (T.certificate i).close Y hY a
  have hXclose : |(X i).path.time a - (T.reference i) a| ≤ selectionTolerance (T.precision i) :=
    (T.certificate i).close (X i) (hX i) a
  have hYX : |Y.path.time a - (X i).path.time a| ≤ 2 * selectionTolerance (T.precision i) := by
    have htri : |Y.path.time a - (X i).path.time a| ≤
        |Y.path.time a - (T.reference i) a| + |(T.reference i) a - (X i).path.time a| :=
      abs_sub_le (Y.path.time a) (T.reference i a) ((X i).path.time a)
    have hrev : |(T.reference i) a - (X i).path.time a| = |(X i).path.time a - (T.reference i) a| :=
      abs_sub_comm _ _
    rw [hrev] at htri
    linarith [htri, hYclose, hXclose]
  have heq2 : Y.path.time a - b a = (Y.path.time a - (X i).path.time a) + ((X i).path.time a - b a) := by ring
  rw [heq2]
  have htri : |(Y.path.time a - (X i).path.time a) + ((X i).path.time a - b a)| ≤
      |Y.path.time a - (X i).path.time a| + |(X i).path.time a - b a| :=
    abs_add_le _ _
  linarith [hYX, hcoords_i a, htol_i]

/-- A nonempty selected pool in one common width has size
`N exp(±o(s))`. The original configuration bounds the union from above. -/
theorem selected_pool_mass_equivalent {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (s : ℕ → ℝ) (hs : ∀ i, 0 < s i)
    (hwidth : ∀ i, ∀ X ∈ T.sources i ∪ T.targets i, X.width = s i) :
    Framework.ExpEquivalent (fun _ => Unit)
      (fun i _ => ((TrackD.poolPts (T.sources i)).card : ℝ))
      (fun i _ => regime.N i) s ∧
    Framework.ExpEquivalent (fun _ => Unit)
      (fun i _ => ((TrackD.poolPts (T.targets i)).card : ℝ))
      (fun i _ => regime.N i) s := by
  have hpool : ∀ (pools : ℕ → Finset (TrackD.Piece d))
      (hsub : ∀ i, pools i ⊆ (T.partition i).pieces)
      (hne : ∀ i, (pools i).Nonempty)
      (hunion : ∀ i, ∀ X ∈ pools i, X ∈ T.sources i ∪ T.targets i),
      Framework.ExpEquivalent (fun _ => Unit)
        (fun i _ => ((TrackD.poolPts (pools i)).card : ℝ))
        (fun i _ => regime.N i) s := by
    intro pools hsub hne hunion
    constructor
    · -- ExpLower
      intro ε hε
      filter_upwards [selected_piece_good_eventually T ε hε 1 zero_lt_one 1 le_rfl] with i hi _
      obtain ⟨X, hX⟩ := hne i
      have hXpts : X.pts ⊆ TrackD.poolPts (pools i) := Finset.subset_biUnion_of_mem _ hX
      have hXcard : (X.pts.card : ℝ) ≤ ((TrackD.poolPts (pools i)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hXpts
      have hXgood := hi X (hunion i X hX)
      have hXsize := hXgood.size
      have hXw := hwidth i X (hunion i X hX)
      rw [hXw] at hXsize
      change regime.N i * Real.exp (-ε * s i) ≤ (X.pts.card : ℝ) at hXsize
      exact hXsize.trans hXcard
    · -- ExpUpper
      intro ε hε
      filter_upwards [] with i _
      have hsubP : TrackD.poolPts (pools i) ⊆ regime.P i := by
        intro x hx
        obtain ⟨X, hX, hxX⟩ := Finset.mem_biUnion.mp hx
        have hXgood := (T.certificate i).good.pieces_good X (hsub i hX)
        exact hXgood.1.subset hxX
      have hcard : ((TrackD.poolPts (pools i)).card : ℝ) ≤ regime.N i := by
        have := Finset.card_le_card hsubP
        dsimp [Regime.N]
        exact_mod_cast this
      have h1le : 1 ≤ Real.exp (ε * s i) := by
        have : 0 ≤ ε * s i := mul_nonneg hε.le (hs i).le
        simpa using Real.exp_le_exp.mpr this
      have hNnonneg : 0 ≤ regime.N i := by
        change 0 ≤ ((regime.P i).card : ℝ)
        exact Nat.cast_nonneg _
      calc
        ((TrackD.poolPts (pools i)).card : ℝ) ≤ regime.N i := hcard
        _ = regime.N i * 1 := by ring
        _ ≤ regime.N i * Real.exp (ε * s i) := mul_le_mul_of_nonneg_left h1le hNnonneg
  refine ⟨hpool T.sources (fun i => (T.certificate i).sources_subset)
    (fun i => (T.certificate i).sources_nonempty) (fun i X hX => Finset.mem_union_left _ hX),
    hpool T.targets (fun i => (T.certificate i).targets_subset)
    (fun i => (T.certificate i).targets_nonempty) (fun i X hX => Finset.mem_union_right _ hX)⟩

end
end DistinctDistances.SparseCones
