import DistinctDistances.TrackE.SeparatedEndpointInputs
import DistinctDistances.TrackE.ProjectedMass

/-! Compare the uniform strict rank on actual surviving rows with the
original cone degree bound; reduce all separated profiles to the final narrow
curve plateau (sparse-cones.tex:783–805). -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- sc:u-separated-contra: a positive strict margin near the last endpoint
contradicts a dense graph of covered rows surviving the original fixed batch. -/
theorem strict_separated_endpoint_contradiction {α : Type*} [Fintype α]
    {F : ConeCoverageSequence regime} (T : SelectedProfileSequence F)
    (S : LimitingSeparatedProfile regime)
    (hsource : ∀ i, T.sources i = {S.sequence.source i})
    (htarget : ∀ i, T.targets i = {S.sequence.target i})
    {plateau : α → ProfilePlateau S} {kind : α → DepthRateKind} {ε : α → ℝ}
    (H : ProfileDepthBatchData T S plateau kind ε) (c τ : ℝ) (hc : 0 < c)
    (hτ : τ < profileLastTime S)
    (hgap : (d : ℝ) * (profileLastTime S - τ) < c / 2)
    (hrank : DirectionRowRankMargin H τ c) : False := by
  classical
  obtain ⟨hgraph, _, _⟩ := selected_profile_batch_graph T S hsource htarget H
  have hρ : 0 < (1 / 8 : ℝ) := by norm_num
  have hdominates := endpoint_rank_target_dominates_cones F S 1 c τ
    (by norm_num) hc hτ hgap
  obtain ⟨i, hgraph_i, hrank_i, hdominates_i, htest_i⟩ :=
    (hgraph.and ((hrank (1 / 8) hρ).and
      (hdominates.and (target_test_degree S τ)))).exists
  let X := (S.sequence.source i).pts
  let Y := (S.sequence.target i).pts
  let Γ := profileBatchGraph H i
  have hN : 0 < TrackD.cfgN (regime.P i) := by
    simpa only [TrackD.cfgN, Regime.N] using regime.N_pos i
  have hXpos : 0 < (X.card : ℝ) :=
    (mul_pos hN (Real.exp_pos _)).trans_le (S.sequence.base_good i).1.size
  have hYpos : 0 < (Y.card : ℝ) :=
    (mul_pos hN (Real.exp_pos _)).trans_le (S.sequence.base_good i).2.size
  have hX : X.Nonempty := Finset.card_pos.mp (by exact_mod_cast hXpos)
  have hY : Y.Nonempty := Finset.card_pos.mp (by exact_mod_cast hYpos)
  have hΓ : Γ ⊆ X ×ˢ Y := by
    intro pq hpq
    have hterminal := (Finset.mem_filter.mp hpq).1
    obtain ⟨hp, hq, _, _, _⟩ := (mem_terminalSelectedGraph T i pq.1 pq.2).mp hterminal
    have hpX : pq.1 ∈ X := by
      simpa only [hsource i, TrackD.poolPts, Finset.singleton_biUnion] using hp
    have hqY : pq.2 ∈ Y := by
      simpa only [htarget i, TrackD.poolPts, Finset.singleton_biUnion] using hq
    exact Finset.mem_product.mpr ⟨hpX, hqY⟩
  have hgraph' : (1 / 8 : ℝ) * (X.card : ℝ) * Y.card ≤ Γ.card := by
    simpa only [Finset.card_image_of_injective _ profile_toC_injective] using hgraph_i
  obtain ⟨p, hpX, hrowDense⟩ :=
    exists_dense_physical_graph_row X Y Γ hΓ hX hY (1 / 8) hρ hgraph'
  let Q := Y.filter (fun q => (p, q) ∈ Γ)
  have hQ : Q.Nonempty := Finset.card_pos.mp (by
    exact_mod_cast (mul_pos hρ hYpos).trans_le hrowDense)
  have hedges : ∀ q ∈ Q, (p, q) ∈ profileBatchGraph H i :=
    fun q hq => (Finset.mem_filter.mp hq).2
  have hrowDenseC : (1 / 8 : ℝ) *
      (((S.sequence.target i).pts.image TrackD.toC).card : ℝ) ≤ Q.card := by
    simpa only [Finset.card_image_of_injective _ profile_toC_injective] using hrowDense
  obtain ⟨hpP, hrow, hcovered⟩ := profile_batch_row_facts T S hsource htarget H
    i p Q hQ hedges (1 / 8) hrowDenseC
  let x := TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ
  let L : ℕ := ⌊x⌋₊
  have hlower := hrank_i (TrackD.toC p) Q hrow
  have hupper := covered_row_direction_rank_upper (F.family i p)
    (F.directional i p hpP) p Q hcovered L
  have hfloor : (L : ℝ) ≤ x := Nat.floor_le (by dsimp [x]; linarith)
  have hLp : (L + 1 : ℝ) ≤ x + 1 := by linarith
  have hxp : 0 ≤ x + 1 := by dsimp [x]; linarith
  have hdegreeQ : 0 ≤ ProjectiveFamily.degree (F.family i p) := by
    unfold ProjectiveFamily.degree
    exact Finset.sum_nonneg (fun V _ => projective_degree_nonneg V)
  have hdegreeR : 0 ≤ (ProjectiveFamily.degree (F.family i p) : ℝ) := by
    exact_mod_cast hdegreeQ
  have hcontradiction : (rowDirectionRank (TrackD.toC p) Q L : ℝ) <
      profileDirectionRankTarget S i τ * Real.exp (c * (S.sequence.target i).width) := by
    calc
      _ ≤ (ProjectiveFamily.degree (F.family i p) : ℝ) * (L + 1 : ℝ) := hupper
      _ ≤ (ProjectiveFamily.degree (F.family i p) : ℝ) * (x + 1) :=
        mul_le_mul_of_nonneg_left hLp hdegreeR
      _ ≤ (F.delta i * regime.N i / regime.A i) * (x + 1) :=
        mul_le_mul_of_nonneg_right (F.degree i p hpP) hxp
      _ < _ := by simpa only [one_mul, x] using hdominates_i
  exact (not_lt_of_ge hlower) hcontradiction

/-- sc:separated.final-curve-reduction: wider centers and every nonfinal
terminal cluster are impossible. The remaining orientation is narrower centers,
with a genuine final one-dimensional open plateau and unchanged physical roles. -/
theorem separated_profile_forces_narrow_final_curve {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (S : LimitingSeparatedProfile regime)
    (hsource : ∀ i, T.sources i = {S.sequence.source i})
    (htarget : ∀ i, T.targets i = {S.sequence.target i}) :
    Tendsto (fun i => (S.sequence.source i).width / (S.sequence.target i).width)
      atTop (𝓝 0) ∧
    S.b ⟨(d - 1) - 1, by have := regime.dimension_ge_three; omega⟩ <
      S.b ⟨d - 1, by have := regime.dimension_ge_three; omega⟩ := by
  classical
  letI : Fintype (ProfilePlateau S) := by
    unfold ProfilePlateau
    infer_instance
  obtain ⟨c, ε, kind, hc, hε, hallowed, hmargin⟩ := separated_direction_rank_margin S
  obtain ⟨H⟩ := selected_profile_depth_batch T S hsource htarget
    (id : ProfilePlateau S → ProfilePlateau S) kind (fun _ => ε)
    (fun _ => hε) hallowed
  obtain ⟨u, hu⟩ := exists_final_open_plateau S
  have hnot : ¬ StrictPlateauEligible S u := by
    intro heligible
    obtain ⟨τ, hleft, hright, hgap⟩ := exists_final_testing_time S u hu c hc
    have hrank := hmargin (ProfilePlateau S) id (fun v => ⟨v, rfl⟩) H u
      heligible τ ⟨hleft, hright⟩
    apply strict_separated_endpoint_contradiction T S hsource htarget H c τ hc
      (by simpa only [hu] using hright) hgap hrank
  have hwide : ¬ Tendsto (fun i => (S.sequence.target i).width /
      (S.sequence.source i).width) atTop (𝓝 0) := fun h => hnot (Or.inr h)
  have hnarrow := S.sequence.separated.resolve_right hwide
  have hindex : u.val.val = d - 1 := by
    have hnonfinal : ¬ u.val.val + 1 < d := fun h => hnot (Or.inl h)
    have := u.val.isLt
    omega
  have hfin : u.val = (⟨d - 1, by have := regime.dimension_ge_three; omega⟩ : Fin d) :=
    Fin.ext hindex
  refine ⟨hnarrow, ?_⟩
  simpa only [hfin] using u.property.2

end
end DistinctDistances.SparseCones
