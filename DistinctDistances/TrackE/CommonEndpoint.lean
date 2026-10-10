import DistinctDistances.TrackE.CommonEndpointNumerics
import DistinctDistances.TrackE.CommonRankProof

/-! The common strict endpoint keeps the selected orientation, physical
pools, and terminal assignment, sparse-cones.tex:318–338. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- Outside the outermost endpoint b_last=1, both literal rank ratios
have one fixed positive exponent margin before chart or graph selection. -/
theorem common_endpoint_margins {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} (M : CommonPoolProfile T)
    (hstrict : (∀ i, 2 * M.s i ≤ Real.log (regime.B i)) ∨ commonLastTime M < 1) :
    ∃ c : ℝ, 0 < c ∧
      (∀ i, Real.exp (c * M.s i) *
        TrackD.testDeg (regime.B i) (M.s i) (commonLastTime M) ≤ regime.A i) ∧
      (∀ i, Real.exp (c * M.s i) *
        (TrackD.cutScale (regime.B i) (M.s i) M.b
          ⟨0, by have := regime.dimension_ge_three; omega⟩ *
         TrackD.cutScale (regime.B i) (M.s i) M.b
          ⟨1, by have := regime.dimension_ge_three; omega⟩) ≤ regime.A i) := by
  obtain ⟨a, ha, _, _, hpair⟩ := M.balance
  obtain ⟨c₀, hc₀, hwidth⟩ : ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ i, (c₀ + commonLastTime M) * M.s i ≤ Real.log (regime.B i) := by
    rcases hstrict with hhalf | hlast
    · refine ⟨1, by norm_num, ?_⟩
      intro i
      have hlastle : commonLastTime M ≤ 1 := common_profile_time_upper M _
      exact (mul_le_mul_of_nonneg_right (by linarith : 1 + commonLastTime M ≤ 2)
        (M.width_pos i).le).trans (hhalf i)
    · refine ⟨1 - commonLastTime M, by linarith, ?_⟩
      intro i
      simpa only [sub_add_cancel, one_mul] using common_pool_width_le_logB M i
  let c : ℝ := min a c₀
  have hc : 0 < c := lt_min ha hc₀
  have hca : c ≤ a := min_le_left _ _
  have hcc : c ≤ c₀ := min_le_right _ _
  refine ⟨c, hc, ?_, ?_⟩
  · intro i
    have htime : (c + commonLastTime M) * M.s i ≤ Real.log (regime.B i) :=
      (mul_le_mul_of_nonneg_right
        (show c + commonLastTime M ≤ c₀ + commonLastTime M by linarith)
        (M.width_pos i).le).trans
        (hwidth i)
    have hexp : Real.exp ((c + commonLastTime M) * M.s i) ≤ regime.B i := by
      simpa only [Real.exp_log (regime.B_pos i)] using Real.exp_le_exp.mpr htime
    calc
      _ = regime.B i * Real.exp ((c + commonLastTime M) * M.s i) := by
        rw [show (c + commonLastTime M) * M.s i =
          c * M.s i + commonLastTime M * M.s i by ring, Real.exp_add]
        unfold TrackD.testDeg
        ring
      _ ≤ regime.B i * regime.B i := mul_le_mul_of_nonneg_left hexp (regime.B_pos i).le
      _ = regime.A i := by rw [regime.A_eq_B_sq i]; ring
  · intro i
    have hsum : c + M.b ⟨0, by have := regime.dimension_ge_three; omega⟩ +
        M.b ⟨1, by have := regime.dimension_ge_three; omega⟩ ≤ 0 := by linarith
    have hexp : Real.exp ((c + M.b ⟨0, by have := regime.dimension_ge_three; omega⟩ +
        M.b ⟨1, by have := regime.dimension_ge_three; omega⟩) * M.s i) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg hsum (M.width_pos i).le)
    calc
      _ = regime.B i ^ 2 * Real.exp ((c +
          M.b ⟨0, by have := regime.dimension_ge_three; omega⟩ +
          M.b ⟨1, by have := regime.dimension_ge_three; omega⟩) * M.s i) := by
        rw [show (c + M.b ⟨0, by have := regime.dimension_ge_three; omega⟩ +
          M.b ⟨1, by have := regime.dimension_ge_three; omega⟩) * M.s i =
          (c * M.s i + M.b ⟨0, by have := regime.dimension_ge_three; omega⟩ * M.s i) +
            M.b ⟨1, by have := regime.dimension_ge_three; omega⟩ * M.s i by ring,
          Real.exp_add, Real.exp_add]
        unfold TrackD.cutScale TrackD.testDeg
        ring
      _ ≤ regime.B i ^ 2 * 1 := mul_le_mul_of_nonneg_left hexp (sq_nonneg _)
      _ = regime.A i := by rw [regime.A_eq_B_sq i, mul_one]

/-- sc:u-common-contra: specialize at the actual centers of a dense
covered chart graph and contradict the common lower rank. -/
theorem strict_common_profile_contradiction {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (M : CommonPoolProfile T)
    (hstrict : (∀ i, 2 * M.s i ≤ Real.log (regime.B i)) ∨ commonLastTime M < 1) :
    False := by
  obtain ⟨c, hc, hfirst, hpair⟩ := common_endpoint_margins M hstrict
  obtain ⟨τ, hτ₀, hτ, hcut, hgap⟩ := exists_common_endpoint_test M c hc
  let θ : ℝ := c / 4
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hgap' : 2 * (d : ℝ) * (commonLastTime M - τ) + θ < c := by
    dsimp [θ]
    linarith
  have hd : 0 < (d : ℝ) := by
    exact_mod_cast (show 0 < d by have := regime.dimension_ge_three; omega)
  let ρ : ℝ := 1 / (4 * (d : ℝ))
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hrank := common_label_rank_proved T M τ (by linarith) hτ hcut θ hθ ρ hρ
  have hdom := common_rank_target_dominates_cones M 1 c θ τ (by norm_num) hτ₀.le hτ
    hgap' (Eventually.of_forall hfirst) (Eventually.of_forall hpair)
  obtain ⟨i, hdense, hranki, hdomi⟩ :=
    ((selected_terminal_graph_dense T).and (hrank.and hdom)).exists
  let Γ := terminalSelectedGraph T i
  have hneq : ∀ pq ∈ Γ, pq.1 ≠ pq.2 := by
    intro pq hpq
    exact ((mem_terminalSelectedGraph T i pq.1 pq.2).mp hpq).2.2.1.1
  obtain ⟨i₀, Γ', hsub, hchart, hcard⟩ := exists_dense_common_chart
    (by have := regime.dimension_ge_three; omega) Γ hneq
  have hpool : Γ' ⊆ TrackD.poolPts (T.sources i) ×ˢ TrackD.poolPts (T.targets i) := by
    intro pq hpq
    obtain ⟨hp, hq, _, _⟩ := (mem_terminalSelectedGraph T i pq.1 pq.2).mp (hsub hpq)
    exact Finset.mem_product.mpr ⟨hp, hq⟩
  have hchartdense : ρ * ((TrackD.poolPts (T.sources i)).card : ℝ) *
      (TrackD.poolPts (T.targets i)).card ≤ Γ'.card := by
    calc
      _ = ((1 / 4 : ℝ) * (TrackD.poolPts (T.sources i)).card *
          (TrackD.poolPts (T.targets i)).card) / (d : ℝ) := by dsimp [ρ]; ring
      _ ≤ (Γ.card : ℝ) / (d : ℝ) := div_le_div_of_nonneg_right hdense hd.le
      _ ≤ Γ'.card := hcard
  have hlower := hranki i₀ Γ' hpool hchart hchartdense
  have hP : ∀ pq ∈ Γ', pq.1 ∈ regime.P i := by
    intro pq hpq
    have hp := ((mem_terminalSelectedGraph T i pq.1 pq.2).mp (hsub hpq)).1
    change pq.1 ∈ (T.sources i).biUnion TrackD.Piece.pts at hp
    obtain ⟨X, hX, hpX⟩ := Finset.mem_biUnion.mp hp
    exact ((T.certificate i).good.pieces_good X
      ((T.certificate i).sources_subset hX)).1.subset hpX
  have hcovered : ∀ pq ∈ Γ', TrackD.DirIn (F.family i pq.1) pq.1 pq.2 := by
    intro pq hpq
    exact ((mem_terminalSelectedGraph T i pq.1 pq.2).mp (hsub hpq)).2.2.1.2.1
  have hδpos : 0 < F.delta i := F.delta_pos i
  have hA : 0 < regime.A i := regime.A_pos i
  have hN : 0 < regime.N i := regime.N_pos i
  let x : ℝ := TrackD.testDeg (regime.B i) (M.s i) τ
  let L : ℕ := ⌊x⌋₊
  have hx : 0 < x := TrackD.RankCore.testDeg_pos (regime.B_pos i) _ _
  have hupper := covered_common_label_rank_upper (regime.P i) (F.family i)
    (F.directional i) (F.delta i * regime.N i / regime.A i) (by positivity)
    (F.degree i) i₀ Γ' hP hchart hcovered L
  have hfloor : (L : ℝ) ≤ x := Nat.floor_le hx.le
  have hupper' : (commonLabelRank i₀ Γ' L : ℝ) <
      commonRankTarget M i τ * Real.exp (-θ * M.s i) := by
    calc
      _ ≤ regime.N i * (F.delta i * regime.N i / regime.A i) * (L + 1 : ℝ) := hupper
      _ ≤ regime.N i * (F.delta i * regime.N i / regime.A i) * (x + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 1 * F.delta i * regime.N i ^ 2 / regime.A i * (x + 1) := by ring
      _ < _ := hdomi
  exact (not_lt_of_ge hlower) hupper'

/-- The original common singleton branch has a strict margin by dyadicity. -/
theorem common_profile_contradiction {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (M : CommonPoolProfile T)
    (hcommon : ∀ i, T.IsCommon i) : False := by
  exact strict_common_profile_contradiction T M
    (Or.inl (common_singleton_width_half T M hcommon))

/-- In the remaining outer branch, the last limiting cut is exactly one. -/
theorem outer_profile_last_eq_one {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (M : CommonPoolProfile T) :
    commonLastTime M = 1 := by
  have hle : commonLastTime M ≤ 1 :=
    common_profile_time_upper M ⟨d - 1, by have := regime.dimension_ge_three; omega⟩
  have hge : 1 ≤ commonLastTime M := by
    by_contra hlt
    have hlt' : commonLastTime M < 1 := lt_of_not_ge hlt
    exact strict_common_profile_contradiction T M (Or.inr hlt')
  exact le_antisymm hle hge

end
end DistinctDistances.SparseCones
