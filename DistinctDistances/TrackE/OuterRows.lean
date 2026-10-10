import DistinctDistances.TrackE.OuterRowsData
import DistinctDistances.TrackE.CommonRankProof
import DistinctDistances.TrackE.OuterRowsSupport

/-! Sparse rows at the outermost endpoint, sparse-cones.tex:340–651. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- sc:u-outer-lift, row form (sparse-cones.tex:340–651). At the outermost
endpoint (`s = log B`, `b_last = 1`), after deleting a negligible part of the
selected covered graph, every row has a negligible number of partners: outer
regularity (426–561) and the discarded components (564–578) give the
deletion, the algebraic lift with its root and degree count and the physical
curve bound give the row bound `C E M = o(n)` (580–651); for `k = 1` the
rows are empty by the global terminal deletion. -/
theorem outer_rows_sparse {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (M : CommonPoolProfile T)
    (houter : ∀ i, T.IsOuter i) (hs : ∀ i, M.s i = Real.log (regime.B i)) :
    ∀ ρ : ℝ, 0 < ρ → ∀ᶠ i in atTop,
      ∃ Γ : Finset (RPoint d × RPoint d), Γ ⊆ outerSelectedGraph T i ∧
        ((outerSelectedGraph T i \ Γ).card : ℝ) ≤
          ρ * ((TrackD.poolPts (T.sources i)).card : ℝ) ^ 2 ∧
        ∀ p : RPoint d, ((Γ.filter (fun pq => pq.1 = p)).card : ℝ) ≤
          ρ * (TrackD.poolPts (T.sources i)).card := by
  intro ρ hρ
  have hd := regime.dimension_ge_three
  obtain ⟨k, j, hj, hkj, hk1, hkd, hβ, htop⟩ := outer_final_plateau_exists M
  have hk : 1 ≤ k ∧ k + 1 < d := ⟨hk1, hkd⟩
  have hβlow : -1 ≤ M.b ⟨j, hj⟩ := common_profile_time_lower M _
  have hj1 : j + 1 < d := by omega
  -- the physical sequence on the final plateau
  have hplat : TrackD.OnPlateau M.b (j + 1) ((1 - M.b ⟨j, hj⟩) / 4)
      ((M.b ⟨j, hj⟩ + 1) / 2) := by
    intro a
    constructor
    · intro ha
      have hle : M.b a ≤ M.b ⟨j, hj⟩ := M.sorted (show a.val ≤ j by omega)
      linarith
    · intro ha
      rw [htop a (by omega)]
      linarith
  obtain ⟨W⟩ := selected_common_physical_retention T M (j + 1) hj1 _ _ (by linarith)
    (by linarith) hplat
  -- the envelope time and tolerance
  obtain ⟨cb, hcb, _, _, hb01⟩ := M.balance
  set m : ℝ := max (M.b ⟨j, hj⟩) (1 + M.b ⟨0, by omega⟩ + M.b ⟨1, by omega⟩) with hm
  have hmβ : M.b ⟨j, hj⟩ ≤ m := le_max_left _ _
  have hmb : 1 + M.b ⟨0, by omega⟩ + M.b ⟨1, by omega⟩ ≤ m := le_max_right _ _
  have hm1 : m < 1 := max_lt hβ (by linarith)
  set t₀ : ℝ := (m + 1) / 2 with ht₀
  set ε : ℝ := (1 - m) / 16 with hεdef
  have hε : 0 < ε := by linarith
  have ht₀1 : t₀ < 1 := by linarith
  have ht₀β : M.b ⟨j, hj⟩ < t₀ := by linarith
  have ht₀b : 1 + M.b ⟨0, by omega⟩ + M.b ⟨1, by omega⟩ < t₀ := by linarith
  have hεβ : 4 * ε < t₀ - M.b ⟨j, hj⟩ := by linarith
  have hεb : 4 * ε < t₀ - (1 + M.b ⟨0, by omega⟩ + M.b ⟨1, by omega⟩) := by linarith
  have hεt : 4 * ε < 1 - t₀ := by linarith
  -- the chart chain 187c → 189 → 190 → 191
  have h190 : ∀ i₀ : Fin d, ∃ c : ℝ, 0 < c ∧ ∀ ρ' : ℝ, 0 < ρ' → ∀ᶠ i in atTop,
      ∃ cert : OuterRegularityCert T M k i j i₀ (1 / 2) ε ρ'
        ((regime.B i) ^ (2 - c)) ((M.b ⟨j, hj⟩ + 1) / 2),
        cert.chart.W = W := fun i₀ =>
    outer_smooth_subfamily T M hs k j hj hkj hk houter htop i₀ (1 / 2) ε (by norm_num) (by norm_num) hε
      _ t₀ ht₀1 ht₀β hεt W (fun ρ'' hρ'' =>
        outer_envelope_larger_components_sparse T M houter hs k j hj hkj hk htop i₀
          (1 / 2) ε ρ'' (by norm_num) (by norm_num) hε hρ'' _ t₀ ht₀1 ht₀β ht₀b hεβ hεb W
          (outer_chart_restriction T M houter hs W k hk hkj htop (1 / 2) ε (by norm_num)
            (by norm_num) hε i₀ ρ'' hρ''))
  choose c hc h190' using h190
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  set ρ' : ℝ := ρ / (6 * d) with hρ'def
  have hρ' : 0 < ρ' := by positivity
  have hall := Filter.eventually_all.mpr (fun i₀ : Fin d =>
    outer_tangent_tests T M k j hkj hk i₀ (1 / 2) ε (fun i => regime.B i ^ (2 - c i₀)) _
      (by norm_num) _ (by linarith) hplat W (h190' i₀) ρ' hρ')
  -- numerics
  have hnum : ∀ᶠ i in atTop, ∀ i₀ : Fin d, regime.B i ^ (2 - c i₀) *
      regime.B i ^ selectionTolerance (T.precision i) ≤ ρ' / 2 * regime.A i :=
    Filter.eventually_all.mpr (fun i₀ =>
      outer_discard_numeric T (c i₀) (ρ' / 2) (hc i₀) (by positivity))
  have htolρ := (selection_tolerance_tendsto_zero T.precision T.precision_grows).eventually
    (Iic_mem_nhds (half_pos hρ))
  have hδ1 := F.delta_tendsto.eventually (Iic_mem_nhds (zero_lt_one' ℝ))
  obtain ⟨C0, hC0, hcurve⟩ := Bridges.curve_sample_bound d
  have hrownum := outer_row_numeric T houter C0 ρ hC0.le hρ
  filter_upwards [hall, hnum, htolρ, hδ1, hrownum] with i hi hnumi htoli hδi hrowi
  choose cert hWpin sys hP using hi
  have hPsub := outer_poolPts_subset_P T i
  set n : ℝ := ((TrackD.poolPts (T.sources i)).card : ℝ) with hn
  have hE : ∀ p ∈ TrackD.poolPts (T.sources i),
      ((ProjectiveFamily.degree (F.family i p) : ℚ) : ℝ) ≤
        F.delta i * regime.N i / regime.A i :=
    fun p hp => F.degree i p (hPsub.1 hp)
  have hsmall : ∀ i₀ : Fin d, F.delta i * regime.N i / regime.A i *
      regime.B i ^ (2 - c i₀) * outerLineCap T i ≤
        ρ' * ((cert i₀).chart.pool.S.card : ℝ) := by
    intro i₀
    have hcap : outerLineCap T i = regime.B i ^ selectionTolerance (T.precision i) := rfl
    rw [hcap, mul_assoc]
    exact outer_discard_arith (F.delta i) (regime.N i) (regime.A i) n _ _ ρ'
      (F.delta_pos i) hδi (regime.A_pos i) (regime.N_pos i) (houter i).2.2
      (cert i₀).chart.pool.hScard (hnumi i₀) hρ'
  have hE0 : 0 ≤ F.delta i * regime.N i / regime.A i := by
    have := F.delta_pos i
    have := regime.N_pos i
    have := regime.A_pos i
    positivity
  obtain ⟨Γ, hΓ, hdel, hrow⟩ := outer_rows_at_index T M k i j hk1 hρ'.le (houter i)
    (fun i₀ => regime.B i ^ (2 - c i₀)) cert sys (fun i₀ => (hP i₀).1) (fun i₀ => (hP i₀).2)
    (F.delta i * regime.N i / regime.A i) hE0 hE hsmall C0 hC0.le
    (fun Y hY => hcurve (regime.P i) Y hY)
  refine ⟨Γ, hΓ, ?_, ?_⟩
  · refine hdel.trans ?_
    have h1 : (d : ℝ) * (3 * ρ' * n ^ 2) = ρ / 2 * n ^ 2 := by
      rw [hρ'def]
      field_simp
      ring
    have hn0 : 0 ≤ n := Nat.cast_nonneg _
    have h2 : n * (selectionTolerance (T.precision i) * n) ≤ n * (ρ / 2 * n) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right htoli hn0) hn0
    nlinarith
  · intro p
    have hMeq : TrackD.cfgM (regime.P i) = regime.M i := by
      simp only [TrackD.cfgM, Regime.M]
      ring
    refine (hrow p).trans ?_
    rw [hMeq]
    exact hrowi

end
end DistinctDistances.SparseCones
