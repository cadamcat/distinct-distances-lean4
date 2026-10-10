import DistinctDistances.TrackE.CommonEndpointInputs

/-! Explicit exponent margins in the common endpoint, sparse-cones.tex:323–338. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- The two endpoint margins and sigma continuity give a literal lower
bound, with the complete loss 2d(last-τ)+θ kept in the exponent. -/
theorem common_rank_target_lower {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} (M : CommonPoolProfile T)
    (i : ℕ) (c θ τ : ℝ) (hτ : τ ≤ commonLastTime M)
    (hfirst : Real.exp (c * M.s i) *
      TrackD.testDeg (regime.B i) (M.s i) (commonLastTime M) ≤ regime.A i)
    (hpair : Real.exp (c * M.s i) *
      (TrackD.cutScale (regime.B i) (M.s i) M.b
        ⟨0, by have := regime.dimension_ge_three; omega⟩ *
       TrackD.cutScale (regime.B i) (M.s i) M.b
        ⟨1, by have := regime.dimension_ge_three; omega⟩) ≤ regime.A i) :
    regime.N i ^ 2 * TrackD.testDeg (regime.B i) (M.s i) τ / regime.A i *
      Real.exp ((c - 2 * (d : ℝ) * (commonLastTime M - τ) - θ) * M.s i) ≤
        commonRankTarget M i τ * Real.exp (-θ * M.s i) := by
  have hA : 0 < regime.A i := regime.A_pos i
  have hN : 0 < regime.N i := regime.N_pos i
  let g : ℝ := (d : ℝ) * (commonLastTime M - τ) * M.s i
  let σ : ℝ := TrackD.sigma (regime.B i) (M.s i) M.b τ
  let x : ℝ := TrackD.testDeg (regime.B i) (M.s i) τ
  let D : ℝ :=
    TrackD.cutScale (regime.B i) (M.s i) M.b
      ⟨0, by have := regime.dimension_ge_three; omega⟩ *
    TrackD.cutScale (regime.B i) (M.s i) M.b
      ⟨1, by have := regime.dimension_ge_three; omega⟩
  have hx : 0 < x := TrackD.RankCore.testDeg_pos (regime.B_pos i) _ _
  have hD : 0 < D := mul_pos
    (TrackD.RankCore.testDeg_pos (regime.B_pos i) _ _)
    (TrackD.RankCore.testDeg_pos (regime.B_pos i) _ _)
  have hσ : 0 ≤ σ := TrackD.RankCore.sigma_nonneg (regime.B_pos i).le _ _ _
  have hsig := TrackD.RankCore.sigma_lipschitz (regime.B_pos i).le
    (M.width_pos i).le hτ M.b
  rw [common_profile_sigma_last M i] at hsig
  change regime.N i ≤ σ * Real.exp g at hsig
  have hsigma : regime.N i * Real.exp (-g) ≤ σ := by
    calc
      _ ≤ (σ * Real.exp g) * Real.exp (-g) :=
        mul_le_mul_of_nonneg_right hsig (Real.exp_nonneg _)
      _ = σ := by
        rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  have hsquare : regime.N i ^ 2 * Real.exp (-2 * g) ≤ σ ^ 2 := by
    calc
      _ = (regime.N i * Real.exp (-g)) ^ 2 := by
        rw [mul_pow, pow_two (Real.exp (-g)), ← Real.exp_add,
          show -g + -g = -2 * g by ring]
      _ ≤ σ ^ 2 := pow_le_pow_left₀ (by positivity) hsigma _
  have hfirstτ : Real.exp (c * M.s i) * x ≤ regime.A i :=
    (mul_le_mul_of_nonneg_left
      (TrackD.RankCore.testDeg_mono (regime.B_pos i).le (M.width_pos i).le hτ)
      (Real.exp_nonneg _)).trans hfirst
  have hmin : Real.exp (c * M.s i) * x / regime.A i ≤ min 1 (x / D) := by
    refine le_min ((div_le_one₀ (regime.A_pos i)).mpr hfirstτ) ?_
    apply (div_le_div_iff₀ (regime.A_pos i) hD).mpr
    calc
      (Real.exp (c * M.s i) * x) * D = x * (Real.exp (c * M.s i) * D) := by ring
      _ ≤ x * regime.A i := mul_le_mul_of_nonneg_left hpair hx.le
  have heq :
      regime.N i ^ 2 * x / regime.A i *
        Real.exp ((c - 2 * (d : ℝ) * (commonLastTime M - τ) - θ) * M.s i) =
      (regime.N i ^ 2 * Real.exp (-2 * g)) *
        (Real.exp (c * M.s i) * x / regime.A i) * Real.exp (-θ * M.s i) := by
    rw [show (c - 2 * (d : ℝ) * (commonLastTime M - τ) - θ) * M.s i =
      (-2 * g + c * M.s i) + (-θ * M.s i) by dsimp [g]; ring,
      Real.exp_add, Real.exp_add]
    ring
  change regime.N i ^ 2 * x / regime.A i *
      Real.exp ((c - 2 * (d : ℝ) * (commonLastTime M - τ) - θ) * M.s i) ≤
    σ ^ 2 * min 1 (x / D) * Real.exp (-θ * M.s i)
  rw [heq]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul hsquare hmin (by positivity) (sq_nonneg σ)) (Real.exp_nonneg _)

/-- A fixed positive residual exponent absorbs every fixed upper-rank
constant. No rate comparing delta with a logarithmic error is an input. -/
theorem common_rank_target_dominates_cones {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} (M : CommonPoolProfile T)
    (C c θ τ : ℝ) (hC : 0 < C) (hτ₀ : 0 ≤ τ)
    (hτ : τ < commonLastTime M)
    (hgap : 2 * (d : ℝ) * (commonLastTime M - τ) + θ < c)
    (hfirst : ∀ᶠ i in atTop, Real.exp (c * M.s i) *
      TrackD.testDeg (regime.B i) (M.s i) (commonLastTime M) ≤ regime.A i)
    (hpair : ∀ᶠ i in atTop, Real.exp (c * M.s i) *
      (TrackD.cutScale (regime.B i) (M.s i) M.b
        ⟨0, by have := regime.dimension_ge_three; omega⟩ *
       TrackD.cutScale (regime.B i) (M.s i) M.b
        ⟨1, by have := regime.dimension_ge_three; omega⟩) ≤ regime.A i) :
    ∀ᶠ i in atTop,
      C * F.delta i * regime.N i ^ 2 / regime.A i *
        (TrackD.testDeg (regime.B i) (M.s i) τ + 1) <
          commonRankTarget M i τ * Real.exp (-θ * M.s i) := by
  let q : ℝ := c - 2 * (d : ℝ) * (commonLastTime M - τ) - θ
  have hq : 0 < q := by dsimp [q]; linarith
  have hgrows : Tendsto (fun i => q * M.s i) atTop atTop :=
    M.width_grows.const_mul_atTop hq
  have hlarge := (Real.tendsto_exp_atTop.comp hgrows).eventually
    (eventually_gt_atTop (2 * C))
  have hdelta := F.delta_tendsto.eventually (Iio_mem_nhds zero_lt_one)
  filter_upwards [hfirst, hpair, hlarge, hdelta,
    regime.B_tendsto.eventually (eventually_ge_atTop (1 : ℝ))]
    with i hfirsti hpairi hlargei hδ hB
  have hδpos : 0 < F.delta i := F.delta_pos i
  have hA : 0 < regime.A i := regime.A_pos i
  have hN : 0 < regime.N i := regime.N_pos i
  let x : ℝ := TrackD.testDeg (regime.B i) (M.s i) τ
  have hx : 0 < x := TrackD.RankCore.testDeg_pos (regime.B_pos i) _ _
  have hxone : 1 ≤ x := by
    have he : 1 ≤ Real.exp (τ * M.s i) :=
      Real.one_le_exp_iff.mpr (mul_nonneg hτ₀ (M.width_pos i).le)
    exact one_le_mul_of_one_le_of_one_le hB he
  have hscale : 0 < regime.N i ^ 2 * x / regime.A i := by
    exact div_pos (mul_pos (sq_pos_of_pos (regime.N_pos i)) hx) (regime.A_pos i)
  have hδC : 2 * C * F.delta i ≤ 2 * C := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hδ.le
      (show 0 ≤ 2 * C by positivity)
  have hlow := common_rank_target_lower M i c θ τ hτ.le hfirsti hpairi
  calc
    C * F.delta i * regime.N i ^ 2 / regime.A i * (x + 1) ≤
        C * F.delta i * regime.N i ^ 2 / regime.A i * (2 * x) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = (regime.N i ^ 2 * x / regime.A i) * (2 * C * F.delta i) := by ring
    _ < (regime.N i ^ 2 * x / regime.A i) * Real.exp (q * M.s i) :=
      mul_lt_mul_of_pos_left (hδC.trans_lt hlargei) hscale
    _ ≤ commonRankTarget M i τ * Real.exp (-θ * M.s i) := hlow

end
end DistinctDistances.SparseCones
