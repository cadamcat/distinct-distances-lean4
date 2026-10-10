import DistinctDistances.TrackE.DepthDataCore

/-! Lemma-level inputs for `G5.narrow` (`depth.tex:170–181`). These statements
split the narrow case into lemma-sized steps. -/

namespace DistinctDistances.SparseCones

open Filter
open scoped Topology BigOperators Classical

noncomputable section

/-- All source cuts, including the last cut. -/
def sourceEquations {d : ℕ} {regime : Regime d}
    (S : LimitingSeparatedProfile regime) (i : ℕ) : Finset (Poly d) :=
  Finset.univ.image (S.sequence.source i).path.cut

/-- One integer bound for every source equation. -/
def sourceIsolationDegree {d : ℕ} {regime : Regime d}
    (S : LimitingSeparatedProfile regime) (i : ℕ) : ℕ :=
  max 1 ⌈regime.B i * Real.exp (3 * (S.sequence.source i).width)⌉₊

/-- `G5.narrow.isolation`: properness of all d cuts isolates the actual
source sample, regardless of larger components away from the sample. -/
theorem source_path_isolation {d : ℕ} {regime : Regime d}
    (S : LimitingSeparatedProfile regime) :
    ∀ i, 1 ≤ sourceIsolationDegree S i ∧
      (∀ f ∈ sourceEquations S i, f.totalDegree ≤ sourceIsolationDegree S i) ∧
      TrackA.IsolatedPoints (sourceEquations S i : Set (Poly d))
        ((S.sequence.source i).pts.image TrackD.toC) := by
  intro i
  have hgood := (S.sequence.base_good i).1
  have hw_pos := (S.sequence.width_pos i).1
  have hB_pos := regime.B_pos i
  refine ⟨le_max_left 1 _, ?_, ?_⟩
  · intro f hf
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hf
    have hdeg := hgood.degree t
    have htime := (hgood.time_range t).2
    have hscale : TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.source i).width
        ((S.sequence.source i).path.time t + 1) ≤
        regime.B i * Real.exp (3 * (S.sequence.source i).width) := by
      change regime.B i * Real.exp (((S.sequence.source i).path.time t + 1) *
        (S.sequence.source i).width) ≤ regime.B i * Real.exp (3 * (S.sequence.source i).width)
      apply mul_le_mul_of_nonneg_left _ hB_pos.le
      apply Real.exp_le_exp.mpr
      nlinarith [htime, hw_pos]
    have htotal : ((S.sequence.source i).path.cut t).totalDegree ≤
        ⌈regime.B i * Real.exp (3 * (S.sequence.source i).width)⌉₊ := by
      exact_mod_cast (hdeg.trans hscale).trans (Nat.le_ceil _)
    exact htotal.trans (le_max_right 1 _)
  · intro p hp
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
    let top : AffineVariety d := AffineVariety.whole
    have hsys0 : (S.sequence.source i).path.system 0 = ⊥ := by simp [TrackD.CutPath.system]
    have htopIdeal : top.ideal = ⊥ := by
      dsimp [top, AffineVariety.whole, AffineVariety.ofIdeal]
      exact Ideal.radical_bot_of_isReduced
    have htopCarrier : (S.sequence.source i).path.IsCarrier 0 top := by
      change top.ideal ∈ ((S.sequence.source i).path.system 0).minimalPrimes
      rw [hsys0, htopIdeal]
      rw [Ideal.minimalPrimes_eq_subsingleton_self]
      simp
    have htopPoint : TrackD.toC x ∈ top := by
      change TrackD.toC x ∈ top.points
      simp [top, AffineVariety.whole, AffineVariety.ofIdeal, AffineVariety.points]
    have hZ : top ∈ (S.sequence.source i).path.localCarriers 0 (TrackD.toC x) :=
      ⟨htopCarrier, htopPoint⟩
    have hmin := TrackD.dprofiles2_final_point_minimal (regime.P i) (S.sequence.source i)
      1 1 1 hgood x hx 0 (by omega) top hZ
    rw [htopIdeal, bot_sup_eq] at hmin
    have heq_range : Set.range (TrackD.dprofiles2TailCut (j := 0) (S.sequence.source i).path (by omega)) =
        (sourceEquations S i : Set (Poly d)) := by
      ext f
      simp only [Set.mem_range, sourceEquations, Finset.coe_image, Finset.coe_univ,
        Set.mem_image, Set.mem_univ, true_and]
      constructor
      · rintro ⟨t, rfl⟩
        refine ⟨⟨t.val, by omega⟩, ?_⟩
        dsimp [TrackD.dprofiles2TailCut]
        congr 1
        ext
        simp
      · rintro ⟨t, rfl⟩
        refine ⟨⟨t.val, by omega⟩, ?_⟩
        dsimp [TrackD.dprofiles2TailCut]
        congr 1
        ext
        simp
    rw [heq_range] at hmin
    exact hmin

/-- `G5.narrow.rounding`: the source width is negligible on the target
scale, and rounding its degree bound costs only a constant factor. -/
theorem source_isolation_expUpper {d : ℕ} {regime : Regime d}
    (S : LimitingSeparatedProfile regime)
    (hnarrow : Tendsto
      (fun i => (S.sequence.source i).width / (S.sequence.target i).width)
      atTop (𝓝 0)) :
    Framework.ExpUpper (fun _ => Unit)
      (fun i _ => (sourceIsolationDegree S i : ℝ)) (fun i _ => regime.B i)
      (fun i => (S.sequence.target i).width) := by
  intro ε hε
  have hinv : Tendsto (fun i => ((S.sequence.target i).width)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp S.sequence.target_grows
  have hlog2_div : Tendsto (fun i => Real.log 2 / (S.sequence.target i).width) atTop (𝓝 0) := by
    have hmul := hinv.const_mul (Real.log 2)
    simp only [mul_zero] at hmul
    have heq : (fun i => Real.log 2 / (S.sequence.target i).width) =
        (fun i => Real.log 2 * ((S.sequence.target i).width)⁻¹) := by
      ext i; ring
    rw [heq]
    exact hmul
  have hratio : Tendsto (fun i => 3 * ((S.sequence.source i).width / (S.sequence.target i).width))
      atTop (𝓝 0) := by
    have hmul := hnarrow.const_mul 3
    simpa only [mul_zero] using hmul
  have hsum_tendsto : Tendsto (fun i =>
      3 * ((S.sequence.source i).width / (S.sequence.target i).width) +
        Real.log 2 / (S.sequence.target i).width) atTop (𝓝 0) := by
    have hsum := hratio.add hlog2_div
    simpa only [add_zero] using hsum
  have hsmall := hsum_tendsto.eventually (gt_mem_nhds hε)
  have hB_ge_one : ∀ᶠ i in atTop, 1 ≤ regime.B i :=
    regime.B_tendsto.eventually_ge_atTop 1
  filter_upwards [hsmall, hB_ge_one] with i hi hB u
  have hw_pos : 0 < (S.sequence.target i).width := (S.sequence.width_pos i).2
  have hv_pos : 0 < (S.sequence.source i).width := (S.sequence.width_pos i).1
  have hB_pos : 0 < regime.B i := regime.B_pos i
  have hX_pos : 1 ≤ regime.B i * Real.exp (3 * (S.sequence.source i).width) := by
    have hexp : 1 ≤ Real.exp (3 * (S.sequence.source i).width) := by
      apply Real.one_le_exp_iff.mpr
      nlinarith [hv_pos]
    nlinarith [hB, hexp]
  have hceil : (⌈regime.B i * Real.exp (3 * (S.sequence.source i).width)⌉₊ : ℝ) ≤
      2 * (regime.B i * Real.exp (3 * (S.sequence.source i).width)) := by
    have hle := Nat.ceil_lt_add_one (by linarith [hX_pos] : 0 ≤ regime.B i * Real.exp (3 * (S.sequence.source i).width))
    linarith [hX_pos]
  have hdeg_le : (sourceIsolationDegree S i : ℝ) ≤
      2 * (regime.B i * Real.exp (3 * (S.sequence.source i).width)) := by
    dsimp [sourceIsolationDegree]
    rw [Nat.cast_max, Nat.cast_one]
    have h1 : (1 : ℝ) ≤ 2 * (regime.B i * Real.exp (3 * (S.sequence.source i).width)) := by
      linarith [hX_pos]
    exact max_le h1 hceil
  have hsum_le : 3 * (S.sequence.source i).width + Real.log 2 ≤
      ε * (S.sequence.target i).width := by
    have hmult := mul_lt_mul_of_pos_right hi hw_pos
    have hcancel : (3 * ((S.sequence.source i).width / (S.sequence.target i).width) +
        Real.log 2 / (S.sequence.target i).width) * (S.sequence.target i).width =
        3 * (S.sequence.source i).width + Real.log 2 := by
      field_simp
    rw [hcancel] at hmult
    exact hmult.le
  calc
    (sourceIsolationDegree S i : ℝ) ≤ 2 * (regime.B i * Real.exp (3 * (S.sequence.source i).width)) :=
      hdeg_le
    _ = regime.B i * (2 * Real.exp (3 * (S.sequence.source i).width)) := by ring
    _ = regime.B i * Real.exp (Real.log 2 + 3 * (S.sequence.source i).width) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ ≤ regime.B i * Real.exp (ε * (S.sequence.target i).width) := by
      apply mul_le_mul_of_nonneg_left _ hB_pos.le
      apply Real.exp_le_exp.mpr
      linarith [hsum_le]

end

end DistinctDistances.SparseCones
