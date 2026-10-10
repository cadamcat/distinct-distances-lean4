import DistinctDistances.TrackE.DepthDataCore

/-! Lemma-level profile inputs for the first limiting cluster
(`depth.tex:145–168`, `profiles.tex:344–356`). -/

namespace DistinctDistances.SparseCones

open Filter
open scoped Topology BigOperators Classical

noncomputable section

/-- `G5.first-cut.pool`: an actual target piece forms a one-piece pool
around its limiting profile at every fixed positive precision. -/
theorem target_singleton_pool_good {d : ℕ} {regime : Regime d}
    (S : LimitingSeparatedProfile regime) (θ ξ ρ : ℝ)
    (hθ : 0 < θ) (hξ : 0 < ξ) (hρ : 0 < ρ) :
    ∀ᶠ i in atTop, TrackD.PoolGood (regime.P i) θ ξ 1 ρ
      {S.sequence.target i} (S.sequence.target i).width S.b := by
  have hclose : ∀ t : Fin d, ∀ᶠ i in atTop,
      |(S.sequence.target i).path.time t - S.b t| ≤ ρ := by
    intro t
    have hlim := S.target_limit t
    have hnhds : {x : ℝ | |x - S.b t| ≤ ρ} ∈ 𝓝 (S.b t) := by
      rw [Metric.mem_nhds_iff]
      refine ⟨ρ, hρ, fun y hy => ?_⟩
      rw [Metric.mem_ball, Real.dist_eq] at hy
      exact hy.le
    exact hlim hnhds
  have hall : ∀ᶠ i in atTop, ∀ t : Fin d,
      |(S.sequence.target i).path.time t - S.b t| ≤ ρ := by
    rw [eventually_all]
    exact hclose
  filter_upwards [S.sequence.good θ hθ ξ hξ 1 le_rfl, hall] with i hgood hclose_all
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro X hX
    have hX_eq : X = S.sequence.target i := Finset.mem_singleton.mp hX
    subst hX_eq
    exact hgood.2
  · intro X hX
    have hX_eq : X = S.sequence.target i := Finset.mem_singleton.mp hX
    subst hX_eq
    rfl
  · intro X hX t
    have hX_eq : X = S.sequence.target i := Finset.mem_singleton.mp hX
    subst hX_eq
    exact hclose_all t
  · simp only [Finset.card_singleton, Nat.cast_one]
    have hw : 0 < (S.sequence.target i).width := (S.sequence.width_pos i).2
    have hexp : 0 ≤ θ * (S.sequence.target i).width := by positivity
    exact Real.one_le_exp hexp
  · intro X hX Y hY hXY
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hX hY
    subst hX
    subst hY
    exact (hXY rfl).elim

/-- `G5.first-cut.test-degree`: every fixed limiting-profile test time
eventually has degree at least one, since s is o(log B). -/
theorem target_test_degree_one {d : ℕ} {regime : Regime d}
    (S : LimitingSeparatedProfile regime) (b : ℝ) :
    ∀ᶠ i in atTop, 1 ≤ TrackD.testDeg (TrackD.cfgB (regime.P i))
      (S.sequence.target i).width b := by
  by_cases hb : b = 0
  · subst hb
    filter_upwards [regime.B_tendsto.eventually_ge_atTop 1] with i hB
    change 1 ≤ regime.B i * Real.exp (0 * (S.sequence.target i).width)
    rw [zero_mul, Real.exp_zero, mul_one]
    exact hB
  · have hbpos : 0 < |b| := abs_pos.mpr hb
    let ε : ℝ := 1 / (2 * |b|)
    have hε : 0 < ε := by positivity
    have hlog : Tendsto (fun i => Real.log (regime.B i)) atTop atTop :=
      Real.tendsto_log_atTop.comp regime.B_tendsto
    filter_upwards [S.sequence.target_small.def hε, hlog.eventually_ge_atTop 0] with i hi hlog₀
    have hwidth_pos : 0 < (S.sequence.target i).width := (S.sequence.width_pos i).2
    have hsmall : (S.sequence.target i).width ≤ ε * Real.log (regime.B i) := by
      simpa only [Real.norm_eq_abs, abs_of_pos hwidth_pos, abs_of_nonneg hlog₀] using hi
    have hscale : |b| * (S.sequence.target i).width ≤ (1 / 2 : ℝ) * Real.log (regime.B i) := by
      calc
        |b| * (S.sequence.target i).width ≤ |b| * (ε * Real.log (regime.B i)) :=
          mul_le_mul_of_nonneg_left hsmall (abs_nonneg b)
        _ = (|b| * (1 / (2 * |b|))) * Real.log (regime.B i) := by ring
        _ = (1 / 2 : ℝ) * Real.log (regime.B i) := by
          have hne : |b| ≠ 0 := hbpos.ne'
          have : |b| * (1 / (2 * |b|)) = (1 / 2 : ℝ) := by
            field_simp
          rw [this]
    have hbs : - ((1 / 2 : ℝ) * Real.log (regime.B i)) ≤ b * (S.sequence.target i).width := by
      have hle : - (|b| * (S.sequence.target i).width) ≤ b * (S.sequence.target i).width := by
        have : -|b| ≤ b := by linarith [neg_le_abs b]
        nlinarith [hwidth_pos]
      linarith
    have hsum : 0 ≤ Real.log (regime.B i) + b * (S.sequence.target i).width := by
      linarith
    change 1 ≤ regime.B i * Real.exp (b * (S.sequence.target i).width)
    have hBpos : 0 < regime.B i := regime.B_pos i
    calc
      (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ ≤ Real.exp (Real.log (regime.B i) + b * (S.sequence.target i).width) :=
        Real.exp_le_exp.mpr hsum
      _ = regime.B i * Real.exp (b * (S.sequence.target i).width) := by
        rw [Real.exp_add, Real.exp_log hBpos]

/-- `G5.first-cut.descendants`: equations common to the prefix carriers
also vanish on every later carrier meeting the actual piece. -/
theorem descendant_equations_vanish {d : ℕ} (X : TrackD.Piece d)
    (r j : ℕ) (hrj : r ≤ j) (q : RPoint d) (hq : q ∈ X.pts)
    (Y : AffineVariety d) (hY : X.path.IsCarrier j Y) (hqY : TrackD.toC q ∈ Y)
    (F : Finset (Poly d))
    (hF : ∀ Z, TrackD.PoolCarrier {X} r Z → ∀ f ∈ F, f ∈ Z.ideal) :
    ∀ f ∈ F, f ∈ Y.ideal := by
  classical
  have hsystem : X.path.system r ≤ X.path.system j := by
    apply Ideal.span_mono
    intro f hf
    rcases hf with ⟨i, hir, rfl⟩
    exact ⟨i, lt_of_lt_of_le hir hrj, rfl⟩
  have hYmin : Y.ideal ∈ (X.path.system j).minimalPrimes := hY
  letI : Y.ideal.IsPrime := hYmin.isPrime
  have hprefix : X.path.system r ≤ Y.ideal := hsystem.trans hYmin.le
  obtain ⟨Q, hQ, hQY⟩ := Ideal.exists_minimalPrimes_le hprefix
  let Z : AffineVariety d := ⟨Q, hQ.isPrime.isRadical⟩
  have hqZ : TrackD.toC q ∈ Z := by
    change TrackD.toC q ∈ MvPolynomial.zeroLocus ℂ Q
    apply MvPolynomial.zeroLocus_anti_mono hQY
    exact hqY
  have hpool : TrackD.PoolCarrier {X} r Z := by
    refine ⟨X, by simp, ?_, q, hq, hqZ⟩
    change Q ∈ (X.path.system r).minimalPrimes
    exact hQ
  intro f hf
  exact hQY (hF Z hpool f hf)

/-- A fixed-precision first-system certificate on the actual target samples. -/
def FirstCutCertificate {d j : ℕ} {regime : Regime d}
    (D : TrackA.SeparatedDepthData regime j) (ε θ : ℝ) (i : ℕ)
    (F : Finset (Poly d)) (bad : Finset (Point d)) : Prop :=
  bad ⊆ D.targets i ∧ (bad.card : ℝ) ≤ θ * (D.targets i).card ∧
    (∀ f ∈ F, (f.totalDegree : ℝ) ≤ D.firstRate i * Real.exp (ε * D.s i)) ∧
    (∀ Y ∈ D.carriers i,
      Y.Subvariety (AffineVariety.ofIdeal (Ideal.span (F : Set (Poly d))))) ∧
    ∀ q ∈ D.targets i, q ∉ bad →
      (AffineVariety.ofIdeal (Ideal.span (F : Set (Poly d)))).IsSmoothAt q ∧
      (AffineVariety.ofIdeal (Ideal.span (F : Set (Poly d)))).localDimension q < d

/-- `G5.first-cut.diagonal`: choose precision slowly so that both the
exceptional fraction and the degree excess tend to zero. -/
theorem first_cut_of_fixed_precision {d j : ℕ} {regime : Regime d}
    (D : TrackA.SeparatedDepthData regime j)
    (hcert : ∀ ε > 0, ∀ θ > 0, ∀ᶠ i in atTop,
      ∃ F bad, FirstCutCertificate D ε θ i F bad) : D.FirstCutInput := by
  classical
  let Q : ℕ → ℕ → Prop := fun h i =>
    ∃ F bad, FirstCutCertificate D (1 / ((h : ℝ) + 1)) (1 / ((h : ℝ) + 1)) i F bad
  have hQ (h : ℕ) : ∀ᶠ i in atTop, Q h i := by
    have heps : (0 : ℝ) < 1 / ((h : ℝ) + 1) := by positivity
    simpa [Q] using hcert _ heps _ heps
  obtain ⟨a, hmono, hagrows, hchosen⟩ := Framework.exists_slow_diagonal Q hQ
  have hgood : ∀ᶠ i in atTop, Q (a i) i := by
    filter_upwards [hchosen] with i hi
    exact hi (a i) le_rfl
  let E : ℕ → Finset (Poly d) := fun i =>
    if hi : Q (a i) i then Classical.choose hi else ∅
  let bad : ℕ → Finset (Point d) := fun i =>
    if hi : Q (a i) i then Classical.choose (Classical.choose_spec hi) else D.targets i
  have hcertificate (i : ℕ) (hi : Q (a i) i) :
      FirstCutCertificate D (1 / ((a i : ℝ) + 1)) (1 / ((a i : ℝ) + 1)) i (E i) (bad i) := by
    simpa only [E, bad, dif_pos hi] using Classical.choose_spec (Classical.choose_spec hi)
  refine ⟨E, bad, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : Q (a i) i
    · exact (hcertificate i hi).1
    · simp [bad, hi]
  · have htargetPos : ∀ᶠ i in atTop, 0 < ((D.targets i).card : ℝ) := by
      filter_upwards [D.target_size.1 1 (by norm_num)] with i hi
      have hpos : (0 : ℝ) < regime.N i * Real.exp (-1 * D.s i) :=
        mul_pos (regime.N_pos i) (Real.exp_pos _)
      have hcard : (0 : ℝ) < (D.targets i).card := lt_of_lt_of_le hpos (hi ())
      exact_mod_cast hcard
    have hratioBound : ∀ᶠ i in atTop,
        0 ≤ ((bad i).card : ℝ) / (D.targets i).card ∧
          ((bad i).card : ℝ) / (D.targets i).card ≤ 1 / ((a i : ℝ) + 1) := by
      filter_upwards [hgood, htargetPos] with i hi hpos
      have hbound := (hcertificate i hi).2.1
      constructor
      · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      · exact (div_le_iff₀ hpos).2 (by simpa [mul_comm] using hbound)
    have hsmall : Tendsto (fun i => (1 : ℝ) / ((a i : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hagrows
    have hratio : Tendsto (fun i => ((bad i).card : ℝ) / (D.targets i).card)
        atTop (𝓝 0) := by
      rw [tendsto_zero_iff_abs_tendsto_zero]
      apply squeeze_zero'
        (Eventually.of_forall fun i => abs_nonneg _)
        (hratioBound.mono fun i hi => by
          calc
            |((bad i).card : ℝ) / (D.targets i).card| =
                ((bad i).card : ℝ) / (D.targets i).card := abs_of_nonneg hi.1
            _ ≤ 1 / ((a i : ℝ) + 1) := hi.2)
      exact hsmall
    have htargetNe : ∀ᶠ i in atTop, ((D.targets i).card : ℝ) ≠ 0 := by
      filter_upwards [htargetPos] with i hi
      exact ne_of_gt hi
    exact (Framework.littleO_iff_ratio htargetNe).mpr hratio
  · intro ε hε
    have hsmall : ∀ᶠ i in atTop, 1 / ((a i : ℝ) + 1) < ε :=
      (tendsto_one_div_add_atTop_nhds_zero_nat.comp hagrows).eventually (Iio_mem_nhds hε)
    filter_upwards [hgood, hsmall, D.s_grows.eventually_gt_atTop 0] with i hi hεi hs
    intro f
    have hdeg := (hcertificate i hi).2.2.1 f.val f.property
    have hs' : 0 ≤ D.s i := hs.le
    have hexp : Real.exp (1 / ((a i : ℝ) + 1) * D.s i) ≤ Real.exp (ε * D.s i) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hεi.le hs')
    calc
      (f.val.totalDegree : ℝ) ≤ D.firstRate i * Real.exp (1 / ((a i : ℝ) + 1) * D.s i) := hdeg
      _ ≤ D.firstRate i * Real.exp (ε * D.s i) :=
        mul_le_mul_of_nonneg_left hexp (mul_nonneg (regime.B_pos i).le (Real.exp_pos _).le)
  · intro i Y hY
    by_cases hi : Q (a i) i
    · exact (hcertificate i hi).2.2.2.1 Y hY
    · change (Ideal.span (E i : Set (Poly d))).radical ≤ Y.ideal
      simp [E, hi]
  · filter_upwards [hgood] with i hi
    intro q hq hqbad
    exact (hcertificate i hi).2.2.2.2 q hq hqbad

end

end DistinctDistances.SparseCones
