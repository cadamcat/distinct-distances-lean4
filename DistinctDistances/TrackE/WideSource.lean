import DistinctDistances.TrackE.DepthDataCore
import DistinctDistances.TrackD.Profiles.RegularityChosenCuts

/-! The positive source plateau in the wider-window branch
(`depth.tex:222–239`). Assignments and ignored points may be fixed before
the component tests; the test threshold is uniform over their polynomials. -/

namespace DistinctDistances.SparseCones

open Filter
open scoped Topology BigOperators Classical

noncomputable section

/-- A fixed interior source plateau before the first positive limiting cut. -/
structure PositiveSourcePlateau {d : ℕ} {regime : Regime d}
    (S : LimitingSeparatedProfile regime) (j : ℕ) where
  r : Fin d
  r_pos : 0 < r.val
  r_le_j : r.val ≤ j
  τ : ℝ
  ξ : ℝ
  τ_pos : 0 < τ
  ξ_pos : 0 < ξ
  plateau : TrackD.OnPlateau S.b r.val (2 * ξ) τ
  prefix_nonpos : ∀ t : Fin d, t.val < r.val → S.b t ≤ 0

/-- `G5.wide.plateau`: choose the first positive drop once on the limiting
profile. The source carrier dimension d-r is between d-j and d-1. -/
theorem positive_source_plateau {d j : ℕ} {regime : Regime d}
    (S : LimitingSeparatedProfile regime) (hj : j < d) (hb : 0 < S.b ⟨j, hj⟩) :
    Nonempty (PositiveSourcePlateau S j) := by
  let pos : Finset (Fin d) := Finset.univ.filter (fun t => 0 < S.b t)
  have hpos_ne : pos.Nonempty := ⟨⟨j, hj⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩⟩
  let r := pos.min' hpos_ne
  have hr_mem : r ∈ pos := Finset.min'_mem pos hpos_ne
  have hr_pos : 0 < S.b r := (Finset.mem_filter.mp hr_mem).2
  have hr_le_j : r.val ≤ j := by
    have hj_mem : ⟨j, hj⟩ ∈ pos := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩
    exact Finset.min'_le pos ⟨j, hj⟩ hj_mem
  have hr_prefix : ∀ t : Fin d, t.val < r.val → S.b t ≤ 0 := by
    intro t ht
    by_contra hnot
    have hpos : 0 < S.b t := lt_of_not_ge hnot
    have ht_mem : t ∈ pos := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos⟩
    have hr_le := Finset.min'_le pos t ht_mem
    exact not_lt_of_ge hr_le ht
  obtain ⟨c, hc_pos, hc0, -, -⟩ := S.balance
  have hr_val_pos : 0 < r.val := by
    by_contra hr0
    have hr_zero : r.val = 0 := by omega
    have hr_eq : r = ⟨0, by have := regime.dimension_ge_three; omega⟩ := Fin.ext hr_zero
    rw [hr_eq] at hr_pos
    linarith
  let τ := S.b r / 2
  let ξ := S.b r / 8
  have hτ_pos : 0 < τ := by positivity
  have hξ_pos : 0 < ξ := by positivity
  have hplateau : TrackD.OnPlateau S.b r.val (2 * ξ) τ := by
    intro i
    constructor
    · intro hi
      have hle := hr_prefix i hi
      dsimp [τ, ξ]
      linarith
    · intro hi
      have hmono : S.b r ≤ S.b i := S.sorted (show r ≤ i from hi)
      dsimp [τ, ξ]
      linarith
  exact ⟨⟨r, hr_val_pos, hr_le_j, τ, ξ, hτ_pos, hξ_pos, hplateau, hr_prefix⟩⟩

/-- `G5.wide.plateau-transfer`: leave a fixed margin for the source's
converging recorded cut times. -/
theorem source_plateau_eventually {d j : ℕ} {regime : Regime d}
    (S : LimitingSeparatedProfile regime) (A : PositiveSourcePlateau S j) :
    ∀ᶠ i in atTop, TrackD.OnPlateau (S.sequence.source i).path.time
      A.r.val A.ξ A.τ := by
  have hclose : ∀ t : Fin d, ∀ᶠ i in atTop,
      |(S.sequence.source i).path.time t - S.b t| ≤ A.ξ := by
    intro t
    have hlim := S.source_limit t
    have hnhds : {x : ℝ | |x - S.b t| ≤ A.ξ} ∈ 𝓝 (S.b t) := by
      rw [Metric.mem_nhds_iff]
      refine ⟨A.ξ, A.ξ_pos, fun y hy => ?_⟩
      rw [Metric.mem_ball, Real.dist_eq] at hy
      exact hy.le
    exact hlim hnhds
  have hall : ∀ᶠ i in atTop, ∀ t : Fin d,
      |(S.sequence.source i).path.time t - S.b t| ≤ A.ξ := by
    rw [eventually_all]
    exact hclose
  filter_upwards [hall] with i hi
  intro t
  obtain ⟨hleft, hright⟩ := A.plateau t
  have hdiff := abs_le.mp (hi t)
  constructor
  · intro ht
    have h1 := hleft ht
    linarith
  · intro ht
    have h2 := hright ht
    linarith

/-- `G5.wide.test-degree`: the positive source time has testing degree
at least one, eventually. -/
theorem source_positive_test_degree {d j : ℕ} {regime : Regime d}
    (S : LimitingSeparatedProfile regime) (A : PositiveSourcePlateau S j) :
    ∀ᶠ i in atTop, 1 ≤ TrackD.testDeg (TrackD.cfgB (regime.P i))
      (S.sequence.source i).width A.τ := by
  have hB : ∀ᶠ i in atTop, 1 ≤ regime.B i :=
    regime.B_tendsto.eventually_ge_atTop 1
  filter_upwards [hB] with i hi
  change 1 ≤ regime.B i * Real.exp (A.τ * (S.sequence.source i).width)
  have hw : 0 < (S.sequence.source i).width := (S.sequence.width_pos i).1
  have hexp : 1 ≤ Real.exp (A.τ * (S.sequence.source i).width) := by
    apply Real.one_le_exp_iff.mpr
    exact mul_nonneg A.τ_pos.le hw.le
  calc
    (1 : ℝ) = 1 * 1 := by ring
    _ ≤ regime.B i * Real.exp (A.τ * (S.sequence.source i).width) := by
      apply mul_le_mul hi hexp zero_le_one (by positivity)

/-- `G5.wide.component-tests`: every later proper component test of degree
B exp(Cs) is negligible on the actual wide source sample. The source assignment
uses local carriers of the same fixed positive plateau. -/
theorem profile_source_component_tests {d j : ℕ} {regime : Regime d}
    (S : LimitingSeparatedProfile regime) (D : TrackA.SeparatedDepthData regime j)
    (hs : D.s = fun i => (S.sequence.target i).width)
    (hv : D.v = fun i => (S.sequence.source i).width)
    (hcenters : ∀ i, D.centers i = (S.sequence.source i).pts.image TrackD.toC)
    (hwide : Tendsto (fun i => D.s i / D.v i) atTop (𝓝 0))
    (A : PositiveSourcePlateau S j)
    (sources : ℕ → AffineFamily.Family d)
    (owner : ℕ → Point d → AffineVariety d) (ignored : ℕ → Finset (Point d))
    (howner : ∀ i p, p ∈ D.centers i → p ∉ ignored i →
      owner i p ∈ sources i ∧
      (S.sequence.source i).path.IsCarrier A.r.val (owner i p) ∧ p ∈ owner i p) :
    ∀ C : ℝ, 0 < C → Framework.UniformLittleO (D.ComponentTests sources C)
      (fun i h => ((D.centers i).filter
        (fun p => p ∉ ignored i ∧ MvPolynomial.eval p (h.val (owner i p)) = 0)).card)
      (fun i _ => (D.centers i).card) := by
  intro C hC
  have hτ := A.τ_pos
  have hξ := A.ξ_pos
  have hdegree : ∀ᶠ i in atTop,
      regime.B i * Real.exp (C * D.s i) ≤
        TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.source i).width A.τ := by
    have hsmall := hwide.eventually
      (gt_mem_nhds (show (0 : ℝ) < A.τ / C by positivity))
    filter_upwards [hsmall] with i hi
    have hvpos : 0 < D.v i := by simpa only [hv] using (S.sequence.width_pos i).1
    have hscale := mul_lt_mul_of_pos_left ((div_lt_iff₀ hvpos).mp hi) hC
    have hcancel : C * (A.τ / C * D.v i) = A.τ * D.v i := by
      field_simp
    rw [hcancel] at hscale
    change regime.B i * Real.exp (C * D.s i) ≤
      regime.B i * Real.exp (A.τ * (S.sequence.source i).width)
    apply mul_le_mul_of_nonneg_left _ (regime.B_pos i).le
    apply Real.exp_le_exp.mpr
    simpa only [hv] using hscale.le
  intro ε hε
  obtain ⟨θ, hθ, η, hη, hηξ, v₀, hcuts⟩ := TrackD.prof_regularity_cuts_with_margin d
    regime.dimension_ge_three ε hε A.ξ A.ξ_pos 1 le_rfl
  filter_upwards [S.sequence.good θ hθ η hη 1 le_rfl,
    S.sequence.source_grows.eventually_ge_atTop v₀, source_plateau_eventually S A,
    source_positive_test_degree S A, hdegree] with i hi hwidth hplateau htest hdeg
  intro h
  let g : AffineVariety d → Poly d := fun Z => if Z ∈ sources i then h.val Z else 0
  have hgdeg : ∀ Z, ((g Z).totalDegree : ℝ) ≤
      1 * TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.source i).width A.τ := by
    intro Z
    by_cases hZ : Z ∈ sources i
    · simp only [g, if_pos hZ, one_mul]
      exact (h.property Z hZ).2.trans hdeg
    · simp only [g, if_neg hZ, MvPolynomial.totalDegree_zero, Nat.cast_zero, one_mul]
      exact (by linarith : (0 : ℝ) ≤
        TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.source i).width A.τ)
  have hcaptured := hcuts (regime.P i) (S.sequence.source i) hi.1 hwidth
    A.r.val A.r.isLt A.τ hplateau htest g hgdeg
  let captured := (S.sequence.source i).pts.filter (fun x =>
    ∃ Z ∈ (S.sequence.source i).path.localCarriers A.r.val (TrackD.toC x),
      g Z ∉ Z.ideal ∧ MvPolynomial.eval (TrackD.toC x) (g Z) = 0)
  have hsubset : ((D.centers i).filter
      (fun p => p ∉ ignored i ∧ MvPolynomial.eval p (h.val (owner i p)) = 0)) ⊆
        captured.image TrackD.toC := by
    intro p hp
    obtain ⟨hp, hpnot, heval⟩ := Finset.mem_filter.mp hp
    have hpin := hp
    rw [hcenters i] at hp
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hmem, hcarrier, hcontains⟩ := howner i (TrackD.toC x) hpin hpnot
    apply Finset.mem_image.mpr
    refine ⟨x, Finset.mem_filter.mpr ⟨hx, owner i (TrackD.toC x),
      ⟨hcarrier, hcontains⟩, ?_, ?_⟩, rfl⟩
    · simpa only [g, if_pos hmem] using (h.property (owner i (TrackD.toC x)) hmem).1
    · simpa only [g, if_pos hmem] using heval
  have hcount : (((D.centers i).filter
      (fun p => p ∉ ignored i ∧ MvPolynomial.eval p (h.val (owner i p)) = 0)).card : ℝ) ≤
        (captured.card : ℝ) := by
    have hcard := Finset.card_le_card hsubset
    rw [Finset.card_image_of_injective _ profile_toC_injective] at hcard
    exact_mod_cast hcard
  have hcenterCard : (D.centers i).card = (S.sequence.source i).pts.card := by
    rw [hcenters i]
    exact Finset.card_image_of_injective _ profile_toC_injective
  rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _), hcenterCard]
  exact hcount.trans hcaptured

end

end DistinctDistances.SparseCones
