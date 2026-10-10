import DistinctDistances.TrackE.DepthDataCore
import DistinctDistances.TrackD.CurveSections

/-! The source's initial plateau supplies the bounded-degree and proper-flat
no-capture inputs of `G5.initial` (`depth.tex:123–165`). -/

namespace DistinctDistances.SparseCones

open Filter
open scoped Topology BigOperators

noncomputable section

/-- Since the source width is `o(log B)`, its testing degree at time -2
eventually dominates every fixed polynomial degree. -/
theorem initial_test_degree {d : ℕ} {regime : Regime d}
    (S : LimitingSeparatedProfile regime) (q : ℕ) :
    ∀ᶠ i in atTop, (q : ℝ) ≤
      TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.source i).width (-2) := by
  let C : ℝ := (q : ℝ) + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hlog : Tendsto (fun i => Real.log (regime.B i)) atTop atTop :=
    Real.tendsto_log_atTop.comp regime.B_tendsto
  filter_upwards [S.sequence.source_small.def (show (0 : ℝ) < (1 / 4 : ℝ) by norm_num),
    hlog.eventually_ge_atTop (max (2 * Real.log C) 0)] with i hi hbound
  have hlog₀ : 0 ≤ Real.log (regime.B i) := (le_max_right _ _).trans hbound
  have hlogC : 2 * Real.log C ≤ Real.log (regime.B i) := (le_max_left _ _).trans hbound
  have hsmall : (S.sequence.source i).width ≤ (1 / 4 : ℝ) * Real.log (regime.B i) := by
    simpa only [Real.norm_eq_abs, abs_of_pos (S.sequence.width_pos i).1,
      abs_of_nonneg hlog₀] using hi
  calc
    (q : ℝ) ≤ C := by dsimp [C]; linarith
    _ = Real.exp (Real.log C) := (Real.exp_log hC).symm
    _ ≤ Real.exp (Real.log (regime.B i) + (-2) * (S.sequence.source i).width) := by
      apply Real.exp_le_exp.mpr
      linarith
    _ = _ := by
      rw [Real.exp_add, Real.exp_log (regime.B_pos i)]
      rfl

/-- At zero cuts the only carrier ideal is zero, so any nonzero polynomial
is a proper test on every local carrier. -/
theorem initial_carrier_ideal {d : ℕ} (path : TrackD.CutPath d) (Z : AffineVariety d)
    (hZ : path.IsCarrier 0 Z) : Z.ideal = ⊥ := by
  have hsystem : path.system 0 = ⊥ := by simp [TrackD.CutPath.system]
  have h := hZ
  change Z.ideal ∈ (path.system 0).minimalPrimes at h
  rw [hsystem, Ideal.minimalPrimes_eq_subsingleton_self] at h
  exact Set.mem_singleton_iff.mp h

open Classical in
/-- Uniform no-capture on the actual complexified source sample. Every
bounded-degree polynomial is tested on the same initial source plateau. -/
theorem source_initial_no_capture {d : ℕ} {regime : Regime d}
    (S : LimitingSeparatedProfile regime) (q : ℕ) :
    Framework.UniformLittleO
      (fun _ => {f : Poly d // f ≠ 0 ∧ f.totalDegree ≤ q})
      (fun i f => ((((S.sequence.source i).pts.image TrackD.toC).filter
        (fun p => MvPolynomial.eval p f.val = 0)).card : ℝ))
      (fun i _ => (((S.sequence.source i).pts.image TrackD.toC).card : ℝ)) := by
  classical
  intro ε hε
  filter_upwards [S.sequence.good ε hε (1 / 2) (by norm_num) 1 le_rfl,
    initial_test_degree S (q + 1)] with i hi htest
  intro f
  have hon : TrackD.OnPlateau (S.sequence.source i).path.time 0 (1 / 2) (-2) := by
    intro t
    constructor
    · intro h
      omega
    · intro h
      have hrange := (S.sequence.base_good i).1.time_range t
      linarith [hrange.1]
  have htest₁ : 1 ≤ TrackD.testDeg (TrackD.cfgB (regime.P i))
      (S.sequence.source i).width (-2) := by
    have hq : (1 : ℝ) ≤ ((q + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ q + 1)
    exact hq.trans htest
  have hdegree : (f.val.totalDegree : ℝ) ≤
      TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.source i).width (-2) := by
    have hf : f.val.totalDegree ≤ q + 1 := f.property.2.trans (by omega)
    have hfReal : (f.val.totalDegree : ℝ) ≤ ((q + 1 : ℕ) : ℝ) := by exact_mod_cast hf
    exact hfReal.trans htest
  have hcap := hi.1.noCapture 0 (by have := regime.dimension_ge_three; omega) (-2)
    hon htest₁ f.val (by simpa only [one_mul] using hdegree)
  have hsubset : (S.sequence.source i).pts.filter
      (fun x => MvPolynomial.eval (TrackD.toC x) f.val = 0) ⊆
        (S.sequence.source i).path.captured 0 (S.sequence.source i).pts f.val := by
    intro x hx
    obtain ⟨hx, heval⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_filter.mpr ⟨hx, heval, ?_⟩
    intro Z hZ
    rw [initial_carrier_ideal _ Z hZ.1]
    simpa only [Ideal.mem_bot] using f.property.1
  have hfilter : (((S.sequence.source i).pts.image TrackD.toC).filter
      (fun p => MvPolynomial.eval p f.val = 0)) =
        ((S.sequence.source i).pts.filter
          (fun x => MvPolynomial.eval (TrackD.toC x) f.val = 0)).image TrackD.toC := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, heval⟩
      exact ⟨x, ⟨hx, heval⟩, rfl⟩
    · rintro ⟨x, ⟨hx, heval⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, heval⟩
  rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _), hfilter,
    Finset.card_image_of_injective _ profile_toC_injective,
    Finset.card_image_of_injective _ profile_toC_injective]
  have hcount : (((S.sequence.source i).pts.filter
      (fun x => MvPolynomial.eval (TrackD.toC x) f.val = 0)).card : ℝ) ≤
      (((S.sequence.source i).path.captured 0 (S.sequence.source i).pts f.val).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsubset
  exact hcount.trans hcap

open Classical in
/-- One nonzero affine-linear polynomial contains any proper complex affine
flat. Its degree is uniformly one, independently of the flat. -/
theorem proper_flat_test {d : ℕ} (a : TrackA.ProperFlat d) :
    ∃ f : Poly d, f ≠ 0 ∧ f.totalDegree ≤ 1 ∧
      ∀ p : Point d, p - a.val.1 ∈ a.val.2 → MvPolynomial.eval p f = 0 := by
  classical
  have htop : a.val.2 ≠ ⊤ := by
    intro h
    have heq : Module.finrank ℂ a.val.2 = d := by rw [h, finrank_top]; simp [Point]
    have hdim := a.property
    omega
  have hex : ∃ v : Point d, v ∉ a.val.2 := by
    by_contra h
    push Not at h
    exact htop (top_unique (fun v _ => h v))
  obtain ⟨v, hv⟩ := hex
  obtain ⟨lam, hlam, hmap⟩ := a.val.2.exists_dual_map_eq_bot_of_notMem hv inferInstance
  let f := TrackD.covectorPoly lam a.val.1
  have hf : f ≠ 0 := by
    intro hf
    have heval : MvPolynomial.eval (a.val.1 + v) f = 0 := by rw [hf]; simp
    have hzero : lam v = 0 := by
      simpa only [f, TrackD.eval_covectorPoly, add_sub_cancel_left] using heval
    simpa [hzero] using hlam
  refine ⟨f, hf, TrackD.covectorPoly_degree_le_one _ _, ?_⟩
  intro p hp
  change MvPolynomial.eval p (TrackD.covectorPoly lam a.val.1) = 0
  rw [TrackD.eval_covectorPoly]
  have hm : lam (p - a.val.1) ∈ a.val.2.map lam := Submodule.mem_map.mpr ⟨_, hp, rfl⟩
  simpa only [hmap, Submodule.mem_bot] using hm

open Classical in
/-- The bounded-degree input implies the proper-flat input with the same
uniform threshold; the test polynomial may depend on the flat. -/
theorem uniform_flat_cap_of_initial {d j : ℕ} {regime : Regime d}
    (D : TrackA.SeparatedDepthData regime j) (h : D.InitialNoCapture) : D.UniformFlatCap := by
  classical
  choose f hf hdegree hvanish using proper_flat_test (d := d)
  intro ε hε
  filter_upwards [h 1 ε hε] with i hi
  intro a
  have hpoly := hi ⟨f a, hf a, hdegree a⟩
  rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)]
  have hsub : (D.centers i).filter (fun p => p - a.val.1 ∈ a.val.2) ⊆
      (D.centers i).filter (fun p => MvPolynomial.eval p (f a) = 0) := by
    intro p hp
    obtain ⟨hp, hflat⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hp, hvanish a p hflat⟩
  have hbound : (((D.centers i).filter (fun p => MvPolynomial.eval p (f a) = 0)).card : ℝ) ≤
      ε * ((D.centers i).card : ℝ) := by
    rw [abs_of_nonneg (show (0 : ℝ) ≤
      (((D.centers i).filter (fun p => MvPolynomial.eval p (f a) = 0)).card : ℝ) from
        Nat.cast_nonneg _),
      abs_of_nonneg (show (0 : ℝ) ≤ ((D.centers i).card : ℝ) from Nat.cast_nonneg _)] at hpoly
    exact hpoly
  have hcount : (((D.centers i).filter (fun p => p - a.val.1 ∈ a.val.2)).card : ℝ) ≤
      (((D.centers i).filter (fun p => MvPolynomial.eval p (f a) = 0)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  exact hcount.trans hbound

end

end DistinctDistances.SparseCones
