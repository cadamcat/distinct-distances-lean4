import DistinctDistances.TrackE.FinalCurvePlacement
import DistinctDistances.TrackE.FinalCurveRegularity
import DistinctDistances.TrackE.TestDegreeRounding

/-! Homogeneous final regularity inputs, sparse-cones.tex:870–918. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- Real coordinates recover every actual physical center from its complexification. -/
def realCenter (p : Point d) : RPoint d := WithLp.toLp 2 (fun k => (p k).re)

/-- The actual integer testing degree at a time fixed by the final narrow batch. -/
def finalNarrowTestDegree {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} {S : LimitingSeparatedProfile regime}
    [Fintype (ProfilePlateau S)] (K : FinalNarrowBatchData T S) (τ : ℝ) (i : ℕ) : ℕ :=
  ⌊TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ⌋₊

/-- Both integer degrees use floors. The later time absorbs any fixed regularity
constant; the ratio retains a strict exponential gap before any envelope choice. -/
theorem final_narrow_regularization_degrees {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} {S : LimitingSeparatedProfile regime}
    [Fintype (ProfilePlateau S)] (K : FinalNarrowBatchData T S) (C : ℕ) :
    ∀ᶠ i in atTop,
      1 ≤ finalNarrowTestDegree K K.b₀ i ∧
      C * finalNarrowTestDegree K K.b₀ i ≤ finalNarrowTestDegree K K.b_eq i ∧
      (finalNarrowTestDegree K K.b₀ i : ℝ) / (finalNarrowTestDegree K K.b_eq i : ℝ) ≤
        4 * Real.exp (-(K.b_eq - K.b₀) * (S.sequence.target i).width) := by
  have hlt : K.b₀ < K.b_eq := K.reserved_times.1
  have heta : (0 : ℝ) < K.b_eq - K.b₀ := sub_pos.mpr hlt
  have hs_grows := S.sequence.target_grows
  have hT0_ge1 : ∀ᶠ i in atTop, 1 ≤ TrackD.testDeg (TrackD.cfgB (regime.P i))
      (S.sequence.target i).width K.b₀ :=
    target_test_degree S K.b₀
  have hshift : ∀ i, TrackD.testDeg (TrackD.cfgB (regime.P i))
        (S.sequence.target i).width K.b_eq =
      TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width K.b₀ *
        Real.exp ((K.b_eq - K.b₀) * (S.sequence.target i).width) := by
    intro i
    exact TrackD.RankCore.testDeg_shift _ _ _ _
  have hrounded := eventually_rounded_test_degrees C
    (fun i => (S.sequence.target i).width)
    (fun i => TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width K.b₀)
    (fun i => TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width K.b_eq)
    (K.b_eq - K.b₀) hs_grows heta hT0_ge1 hshift
  have hs_pos_all : ∀ i, (0 : ℝ) < (S.sequence.target i).width :=
    fun i => (S.sequence.width_pos i).2
  filter_upwards [hrounded, hT0_ge1] with i hround hT0
  obtain ⟨hceil1, hceil_thresh, hceil_ratio⟩ := hround
  have hT0_nonneg : (0 : ℝ) ≤ TrackD.testDeg (TrackD.cfgB (regime.P i))
      (S.sequence.target i).width K.b₀ :=
    le_trans (by norm_num) hT0
  have hfloor_ge1 : 1 ≤ finalNarrowTestDegree K K.b₀ i := by
    unfold finalNarrowTestDegree
    have hmono := Nat.floor_mono hT0
    simpa using hmono
  have hfloor_le_ceil : (finalNarrowTestDegree K K.b₀ i : ℝ) ≤
      (⌈TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width K.b₀⌉₊ : ℝ) := by
    unfold finalNarrowTestDegree
    have hfl : (⌊TrackD.testDeg (TrackD.cfgB (regime.P i))
          (S.sequence.target i).width K.b₀⌋₊ : ℝ) ≤
        TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width K.b₀ :=
      Nat.floor_le hT0_nonneg
    have hce : TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width K.b₀ ≤
        (⌈TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width K.b₀⌉₊ : ℝ) :=
      Nat.le_ceil (TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width K.b₀)
    exact hfl.trans hce
  have hBpos : (0 : ℝ) < TrackD.cfgB (regime.P i) := by
    unfold TrackD.cfgB
    exact Real.rpow_pos_of_pos (regime.N_pos i) _
  have hL1_pos : (0 : ℝ) < (finalNarrowTestDegree K K.b_eq i : ℝ) := by
    have hT1_ge1 : (1 : ℝ) ≤ TrackD.testDeg (TrackD.cfgB (regime.P i))
        (S.sequence.target i).width K.b_eq := by
      have hmono := TrackD.RankCore.testDeg_mono hBpos.le (hs_pos_all i).le hlt.le
      exact hT0.trans hmono
    unfold finalNarrowTestDegree
    have hmono := Nat.floor_mono hT1_ge1
    have h1 : (1 : ℕ) ≤ ⌊TrackD.testDeg (TrackD.cfgB (regime.P i))
        (S.sequence.target i).width K.b_eq⌋₊ := by simpa using hmono
    have h1R : (1 : ℝ) ≤ (⌊TrackD.testDeg (TrackD.cfgB (regime.P i))
        (S.sequence.target i).width K.b_eq⌋₊ : ℝ) := by exact_mod_cast h1
    linarith
  have hthresh : C * finalNarrowTestDegree K K.b₀ i ≤
      finalNarrowTestDegree K K.b_eq i := by
    have hreal : (C : ℝ) * (finalNarrowTestDegree K K.b₀ i : ℝ) ≤
        (finalNarrowTestDegree K K.b_eq i : ℝ) := by
      calc (C : ℝ) * (finalNarrowTestDegree K K.b₀ i : ℝ)
          ≤ (C : ℝ) * (⌈TrackD.testDeg (TrackD.cfgB (regime.P i))
              (S.sequence.target i).width K.b₀⌉₊ : ℝ) :=
            mul_le_mul_of_nonneg_left hfloor_le_ceil (Nat.cast_nonneg _)
        _ ≤ (⌊TrackD.testDeg (TrackD.cfgB (regime.P i))
              (S.sequence.target i).width K.b_eq⌋₊ : ℝ) := by
            exact_mod_cast hceil_thresh
        _ = (finalNarrowTestDegree K K.b_eq i : ℝ) := rfl
    have hnat : C * finalNarrowTestDegree K K.b₀ i ≤
        finalNarrowTestDegree K K.b_eq i := by
      exact_mod_cast hreal
    exact hnat
  have hratio : (finalNarrowTestDegree K K.b₀ i : ℝ) /
        (finalNarrowTestDegree K K.b_eq i : ℝ) ≤
      4 * Real.exp (-(K.b_eq - K.b₀) * (S.sequence.target i).width) := by
    have hle : (finalNarrowTestDegree K K.b₀ i : ℝ) /
          (finalNarrowTestDegree K K.b_eq i : ℝ) ≤
        (⌈TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width K.b₀⌉₊ : ℝ) /
          (⌊TrackD.testDeg (TrackD.cfgB (regime.P i))
            (S.sequence.target i).width K.b_eq⌋₊ : ℝ) := by
      apply div_le_div_of_nonneg_right _ hL1_pos.le
      · exact hfloor_le_ceil
    exact hle.trans hceil_ratio
  exact ⟨hfloor_ge1, hthresh, hratio⟩

/-- Rewrite the final entry of the unchanged common batch to the literal
narrowRate, with its original bad incidences and common bad centers. -/
theorem final_narrow_depth_lower {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} {S : LimitingSeparatedProfile regime}
    [Fintype (ProfilePlateau S)] (K : FinalNarrowBatchData T S) :
    let D := K.H.data K.finalPlateau
    ∀ ρ : ℝ, 0 < ρ → ∀ᶠ i in atTop,
      ∀ p ∈ D.centers i, p ∉ K.H.batch.badCenters i →
      ∀ J : AffineFamily.Family d, J ⊆ D.retained i (K.H.batch.bad K.finalPlateau i) p →
        ρ * ((D.targets i).card : ℝ) ≤ D.submass i J →
        D.degreeBudget i / D.narrowRate i * Real.exp (-K.ε * D.s i) ≤
          (ProjectiveFamily.degree (TrackA.projectedFamily p J) : ℝ) := by
  intro D ρ hρ
  have hfrom : DepthFromProfile S D := K.H.from_profile K.finalPlateau
  have hRate : ∀ i, profileDepthRate S K.finalPlateau.val.val (K.kind K.finalPlateau) i =
      D.narrowRate i := by
    intro i
    rw [K.final_rate]
    unfold profileDepthRate TrackA.SeparatedDepthData.narrowRate
    rw [hfrom.1, hfrom.2.2.1]
  have hcenters : ∀ i, D.centers i =
      (S.sequence.source i).pts.image TrackD.toC := fun i => (hfrom.2.2.2 i).1
  have htargets : ∀ i, D.targets i =
      (S.sequence.target i).pts.image TrackD.toC := fun i => (hfrom.2.2.2 i).2.1
  have hdeg := K.H.batch.degree ρ hρ
  filter_upwards [hdeg] with i hi
  intro p hp hnot J hJ hmass
  have hp' : p ∈ (S.sequence.source i).pts.image TrackD.toC := by
    rw [← hcenters i]
    exact hp
  have hmass' : ρ * ((((S.sequence.target i).pts.image TrackD.toC).card : ℕ) : ℝ) ≤
      D.submass i J := by
    rw [← htargets i]
    exact hmass
  have hi' := hi K.finalPlateau p hp' hnot J hJ hmass'
  have hRw : D.degreeBudget i /
        profileDepthRate S K.finalPlateau.val.val (K.kind K.finalPlateau) i *
        Real.exp (-K.ε * D.s i) ≤
        (ProjectiveFamily.degree (TrackA.projectedFamily p J) : ℝ) := by
    have h1 := hi'
    simpa using h1
  rw [hRate i] at hRw
  exact hRw

/-- Retain the homogeneous witness through the existing uniform regularity and
assigned-mass argument; the center deletions precede all later family choices. -/
theorem homogeneous_final_curve_regularity (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℕ, 0 < C ∧
      ∀ {j : ℕ} {regime : Regime (n + 1)}
        (D : TrackA.SeparatedDepthData regime j) (hlast : j + 1 = n + 1)
        (Cf Cr ε η : ℝ), 0 < Cf → 0 < Cr → ε < η →
      ∀ (bad : ℕ → Finset (Point (n + 1) × AffineVariety (n + 1)))
        (badCenters : ℕ → Finset (Point (n + 1))),
        (∀ ρ : ℝ, 0 < ρ → ∀ᶠ i in atTop,
          ∀ p ∈ D.centers i, p ∉ badCenters i →
          ∀ J : AffineFamily.Family (n + 1), J ⊆ D.retained i (bad i) p →
            ρ * ((D.targets i).card : ℝ) ≤ D.submass i J →
            D.degreeBudget i / D.narrowRate i * Real.exp (-ε * D.s i) ≤
              (ProjectiveFamily.degree (TrackA.projectedFamily p J) : ℝ)) →
      ∀ (δ : ℕ → ℝ), (∀ᶠ i in atTop, 0 ≤ δ i ∧ δ i ≤ 1) →
      ∀ (L T : ℕ → ℕ) (F : ℕ → Point (n + 1) → ProjectiveFamily.Family (n + 1)),
        (∀ᶠ i in atTop, ∀ p ∈ D.centers i, p ∉ badCenters i →
          ProjectiveFamily.IsPure (F i p) 1 ∧ 1 ≤ L i ∧
          TrackA.FromProjectiveLists (F i p) (L i) ∧ C * L i ≤ T i ∧
          (ProjectiveFamily.degree (F i p) : ℝ) ≤ Cf * δ i * (regime.N i / regime.A i) ∧
          (L i : ℝ) / (T i : ℝ) ≤ Cr * Real.exp (-η * D.s i)) →
      ∃ (badFamily : ℕ → Point (n + 1) → ProjectiveFamily.Family (n + 1))
        (E : ℕ → Point (n + 1) → List (Poly (n + 1)))
        (g : ℕ → Point (n + 1) → Poly (n + 1)),
        (∀ᶠ i in atTop, ∀ p ∈ D.centers i, p ∉ badCenters i →
          HomogeneousCurveRegularityCertificate (F i p) (badFamily i p) (E i p) (g i p) C (T i) ∧
          (ProjectiveFamily.degree (badFamily i p) : ℝ) ≤
            ((C : ℝ) * Cf * Cr) * δ i * (regime.N i / regime.A i) *
              Real.exp (-η * D.s i)) ∧
        Framework.UniformLittleO
          (fun i => {p : Point (n + 1) // p ∈ D.centers i ∧ p ∉ badCenters i})
          (fun i p => (((D.targets i).filter (fun q => D.owner i q ∈
            exceptional_carriers D i (bad i) p.val (badFamily i p.val))).card : ℝ))
          (fun i _ => (D.targets i).card) := by
  classical
  obtain ⟨C, hC, hregular⟩ := homogeneous_curve_regularity_budget n hn
  refine ⟨C, hC, ?_⟩
  intro j regime D hlast Cf Cr ε η hCf hCr hgap bad badCenters hlower δ hδ L T F hF
  let Q := fun i p =>
    ProjectiveFamily.IsPure (F i p) 1 ∧ 1 ≤ L i ∧
    TrackA.FromProjectiveLists (F i p) (L i) ∧ C * L i ≤ T i ∧
    (ProjectiveFamily.degree (F i p) : ℝ) ≤ Cf * δ i * (regime.N i / regime.A i) ∧
    (L i : ℝ) / (T i : ℝ) ≤ Cr * Real.exp (-η * D.s i) ∧ 0 ≤ δ i
  have hchoices : ∀ i p,
      ∃ (badF : ProjectiveFamily.Family (n + 1)) (E : List (Poly (n + 1))) (g : Poly (n + 1)),
        Q i p → HomogeneousCurveRegularityCertificate (F i p) badF E g C (T i) ∧
          (ProjectiveFamily.degree badF : ℝ) ≤
            ((C : ℝ) * Cf * Cr) * δ i * (regime.N i / regime.A i) *
              Real.exp (-η * D.s i) := by
    intro i p
    by_cases hQ : Q i p
    · obtain ⟨hpure, hL, hlists, hT, hdegree, hratio, hδ₀⟩ := hQ
      obtain ⟨badF, E, g, hcert, hbound⟩ :=
        hregular (F i p) (L i) (T i) hpure hL hlists hT
          Cf Cr (δ i) (regime.N i / regime.A i) η (D.s i)
          hCf hCr hδ₀ (div_pos (regime.N_pos i) (regime.A_pos i)).le hdegree hratio
      exact ⟨badF, E, g, fun _ => ⟨hcert, hbound⟩⟩
    · exact ⟨∅, [], 0, fun h => (hQ h).elim⟩
  choose badFamily E g hchoice using hchoices
  have hcert : ∀ᶠ i in atTop, ∀ p ∈ D.centers i, p ∉ badCenters i →
      HomogeneousCurveRegularityCertificate (F i p) (badFamily i p) (E i p) (g i p) C (T i) ∧
      (ProjectiveFamily.degree (badFamily i p) : ℝ) ≤
        ((C : ℝ) * Cf * Cr) * δ i * (regime.N i / regime.A i) * Real.exp (-η * D.s i) := by
    filter_upwards [hF, hδ] with i hi hδi
    intro p hp hgood
    obtain ⟨hpure, hL, hlists, hT, hdegree, hratio⟩ := hi p hp hgood
    exact hchoice i p ⟨hpure, hL, hlists, hT, hdegree, hratio, hδi.1⟩
  refine ⟨badFamily, E, g, hcert, ?_⟩
  have hupper : ∀ᶠ i in atTop, ∀ p ∈ D.centers i, p ∉ badCenters i →
      (ProjectiveFamily.degree (badFamily i p) : ℝ) ≤
        ((C : ℝ) * Cf * Cr) * δ i * (regime.N i / regime.A i) * Real.exp (-η * D.s i) := by
    filter_upwards [hcert] with i hi
    exact fun p hp hgood => (hi p hp hgood).2
  have hmass := final_narrow_exceptional_mass D hlast ((C : ℝ) * Cf * Cr) ε η
    (by positivity) hgap bad badCenters hlower δ hδ badFamily hupper
  simpa only [submass_eq_assigned_card] using hmass

/-- Only labels whose original owner's complete projection admits a proper
minor test are counted. Zeros are tested on the physical vector q-p. -/
def properMinorZeroTargets {j : ℕ} (D : TrackA.SeparatedDepthData regime j)
    (i : ℕ) (p : Point d) (Q : Finset (RPoint d)) (g : Poly d) : Finset (RPoint d) :=
  Q.filter fun q => g ∉ (radialImage p (D.owner i (TrackD.toC q))).ideal ∧
    MvPolynomial.eval (TrackD.toC q - p) g = 0

/-- Nonvanishing on physical representatives is nonvanishing at the actual
projective label; the homogeneous degree need not be positive. -/
theorem retained_minor_label_nonzero {j r : ℕ}
    (D : TrackA.SeparatedDepthData regime j) (i : ℕ) (p : Point d)
    (Q : Finset (RPoint d)) (g : Poly d) (hg : g.IsHomogeneous r)
    (q : RPoint d) (hq : q ∈ Q) (hneq : TrackD.toC q ≠ p)
    (hproper : g ∉ (radialImage p (D.owner i (TrackD.toC q))).ideal)
    (hzero : q ∉ properMinorZeroTargets D i p Q g) :
    MvPolynomial.eval (radialProjection p (TrackD.toC q) hneq).rep g ≠ 0 := by
  have hv : TrackD.toC q - p ≠ 0 := sub_ne_zero.mpr hneq
  have heval_ne : MvPolynomial.eval (TrackD.toC q - p) g ≠ 0 := by
    intro heq
    apply hzero
    rw [properMinorZeroTargets, Finset.mem_filter]
    exact ⟨hq, hproper, heq⟩
  have hiff := Bridges.homogeneous_eval_zero_mk_iff g hg (TrackD.toC q - p) hv
  have hproj : radialProjection p (TrackD.toC q) hneq =
      Projectivization.mk ℂ (TrackD.toC q - p) hv := rfl
  rw [hproj]
  intro hrep0
  exact heval_ne (hiff.mp hrep0)

end
end DistinctDistances.SparseCones
