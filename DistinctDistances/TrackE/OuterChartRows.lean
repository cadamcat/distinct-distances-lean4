import DistinctDistances.TrackE.OuterDegree
import DistinctDistances.TrackE.ProjectedMass
import DistinctDistances.TrackE.DepthDataCore

/-! Rows of one regular chart piece at the outer endpoint
(sparse-cones.tex:580–651).

`outer_chart_lift` produces the algebraic lift at a surviving pair from the
lead leaf `outer_lift_curve`; `outer_chart_terminal_empty` resolves `k = 1`
(sc:596–599); `outer_chart_row_bound` bounds one row for `k ≥ 2` by pooling
the lifts over each direction component (`outer_lift_map_degree`), bounding
their degrees (`outer_lift_degree_bound`) and summing the physical curve bound
(`outer_row_sparse`). -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

theorem outer_subvariety_points {n : ℕ} {V W : AffineVariety n} (h : V.Subvariety W) :
    V.points ⊆ W.points :=
  MvPolynomial.zeroLocus_anti_mono h


theorem outer_sum_biUnion_le_of_nonneg {ι α : Type*} (s : Finset ι) (t : ι → Finset α)
    (f : α → ℚ) (hf : ∀ i ∈ s, ∀ a ∈ t i, 0 ≤ f a) :
    ∑ a ∈ s.biUnion t, f a ≤ ∑ i ∈ s, ∑ a ∈ t i, f a := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hi]
    have h := Finset.sum_union_inter (s₁ := t i) (s₂ := s.biUnion t) (f := f)
    have hnn : 0 ≤ ∑ a ∈ t i ∩ s.biUnion t, f a := by
      apply Finset.sum_nonneg
      intro a ha
      exact hf i (Finset.mem_insert_self i s) a (Finset.mem_inter.mp ha).1
    have ih' := ih (fun i' hi' a ha => hf i' (Finset.mem_insert_of_mem hi') a ha)
    linarith

theorem outer_affine_degree_nonneg {n : ℕ} {V : AffineVariety n}
    (hV : V.IsIrreducible) : 0 ≤ V.degree := by
  have h := OAI.QuarticPowerFree.one_le_affineDegree V.ideal (Ideal.IsPrime.ne_top hV)
  exact le_trans (by norm_num) h

section
variable {F : ConeCoverageSequence regime} {T : SelectedProfileSequence F}
  {M : CommonPoolProfile T}

/-- A retained point lies in one original piece of the pools. -/
theorem CommonPhysicalSequence.exists_piece {jW : ℕ} {τ : ℝ}
    (W : CommonPhysicalSequence T M jW τ) (i : ℕ) {q : RPoint d}
    (hq : q ∈ W.sources i ∪ W.targets i) :
    ∃ X ∈ T.sources i ∪ T.targets i, q ∈ X.pts := by
  rcases Finset.mem_union.mp hq with h | h
  · simp only [CommonPhysicalSequence.sources, retainedCommonPool, Finset.mem_filter,
      TrackD.poolPts, Finset.mem_biUnion] at h
    obtain ⟨⟨X, hX, hqX⟩, _⟩ := h
    exact ⟨X, Finset.mem_union_left _ hX, hqX⟩
  · simp only [CommonPhysicalSequence.targets, retainedCommonPool, Finset.mem_filter,
      TrackD.poolPts, Finset.mem_biUnion] at h
    obtain ⟨⟨X, hX, hqX⟩, _⟩ := h
    exact ⟨X, Finset.mem_union_right _ hX, hqX⟩

/-- The owner of a retained point is a pool carrier through it. -/
theorem CommonPhysicalSequence.owner_poolCarrier {jW : ℕ} {τ : ℝ}
    (W : CommonPhysicalSequence T M jW τ) (i : ℕ) {q : RPoint d}
    (hq : q ∈ W.sources i ∪ W.targets i) :
    TrackD.PoolCarrier (T.sources i ∪ T.targets i) jW (W.owner i q) ∧
      TrackD.toC q ∈ (W.owner i q).points := by
  obtain ⟨X, hX, hqX⟩ := W.exists_piece i hq
  obtain ⟨hcarr, hmem⟩ := W.supported i X hX q hqX
  exact ⟨⟨X, hX, hcarr, q, hqX, hmem⟩, hmem⟩

variable {k i j : ℕ} {i₀ : Fin d} {ρ ε ρ' τ : ℝ}

/-- Owner facts at a pair of a chart piece. -/
theorem OuterChartCert.owner_facts (c : OuterChartCert T M k i j i₀ ρ ε ρ' τ)
    {pq : RPoint d × RPoint d} (h : pq ∈ c.G) :
    (c.W.owner i pq.1).IsIrreducible ∧ (c.W.owner i pq.1).dimension = k ∧
    (c.W.owner i pq.2).IsIrreducible ∧ (c.W.owner i pq.2).dimension = k ∧
    TrackD.toC pq.1 ∈ (c.W.owner i pq.1).points ∧
    TrackD.toC pq.2 ∈ (c.W.owner i pq.2).points ∧
    pq.1 ∈ c.W.sources i ∪ c.W.targets i ∧ pq.2 ∈ c.W.sources i ∪ c.W.targets i := by
  obtain ⟨r, hr, h1, h2⟩ := c.hown pq h
  obtain ⟨hs, ht, _⟩ := c.hGpoolsList pq h
  have hs' : pq.1 ∈ c.W.sources i ∪ c.W.targets i := Finset.mem_union_left _ hs
  have ht' : pq.2 ∈ c.W.sources i ∪ c.W.targets i := Finset.mem_union_right _ ht
  rw [c.hWownF pq.1, c.hWownF pq.2, h1, h2]
  have hm1 := (c.W.owner_poolCarrier i hs').2
  have hm2 := (c.W.owner_poolCarrier i ht').2
  rw [c.hWownF pq.1, h1] at hm1
  rw [c.hWownF pq.2, h2] at hm2
  exact ⟨(c.pool.hRirr r hr).1, (c.pool.hRdim r hr).1, (c.pool.hRirr r hr).2,
    (c.pool.hRdim r hr).2, hm1, hm2, hs', ht'⟩

/-- A pair of a chart piece is a selected incidence of the original covering. -/
theorem OuterChartCert.selected (c : OuterChartCert T M k i j i₀ ρ ε ρ' τ)
    {pq : RPoint d × RPoint d} (h : pq ∈ c.G) :
    TrackD.SelectedIncidence (regime.P i) (F.family i) (T.terminal i)
      (selectionTolerance (T.precision i)) pq.1 pq.2 := by
  have h' := c.hGsub h
  simp only [outerSelectedGraph, Finset.mem_filter] at h'
  exact h'.2

variable {Bdeg : ℝ}

/-- sc:580–594 at one surviving pair: the algebraic lift over a direction
component `γ` through the direction of the pair. -/
theorem outer_chart_lift
    (cert : OuterRegularityCert T M k i j i₀ ρ ε ρ' Bdeg τ)
    (sys : @OuterTestSystem d)
    (hP1 : ∀ pq ∈ cert.chart.G, cert.good pq → ∀ X Y : AffineVariety d,
      cert.chart.W.owner i pq.1 = X → cert.chart.W.owner i pq.2 = Y →
      OuterTestsNonvanishing sys (TrackD.toC pq.1) (TrackD.toC pq.2) ∧
      Nonempty (OuterTangentData i₀ (TrackD.toC pq.1) (TrackD.toC pq.2) X Y k
        (outerLabelTangent cert.Eqs i₀ (TrackD.toC pq.1) (TrackD.toC pq.2))))
    (D : Finset (RPoint d × RPoint d))
    (hDisc : ∀ pq ∈ cert.chart.G \ D, cert.good pq → ∀ γ ∈ F.family i pq.1,
      γ.IsIrreducible → γ.dimension = 1 →
      (∃ h : TrackD.toC pq.2 ≠ TrackD.toC pq.1,
        radialProjection (TrackD.toC pq.1) (TrackD.toC pq.2) h ∈ γ.points) →
      outerGammaInEqs i₀ cert.Eqs (TrackD.toC pq.1) γ)
    {pq : RPoint d × RPoint d} (hpq : pq ∈ cert.chart.G \ D) (hgood : cert.good pq)
    {γ : ProjectiveVariety d} (hγF : γ ∈ F.family i pq.1)
    (hγ : γ.IsIrreducible) (hγdim : γ.dimension = 1)
    (hdir : ∃ h : TrackD.toC pq.2 ≠ TrackD.toC pq.1,
      radialProjection (TrackD.toC pq.1) (TrackD.toC pq.2) h ∈ γ.points) :
    Nonempty (OuterLiftData i₀ (TrackD.toC pq.1) (TrackD.toC pq.2)
      (cert.chart.W.owner i pq.1) (cert.chart.W.owner i pq.2) γ) := by
  have hG : pq ∈ cert.chart.G := (Finset.mem_sdiff.mp hpq).1
  obtain ⟨hXi, hXd, hYi, hYd, hpX, hqY, _, _⟩ := cert.chart.owner_facts hG
  obtain ⟨_, ⟨tdata⟩⟩ := hP1 pq hG hgood _ _ rfl rfl
  have hdir' : ∃ h : TrackD.toC pq.2 ≠ TrackD.toC pq.1,
      radialProjection (TrackD.toC pq.1) (TrackD.toC pq.2) h ∈ γ.points := hdir
  exact outer_lift_curve T M k i₀ (TrackD.toC pq.1) (TrackD.toC pq.2) γ hγ hγdim hdir'
    _ _ hXi hYi hXd hYd hpX hqY cert.Eqs tdata (cert.hsmooth pq hG hgood)
    (cert.hvanish pq hG hgood) (hDisc pq hpq hgood γ hγF hγ hγdim hdir)

/-- sc:596–599 (`k = 1`): a surviving good pair whose target has a global
terminal curve is impossible; the lift is the target carrier itself, which
then projects into `C_p`, contradicting the terminal deletion. -/
theorem outer_chart_terminal_false (hk1 : k = 1)
    (cert : OuterRegularityCert T M k i j i₀ ρ ε ρ' Bdeg τ)
    (sys : @OuterTestSystem d)
    (hP1 : ∀ pq ∈ cert.chart.G, cert.good pq → ∀ X Y : AffineVariety d,
      cert.chart.W.owner i pq.1 = X → cert.chart.W.owner i pq.2 = Y →
      OuterTestsNonvanishing sys (TrackD.toC pq.1) (TrackD.toC pq.2) ∧
      Nonempty (OuterTangentData i₀ (TrackD.toC pq.1) (TrackD.toC pq.2) X Y k
        (outerLabelTangent cert.Eqs i₀ (TrackD.toC pq.1) (TrackD.toC pq.2))))
    (D : Finset (RPoint d × RPoint d))
    (hDisc : ∀ pq ∈ cert.chart.G \ D, cert.good pq → ∀ γ ∈ F.family i pq.1,
      γ.IsIrreducible → γ.dimension = 1 →
      (∃ h : TrackD.toC pq.2 ≠ TrackD.toC pq.1,
        radialProjection (TrackD.toC pq.1) (TrackD.toC pq.2) h ∈ γ.points) →
      outerGammaInEqs i₀ cert.Eqs (TrackD.toC pq.1) γ)
    (hdirfam : ∀ p ∈ cert.chart.pool.S, TrackD.IsDirectionalFamily (F.family i p))
    {pq : RPoint d × RPoint d} (hpq : pq ∈ cert.chart.G \ D) (hgood : cert.good pq)
    {Y : AffineVariety d} (hterm : T.terminal i pq.2 = some Y) : False := by
  have hG : pq ∈ cert.chart.G := (Finset.mem_sdiff.mp hpq).1
  have hsel := cert.chart.selected hG
  obtain ⟨_, _, hYi, hYd, _, _, _, hq⟩ := cert.chart.owner_facts hG
  obtain ⟨_, hdirin, _, _⟩ := hsel
  obtain ⟨hne, hz⟩ := hdirin
  simp only [TrackD.familyPoints, Set.mem_iUnion] at hz
  obtain ⟨γ, hγF, hzγ⟩ := hz
  have hpS : pq.1 ∈ cert.chart.pool.S := (cert.chart.hGmem pq hG).1
  obtain ⟨hγi, hγd, _⟩ := hdirfam pq.1 hpS γ hγF
  obtain ⟨L⟩ := outer_chart_lift cert sys hP1 D hDisc hpq hgood hγF hγi hγd ⟨hne, hzγ⟩
  -- the owner of the target is its terminal curve
  have hjd : j + 1 = d - 1 := by have := cert.chart.pool.hkj; omega
  have hqpool : pq.2 ∈ TrackD.poolPts (T.sources i ∪ T.targets i) := by
    obtain ⟨X, hX, hqX⟩ := cert.chart.W.exists_piece i hq
    exact Finset.mem_biUnion.mpr ⟨X, hX, hqX⟩
  have hownY : cert.chart.W.owner i pq.2 = Y :=
    cert.chart.W.terminal hjd i pq.2 hqpool Y hterm
  -- the lift is the whole target carrier
  obtain ⟨hCi, hCd, _, hCY⟩ := L.hC
  have hYdim : (cert.chart.W.owner i pq.2).dimension = 1 := by rw [hYd, hk1]
  have hCeq : L.C = cert.chart.W.owner i pq.2 :=
    TrackD.irreducible_subvariety_eq_of_pos_dimension_eq _ _ hCi hYi hCY
      (by rw [hYdim]; norm_num) (by rw [hCd, hYdim])
  have hterm' : T.terminal i pq.2 = some (cert.chart.W.owner i pq.2) := by
    rw [hownY]; exact hterm
  have hγfam : γ.points ⊆ TrackD.familyPoints (F.family i pq.1) := by
    intro z hz
    simp only [TrackD.familyPoints, Set.mem_iUnion]
    exact ⟨γ, hγF, hz⟩
  exact outer_terminal_curve_resolution T k hk1 i₀ i pq.1 pq.2 γ _ _ L hCeq hterm'
    (regime.P i) (F.family i) _ (cert.chart.selected hG) hγfam

/-- sc:601–651 (`k ≥ 2`): one row of a regular chart piece, after the
discard `D`, has at most `C₀·M·2E` good partners. The targets are covered by
lifts over the components `γ ⊂ C_p`; per `γ`, pooled lifts with distinct
curves have `∑ deg(C→γ) ≤ 1` (195) and `deg C ≤ 2 deg γ deg(C→γ)` (196), so
the total lift degree is `≤ 2 deg C_p ≤ 2E`; the physical curve bound (197)
finishes. -/
theorem outer_chart_row_bound (hk2 : 2 ≤ k)
    (cert : OuterRegularityCert T M k i j i₀ ρ ε ρ' Bdeg τ)
    (sys : @OuterTestSystem d)
    (hP1 : ∀ pq ∈ cert.chart.G, cert.good pq → ∀ X Y : AffineVariety d,
      cert.chart.W.owner i pq.1 = X → cert.chart.W.owner i pq.2 = Y →
      OuterTestsNonvanishing sys (TrackD.toC pq.1) (TrackD.toC pq.2) ∧
      Nonempty (OuterTangentData i₀ (TrackD.toC pq.1) (TrackD.toC pq.2) X Y k
        (outerLabelTangent cert.Eqs i₀ (TrackD.toC pq.1) (TrackD.toC pq.2))))
    (hP2 : ∀ pq ∈ cert.chart.G, cert.good pq → ∀ X Y : AffineVariety d, ∀ q' : Point d,
      cert.chart.W.owner i pq.1 = X → cert.chart.W.owner i pq.2 = Y →
      q' ∈ Y.points →
      (q' - TrackD.toC pq.1) i₀ ≠ 0 →
      (fun kk => TrackD.labelPt i₀ (TrackD.toC pq.1) q'
        (finSumFinEquiv.symm kk)) ∈ (commonProductImage i₀ X Y).points →
      OuterTestsNonvanishing sys (TrackD.toC pq.1) q' →
      Nonempty (OuterTangentData i₀ (TrackD.toC pq.1) q' X Y k
        (outerLabelTangent cert.Eqs i₀ (TrackD.toC pq.1) q')))
    (D : Finset (RPoint d × RPoint d))
    (hDisc : ∀ pq ∈ cert.chart.G \ D, cert.good pq → ∀ γ ∈ F.family i pq.1,
      γ.IsIrreducible → γ.dimension = 1 →
      (∃ h : TrackD.toC pq.2 ≠ TrackD.toC pq.1,
        radialProjection (TrackD.toC pq.1) (TrackD.toC pq.2) h ∈ γ.points) →
      outerGammaInEqs i₀ cert.Eqs (TrackD.toC pq.1) γ)
    (hdirfam : ∀ p ∈ cert.chart.pool.S, TrackD.IsDirectionalFamily (F.family i p))
    (E : ℝ) (hE0 : 0 ≤ E)
    (hE : ∀ p ∈ cert.chart.pool.S,
      ((ProjectiveFamily.degree (F.family i p) : ℚ) : ℝ) ≤ E)
    (C0 : ℝ) (hC0 : 0 ≤ C0)
    (hcurve : ∀ Y : AffineVariety d, TrackD.IsCurve Y →
      (TrackD.massOn (regime.P i) Y.points : ℝ) ≤
        C0 * ((Y.degree : ℚ) : ℝ) * TrackD.cfgM (regime.P i))
    (hGP : ∀ pq ∈ cert.chart.G, pq.2 ∈ regime.P i)
    (p : RPoint d) :
    (((cert.chart.G \ D).filter (fun pq => cert.good pq ∧ pq.1 = p)).card : ℝ) ≤
      C0 * TrackD.cfgM (regime.P i) * (2 * E) := by
  set rows := (cert.chart.G \ D).filter (fun pq => cert.good pq ∧ pq.1 = p) with hrows
  have hM0 : 0 ≤ TrackD.cfgM (regime.P i) := by unfold TrackD.cfgM; positivity
  rcases rows.eq_empty_or_nonempty with hemp | ⟨pq0, hpq0⟩
  · rw [hemp, Finset.card_empty, Nat.cast_zero]; positivity
  have hpS : p ∈ cert.chart.pool.S := by
    obtain ⟨hmem, _, h1⟩ := Finset.mem_filter.mp hpq0
    have := (cert.chart.hGmem pq0 (Finset.mem_sdiff.mp hmem).1).1
    rwa [h1] at this
  set X := cert.chart.W.owner i p with hXdef
  set Cf := F.family i p with hCfdef
  set Q := rows.image Prod.snd with hQdef
  have hQ : ∀ q ∈ Q, (p, q) ∈ rows := by
    intro q hq
    obtain ⟨pq, hpq, rfl⟩ := Finset.mem_image.mp hq
    have h1 := (Finset.mem_filter.mp hpq).2.2
    have : pq = (p, pq.2) := Prod.ext h1 rfl
    rw [← this]; exact hpq
  have hrowsQ : rows.card = Q.card := by
    rw [hQdef, Finset.card_image_of_injOn]
    intro a ha b hb hab
    have ha1 := (Finset.mem_filter.mp ha).2.2
    have hb1 := (Finset.mem_filter.mp hb).2.2
    exact Prod.ext (ha1.trans hb1.symm) hab
  have hQmem : ∀ q ∈ Q, (p, q) ∈ cert.chart.G \ D ∧ cert.good (p, q) := fun q hq =>
    ⟨(Finset.mem_filter.mp (hQ q hq)).1, (Finset.mem_filter.mp (hQ q hq)).2.1⟩
  have hQG : ∀ q ∈ Q, (p, q) ∈ cert.chart.G := fun q hq =>
    (Finset.mem_sdiff.mp (hQmem q hq).1).1
  have hpq0G : pq0 ∈ cert.chart.G := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hpq0).1).1
  have hpq01 : pq0.1 = p := (Finset.mem_filter.mp hpq0).2.2
  obtain ⟨hXi, hXd, _, _, hpX, _, hpW, _⟩ := cert.chart.owner_facts hpq0G
  rw [hpq01] at hXi hXd hpX hpW
  -- the lifts
  let dirIn : RPoint d → ProjectiveVariety d → Prop := fun q γ =>
    ∃ h : TrackD.toC q ≠ TrackD.toC p, radialProjection (TrackD.toC p) (TrackD.toC q) h ∈ γ.points
  have hlift : ∀ (q : RPoint d) (γ : ProjectiveVariety d), ∃ (C : AffineVariety d) (r : ℕ),
      q ∈ Q → γ ∈ Cf → dirIn q γ →
        (C.IsIrreducible ∧ C.dimension = 1 ∧ TrackD.toC q ∈ C.points ∧
          C.Subvariety (cert.chart.W.owner i q)) ∧
        (radialImage (TrackD.toC p) C).points ⊆ γ.points ∧
        GenericallyFiniteRadialDegree (TrackD.toC p) C r := by
    intro q γ
    by_cases h : q ∈ Q ∧ γ ∈ Cf ∧ dirIn q γ
    · obtain ⟨hq, hγ, hdir⟩ := h
      obtain ⟨hγi, hγd, _⟩ := hdirfam p hpS γ hγ
      obtain ⟨L⟩ := outer_chart_lift cert sys hP1 D hDisc (hQmem q hq).1 (hQmem q hq).2
        hγ hγi hγd hdir
      exact ⟨L.C, L.r, fun _ _ _ => ⟨L.hC, L.hproj, L.hdeg⟩⟩
    · exact ⟨AffineVariety.whole, 0, fun hq hγ hd => absurd ⟨hq, hγ, hd⟩ h⟩
  choose LC Lr hL using hlift
  let Qγ : ProjectiveVariety d → Finset (RPoint d) := fun γ => Q.filter (fun q => dirIn q γ)
  let Csγ : ProjectiveVariety d → Finset (AffineVariety d) := fun γ =>
    (Qγ γ).image (fun q => LC q γ)
  let Cs : Finset (AffineVariety d) := Cf.biUnion Csγ
  have hCsγ : ∀ γ ∈ Cf, ∀ C ∈ Csγ γ, ∃ q ∈ Q, dirIn q γ ∧ LC q γ = C := by
    intro γ _ C hC
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hC
    exact ⟨q, (Finset.mem_filter.mp hq).1, (Finset.mem_filter.mp hq).2, rfl⟩
  have hCs : ∀ C ∈ Cs, C.IsIrreducible ∧ C.dimension = 1 := by
    intro C hC
    obtain ⟨γ, hγ, hCγ⟩ := Finset.mem_biUnion.mp hC
    obtain ⟨q, hq, hdq, rfl⟩ := hCsγ γ hγ C hCγ
    exact ⟨(hL q γ hq hγ hdq).1.1, (hL q γ hq hγ hdq).1.2.1⟩
  -- per-component degree bound
  have key : ∀ γ ∈ Cf, ∑ C ∈ Csγ γ, C.degree ≤ 2 * γ.degree := by
    intro γ hγ
    obtain ⟨hγi, hγd, _⟩ := hdirfam p hpS γ hγ
    let rep : AffineVariety d → RPoint d := fun C =>
      if h : ∃ q ∈ Qγ γ, LC q γ = C then Classical.choose h else p
    have hrep : ∀ C ∈ Csγ γ, rep C ∈ Qγ γ ∧ LC (rep C) γ = C := by
      intro C hC
      have h : ∃ q ∈ Qγ γ, LC q γ = C := Finset.mem_image.mp hC
      simp only [rep, dif_pos h]
      exact Classical.choose_spec h
    set R := (Csγ γ).image rep with hRdef
    have hRinj : Set.InjOn rep (Csγ γ) := fun C₁ h₁ C₂ h₂ he => by
      rw [← (hrep C₁ h₁).2, ← (hrep C₂ h₂).2]
      exact congrArg (fun q => LC q γ) he
    have hsumR : ∑ C ∈ Csγ γ, C.degree = ∑ q ∈ R, (LC q γ).degree := by
      rw [hRdef, Finset.sum_image hRinj]
      exact Finset.sum_congr rfl fun C hC => by rw [(hrep C hC).2]
    have hcond : ∀ q ∈ R, q ∈ Q ∧ γ ∈ Cf ∧ dirIn q γ := by
      intro q hq
      obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hq
      have h := (hrep C hC).1
      exact ⟨(Finset.mem_filter.mp h).1, hγ, (Finset.mem_filter.mp h).2⟩
    let mkB : {q // q ∈ R} → OuterLiftBundle i₀ (TrackD.toC p) X γ := fun q =>
      ⟨TrackD.toC q.1, cert.chart.W.owner i q.1,
        { C := LC q.1 γ, r := Lr q.1 γ,
          hC := (hL q.1 γ (hcond q.1 q.2).1 (hcond q.1 q.2).2.1 (hcond q.1 q.2).2.2).1
          hproj := (hL q.1 γ (hcond q.1 q.2).1 (hcond q.1 q.2).2.1 (hcond q.1 q.2).2.2).2.1
          hdeg := (hL q.1 γ (hcond q.1 q.2).1 (hcond q.1 q.2).2.1 (hcond q.1 q.2).2.2).2.2 }⟩
    have hmkB_inj : Function.Injective mkB := by
      intro a b h
      have : TrackD.toC a.1 = TrackD.toC b.1 := congrArg OuterLiftBundle.q h
      exact Subtype.ext (profile_toC_injective this)
    have hRrep : ∀ q ∈ R, rep (LC q γ) = q := by
      intro q hq
      obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hq
      rw [(hrep C hC).2]
    have h195 := outer_lift_map_degree T k hk2 i₀ (TrackD.toC p) γ hγi hγd X hpX cert.Eqs
      (R.attach.image mkB)
      (by
        intro l₁ hl₁ l₂ hl₂ hC
        obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hl₁
        obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hl₂
        have hC' : LC a.1 γ = LC b.1 γ := hC
        have : a.1 = b.1 := by rw [← hRrep a.1 a.2, ← hRrep b.1 b.2, hC']
        rw [Subtype.ext this])
      (by
        intro l hl
        obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hl
        exact cert.chart.hchart (p, a.1) (hQG a.1 (hcond a.1 a.2).1))
      sys
      (by
        intro l hl
        obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hl
        exact (hP1 (p, a.1) (hQG a.1 (hcond a.1 a.2).1) (hQmem a.1 (hcond a.1 a.2).1).2
          _ _ rfl rfl).1)
      (by
        intro l hl q' hq' hch hlab hnz
        obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hl
        exact hP2 (p, a.1) (hQG a.1 (hcond a.1 a.2).1) (hQmem a.1 (hcond a.1 a.2).1).2
          _ _ q' rfl rfl hq' hch hlab hnz)
    have hsum_r : ∑ l ∈ R.attach.image mkB, l.lift.r = ∑ q ∈ R, Lr q γ := by
      rw [Finset.sum_image (fun a _ b _ h => hmkB_inj h)]
      exact Finset.sum_attach R (fun q => Lr q γ)
    have hreg := fun q (hq : q ∈ R) =>
      outer_carrier_regular T M cert.chart.W k i p X hpW ⟨hXi, hXd⟩ hpX rfl
    have h196 : ∀ q ∈ R, (LC q γ).degree ≤ 2 * γ.degree * (Lr q γ : ℚ) := by
      intro q hq
      obtain ⟨hqQ, _, hdq⟩ := hcond q hq
      obtain ⟨⟨hCi, hCd, hqC, hCY⟩, hproj, hdeg⟩ := hL q γ hqQ hγ hdq
      obtain ⟨_, _, hYi, hYd, _, _, _, hqW⟩ := cert.chart.owner_facts (hQG q hqQ)
      obtain ⟨hsm, huniq⟩ := hreg q hq
      obtain ⟨_, ⟨tdata⟩⟩ := hP1 (p, q) (hQG q hqQ) (hQmem q hqQ).2 _ _ rfl rfl
      have htan : TrackD.toC q - TrackD.toC p ∉ X.tangentSpace (TrackD.toC p) := by
        rw [← tdata.hTX]; exact tdata.hsrc
      obtain ⟨himg, himgdeg⟩ := outer_projection_image_bounds (TrackD.toC p) (LC q γ) γ
        ⟨hCi, hCd⟩ ⟨hγi, hγd⟩ hproj (Lr q γ) hdeg
      exact outer_lift_degree_bound (LC q γ) X (cert.chart.W.owner i q) (TrackD.toC p)
        (TrackD.toC q) γ hCi hCd hqC hCY
        (fun hpC => huniq _ (cert.chart.W.owner_poolCarrier i hqW).1 hYi hYd
          (outer_subvariety_points hCY hpC))
        hsm htan (Lr q γ) hdeg himg himgdeg
    have hγ0 : 0 ≤ γ.degree := projective_degree_nonneg γ
    have hr1 : ((∑ q ∈ R, Lr q γ : ℕ) : ℚ) ≤ 1 := by
      rw [← hsum_r]; exact_mod_cast h195
    calc ∑ C ∈ Csγ γ, C.degree = ∑ q ∈ R, (LC q γ).degree := hsumR
      _ ≤ ∑ q ∈ R, 2 * γ.degree * (Lr q γ : ℚ) := Finset.sum_le_sum h196
      _ = 2 * γ.degree * ((∑ q ∈ R, Lr q γ : ℕ) : ℚ) := by
          rw [Nat.cast_sum, Finset.mul_sum]
      _ ≤ 2 * γ.degree * 1 := by gcongr
      _ = 2 * γ.degree := mul_one _
  have hDtotQ : ∑ C ∈ Cs, C.degree ≤ 2 * ProjectiveFamily.degree Cf := by
    calc ∑ C ∈ Cs, C.degree ≤ ∑ γ ∈ Cf, ∑ C ∈ Csγ γ, C.degree := by
          apply outer_sum_biUnion_le_of_nonneg
          intro γ hγ C hC
          obtain ⟨q, hq, hdq, rfl⟩ := hCsγ γ hγ C hC
          exact outer_affine_degree_nonneg (hL q γ hq hγ hdq).1.1
      _ ≤ ∑ γ ∈ Cf, 2 * γ.degree := Finset.sum_le_sum key
      _ = 2 * ProjectiveFamily.degree Cf := by
          rw [ProjectiveFamily.degree, Finset.mul_sum]
  have hDtot : ∑ C ∈ Cs, ((C.degree : ℚ) : ℝ) ≤ 2 * E := by
    have h := hE p hpS
    have h' : ((∑ C ∈ Cs, C.degree : ℚ) : ℝ) ≤ ((2 * ProjectiveFamily.degree Cf : ℚ) : ℝ) :=
      by exact_mod_cast hDtotQ
    push_cast at h'
    linarith
  -- the row count
  have hcover : ∀ q ∈ Q, ∃ C ∈ Cs, TrackD.toC q ∈ C.points := by
    intro q hq
    have hsel := cert.chart.selected (hQG q hq)
    obtain ⟨_, ⟨hne, hz⟩, _, _⟩ := hsel
    simp only [TrackD.familyPoints, Set.mem_iUnion] at hz
    obtain ⟨γ, hγ, hzγ⟩ := hz
    have hdq : dirIn q γ := ⟨hne, hzγ⟩
    refine ⟨LC q γ, Finset.mem_biUnion.mpr ⟨γ, hγ, ?_⟩, (hL q γ hq hγ hdq).1.2.2.1⟩
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hq, hdq⟩)
  have hsample : ∀ C ∈ Cs, ((Q.filter (fun q => TrackD.toC q ∈ C.points)).card : ℝ) ≤
      C0 * ((C.degree : ℚ) : ℝ) * TrackD.cfgM (regime.P i) := by
    intro C hC
    refine le_trans ?_ (hcurve C (hCs C hC))
    unfold TrackD.massOn
    exact_mod_cast Finset.card_le_card (fun q hq => by
      obtain ⟨hqQ, hqC⟩ := Finset.mem_filter.mp hq
      exact Finset.mem_filter.mpr ⟨hGP (p, q) (hQG q hqQ), hqC⟩)
  have h197 := outer_row_sparse Q Cs hcover hCs (2 * E) hDtot C0 (TrackD.cfgM (regime.P i))
    hC0 hM0 hsample
  rw [hrowsQ]
  exact h197

end
end
end DistinctDistances.SparseCones
