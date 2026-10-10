import DistinctDistances.TrackE.CoveringEnvelopeInputs

/-! Complete covering-envelope component bounds and exclusion of actual labels
on larger components, sparse-cones.tex:809–857. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- sc:u-final-curve.whole-envelope-rank: the complete component group has
lower rank at L; every physical subrow on it has the corresponding earlier
Hilbert upper bound. Both compare to the original covering family's degree. -/
theorem covering_envelope_component_rank (d : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (C : ProjectiveFamily.Family d)
      (hC : TrackD.IsDirectionalFamily C) (L : ℕ) (hL : 1 ≤ L)
      (G : CoveringEnvelopeComponents C L) (h : ℕ),
      c * (ProjectiveFamily.degree (envelopeDimensionPart G.components h) : ℝ) * (L : ℝ)^h ≤
        (ProjectiveFamily.degree C : ℝ) * (L + 1 : ℝ) ∧
      ∀ (p : Point d) (Q : Finset (RPoint d)), rowDirections p Q ⊆
        (ProjectiveFamily.locus (envelopeDimensionPart G.components h)).points → ∀ E : ℕ,
        (rowDirectionRank p Q E : ℝ) ≤
          (ProjectiveFamily.degree (envelopeDimensionPart G.components h) : ℝ) * ((E+h).choose h : ℝ) := by
  classical
  obtain ⟨c, hc, hlow⟩ := TrackA.poly_hilbert_projective_at_L d
  have hcR : 0 < (c : ℝ) := by exact_mod_cast hc
  refine ⟨(c : ℝ), hcR, ?_⟩
  intro C hC L hL G h
  let V := envelopeDimensionPart G.components h
  have hpure : ProjectiveFamily.IsPure V h := by
    intro W hW
    obtain ⟨hWG, hdim⟩ := Finset.mem_filter.mp hW
    exact ⟨(G.spec W hWG).1, hdim⟩
  have hdefined : ProjectiveFamily.ComponentsDefinedInDegree V L := by
    obtain ⟨E, hE, hcomp⟩ := G.defined
    refine ⟨E, hE, ?_⟩
    intro W hW
    exact hcomp W (Finset.mem_filter.mp hW).1
  have hlists : TrackA.FromProjectiveLists V L := by
    refine ⟨1, fun _ => V, fun _ => L, ?_⟩
    constructor
    · intro a
      exact ⟨hL, hdefined⟩
    constructor
    · intro W
      simp
    · simp
  have hVenv : ∀ W ∈ V, W.Subvariety (coveringDirectionEnvelope C L) := by
    intro W hW
    change (coveringDirectionEnvelope C L).ideal ≤ W.ideal
    rw [← G.locus, ← ProjectiveVariety.vanishingIdeal_points,
      ← ProjectiveVariety.vanishingIdeal_points W]
    apply MvPolynomial.vanishingIdeal_anti_mono (k := ℂ)
    rintro v ⟨hv, hpW⟩
    refine ⟨hv, ?_⟩
    rw [ProjectiveFamily.points_locus]
    exact Set.mem_iUnion.mpr ⟨W, Set.mem_iUnion.mpr
      ⟨(Finset.mem_filter.mp hW).1, hpW⟩⟩
  have hlower := hlow V h L hpure hL hlists
  have hmono := projective_family_hilbert_mono V (coveringDirectionEnvelope C L) hVenv L
  rw [covering_direction_envelope_rank] at hmono
  have hCpure : ProjectiveFamily.IsPure C 1 :=
    fun W hW => ⟨(hC W hW).1, (hC W hW).2.1⟩
  have hupperC := TrackA.poly_hilbert_projective_upper C 1 hCpure L
  have hupperCQ : (ProjectiveFamily.hilbert C L : ℚ) ≤
      ProjectiveFamily.degree C * (L + 1 : ℚ) := by simpa using hupperC
  have hupperCR : (ProjectiveFamily.hilbert C L : ℝ) ≤
      (ProjectiveFamily.degree C : ℝ) * (L + 1 : ℝ) := by exact_mod_cast hupperCQ
  have hlowerR : (c : ℝ) * (ProjectiveFamily.degree V : ℝ) * (L : ℝ)^h ≤
      (ProjectiveFamily.hilbert V L : ℝ) := by exact_mod_cast hlower
  have hmonoR : (ProjectiveFamily.hilbert V L : ℝ) ≤
      (ProjectiveFamily.hilbert C L : ℝ) := by exact_mod_cast hmono
  refine ⟨hlowerR.trans (hmonoR.trans hupperCR), ?_⟩
  intro p Q hQ E
  have hpoint := row_direction_rank_le p Q (ProjectiveFamily.locus V) hQ E
  have hupper := TrackA.poly_hilbert_projective_upper V h hpure E
  have hupperR : (ProjectiveFamily.hilbert V E : ℝ) ≤
      (ProjectiveFamily.degree V : ℝ) * ((E+h).choose h : ℝ) := by exact_mod_cast hupper
  exact (show (rowDirectionRank p Q E : ℝ) ≤ (ProjectiveFamily.hilbert V E : ℝ) by
    exact_mod_cast hpoint).trans hupperR

/-- sc:last-family-degree: every one-dimensional component is retained,
including unrepresented components. Its defining equations and total degree
are suitable for whole-family regularity. -/
theorem covering_envelope_curve_family (d : ℕ) :
    ∃ Cf : ℝ, 0 < Cf ∧ ∀ (C : ProjectiveFamily.Family d)
      (hC : TrackD.IsDirectionalFamily C) (L : ℕ) (hL : 1 ≤ L)
      (G : CoveringEnvelopeComponents C L),
      ProjectiveFamily.IsPure (envelopeDimensionPart G.components 1) 1 ∧
      TrackA.FromProjectiveLists (envelopeDimensionPart G.components 1) L ∧
      (ProjectiveFamily.degree (envelopeDimensionPart G.components 1) : ℝ) ≤
        Cf * (ProjectiveFamily.degree C : ℝ) := by
  classical
  obtain ⟨c, hc, hbounds⟩ := covering_envelope_component_rank d
  refine ⟨2 / c, by positivity, ?_⟩
  intro C hC L hL G
  let V := envelopeDimensionPart G.components 1
  have hpure : ProjectiveFamily.IsPure V 1 := by
    intro W hW
    obtain ⟨hWG, hdim⟩ := Finset.mem_filter.mp hW
    exact ⟨(G.spec W hWG).1, hdim⟩
  have hdefined : ProjectiveFamily.ComponentsDefinedInDegree V L := by
    obtain ⟨E, hE, hcomp⟩ := G.defined
    refine ⟨E, hE, ?_⟩
    intro W hW
    exact hcomp W (Finset.mem_filter.mp hW).1
  have hlists : TrackA.FromProjectiveLists V L := by
    refine ⟨1, fun _ => V, fun _ => L, ?_⟩
    constructor
    · intro a
      exact ⟨hL, hdefined⟩
    constructor
    · intro W
      simp
    · simp
  refine ⟨hpure, hlists, ?_⟩
  have hdegreeQ : 0 ≤ ProjectiveFamily.degree C := by
    unfold ProjectiveFamily.degree
    exact Finset.sum_nonneg (fun W _ => projective_degree_nonneg W)
  have hdegreeR : 0 ≤ (ProjectiveFamily.degree C : ℝ) := by exact_mod_cast hdegreeQ
  have hLreal : 1 ≤ (L : ℝ) := by exact_mod_cast hL
  have hLpos : 0 < (L : ℝ) := by linarith
  have hlow := (hbounds C hC L hL G 1).1
  simp only [pow_one] at hlow
  have htwo : (ProjectiveFamily.degree C : ℝ) * (L + 1 : ℝ) ≤
      (2 * (ProjectiveFamily.degree C : ℝ)) * (L : ℝ) := by nlinarith
  have hcancel : c * (ProjectiveFamily.degree V : ℝ) ≤
      2 * (ProjectiveFamily.degree C : ℝ) :=
    le_of_mul_le_mul_right (hlow.trans htwo) hLpos
  calc
    _ ≤ (2 * (ProjectiveFamily.degree C : ℝ)) / c :=
      (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hcancel)
    _ = _ := by ring

/-- sc:u-final-curve.large: a preceding strict physical-row margin rules out
a positive density of actual labels on any larger component of Env(C_p).
The same batch survives, and every envelope and physical row is adaptive.
The endpoint gap is fixed before the density quantifier. -/
theorem covering_envelope_large_labels_small {α : Type*} [Fintype α]
    {F : ConeCoverageSequence regime} {T : SelectedProfileSequence F}
    (S : LimitingSeparatedProfile regime)
    {plateau : α → ProfilePlateau S} {kind : α → DepthRateKind} {ε : α → ℝ}
    (H : ProfileDepthBatchData T S plateau kind ε)
    (u : ProfilePlateau S) (hu : u.val.val + 1 = d)
    (a b₀ κ m : ℝ) (hm : 0 < m)
    (ha : a ≤ profilePlateauLeft S u) (hκ : profilePlateauLeft S u - a ≤ κ)
    (hb₀ : profilePlateauLeft S u < b₀ ∧ b₀ < S.b u.val)
    (hcluster : (d : ℝ) * κ ≤ m / 4)
    (hendpoint : (d : ℝ) * (profileLastTime S - b₀) < m / 4)
    (hrank : DirectionRowRankMargin H a m) :
    ∀ ρ : ℝ, 0 < ρ → ∀ᶠ i in atTop,
      ∀ p ∈ regime.P i, ∀ Q : Finset (RPoint d),
        DenseSurvivingDirectionRow H i (TrackD.toC p) Q 0 →
      ∀ G : CoveringEnvelopeComponents (F.family i p)
        ⌊TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width b₀⌋₊,
        ((coveringEnvelopeLargeLabels G (TrackD.toC p) Q).card : ℝ) ≤
          ρ * (((S.sequence.target i).pts.image TrackD.toC).card : ℝ) := by
  classical
  obtain ⟨c, hc, hbounds⟩ := covering_envelope_component_rank d
  let c' : ℝ := c / (4 : ℝ)^d
  have hc' : 0 < c' := by dsimp [c']; positivity
  have hmquarter : 0 < m / 4 := by positivity
  have hmhalf : 0 < m / 2 := by positivity
  have hindex : u.val.val = d - 1 := by omega
  have hfin : u.val = (⟨d - 1, by have := regime.dimension_ge_three; omega⟩ : Fin d) :=
    Fin.ext hindex
  have huLast : S.b u.val = profileLastTime S := by
    simpa only [profileLastTime] using congrArg S.b hfin
  obtain ⟨hz, hb⟩ := limiting_plateau_boundary S u b₀ hb₀
  intro ρ hρ
  let ρ' : ℝ := ρ / (d + 1 : ℝ)
  have hρ' : 0 < ρ' := by dsimp [ρ']; positivity
  filter_upwards [hrank ρ' hρ', target_test_degree S a, target_test_degree S b₀,
    target_absorb_lower_constant S c' (m / 4) hc' hmquarter,
    endpoint_rank_target_dominates_cones F S 1 (m / 2) b₀ (by norm_num) hmhalf
      (by simpa only [huLast] using hb₀.2) (by linarith)]
    with i hprior htesta htestb hconstant hdominates
  intro p hpP Q hrow G
  by_contra hnot
  have hlarge : ρ * (((S.sequence.target i).pts.image TrackD.toC).card : ℝ) ≤
      ((coveringEnvelopeLargeLabels G (TrackD.toC p) Q).card : ℝ) :=
    (lt_of_not_ge hnot).le
  obtain ⟨h, hh2, hhd, Q', hQ'large, hcard, hdirs⟩ :=
    covering_large_labels_dimension_group (by have := regime.dimension_ge_three; omega)
      G (TrackD.toC p) Q
  have hQ'Q : Q' ⊆ Q := hQ'large.trans (Finset.filter_subset _ _)
  have hQ'mass : ρ' * (((S.sequence.target i).pts.image TrackD.toC).card : ℝ) ≤ Q'.card := by
    have htotal := hlarge.trans hcard
    change (ρ / (d + 1 : ℝ)) *
      (((S.sequence.target i).pts.image TrackD.toC).card : ℝ) ≤ Q'.card
    calc
      _ = (ρ * (((S.sequence.target i).pts.image TrackD.toC).card : ℝ)) /
          (d + 1 : ℝ) := by ring
      _ ≤ _ := (div_le_iff₀ (by positivity)).mpr
        (by simpa only [mul_comm] using htotal)
  obtain ⟨hp, htypical, hQ, hneq, hsurvives, _⟩ := hrow
  have hrow' : DenseSurvivingDirectionRow H i (TrackD.toC p) Q' ρ' :=
    ⟨hp, htypical, hQ'Q.trans hQ, fun q hq => hneq q (hQ'Q hq),
      fun q hq => hsurvives q (hQ'Q hq), hQ'mass⟩
  let x := TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width b₀
  let y := TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width a
  let L : ℕ := ⌊x⌋₊
  let E : ℕ := ⌊y⌋₊
  let V : ℝ := (ProjectiveFamily.degree (F.family i p) : ℝ) * (L + 1 : ℝ)
  have hL : 1 ≤ L := (Nat.le_floor_iff' (by decide : (1 : ℕ) ≠ 0)).mpr
    (by simpa only [Nat.cast_one] using htestb)
  have hdegreeQ : 0 ≤ ProjectiveFamily.degree (F.family i p) := by
    unfold ProjectiveFamily.degree
    exact Finset.sum_nonneg (fun W _ => projective_degree_nonneg W)
  have hdegreeR : 0 ≤ (ProjectiveFamily.degree (F.family i p) : ℝ) := by
    exact_mod_cast hdegreeQ
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hparts := hbounds (F.family i p) (F.directional i p hpP) L hL G h
  have hupper := hparts.2 (TrackD.toC p) Q' hdirs E
  have hborrow : c * (rowDirectionRank (TrackD.toC p) Q' E : ℝ) * (L : ℝ)^h ≤
      V * ((E+h).choose h : ℝ) := by
    calc
      _ ≤ c * ((ProjectiveFamily.degree (envelopeDimensionPart G.components h) : ℝ) *
          ((E+h).choose h : ℝ)) * (L : ℝ)^h :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hupper hc.le)
          (pow_nonneg (Nat.cast_nonneg _) _)
      _ = (c * (ProjectiveFamily.degree (envelopeDimensionPart G.components h) : ℝ) *
          (L : ℝ)^h) * ((E+h).choose h : ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hparts.1 (Nat.cast_nonneg _)
  have hcompare : c' * (rowDirectionRank (TrackD.toC p) Q' E : ℝ) * (x / y)^h ≤ V :=
    borrowed_floor_growth d h hhd c (rowDirectionRank (TrackD.toC p) Q' E) V x y
      hc.le (Nat.cast_nonneg _) hV htestb htesta hborrow
  have hstart := hprior (TrackD.toC p) Q' hrow'
  have hstep := direction_target_propagate_step (regime.B_pos i) (regime.A_pos i)
    (S.sequence.width_pos i).2.le ha hb₀.1.le hκ S.b u.val.val h u.val.isLt.le
    (by omega) hz hb hconstant hstart (by
      simpa only [E, x, y, TrackD.cfgB, Regime.B, Regime.N] using hcompare)
  have hstep' : profileDirectionRankTarget S i b₀ *
      Real.exp ((m - m / 4 - (d : ℝ) * κ) * (S.sequence.target i).width) ≤ V := by
    simpa only [profileDirectionRankTarget, TrackD.cfgB, Regime.B, Regime.N] using hstep
  have htarget : 0 ≤ profileDirectionRankTarget S i b₀ := by
    unfold profileDirectionRankTarget
    exact div_nonneg
      (mul_nonneg (TrackD.RankCore.sigma_nonneg (regime.B_pos i).le _ _ _)
        (TrackD.RankCore.testDeg_pos (regime.B_pos i) _ _).le) (regime.A_pos i).le
  have hlower : profileDirectionRankTarget S i b₀ *
      Real.exp ((m / 2) * (S.sequence.target i).width) ≤ V :=
    (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith)
        (S.sequence.width_pos i).2.le)) htarget).trans hstep'
  have hfloor : (L : ℝ) ≤ x := Nat.floor_le (by dsimp [x]; linarith)
  have hupperV : V ≤ (F.delta i * regime.N i / regime.A i) * (x + 1) := by
    calc
      _ ≤ (ProjectiveFamily.degree (F.family i p) : ℝ) * (x + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) hdegreeR
      _ ≤ _ := mul_le_mul_of_nonneg_right (F.degree i p hpP) (by dsimp [x]; linarith)
  have hstrict : V < profileDirectionRankTarget S i b₀ *
      Real.exp ((m / 2) * (S.sequence.target i).width) :=
    hupperV.trans_lt (by simpa only [one_mul, x] using hdominates)
  exact (not_lt_of_ge hlower) hstrict

end
end DistinctDistances.SparseCones
