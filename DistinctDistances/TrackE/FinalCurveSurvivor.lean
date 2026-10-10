import DistinctDistances.TrackE.FinalCurveIdentification

/-! Combine all final losses on an original terminal-selected physical row,
sparse-cones.tex:849–928. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section

/-- sc:u-final-curve.survivor: the fixed narrow batch and its later homogeneous
certificates leave an original terminal-selected edge whose unchanged owner
projects into its original covering family. All four removals count physical
labels and follow the same earlier depth deletion and owner assignment. -/
theorem final_narrow_regular_row_survives {n : ℕ} {regime : Regime (n + 1)}
    {F : ConeCoverageSequence regime} (T : SelectedProfileSequence F)
    (S : LimitingSeparatedProfile regime) [Fintype (ProfilePlateau S)]
    (hsource : ∀ i, T.sources i = {S.sequence.source i})
    (htarget : ∀ i, T.targets i = {S.sequence.target i})
    (K : FinalNarrowBatchData T S)
    (G : ∀ i (p : RPoint (n + 1)), CoveringEnvelopeComponents (F.family i p)
      (finalNarrowTestDegree K K.b₀ i))
    (badFamily : ℕ → Point (n + 1) → ProjectiveFamily.Family (n + 1))
    (E : ℕ → Point (n + 1) → List (Poly (n + 1)))
    (g : ℕ → Point (n + 1) → Poly (n + 1)) (Creg : ℕ)
    (hcert : ∀ᶠ i in atTop, ∀ p ∈ (S.sequence.source i).pts,
      TrackD.toC p ∉ K.H.batch.badCenters i →
      HomogeneousCurveRegularityCertificate (envelopeDimensionPart (G i p).components 1)
        (badFamily i (TrackD.toC p)) (E i (TrackD.toC p)) (g i (TrackD.toC p))
        Creg (finalNarrowTestDegree K K.b_eq i))
    (hmass : let D := K.H.data K.finalPlateau
      Framework.UniformLittleO
        (fun i => {p : Point (n + 1) // p ∈ D.centers i ∧ p ∉ K.H.batch.badCenters i})
        (fun i p => (((D.targets i).filter (fun q => D.owner i q ∈
          exceptional_carriers D i (K.H.batch.bad K.finalPlateau i) p.val
            (badFamily i p.val))).card : ℝ))
        (fun i _ => (D.targets i).card)) :
    ∀ᶠ i in atTop, ∃ p ∈ regime.P i, ∃ q,
      (p, q) ∈ profileBatchGraph K.H i ∧
      TrackD.ProjectsInto (F.family i p) p
        ((K.H.data K.finalPlateau).owner i (TrackD.toC q)) := by
  classical
  let D := K.H.data K.finalPlateau
  have hfrom : DepthFromProfile S D := K.H.from_profile K.finalPlateau
  obtain ⟨hgraph, _, _⟩ := selected_profile_batch_graph T S hsource htarget K.H
  have hρ : 0 < (1 / 64 : ℝ) := by norm_num
  have hrowρ : 0 < (1 / 8 : ℝ) := by norm_num
  have htestTime : profilePlateauLeft S K.finalPlateau < K.b_test ∧
      K.b_test < S.b K.finalPlateau.val :=
    ⟨lt_trans K.plateau_time.1 (lt_trans K.reserved_times.1 K.reserved_times.2.1),
      K.reserved_times.2.2⟩
  filter_upwards [hgraph, hcert, hmass (1 / 64) hρ,
    covering_projection_failures_small S K.finalPlateau D hfrom K.b₀ K.plateau_time (1 / 64) hρ,
    final_narrow_large_labels_small K (1 / 64) hρ,
    final_homogeneous_minor_zeros_small S K.finalPlateau D hfrom K.b_eq K.b_test
      K.reserved_times.2.1.le htestTime (1 / 64) hρ,
    covering_retained_curve_members S K.H K.finalPlateau K.final_index K.b₀]
      with i hgraph_i hcert_i hmass_i hcapture_i hlarge_i hzero_i hmembers_i
  let X := (S.sequence.source i).pts
  let Y := (S.sequence.target i).pts
  let Γ := profileBatchGraph K.H i
  have hN : 0 < TrackD.cfgN (regime.P i) := by
    simpa only [TrackD.cfgN, Regime.N] using regime.N_pos i
  have hXpos : 0 < (X.card : ℝ) :=
    (mul_pos hN (Real.exp_pos _)).trans_le (S.sequence.base_good i).1.size
  have hYpos : 0 < (Y.card : ℝ) :=
    (mul_pos hN (Real.exp_pos _)).trans_le (S.sequence.base_good i).2.size
  have hX : X.Nonempty := Finset.card_pos.mp (by exact_mod_cast hXpos)
  have hY : Y.Nonempty := Finset.card_pos.mp (by exact_mod_cast hYpos)
  have hΓ : Γ ⊆ X ×ˢ Y := by
    intro pq hpq
    have hterminal := (Finset.mem_filter.mp hpq).1
    obtain ⟨hp, hq, _, _, _⟩ := (mem_terminalSelectedGraph T i pq.1 pq.2).mp hterminal
    exact Finset.mem_product.mpr
      ⟨by simpa only [hsource i, TrackD.poolPts, Finset.singleton_biUnion] using hp,
        by simpa only [htarget i, TrackD.poolPts, Finset.singleton_biUnion] using hq⟩
  have hgraph' : (1 / 8 : ℝ) * (X.card : ℝ) * Y.card ≤ Γ.card := by
    simpa only [Finset.card_image_of_injective _ profile_toC_injective] using hgraph_i
  obtain ⟨p, hpX, hrowDense⟩ :=
    exists_dense_physical_graph_row X Y Γ hΓ hX hY (1 / 8) hrowρ hgraph'
  let Q := Y.filter (fun q => (p, q) ∈ Γ)
  change (1 / 8 : ℝ) * Y.card ≤ Q.card at hrowDense
  have hQnonempty : Q.Nonempty := Finset.card_pos.mp (by
    exact_mod_cast (mul_pos hrowρ hYpos).trans_le hrowDense)
  have hedges : ∀ q ∈ Q, (p, q) ∈ profileBatchGraph K.H i :=
    fun q hq => (Finset.mem_filter.mp hq).2
  have hrowDenseC : (1 / 8 : ℝ) *
      (((S.sequence.target i).pts.image TrackD.toC).card : ℝ) ≤ Q.card := by
    simpa only [Finset.card_image_of_injective _ profile_toC_injective] using hrowDense
  obtain ⟨hpP, hrow, hcovered⟩ := profile_batch_row_facts T S hsource htarget K.H
    i p Q hQnonempty hedges (1 / 8) hrowDenseC
  obtain ⟨hpCenter, hpGood, hQ, hneq, hsurvives, _⟩ := hrow
  have hrow0 : DenseSurvivingDirectionRow K.H i (TrackD.toC p) Q 0 :=
    ⟨hpCenter, hpGood, hQ, hneq, hsurvives, by simp⟩
  have hpD : TrackD.toC p ∈ D.centers i := by
    rw [(hfrom.2.2.2 i).1]
    exact hpCenter
  have hQimage : Q.image TrackD.toC ⊆ D.targets i := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
    rw [(hfrom.2.2.2 i).2.1]
    exact Finset.mem_image.mpr ⟨q, hQ hq, rfl⟩
  have htargetCard : (D.targets i).card = Y.card := by
    rw [(hfrom.2.2.2 i).2.1]
    exact Finset.card_image_of_injective _ profile_toC_injective
  have hcertP := hcert_i p hpX hpGood
  have hgHom := hcertP.2.1
  have hgHom' : (g i (TrackD.toC p)).IsHomogeneous ((n + 1 - 2) *
      (finalNarrowTestDegree K K.b_eq i - 1)) := by
    simpa only [show n + 1 - 2 = n - 1 by omega] using hgHom
  let B₁ := coveringProjectionFailures D i (TrackD.toC p) Q (F.family i p)
    (finalNarrowTestDegree K K.b₀ i)
  let B₂ := coveringEnvelopeLargeLabels (G i p) (TrackD.toC p) Q
  let B₃ := realExceptionalTargets D i (K.H.batch.bad K.finalPlateau i)
    (TrackD.toC p) Q (badFamily i (TrackD.toC p))
  let B₄ := properMinorZeroTargets D i (TrackD.toC p) Q (g i (TrackD.toC p))
  have hcover : rowDirections (TrackD.toC p) Q ⊆ (ProjectiveFamily.locus (F.family i p)).points := by
    rintro z ⟨q, hq, hne, rfl⟩
    obtain ⟨hne', hz⟩ := hcovered q hq
    simpa only [TrackD.familyPoints, ProjectiveFamily.points_locus] using hz
  have hB₁ : (B₁.card : ℝ) ≤ (1 / 64 : ℝ) * Y.card :=
    hcapture_i (TrackD.toC p) Q hQ hneq (F.family i p) hcover
  have hB₂ : (B₂.card : ℝ) ≤ (1 / 64 : ℝ) * Y.card := by
    have hl := hlarge_i p hpP Q hrow0 (G i p)
    have hc : ((S.sequence.target i).pts.image TrackD.toC).card = Y.card :=
      Finset.card_image_of_injective _ profile_toC_injective
    rw [hc] at hl
    exact hl
  have hB₃ : (B₃.card : ℝ) ≤ (1 / 64 : ℝ) * Y.card := by
    have hb := real_exceptional_targets_card_le D i (K.H.batch.bad K.finalPlateau i)
      (TrackD.toC p) Q (badFamily i (TrackD.toC p)) hQimage
    have hm := hmass_i ⟨TrackD.toC p, hpD, hpGood⟩
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at hm
    change (((D.targets i).filter (fun q => D.owner i q ∈
      exceptional_carriers D i (K.H.batch.bad K.finalPlateau i) (TrackD.toC p)
        (badFamily i (TrackD.toC p)))).card : ℝ) ≤
      (1 / 64 : ℝ) * ((D.targets i).card : ℝ) at hm
    rw [htargetCard] at hm
    exact hb.trans hm
  have hB₄ : (B₄.card : ℝ) ≤ (1 / 64 : ℝ) * Y.card :=
    hzero_i (TrackD.toC p) Q hQ (g i (TrackD.toC p)) hgHom'
  have hgap : (B₁.card : ℝ) + B₂.card + B₃.card + B₄.card < Q.card := by
    linarith
  obtain ⟨q, hq, hq₁, hq₂, hq₃, hq₄⟩ := four_removals_leave_label Q B₁ B₂ B₃ B₄ hgap
  have hqD : TrackD.toC q ∈ D.targets i := hQimage (Finset.mem_image.mpr ⟨q, hq, rfl⟩)
  have hmember := hmembers_i (TrackD.toC p) Q hrow0 (F.family i p) (G i p)
    q hq hq₁ hq₂
  have hretained : D.owner i (TrackD.toC q) ∈
      D.retained i (K.H.batch.bad K.finalPlateau i) (TrackD.toC p) :=
    K.H.batch.owner_retained i (TrackD.toC p) (TrackD.toC q)
      (Finset.mem_image.mpr ⟨q, hQ hq, rfl⟩) (hsurvives q hq) K.finalPlateau
  have hnotBad : radialImage (TrackD.toC p) (D.owner i (TrackD.toC q)) ∉
      badFamily i (TrackD.toC p) := by
    intro hbad
    exact hq₃ (Finset.mem_filter.mpr ⟨hq, Finset.mem_filter.mpr ⟨hretained, hbad⟩⟩)
  have hproper := hcertP.1.2.2.2.1 _ hmember hnotBad
  have hgLabel := retained_minor_label_nonzero D i (TrackD.toC p) Q
    (g i (TrackD.toC p)) hgHom q hq (hneq q hq) hproper hq₄
  refine ⟨p, hpP, q, hedges q hq, ?_⟩
  exact regular_covering_label_projects_into D i p Q (F.family i p) (F.directional i p hpP)
    (finalNarrowTestDegree K K.b₀ i) (G i p) (badFamily i (TrackD.toC p))
    (E i (TrackD.toC p)) (g i (TrackD.toC p)) Creg (finalNarrowTestDegree K K.b_eq i)
    hcertP.1 q hq hqD (hneq q hq) (hcovered q hq) hq₂ hmember hgLabel

end
end DistinctDistances.SparseCones
