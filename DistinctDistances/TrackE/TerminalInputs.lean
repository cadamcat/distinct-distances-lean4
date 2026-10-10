import DistinctDistances.TrackE.SelectionSequence

/-! Fixed terminal owners and literal selected incidences
(`profiles.tex:540–560`; `sparse-cones.tex:658–688, 795–928`). -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- Preserve every global assignment, choosing a fallback only when it is absent. -/
def terminalOwner (τ : RPoint d → Option (AffineVariety d))
    (fallback : RPoint d → AffineVariety d) (q : RPoint d) : AffineVariety d :=
  (τ q).getD (fallback q)

/-- The actual selected graph after removing globally unassigned target columns. -/
def terminalSelectedGraph {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (i : ℕ) : Finset (RPoint d × RPoint d) :=
  (TrackD.poolPts (T.sources i) ×ˢ TrackD.poolPts (T.targets i)).filter (fun pq =>
    TrackD.SelectedIncidence (regime.P i) (F.family i) (T.terminal i)
      (selectionTolerance (T.precision i)) pq.1 pq.2 ∧ T.terminal i pq.2 ≠ none)

/-- A global terminal assignment overrides any fallback assignment on the
same actual target pool, including physical carrier intersections. -/
theorem terminal_owner_assignment {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (fallback : ℕ → RPoint d → AffineVariety d)
    (hfb : ∀ i, TrackD.CarrierAssignment (T.targets i) (d - 1) (fallback i)) :
    ∀ i, TrackD.CarrierAssignment (T.targets i) (d - 1)
      (terminalOwner (T.terminal i) (fallback i)) := by
  intro i X hX q hq
  unfold terminalOwner
  rcases hτ : T.terminal i q with _ | Y
  · simp only [Option.getD_none]
    exact hfb i X hX q hq
  · simp only [Option.getD_some]
    have hpiece : X ∈ (T.partition i).pieces := (T.certificate i).targets_subset hX
    exact (T.certificate i).terminal.carrier X hpiece q hq Y hτ

/-- Disjoint piece bounds sum to the same omission fraction in their union. -/
theorem terminal_unassigned_pool_bound (Q : TrackD.Partition d) (θ : ℝ)
    (τ : RPoint d → Option (AffineVariety d))
    (hτ : TrackD.TerminalAssignment Q θ τ) (pl : Finset (TrackD.Piece d))
    (hsub : pl ⊆ Q.pieces) (hdisjoint : (pl : Set (TrackD.Piece d)).PairwiseDisjoint TrackD.Piece.pts) :
    (((TrackD.poolPts pl).filter (fun q => τ q = none)).card : ℝ) ≤
      θ * (TrackD.poolPts pl).card := by
  have hbiUnion : TrackD.poolPts pl = pl.biUnion TrackD.Piece.pts := rfl
  have hfilterEq : (TrackD.poolPts pl).filter (fun q => τ q = none) =
      pl.biUnion (fun X => X.pts.filter (fun q => τ q = none)) := by
    rw [hbiUnion, Finset.filter_biUnion]
  have hdisjoint' : (pl : Set (TrackD.Piece d)).PairwiseDisjoint (fun X => X.pts.filter (fun q => τ q = none)) := by
    intro X hX Y hY hne
    have hdis := hdisjoint hX hY hne
    exact hdis.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hcardFilter : ((TrackD.poolPts pl).filter (fun q => τ q = none)).card =
      ∑ X ∈ pl, (X.pts.filter (fun q => τ q = none)).card := by
    rw [hfilterEq]
    exact Finset.card_biUnion (fun X hX Y hY hne => hdisjoint' (Finset.mem_coe.mpr hX) (Finset.mem_coe.mpr hY) hne)
  have hcardTotal : (TrackD.poolPts pl).card = ∑ X ∈ pl, X.pts.card := by
    rw [hbiUnion]
    exact Finset.card_biUnion (fun X hX Y hY hne => hdisjoint (Finset.mem_coe.mpr hX) (Finset.mem_coe.mpr hY) hne)
  rw [hcardFilter, hcardTotal, Nat.cast_sum, Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro X hX
  exact hτ.unassigned X (hsub hX)

/-- The omissions are negligible in either original selected pool. -/
theorem selected_terminal_omissions_small {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) :
    Framework.LittleO
      (fun i => (((TrackD.poolPts (T.sources i)).filter
        (fun q => T.terminal i q = none)).card : ℝ))
      (fun i => ((TrackD.poolPts (T.sources i)).card : ℝ)) ∧
    Framework.LittleO
      (fun i => (((TrackD.poolPts (T.targets i)).filter
        (fun q => T.terminal i q = none)).card : ℝ))
      (fun i => ((TrackD.poolPts (T.targets i)).card : ℝ)) := by
  have htol := selection_tolerance_tendsto_zero T.precision T.precision_grows
  have hone : ∀ (pools : ℕ → Finset (TrackD.Piece d))
      (hsub : ∀ i, pools i ⊆ (T.partition i).pieces),
      Framework.LittleO
        (fun i => (((TrackD.poolPts (pools i)).filter
          (fun q => T.terminal i q = none)).card : ℝ))
        (fun i => ((TrackD.poolPts (pools i)).card : ℝ)) := by
    intro pools hsub
    apply Asymptotics.IsLittleO.of_bound
    intro c hc
    have htolc : ∀ᶠ i in atTop, selectionTolerance (T.precision i) ≤ c :=
      (htol.eventually (Iio_mem_nhds hc)).mono fun i hi => hi.le
    filter_upwards [htolc] with i hi
    have hdisjoint : (pools i : Set (TrackD.Piece d)).PairwiseDisjoint TrackD.Piece.pts :=
      (T.certificate i).good.pieces_disjoint.subset (Finset.coe_subset.mpr (hsub i))
    have hbound := terminal_unassigned_pool_bound (T.partition i)
      (selectionTolerance (T.precision i)) (T.terminal i)
      (T.certificate i).terminal (pools i) (hsub i) hdisjoint
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)]
    calc
      (((TrackD.poolPts (pools i)).filter (fun q => T.terminal i q = none)).card : ℝ) ≤
          selectionTolerance (T.precision i) * (TrackD.poolPts (pools i)).card := hbound
      _ ≤ c * (TrackD.poolPts (pools i)).card :=
        mul_le_mul_of_nonneg_right hi (Nat.cast_nonneg _)
  exact ⟨hone T.sources (fun i => (T.certificate i).sources_subset),
    hone T.targets (fun i => (T.certificate i).targets_subset)⟩

/-- Column omission loses at most its fraction of all pairs, leaving a fixed
positive-density graph with all original terminal and light-line restrictions. -/
theorem selected_terminal_graph_dense {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) :
    ∀ᶠ i in atTop, (1 / 4 : ℝ) * (TrackD.poolPts (T.sources i)).card *
      (TrackD.poolPts (T.targets i)).card ≤ (terminalSelectedGraph T i).card := by
  have htol := selection_tolerance_tendsto_zero T.precision T.precision_grows
  have htol_small : ∀ᶠ i in atTop, 2 * selectionTolerance (T.precision i) ≤ 1 / 4 := by
    have hlim : Tendsto (fun i => 2 * selectionTolerance (T.precision i)) atTop (𝓝 (2 * 0)) :=
      htol.const_mul 2
    rw [mul_zero] at hlim
    have hpos : (0 : ℝ) < 1 / 4 := by norm_num
    exact (hlim.eventually (Iio_mem_nhds hpos)).mono fun i hi => hi.le
  filter_upwards [htol_small] with i hi
  let G_orig := (TrackD.poolPts (T.sources i) ×ˢ TrackD.poolPts (T.targets i)).filter (fun pq =>
    TrackD.SelectedIncidence (regime.P i) (F.family i) (T.terminal i)
      (selectionTolerance (T.precision i)) pq.1 pq.2)
  have hG_dense := (T.certificate i).selected
  have hbad_subset : G_orig \ (terminalSelectedGraph T i) ⊆
      TrackD.poolPts (T.sources i) ×ˢ
        ((TrackD.poolPts (T.targets i)).filter (fun q => T.terminal i q = none)) := by
    intro pq hpq
    rw [Finset.mem_sdiff] at hpq
    have hG := hpq.1
    have hnot := hpq.2
    simp only [G_orig, Finset.mem_filter, Finset.mem_product] at hG
    have hp_src : pq.1 ∈ TrackD.poolPts (T.sources i) := hG.1.1
    have hq_tgt : pq.2 ∈ TrackD.poolPts (T.targets i) := hG.1.2
    have hinc : TrackD.SelectedIncidence (regime.P i) (F.family i) (T.terminal i)
      (selectionTolerance (T.precision i)) pq.1 pq.2 := hG.2
    rw [Finset.mem_product, Finset.mem_filter]
    refine ⟨hp_src, hq_tgt, ?_⟩
    by_contra hterm_ne
    apply hnot
    simp only [terminalSelectedGraph, Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hp_src, hq_tgt⟩, hinc, hterm_ne⟩
  have hbad_card : ((G_orig \ (terminalSelectedGraph T i)).card : ℝ) ≤
      (TrackD.poolPts (T.sources i)).card *
        (((TrackD.poolPts (T.targets i)).filter (fun q => T.terminal i q = none)).card : ℝ) := by
    have := Finset.card_le_card hbad_subset
    rw [Finset.card_product] at this
    exact_mod_cast this
  have hdisjoint : (T.targets i : Set (TrackD.Piece d)).PairwiseDisjoint TrackD.Piece.pts :=
    (T.certificate i).good.pieces_disjoint.subset (Finset.coe_subset.mpr (T.certificate i).targets_subset)
  have homit := terminal_unassigned_pool_bound (T.partition i)
    (selectionTolerance (T.precision i)) (T.terminal i)
    (T.certificate i).terminal (T.targets i) (T.certificate i).targets_subset hdisjoint
  have hbad_bound : ((G_orig \ (terminalSelectedGraph T i)).card : ℝ) ≤
      selectionTolerance (T.precision i) * (TrackD.poolPts (T.sources i)).card *
        (TrackD.poolPts (T.targets i)).card := by
    calc
      ((G_orig \ (terminalSelectedGraph T i)).card : ℝ) ≤
          (TrackD.poolPts (T.sources i)).card *
            (((TrackD.poolPts (T.targets i)).filter (fun q => T.terminal i q = none)).card : ℝ) := hbad_card
      _ ≤ (TrackD.poolPts (T.sources i)).card *
            (selectionTolerance (T.precision i) * (TrackD.poolPts (T.targets i)).card) :=
        mul_le_mul_of_nonneg_left homit (Nat.cast_nonneg _)
      _ = selectionTolerance (T.precision i) * (TrackD.poolPts (T.sources i)).card *
            (TrackD.poolPts (T.targets i)).card := by ring
  have hsub_G : (terminalSelectedGraph T i) ⊆ G_orig := by
    intro pq hpq
    simp only [terminalSelectedGraph, Finset.mem_filter] at hpq
    simp only [G_orig, Finset.mem_filter]
    exact ⟨hpq.1, hpq.2.1⟩
  have hlower : (terminalSelectedGraph T i).card ≥
      (G_orig.card : ℝ) - (G_orig \ (terminalSelectedGraph T i)).card := by
    have hsub : G_orig ⊆ terminalSelectedGraph T i ∪ (G_orig \ terminalSelectedGraph T i) := fun x hx => by
      by_cases h : x ∈ terminalSelectedGraph T i
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx, h⟩)
    have hle_card := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hle : (G_orig.card : ℝ) ≤ (terminalSelectedGraph T i).card + (G_orig \ (terminalSelectedGraph T i)).card := by
      exact_mod_cast hle_card
    linarith
  have htol_ge : (1 / 4 : ℝ) * (TrackD.poolPts (T.sources i)).card * (TrackD.poolPts (T.targets i)).card ≤
      (terminalSelectedGraph T i).card := by
    calc
      (1 / 4 : ℝ) * (TrackD.poolPts (T.sources i)).card * (TrackD.poolPts (T.targets i)).card ≤
          (1 / 2 - 2 * selectionTolerance (T.precision i)) *
            (TrackD.poolPts (T.sources i)).card * (TrackD.poolPts (T.targets i)).card := by
              have hfac : 1 / 4 ≤ 1 / 2 - 2 * selectionTolerance (T.precision i) := by linarith
              have hprod : (0 : ℝ) ≤ (TrackD.poolPts (T.sources i)).card * (TrackD.poolPts (T.targets i)).card := by positivity
              calc
                (1 / 4 : ℝ) * (TrackD.poolPts (T.sources i)).card * (TrackD.poolPts (T.targets i)).card =
                    (1 / 4 : ℝ) * ((TrackD.poolPts (T.sources i)).card * (TrackD.poolPts (T.targets i)).card) := by ring
                _ ≤ (1 / 2 - 2 * selectionTolerance (T.precision i)) *
                      ((TrackD.poolPts (T.sources i)).card * (TrackD.poolPts (T.targets i)).card) :=
                  mul_le_mul_of_nonneg_right hfac hprod
                _ = (1 / 2 - 2 * selectionTolerance (T.precision i)) *
                      (TrackD.poolPts (T.sources i)).card * (TrackD.poolPts (T.targets i)).card := by ring
      _ = (1 / 2 - selectionTolerance (T.precision i)) * (TrackD.poolPts (T.sources i)).card *
            (TrackD.poolPts (T.targets i)).card -
          selectionTolerance (T.precision i) * (TrackD.poolPts (T.sources i)).card *
            (TrackD.poolPts (T.targets i)).card := by ring
      _ ≤ (G_orig.card : ℝ) - ((G_orig \ (terminalSelectedGraph T i)).card : ℝ) := sub_le_sub hG_dense hbad_bound
      _ ≤ (terminalSelectedGraph T i).card := hlower
  exact htol_ge

/-- Membership retains the actual selected incidence and its assigned curve. -/
theorem mem_terminalSelectedGraph {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (i : ℕ) (p q : RPoint d) :
    (p, q) ∈ terminalSelectedGraph T i ↔
      p ∈ TrackD.poolPts (T.sources i) ∧ q ∈ TrackD.poolPts (T.targets i) ∧
      TrackD.SelectedIncidence (regime.P i) (F.family i) (T.terminal i)
        (selectionTolerance (T.precision i)) p q ∧
      ∃ Y, T.terminal i q = some Y := by
  unfold terminalSelectedGraph
  simp only [Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨hp, hq⟩, hinc, hnot⟩
    cases h : T.terminal i q with
    | none => contradiction
    | some Y => exact ⟨hp, hq, hinc, Y, rfl⟩
  · rintro ⟨hp, hq, hinc, Y, hY⟩
    refine ⟨⟨hp, hq⟩, hinc, ?_⟩
    rw [hY]
    intro h
    cases h

end

end DistinctDistances.SparseCones
