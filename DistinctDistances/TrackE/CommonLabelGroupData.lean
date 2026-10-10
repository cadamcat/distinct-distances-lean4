import DistinctDistances.TrackE.CommonLabelEnvelope
import DistinctDistances.TrackE.MELabelAux

/-! Complete product images of a dense label graph inside its envelope,
with the retained image mass, and their grouping by envelope component
dimension (sparse-cones.tex:239–306). -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- Certificate for one dense graph `Γ` at the label degree `L`, on the
plateau after the zero-based cut `j` (`k = d-(j+1)`): a retained subgraph
`Γr` of `Γ` missing at most `(ρ/2)|S_x||S_y|` pairs, and for each retained
pair an irreducible `2k`-dimensional variety `Z pq` (its complete product
image) containing its label and contained in the degree-`L` envelope of the
labels of `Γ`; every subgraph of `Γr` has distinct images of total degree
at least `lower · e^{-θ s} · |Γ''| / (|S_x||S_y|)` (the retained image mass). -/
def CommonImageCertificate {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} (M : CommonPoolProfile T) (j : ℕ) (θ ρ : ℝ)
    (i : ℕ) (i₀ : Fin d) (L : ℕ) (Γ Γr : Finset (RPoint d × RPoint d))
    (Z : RPoint d × RPoint d → AffineVariety (d + d)) : Prop :=
  Γr ⊆ Γ ∧
  ((Γ \ Γr).card : ℝ) ≤ (ρ / 2) * ((TrackD.poolPts (T.sources i)).card : ℝ) *
    (TrackD.poolPts (T.targets i)).card ∧
  (∀ pq ∈ Γr, (Z pq).IsIrreducible ∧ (Z pq).dimension = 2 * (d - (j + 1)) ∧
    (Z pq).Subvariety (envelope (commonLabelPoints i₀ Γ) L) ∧
    (fun k => TrackD.labelPt i₀ (TrackD.toC pq.1) (TrackD.toC pq.2)
      (finSumFinEquiv.symm k)) ∈ (Z pq).points) ∧
  ∀ Γ'' ⊆ Γr, commonEqualDimLower M i j * Real.exp (-θ * M.s i) * (Γ''.card : ℝ) ≤
    ((TrackD.poolPts (T.sources i)).card : ℝ) * (TrackD.poolPts (T.targets i)).card *
      ((AffineFamily.degree (Γ''.image Z) : ℚ) : ℝ)

/-- Pigeonhole over envelope component dimensions (sparse-cones.tex:262–270,
297–306). Each retained image lies in one envelope component of dimension
at least `2k`; some dimension `h` carries a fraction `1/(2d+1)` of the
retained graph, its labels lie on that group, and when `h = 2k` every image
of that portion IS a member of the group, so the group degree inherits the
certificate's mass bound. -/
theorem common_label_dense_group_of_certificate {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} (M : CommonPoolProfile T) (j : ℕ) (hj : j + 1 < d)
    (θ ρ : ℝ) (hρ : 0 < ρ) (i : ℕ) (i₀ : Fin d) (L : ℕ)
    (Γ Γr : Finset (RPoint d × RPoint d)) (Z : RPoint d × RPoint d → AffineVariety (d + d))
    (hcert : CommonImageCertificate M j θ ρ i i₀ L Γ Γr Z)
    (hdense : ρ * ((TrackD.poolPts (T.sources i)).card : ℝ) *
      (TrackD.poolPts (T.targets i)).card ≤ Γ.card) :
    ∃ h : ℕ, 2 * (d - (j + 1)) ≤ h ∧ h ≤ 2 * d ∧
      ∃ Γ' : Finset (RPoint d × RPoint d), Γ' ⊆ Γ ∧
        (ρ / (2 * (2 * d + 1 : ℝ))) * ((TrackD.poolPts (T.sources i)).card : ℝ) *
          (TrackD.poolPts (T.targets i)).card ≤ Γ'.card ∧
        commonLabelPoints i₀ Γ' ⊆ (AffineFamily.locus (commonLabelGroup i₀ Γ L h)).points ∧
        (h = 2 * (d - (j + 1)) →
          commonEqualDimLower M i j * Real.exp (-θ * M.s i) * (ρ / (2 * (2 * d + 1 : ℝ))) ≤
            ((AffineFamily.degree (commonLabelGroup i₀ Γ L h) : ℚ) : ℝ)) := by
  classical
  have hk1 : 1 ≤ d - (j + 1) := by omega
  obtain ⟨hsub, hdiff, hZmem, hmass⟩ := hcert
  have hcard_eq : (Γ.card : ℝ) = (Γr.card : ℝ) + ((Γ \ Γr).card : ℝ) := by
    have h := Finset.card_sdiff_add_card_eq_card hsub
    have hc : ((Γ \ Γr).card + Γr.card : ℕ) = Γ.card := h
    have hcast := congrArg (Nat.cast : ℕ → ℝ) hc
    push_cast at hcast
    linarith
  have hΓr_ge : (ρ / 2) * (((TrackD.poolPts (T.sources i)).card : ℝ) *
      (TrackD.poolPts (T.targets i)).card) ≤ (Γr.card : ℝ) := by
    have h1 : ρ * (TrackD.poolPts (T.sources i)).card *
        (TrackD.poolPts (T.targets i)).card ≤ (Γ.card : ℝ) := hdense
    linarith [hcard_eq]
  by_cases hS0 : ((TrackD.poolPts (T.sources i)).card : ℝ) *
      (TrackD.poolPts (T.targets i)).card = 0
  · refine ⟨2 * (d - (j + 1)) + 1, by omega, by omega, ∅, (Finset.empty_subset Γ), ?_, ?_, ?_⟩
    · have h0 : (ρ / (2 * (2 * (d : ℝ) + 1))) *
          (TrackD.poolPts (T.sources i)).card *
          (TrackD.poolPts (T.targets i)).card = 0 := by
        have h00 : (ρ / (2 * (2 * (d : ℝ) + 1))) *
            (((TrackD.poolPts (T.sources i)).card : ℝ) *
              (TrackD.poolPts (T.targets i)).card) = 0 := by
          rw [hS0]; ring
        linarith [h00]
      rw [h0]
      simp
    · intro y hy
      simp [commonLabelPoints] at hy
    · intro heq
      omega
  · have hSpos : 0 < ((TrackD.poolPts (T.sources i)).card : ℝ) *
        (TrackD.poolPts (T.targets i)).card :=
      lt_of_le_of_ne (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Ne.symm hS0)
    have hWex : ∀ pq ∈ Γr, ∃ W : AffineVariety (d + d),
        W ∈ Bridges.envelopeComponents (commonLabelPoints i₀ Γ) L ∧
        (Z pq).Subvariety W ∧ 2 * (d - (j + 1)) ≤ W.dimension ∧ W.dimension ≤ 2 * d ∧
        W.IsIrreducible := by
      intro pq hpq
      obtain ⟨hZirr, hZdim, hZsub, _⟩ := hZmem pq hpq
      haveI : (Z pq).ideal.IsPrime := hZirr
      obtain ⟨Q, hQmin, hQle⟩ :=
        Ideal.exists_minimalPrimes_le
          (show (envelope (commonLabelPoints i₀ Γ) L).ideal ≤ (Z pq).ideal from hZsub)
      let C : (envelope (commonLabelPoints i₀ Γ) L).Component := ⟨Q, hQmin⟩
      have hCmem : C.variety ∈ Bridges.envelopeComponents (commonLabelPoints i₀ Γ) L := by
        unfold Bridges.envelopeComponents
        exact Finset.mem_image_of_mem _ (Finset.mem_univ C)
      have hCsub : (Z pq).Subvariety C.variety := by
        unfold AffineVariety.Subvariety
        have hCideal : C.variety.ideal = Q := rfl
        rw [hCideal]
        exact hQle
      have hCirr : C.variety.IsIrreducible := C.irreducible
      refine ⟨C.variety, hCmem, hCsub, ?_, ?_, hCirr⟩
      · rw [← hZdim]
        exact TrackD.irreducible_dimension_mono _ _ hZirr hCirr hCsub
      · have hle := TrackA.pooling_dimension_le_ambient C.variety hCirr
        omega
    have hWall : ∀ pq : RPoint d × RPoint d, ∃ W : AffineVariety (d + d),
        pq ∈ Γr →
          (W ∈ Bridges.envelopeComponents (commonLabelPoints i₀ Γ) L ∧
          (Z pq).Subvariety W ∧ 2 * (d - (j + 1)) ≤ W.dimension ∧ W.dimension ≤ 2 * d ∧
          W.IsIrreducible) := by
      intro pq
      by_cases h : pq ∈ Γr
      · obtain ⟨W, h1, h2, h3, h4, h5⟩ := hWex pq h
        exact ⟨W, fun _ => ⟨h1, h2, h3, h4, h5⟩⟩
      · exact ⟨Z pq, fun h' => absurd h' h⟩
    choose V hV using hWall
    have hVmem : ∀ pq ∈ Γr, V pq ∈ Bridges.envelopeComponents (commonLabelPoints i₀ Γ) L :=
      fun pq hpq => (hV pq hpq).1
    have hVsub : ∀ pq ∈ Γr, (Z pq).Subvariety (V pq) :=
      fun pq hpq => (hV pq hpq).2.1
    have hVlo : ∀ pq ∈ Γr, 2 * (d - (j + 1)) ≤ (V pq).dimension :=
      fun pq hpq => (hV pq hpq).2.2.1
    have hVhi : ∀ pq ∈ Γr, (V pq).dimension ≤ 2 * d :=
      fun pq hpq => (hV pq hpq).2.2.2.1
    have hVirr : ∀ pq ∈ Γr, (V pq).IsIrreducible :=
      fun pq hpq => (hV pq hpq).2.2.2.2
    have hHs_mem : ∀ pq ∈ Γr, (V pq).dimension ∈ Finset.Icc (2 * (d - (j + 1))) (2 * d) := by
      intro pq hpq
      exact Finset.mem_Icc.mpr ⟨hVlo pq hpq, hVhi pq hpq⟩
    have hHs_nonempty : (Finset.Icc (2 * (d - (j + 1))) (2 * d)).Nonempty :=
      Finset.nonempty_Icc.mpr (by omega)
    have hsum_nat : Γr.card =
        ∑ hh ∈ Finset.Icc (2 * (d - (j + 1))) (2 * d),
          (Γr.filter (fun pq => (V pq).dimension = hh)).card := by
      have hmap : Set.MapsTo (fun pq => (V pq).dimension) (Γr : Set (RPoint d × RPoint d))
          ((Finset.Icc (2 * (d - (j + 1))) (2 * d) : Finset ℕ) : Set ℕ) := by
        intro pq hpq
        exact Finset.mem_coe.mpr (hHs_mem pq (Finset.mem_coe.mp hpq))
      have h := Finset.card_eq_sum_card_fiberwise (s := Γr)
        (t := Finset.Icc (2 * (d - (j + 1))) (2 * d))
        (f := fun pq => (V pq).dimension) hmap
      simpa using h
    obtain ⟨h, hhHs, hmax⟩ := Finset.exists_max_image
      (Finset.Icc (2 * (d - (j + 1))) (2 * d))
      (fun hh => (Γr.filter (fun pq => (V pq).dimension = hh)).card) hHs_nonempty
    have hhIcc : 2 * (d - (j + 1)) ≤ h ∧ h ≤ 2 * d := Finset.mem_Icc.mp hhHs
    have hsum_le : ∑ hh ∈ Finset.Icc (2 * (d - (j + 1))) (2 * d),
          (Γr.filter (fun pq => (V pq).dimension = hh)).card ≤
        (Finset.Icc (2 * (d - (j + 1))) (2 * d)).card *
          (Γr.filter (fun pq => (V pq).dimension = h)).card := by
      calc ∑ hh ∈ Finset.Icc (2 * (d - (j + 1))) (2 * d),
              (Γr.filter (fun pq => (V pq).dimension = hh)).card
          ≤ ∑ _hh ∈ Finset.Icc (2 * (d - (j + 1))) (2 * d),
              (Γr.filter (fun pq => (V pq).dimension = h)).card :=
            Finset.sum_le_sum (fun hh hhh => hmax hh hhh)
        _ = (Finset.Icc (2 * (d - (j + 1))) (2 * d)).card *
              (Γr.filter (fun pq => (V pq).dimension = h)).card := by
            simp [Finset.sum_const]
    have hHs_card_le : (Finset.Icc (2 * (d - (j + 1))) (2 * d)).card ≤ 2 * d + 1 := by
      rw [Nat.card_Icc]
      omega
    have hN_le : (Γr.card : ℝ) ≤
        ((Finset.Icc (2 * (d - (j + 1))) (2 * d)).card : ℝ) *
          ((Γr.filter (fun pq => (V pq).dimension = h)).card : ℝ) := by
      have hn : Γr.card ≤ (Finset.Icc (2 * (d - (j + 1))) (2 * d)).card *
          (Γr.filter (fun pq => (V pq).dimension = h)).card := hsum_nat ▸ hsum_le
      exact_mod_cast hn
    have hdenom_pos : (0 : ℝ) < ((2 * d + 1 : ℕ) : ℝ) := by positivity
    have hΓr_le : (Γr.card : ℝ) ≤
        ((Γr.filter (fun pq => (V pq).dimension = h)).card : ℝ) * ((2 * d + 1 : ℕ) : ℝ) := by
      calc (Γr.card : ℝ)
          ≤ ((Finset.Icc (2 * (d - (j + 1))) (2 * d)).card : ℝ) *
              ((Γr.filter (fun pq => (V pq).dimension = h)).card : ℝ) := hN_le
        _ ≤ ((2 * d + 1 : ℕ) : ℝ) *
              ((Γr.filter (fun pq => (V pq).dimension = h)).card : ℝ) := by
            apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
            exact_mod_cast hHs_card_le
        _ = ((Γr.filter (fun pq => (V pq).dimension = h)).card : ℝ) *
              ((2 * d + 1 : ℕ) : ℝ) := by ring
    have havg : (Γr.card : ℝ) / ((2 * d + 1 : ℕ) : ℝ) ≤
        ((Γr.filter (fun pq => (V pq).dimension = h)).card : ℝ) :=
      (div_le_iff₀ hdenom_pos).mpr hΓr_le
    have hdense' : (ρ / (2 * (2 * (d : ℝ) + 1))) *
          (TrackD.poolPts (T.sources i)).card *
          (TrackD.poolPts (T.targets i)).card ≤
        ((Γr.filter (fun pq => (V pq).dimension = h)).card : ℝ) := by
      have hle : (ρ / 2) * (((TrackD.poolPts (T.sources i)).card : ℝ) *
          (TrackD.poolPts (T.targets i)).card) ≤
          ((Γr.filter (fun pq => (V pq).dimension = h)).card : ℝ) *
            ((2 * d + 1 : ℕ) : ℝ) := hΓr_ge.trans hΓr_le
      have heq : (ρ / (2 * (2 * (d : ℝ) + 1))) *
            (TrackD.poolPts (T.sources i)).card *
            (TrackD.poolPts (T.targets i)).card =
          (((ρ / 2) * (((TrackD.poolPts (T.sources i)).card : ℝ) *
            (TrackD.poolPts (T.targets i)).card))) / ((2 * d + 1 : ℕ) : ℝ) := by
        rw [div_eq_mul_inv, mul_inv]
        push_cast
        ring
      rw [heq]
      rwa [div_le_iff₀ hdenom_pos]
    refine ⟨h, hhIcc.1, hhIcc.2, Γr.filter (fun pq => (V pq).dimension = h),
      (Finset.filter_subset _ _).trans hsub, hdense', ?_, ?_⟩
    · intro y hy
      obtain ⟨pq, hpq_mem, rfl⟩ := hy
      have hpqΓ' : pq ∈ Γr.filter (fun pq => (V pq).dimension = h) :=
        Finset.mem_coe.mp hpq_mem
      have hpqΓr : pq ∈ Γr := (Finset.filter_subset _ _) hpqΓ'
      have hfil : (V pq).dimension = h := (Finset.mem_filter.mp hpqΓ').2
      have hVgroup : V pq ∈ commonLabelGroup i₀ Γ L h :=
        Finset.mem_filter.mpr ⟨hVmem pq hpqΓr, hfil⟩
      obtain ⟨_, _, _, hZpt⟩ := hZmem pq hpqΓr
      have hsub_pts : (Z pq).points ⊆ (V pq).points :=
        (AffineVariety.subvariety_iff_points_subset _ _).mp (hVsub pq hpqΓr)
      have hVpt : (fun kk => TrackD.labelPt i₀ (TrackD.toC pq.1) (TrackD.toC pq.2)
          (finSumFinEquiv.symm kk)) ∈ (V pq).points := hsub_pts hZpt
      rw [AffineFamily.points_locus]
      exact Set.mem_biUnion hVgroup hVpt
    · intro heq
      have hZeqV : ∀ pq ∈ Γr.filter (fun pq => (V pq).dimension = h), Z pq = V pq := by
        intro pq hpq
        have hpqΓr : pq ∈ Γr := (Finset.filter_subset _ _) hpq
        have hfil : (V pq).dimension = h := (Finset.mem_filter.mp hpq).2
        obtain ⟨hZirr, hZdim, _, _⟩ := hZmem pq hpqΓr
        have hVirr := hVirr pq hpqΓr
        have hsubVW := hVsub pq hpqΓr
        have hpos : 0 < (V pq).dimension := by omega
        have hdimEq : (Z pq).dimension = (V pq).dimension := by omega
        exact TrackD.irreducible_subvariety_eq_of_pos_dimension_eq _ _ hZirr hVirr
          hsubVW hpos hdimEq
      have himg_eq : (Γr.filter (fun pq => (V pq).dimension = h)).image Z =
          (Γr.filter (fun pq => (V pq).dimension = h)).image V := by
        apply Finset.image_congr
        intro pq hpq
        exact hZeqV pq (Finset.mem_coe.mp hpq)
      have himg_sub : (Γr.filter (fun pq => (V pq).dimension = h)).image V ⊆
          commonLabelGroup i₀ Γ L h := by
        intro W hW
        obtain ⟨pq, hpq, rfl⟩ := Finset.mem_image.mp hW
        have hpqΓr : pq ∈ Γr := (Finset.mem_filter.mp hpq).1
        have hfil : (V pq).dimension = h := (Finset.mem_filter.mp hpq).2
        exact Finset.mem_filter.mpr ⟨hVmem pq hpqΓr, hfil⟩
      have himg_subZ : (Γr.filter (fun pq => (V pq).dimension = h)).image Z ⊆
          commonLabelGroup i₀ Γ L h := himg_eq ▸ himg_sub
      have hdeg_nn : ∀ W ∈ commonLabelGroup i₀ Γ L h,
          W ∉ (Γr.filter (fun pq => (V pq).dimension = h)).image Z →
          (0 : ℚ) ≤ W.degree := by
        intro W hW _
        have hWmem : W ∈ Bridges.envelopeComponents (commonLabelPoints i₀ Γ) L := by
          unfold commonLabelGroup at hW
          exact (Finset.mem_filter.mp hW).1
        have hWirrW := envelopeComponents_irreducible _ _ W hWmem
        have h1 : (1 : ℚ) ≤ W.degree := AffineVariety.one_le_degree W hWirrW.ne_top
        linarith
      have hdeg_le_Q : AffineFamily.degree
            ((Γr.filter (fun pq => (V pq).dimension = h)).image Z) ≤
          AffineFamily.degree (commonLabelGroup i₀ Γ L h) :=
        Finset.sum_le_sum_of_subset_of_nonneg himg_subZ hdeg_nn
      have hdeg_le : ((AffineFamily.degree
          ((Γr.filter (fun pq => (V pq).dimension = h)).image Z) : ℚ) : ℝ) ≤
          ((AffineFamily.degree (commonLabelGroup i₀ Γ L h) : ℚ) : ℝ) := by
        exact_mod_cast hdeg_le_Q
      have hmass' := hmass (Γr.filter (fun pq => (V pq).dimension = h))
        (Finset.filter_subset _ _)
      have hlower_nn : 0 ≤ commonEqualDimLower M i j :=
        commonEqualDimLower_nonneg M i j
      have hexp_pos : 0 < Real.exp (-θ * M.s i) := Real.exp_pos _
      have hc0_nn : 0 ≤ commonEqualDimLower M i j * Real.exp (-θ * M.s i) :=
        mul_nonneg hlower_nn hexp_pos.le
      have hrr : (ρ / (2 * (2 * (d : ℝ) + 1))) *
          (((TrackD.poolPts (T.sources i)).card : ℝ) *
            (TrackD.poolPts (T.targets i)).card) ≤
          ((Γr.filter (fun pq => (V pq).dimension = h)).card : ℝ) := by
        have := hdense'
        rwa [mul_assoc] at this
      have h1 : (commonEqualDimLower M i j * Real.exp (-θ * M.s i)) *
          ((ρ / (2 * (2 * (d : ℝ) + 1))) *
            (((TrackD.poolPts (T.sources i)).card : ℝ) *
              (TrackD.poolPts (T.targets i)).card)) ≤
          (commonEqualDimLower M i j * Real.exp (-θ * M.s i)) *
            ((Γr.filter (fun pq => (V pq).dimension = h)).card : ℝ) :=
        mul_le_mul_of_nonneg_left hrr hc0_nn
      have h2 : (commonEqualDimLower M i j * Real.exp (-θ * M.s i)) *
          ((Γr.filter (fun pq => (V pq).dimension = h)).card : ℝ) ≤
          (((TrackD.poolPts (T.sources i)).card : ℝ) *
            (TrackD.poolPts (T.targets i)).card) *
            ((AffineFamily.degree
              ((Γr.filter (fun pq => (V pq).dimension = h)).image Z) : ℚ) : ℝ) := by
        have := hmass'
        ring_nf at this ⊢
        linarith [this]
      have h3 : (((TrackD.poolPts (T.sources i)).card : ℝ) *
          (TrackD.poolPts (T.targets i)).card) *
          ((AffineFamily.degree
            ((Γr.filter (fun pq => (V pq).dimension = h)).image Z) : ℚ) : ℝ) ≤
          (((TrackD.poolPts (T.sources i)).card : ℝ) *
            (TrackD.poolPts (T.targets i)).card) *
            ((AffineFamily.degree (commonLabelGroup i₀ Γ L h) : ℚ) : ℝ) :=
        mul_le_mul_of_nonneg_left hdeg_le (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      have h4 : (commonEqualDimLower M i j * Real.exp (-θ * M.s i)) *
          ((ρ / (2 * (2 * (d : ℝ) + 1))) *
            (((TrackD.poolPts (T.sources i)).card : ℝ) *
              (TrackD.poolPts (T.targets i)).card)) ≤
          (((TrackD.poolPts (T.sources i)).card : ℝ) *
            (TrackD.poolPts (T.targets i)).card) *
            ((AffineFamily.degree (commonLabelGroup i₀ Γ L h) : ℚ) : ℝ) :=
        h1.trans (h2.trans h3)
      have h5 : ((commonEqualDimLower M i j * Real.exp (-θ * M.s i)) *
          (ρ / (2 * (2 * (d : ℝ) + 1)))) *
          (((TrackD.poolPts (T.sources i)).card : ℝ) *
            (TrackD.poolPts (T.targets i)).card) ≤
          ((AffineFamily.degree (commonLabelGroup i₀ Γ L h) : ℚ) : ℝ) *
            (((TrackD.poolPts (T.sources i)).card : ℝ) *
              (TrackD.poolPts (T.targets i)).card) := by
        calc ((commonEqualDimLower M i j * Real.exp (-θ * M.s i)) *
              (ρ / (2 * (2 * (d : ℝ) + 1)))) *
              (((TrackD.poolPts (T.sources i)).card : ℝ) *
                (TrackD.poolPts (T.targets i)).card)
            = (commonEqualDimLower M i j * Real.exp (-θ * M.s i)) *
              ((ρ / (2 * (2 * (d : ℝ) + 1))) *
                (((TrackD.poolPts (T.sources i)).card : ℝ) *
                  (TrackD.poolPts (T.targets i)).card)) := by ring
          _ ≤ (((TrackD.poolPts (T.sources i)).card : ℝ) *
              (TrackD.poolPts (T.targets i)).card) *
              ((AffineFamily.degree (commonLabelGroup i₀ Γ L h) : ℚ) : ℝ) := h4
          _ = ((AffineFamily.degree (commonLabelGroup i₀ Γ L h) : ℚ) : ℝ) *
              (((TrackD.poolPts (T.sources i)).card : ℝ) *
                (TrackD.poolPts (T.targets i)).card) := by ring
      have hfin : (commonEqualDimLower M i j * Real.exp (-θ * M.s i)) *
          (ρ / (2 * (2 * (d : ℝ) + 1))) ≤
          ((AffineFamily.degree (commonLabelGroup i₀ Γ L h) : ℚ) : ℝ) :=
        le_of_mul_le_mul_right h5 hSpos
      calc commonEqualDimLower M i j * Real.exp (-θ * M.s i) *
            (ρ / (2 * (2 * (d : ℝ) + 1)))
          = (commonEqualDimLower M i j * Real.exp (-θ * M.s i)) *
            (ρ / (2 * (2 * (d : ℝ) + 1))) := by ring
        _ ≤ ((AffineFamily.degree (commonLabelGroup i₀ Γ L h) : ℚ) : ℝ) := hfin

end
end DistinctDistances.SparseCones
