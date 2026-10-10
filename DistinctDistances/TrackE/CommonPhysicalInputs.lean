import DistinctDistances.TrackE.CommonPhysicalData
import DistinctDistances.TrackE.CommonEndpointInputs

/-! Page-sized physical retention inputs, sparse-cones.tex:99–141. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- The literal original union is a good pool at every fixed precision. -/
theorem selected_common_union_good {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} (M : CommonPoolProfile T)
    (θ η ρ : ℝ) (hθ : 0 < θ) (hη : 0 < η) (hρ : 0 < ρ) :
    ∀ᶠ i in atTop, TrackD.PoolGood (regime.P i) θ η 1 ρ
      (T.sources i ∪ T.targets i) (M.s i) M.b := by
  have hpieces := selected_piece_good_eventually T θ hθ η hη 1 le_rfl
  have hlim := M.limit ρ hρ
  have htol := selection_tolerance_tendsto_zero T.precision T.precision_grows
  have htol_le : ∀ᶠ i in atTop, selectionTolerance (T.precision i) ≤ θ :=
    (htol.eventually (Iio_mem_nhds hθ)).mono fun _ hi => hi.le
  filter_upwards [hpieces, hlim, htol_le] with i hpieces_i hlim_i htol_i
  have hQ := (T.certificate i).good
  have hsub : T.sources i ∪ T.targets i ⊆ (T.partition i).pieces :=
    Finset.union_subset (T.certificate i).sources_subset (T.certificate i).targets_subset
  have hwidth : ∀ X ∈ T.sources i ∪ T.targets i, X.width = M.s i :=
    fun X hX => M.width i X hX
  have hclose : ∀ X ∈ T.sources i ∪ T.targets i, ∀ a,
      |X.path.time a - M.b a| ≤ ρ :=
    fun X hX a => hlim_i X hX a
  have hN : 0 < TrackD.cfgN (regime.P i) := by
    have h2 : 2 ≤ (regime.P i).card := regime.card_ge_two i
    unfold TrackD.cfgN
    have hpos : 0 < ((regime.P i).card : ℝ) := by
      have : 0 < (regime.P i).card := by omega
      exact_mod_cast this
    linarith
  have hpool_small := pool_good_of_partition (regime.P i) (T.partition i)
    (F.delta i) (selectionTolerance (T.precision i)) (selectionTolerance (T.precision i))
    (selectionScale (T.precision i)) (selectionScale (T.precision i)) ρ (M.s i) M.b
    hN hQ _ hsub hwidth hclose
  have hcount : (((T.sources i ∪ T.targets i).card : ℕ) : ℝ) ≤
      Real.exp (θ * M.s i) := by
    calc (((T.sources i ∪ T.targets i).card : ℕ) : ℝ)
        ≤ Real.exp (selectionTolerance (T.precision i) * M.s i) :=
          hpool_small.count
      _ ≤ Real.exp (θ * M.s i) :=
          Real.exp_le_exp.mpr
            (mul_le_mul_of_nonneg_right htol_i (M.width_pos i).le)
  exact ⟨hpieces_i, hwidth, hlim_i, hcount, hpool_small.disjoint⟩

/-- At every physical interior time above -1 the test degree is eventually
at least one, including a negative testing time in the outer window. -/
theorem common_physical_test_degree_one {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} (M : CommonPoolProfile T)
    (τ : ℝ) (hτ : -1 < τ) :
    ∀ᶠ i in atTop, 1 ≤ TrackD.testDeg (TrackD.cfgB (regime.P i)) (M.s i) τ := by
  have hB_eq : ∀ i, TrackD.cfgB (regime.P i) = regime.B i := fun i => by
    simp [TrackD.cfgB, Regime.B, Regime.N]
  have h1τ : 0 < 1 + τ := by linarith
  apply Filter.Eventually.of_forall
  intro i
  rw [hB_eq i]
  have hBpos : 0 < regime.B i := regime.B_pos i
  have hs_pos : 0 < M.s i := M.width_pos i
  have hs_le : M.s i ≤ Real.log (regime.B i) := common_pool_width_le_logB M i
  have hge : (1 + τ) * M.s i ≤ Real.log (regime.B i) + τ * M.s i := by
    linarith [hs_le]
  have hpos : 0 < (1 + τ) * M.s i := mul_pos h1τ hs_pos
  have hnonneg : 0 ≤ Real.log (regime.B i) + τ * M.s i :=
    le_trans hpos.le hge
  have hBexp : regime.B i = Real.exp (Real.log (regime.B i)) :=
    (Real.exp_log hBpos).symm
  have htest : TrackD.testDeg (regime.B i) (M.s i) τ =
      Real.exp (Real.log (regime.B i) + τ * M.s i) := by
    unfold TrackD.testDeg
    conv_lhs => rw [hBexp]
    rw [← Real.exp_add]
  rw [htest]
  exact Real.one_le_exp hnonneg

/-- One original supported map for both roles; at the curve stage it uses
every assigned global terminal owner, including points later deleted. -/
theorem exists_selected_common_owner {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (j : ℕ) (hj : j < d) :
    ∃ α : ℕ → RPoint d → AffineVariety d,
      (∀ i, TrackD.CarrierAssignment (T.sources i ∪ T.targets i) j (α i)) ∧
      (j = d - 1 → ∀ i q, q ∈ TrackD.poolPts (T.sources i ∪ T.targets i) →
        ∀ Y, T.terminal i q = some Y → α i q = Y) := by
  classical
  -- Per-piece local carriers exist via minimal primes below the point ideal.
  have hpiece_exists : ∀ (i : ℕ) (X : TrackD.Piece d),
      X ∈ (T.sources i ∪ T.targets i) → ∀ q ∈ X.pts,
      ∃ Z : AffineVariety d, X.path.IsCarrier j Z ∧ TrackD.toC q ∈ Z := by
    intro i X hX q hq
    have hmem_pieces : X ∈ (T.partition i).pieces := by
      rcases Finset.mem_union.mp hX with h | h
      · exact (T.certificate i).sources_subset h
      · exact (T.certificate i).targets_subset h
    have hgood := ((T.certificate i).good.pieces_good X hmem_pieces).1
    have hsys : X.path.system j ≤ pointIdeal (TrackD.toC q) := by
      apply Ideal.span_le.mpr
      rintro f ⟨k, hk, rfl⟩
      change X.path.cut k ∈ MvPolynomial.vanishingIdeal ℂ {TrackD.toC q}
      rw [MvPolynomial.mem_vanishingIdeal_iff]
      intro z hz
      have hzx : z = TrackD.toC q := Set.mem_singleton_iff.mp hz
      subst hzx
      exact hgood.vanish q hq k
    haveI : (pointIdeal (TrackD.toC q)).IsPrime :=
      (pointIdeal_isMaximal (TrackD.toC q)).isPrime
    obtain ⟨I, hI, hIle⟩ := Ideal.exists_minimalPrimes_le hsys
    refine ⟨⟨I, hI.isPrime.isRadical⟩, hI, ?_⟩
    change TrackD.toC q ∈ MvPolynomial.zeroLocus ℂ I
    intro f hf
    have hfp : f ∈ pointIdeal (TrackD.toC q) := hIle hf
    have hvan : f ∈ MvPolynomial.vanishingIdeal ℂ {TrackD.toC q} := by
      simpa [pointIdeal] using hfp
    exact MvPolynomial.mem_vanishingIdeal_iff.mp hvan _ (by simp)
  -- Disjointness of the union follows from the partition certificate.
  have hdisjoint_union : ∀ i,
      ((T.sources i ∪ T.targets i : Finset (TrackD.Piece d)) : Set (TrackD.Piece d)).PairwiseDisjoint
        TrackD.Piece.pts := by
    intro i
    have hQdis := (T.certificate i).good.pieces_disjoint
    have hsub : T.sources i ∪ T.targets i ⊆ (T.partition i).pieces :=
      Finset.union_subset (T.certificate i).sources_subset
        (T.certificate i).targets_subset
    exact hQdis.subset (Finset.coe_subset.mpr hsub)
  -- Pool-level existence packages a witness piece with the carrier.
  have hpool_exists : ∀ (i : ℕ) (q : RPoint d),
      q ∈ TrackD.poolPts (T.sources i ∪ T.targets i) →
      ∃ Z : AffineVariety d, ∃ X ∈ (T.sources i ∪ T.targets i),
        q ∈ X.pts ∧ X.path.IsCarrier j Z ∧ TrackD.toC q ∈ Z := by
    intro i q hq
    simp only [TrackD.poolPts, Finset.mem_biUnion] at hq
    obtain ⟨X, hX, hqX⟩ := hq
    obtain ⟨Z, hcarrier, hpoint⟩ := hpiece_exists i X hX q hqX
    exact ⟨Z, X, hX, hqX, hcarrier, hpoint⟩
  -- Fallback map: chosen carrier on the pool, whole space elsewhere.
  let fallback : ℕ → RPoint d → AffineVariety d := fun i q =>
    dite (q ∈ TrackD.poolPts (T.sources i ∪ T.targets i))
      (fun h => Classical.choose (hpool_exists i q h))
      (fun _ => AffineVariety.whole)
  have hfallback_spec : ∀ (i : ℕ) (q : RPoint d)
      (h : q ∈ TrackD.poolPts (T.sources i ∪ T.targets i)),
      ∃ X ∈ (T.sources i ∪ T.targets i),
        q ∈ X.pts ∧ X.path.IsCarrier j (fallback i q) ∧
          TrackD.toC q ∈ (fallback i q) := by
    intro i q h
    have hfb : fallback i q = Classical.choose (hpool_exists i q h) := by
      simp only [fallback, dif_pos h]
    rw [hfb]
    exact Classical.choose_spec (hpool_exists i q h)
  have hfallback : ∀ i,
      TrackD.CarrierAssignment (T.sources i ∪ T.targets i) j (fallback i) := by
    intro i X hX q hqX
    obtain ⟨X', hX', hqX', hcarrier', hpoint'⟩ := hfallback_spec i q (by
      simp only [TrackD.poolPts, Finset.mem_biUnion]
      exact ⟨X, hX, hqX⟩)
    -- Uniqueness of the containing piece via disjointness.
    have hXX : X' = X := by
      by_contra hne
      have hdis := hdisjoint_union i (Finset.mem_coe.mpr hX')
        (Finset.mem_coe.mpr hX) hne
      exact (Finset.disjoint_left.mp hdis) hqX' hqX
    subst hXX
    exact ⟨hcarrier', hpoint'⟩
  -- Terminal override only at the curve stage j = d - 1.
  let α : ℕ → RPoint d → AffineVariety d := fun i q =>
    dite (j = d - 1) (fun _ => (T.terminal i q).getD (fallback i q))
      (fun _ => fallback i q)
  have hα_eq_fallback : ∀ i q, j ≠ d - 1 → α i q = fallback i q := by
    intro i q hne
    simp only [α, dif_neg hne]
  have hα_eq_terminal : ∀ i q (h : j = d - 1),
      α i q = (T.terminal i q).getD (fallback i q) := by
    intro i q h
    simp only [α, dif_pos h]
  refine ⟨α, ?_, ?_⟩
  · intro i X hX q hqX
    by_cases hj_eq : j = d - 1
    · have hαeq := hα_eq_terminal i q hj_eq
      rw [hαeq]
      rcases hτ : T.terminal i q with _ | Y
      · simp only [Option.getD_none]
        exact (hfallback i X hX q hqX)
      · simp only [Option.getD_some]
        have hmem_pieces : X ∈ (T.partition i).pieces := by
          rcases Finset.mem_union.mp hX with h | h
          · exact (T.certificate i).sources_subset h
          · exact (T.certificate i).targets_subset h
        have hterm := (T.certificate i).terminal.carrier X hmem_pieces q hqX Y hτ
        have hterm' : X.path.IsCarrier j Y ∧ TrackD.toC q ∈ Y := by
          rw [hj_eq]
          exact hterm
        exact hterm'
    · rw [hα_eq_fallback i q hj_eq]
      exact (hfallback i X hX q hqX)
  · intro hj_eq i q hqpool Y hY
    rw [hα_eq_terminal i q hj_eq, hY, Option.getD_some]

/-- Per-piece losses bound the omitted physical points of either role.
The original supported owner turns every nonreal owner into a local carrier. -/
theorem common_physical_omissions_card (pl allpl : Finset (TrackD.Piece d))
    (hsub : pl ⊆ allpl)
    (hdis : (pl : Set (TrackD.Piece d)).PairwiseDisjoint TrackD.Piece.pts)
    (j : ℕ) (E : Finset (Poly d)) (g : Poly d)
    (α : RPoint d → AffineVariety d) (hα : TrackD.CarrierAssignment allpl j α)
    (θ : ℝ)
    (hregular : ∀ X ∈ pl, ((X.pts.filter (fun q =>
      ¬ TrackD.JacRegularAt allpl j E g (TrackD.toC q))).card : ℝ) ≤
        (θ / 2) * X.pts.card)
    (hnonreal : ∀ X ∈ pl, ((X.pts.filter (fun q =>
      ∃ Z ∈ X.path.localCarriers j (TrackD.toC q),
        TrackD.IsFlat Z ∧ ¬ TrackD.IsRealFlat Z)).card : ℝ) ≤
          (θ / 2) * X.pts.card) :
    (((TrackD.poolPts pl) \ retainedCommonPool pl allpl j E g α).card : ℝ) ≤
      θ * (TrackD.poolPts pl).card := by
  classical
  have hsdiff : (TrackD.poolPts pl \ retainedCommonPool pl allpl j E g α) =
      (TrackD.poolPts pl).filter (fun q =>
        ¬ (TrackD.JacRegularAt allpl j E g (TrackD.toC q) ∧
          keepRealCarrier (α q))) := by
    ext q
    simp only [retainedCommonPool, Finset.mem_sdiff, Finset.mem_filter]
    tauto
  rw [hsdiff]
  -- Per-piece omitted set is covered by the two bad sets.
  have hsubX : ∀ X ∈ pl,
      (X.pts.filter (fun q =>
        ¬ (TrackD.JacRegularAt allpl j E g (TrackD.toC q) ∧
          keepRealCarrier (α q)))) ⊆
      ((X.pts.filter (fun q =>
        ¬ TrackD.JacRegularAt allpl j E g (TrackD.toC q))) ∪
       (X.pts.filter (fun q =>
        ∃ Z ∈ X.path.localCarriers j (TrackD.toC q),
          TrackD.IsFlat Z ∧ ¬ TrackD.IsRealFlat Z))) := by
    intro X hX q hq
    rw [Finset.mem_filter] at hq
    obtain ⟨hqX, hneg⟩ := hq
    by_cases hJ : TrackD.JacRegularAt allpl j E g (TrackD.toC q)
    · -- Regular, so the owner must be nonreal; use α q as witness.
      have hkeep_neg : ¬ keepRealCarrier (α q) := fun hkeep =>
        hneg ⟨hJ, hkeep⟩
      have hflat : TrackD.IsFlat (α q) := by
        by_contra hflat
        exact hkeep_neg (fun h => absurd h hflat)
      have hnonreal_flat : ¬ TrackD.IsRealFlat (α q) := by
        intro hreal
        exact hkeep_neg (fun _ => hreal)
      have hXall : X ∈ allpl := hsub hX
      obtain ⟨hcarrier, hpoint⟩ := hα X hXall q hqX
      have hmem : (α q) ∈ X.path.localCarriers j (TrackD.toC q) :=
        ⟨hcarrier, hpoint⟩
      rw [Finset.mem_union]
      exact Or.inr (Finset.mem_filter.mpr
        ⟨hqX, (α q), hmem, hflat, hnonreal_flat⟩)
    · rw [Finset.mem_union]
      exact Or.inl (Finset.mem_filter.mpr ⟨hqX, hJ⟩)
  have hcardX : ∀ X ∈ pl,
      (((X.pts.filter (fun q =>
        ¬ (TrackD.JacRegularAt allpl j E g (TrackD.toC q) ∧
          keepRealCarrier (α q)))).card : ℝ) ≤
      ((X.pts.filter (fun q =>
        ¬ TrackD.JacRegularAt allpl j E g (TrackD.toC q))).card : ℝ) +
      ((X.pts.filter (fun q =>
        ∃ Z ∈ X.path.localCarriers j (TrackD.toC q),
          TrackD.IsFlat Z ∧ ¬ TrackD.IsRealFlat Z)).card : ℝ)) := by
    intro X hX
    set R := X.pts.filter (fun q =>
      ¬ TrackD.JacRegularAt allpl j E g (TrackD.toC q)) with hRdef
    set N := X.pts.filter (fun q => ∃ Z ∈ X.path.localCarriers j (TrackD.toC q),
      TrackD.IsFlat Z ∧ ¬ TrackD.IsRealFlat Z) with hNdef
    set O := X.pts.filter (fun q =>
      ¬ (TrackD.JacRegularAt allpl j E g (TrackD.toC q) ∧
        keepRealCarrier (α q))) with hOdef
    have hle_nat : O.card ≤ (R ∪ N).card :=
      Finset.card_le_card (hsubX X hX)
    have hunion_nat : ((R ∪ N).card : ℝ) ≤ (R.card : ℝ) + (N.card : ℝ) := by
      have hnat : (R ∪ N).card ≤ R.card + N.card :=
        Finset.card_union_le R N
      have hcast : ((R ∪ N).card : ℝ) ≤ ((R.card + N.card : ℕ) : ℝ) :=
        Nat.cast_le.mpr hnat
      rwa [Nat.cast_add] at hcast
    exact (Nat.cast_le.mpr hle_nat).trans hunion_nat
  -- Global omitted set is covered by the per-piece omitted sets.
  have hglobal_sub : ((TrackD.poolPts pl).filter (fun q =>
        ¬ (TrackD.JacRegularAt allpl j E g (TrackD.toC q) ∧
          keepRealCarrier (α q)))) ⊆
      pl.biUnion (fun X => X.pts.filter (fun q =>
        ¬ (TrackD.JacRegularAt allpl j E g (TrackD.toC q) ∧
          keepRealCarrier (α q)))) := by
    intro q hq
    rw [Finset.mem_filter] at hq
    obtain ⟨hqS, hneg⟩ := hq
    simp only [TrackD.poolPts, Finset.mem_biUnion] at hqS
    obtain ⟨X, hX, hqX⟩ := hqS
    exact Finset.mem_biUnion.mpr ⟨X, hX, Finset.mem_filter.mpr ⟨hqX, hneg⟩⟩
  have hglobal_nat : (((TrackD.poolPts pl).filter (fun q =>
        ¬ (TrackD.JacRegularAt allpl j E g (TrackD.toC q) ∧
          keepRealCarrier (α q)))).card) ≤
      ∑ X ∈ pl, (X.pts.filter (fun q =>
        ¬ (TrackD.JacRegularAt allpl j E g (TrackD.toC q) ∧
          keepRealCarrier (α q)))).card :=
    (Finset.card_le_card hglobal_sub).trans Finset.card_biUnion_le
  have hglobal : ((((TrackD.poolPts pl).filter (fun q =>
        ¬ (TrackD.JacRegularAt allpl j E g (TrackD.toC q) ∧
          keepRealCarrier (α q)))).card : ℝ) ≤
      ∑ X ∈ pl, ((X.pts.filter (fun q =>
        ¬ (TrackD.JacRegularAt allpl j E g (TrackD.toC q) ∧
          keepRealCarrier (α q)))).card : ℝ)) := by
    have h : ((((TrackD.poolPts pl).filter (fun q =>
        ¬ (TrackD.JacRegularAt allpl j E g (TrackD.toC q) ∧
          keepRealCarrier (α q)))).card : ℝ) ≤
        (((∑ X ∈ pl, (X.pts.filter (fun q =>
          ¬ (TrackD.JacRegularAt allpl j E g (TrackD.toC q) ∧
            keepRealCarrier (α q)))).card : ℕ)) : ℝ)) :=
      Nat.cast_le.mpr hglobal_nat
    rwa [Nat.cast_sum] at h
  have hsum_split : (∑ X ∈ pl, ((X.pts.filter (fun q =>
        ¬ (TrackD.JacRegularAt allpl j E g (TrackD.toC q) ∧
          keepRealCarrier (α q)))).card : ℝ)) ≤
      (∑ X ∈ pl, ((X.pts.filter (fun q =>
        ¬ TrackD.JacRegularAt allpl j E g (TrackD.toC q))).card : ℝ)) +
      (∑ X ∈ pl, ((X.pts.filter (fun q =>
        ∃ Z ∈ X.path.localCarriers j (TrackD.toC q),
          TrackD.IsFlat Z ∧ ¬ TrackD.IsRealFlat Z)).card : ℝ)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun X hX => hcardX X hX)
  have hsum_reg : (∑ X ∈ pl, ((X.pts.filter (fun q =>
      ¬ TrackD.JacRegularAt allpl j E g (TrackD.toC q))).card : ℝ)) ≤
      (θ / 2) * ∑ X ∈ pl, (X.pts.card : ℝ) := by
    calc ∑ X ∈ pl, ((X.pts.filter (fun q =>
          ¬ TrackD.JacRegularAt allpl j E g (TrackD.toC q))).card : ℝ)
        ≤ ∑ X ∈ pl, (θ / 2) * (X.pts.card : ℝ) :=
          Finset.sum_le_sum (fun X hX => hregular X hX)
      _ = (θ / 2) * ∑ X ∈ pl, (X.pts.card : ℝ) := by rw [Finset.mul_sum]
  have hsum_nonreal : (∑ X ∈ pl, ((X.pts.filter (fun q =>
      ∃ Z ∈ X.path.localCarriers j (TrackD.toC q),
        TrackD.IsFlat Z ∧ ¬ TrackD.IsRealFlat Z)).card : ℝ)) ≤
      (θ / 2) * ∑ X ∈ pl, (X.pts.card : ℝ) := by
    calc ∑ X ∈ pl, ((X.pts.filter (fun q =>
          ∃ Z ∈ X.path.localCarriers j (TrackD.toC q),
            TrackD.IsFlat Z ∧ ¬ TrackD.IsRealFlat Z)).card : ℝ)
        ≤ ∑ X ∈ pl, (θ / 2) * (X.pts.card : ℝ) :=
          Finset.sum_le_sum (fun X hX => hnonreal X hX)
      _ = (θ / 2) * ∑ X ∈ pl, (X.pts.card : ℝ) := by rw [Finset.mul_sum]
  have hpool_eq : ((TrackD.poolPts pl).card : ℝ) =
      ∑ X ∈ pl, (X.pts.card : ℝ) := by
    have hnat : (TrackD.poolPts pl).card = ∑ X ∈ pl, X.pts.card := by
      unfold TrackD.poolPts
      exact Finset.card_biUnion (fun X hX Y hY hne =>
        hdis (Finset.mem_coe.mpr hX) (Finset.mem_coe.mpr hY) hne)
    rw [hnat, Nat.cast_sum]
  set G : ℝ := ((((TrackD.poolPts pl).filter (fun q =>
    ¬ (TrackD.JacRegularAt allpl j E g (TrackD.toC q) ∧
      keepRealCarrier (α q)))).card : ℕ) : ℝ) with hGdef
  set O : ℝ := ∑ X ∈ pl, ((X.pts.filter (fun q =>
    ¬ (TrackD.JacRegularAt allpl j E g (TrackD.toC q) ∧
      keepRealCarrier (α q)))).card : ℝ) with hOdef
  set Rsum : ℝ := ∑ X ∈ pl, ((X.pts.filter (fun q =>
    ¬ TrackD.JacRegularAt allpl j E g (TrackD.toC q))).card : ℝ) with hRsumdef
  set Nsum : ℝ := ∑ X ∈ pl, ((X.pts.filter (fun q => ∃ Z ∈
    X.path.localCarriers j (TrackD.toC q),
      TrackD.IsFlat Z ∧ ¬ TrackD.IsRealFlat Z)).card : ℝ) with hNsumdef
  set S : ℝ := ∑ X ∈ pl, (X.pts.card : ℝ) with hSdef
  have h1 : G ≤ O := hglobal
  have h2 : O ≤ Rsum + Nsum := hsum_split
  have h3 : Rsum + Nsum ≤ (θ / 2) * S + ((θ / 2) * S) :=
    add_le_add hsum_reg hsum_nonreal
  have heq : (θ / 2) * S + ((θ / 2) * S) = θ * S := by ring
  have h13 : G ≤ θ * S := (h1.trans h2).trans ((h3).trans_eq heq)
  have hSf : S = ((TrackD.poolPts pl).card : ℝ) := hpool_eq.symm
  rw [hSf] at h13
  simpa [hGdef] using h13

/-- At every retained point the supported original owner is the unique
smooth carrier of the complete union, with the common Jacobian tangent. -/
theorem common_retained_owner_regular (pl allpl : Finset (TrackD.Piece d))
    (hsub : pl ⊆ allpl) (j : ℕ) (E : Finset (Poly d)) (g : Poly d)
    (α : RPoint d → AffineVariety d) (hα : TrackD.CarrierAssignment allpl j α)
    (q : RPoint d) (hq : q ∈ retainedCommonPool pl allpl j E g α) :
    TrackD.PoolCarrier allpl j (α q) ∧ TrackD.toC q ∈ α q ∧
    (∀ Z, TrackD.PoolCarrier allpl j Z ∧ TrackD.toC q ∈ Z → Z = α q) ∧
    (α q).IsSmoothAt (TrackD.toC q) ∧
    (α q).tangentSpace (TrackD.toC q) = TrackD.jacKer E (TrackD.toC q) ∧
    MvPolynomial.eval (TrackD.toC q) g ≠ 0 ∧ keepRealCarrier (α q) := by
  classical
  unfold retainedCommonPool at hq
  rw [Finset.mem_filter] at hq
  obtain ⟨hqpool, hJac, hkeep⟩ := hq
  obtain ⟨heval, Z, hZmem, hZuniq, hZsmooth, hZtangent⟩ := hJac
  have hqX : ∃ X ∈ pl, q ∈ X.pts := by
    simp only [TrackD.poolPts, Finset.mem_biUnion] at hqpool
    exact hqpool
  obtain ⟨X, hXpl, hqX⟩ := hqX
  have hXall : X ∈ allpl := hsub hXpl
  obtain ⟨hcarrier, hpoint⟩ := hα X hXall q hqX
  have hαPool : TrackD.PoolCarrier allpl j (α q) :=
    ⟨X, hXall, hcarrier, q, hqX, hpoint⟩
  have hZeq : Z = α q := (hZuniq (α q) ⟨hαPool, hpoint⟩).symm
  subst hZeq
  exact ⟨hαPool, hpoint, hZuniq, hZsmooth, hZtangent, heval, hkeep⟩

/-- Equal physical pools use exactly the same point deletion and map. -/
theorem common_physical_same_pool {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} {M : CommonPoolProfile T} {j : ℕ} {τ : ℝ}
    (W : CommonPhysicalSequence T M j τ) (i : ℕ)
    (hpool : T.sources i = T.targets i) : W.sources i = W.targets i := by
  simp only [CommonPhysicalSequence.sources, CommonPhysicalSequence.targets, hpool]

end
end DistinctDistances.SparseCones
