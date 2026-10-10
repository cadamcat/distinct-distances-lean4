import DistinctDistances.TrackE.CommonRankAlternativeData
import DistinctDistances.Bridges.PairFlatEnvelope
import DistinctDistances.Bridges.AffineRank
import DistinctDistances.TrackA.Hilbert

/-! Hilbert bounds for one dimension group of a label envelope,
sparse-cones.tex:262–275 (affine form of `direction_envelope_component_rank`). -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ}

/-- The actual chart labels of a graph in the shared coordinates `Fin (d + d)`
(the coordinates of `commonProductImage` and `commonPairEquation`). -/
def commonLabelPoints (i₀ : Fin d) (Γ : Finset (RPoint d × RPoint d)) :
    Set (Point (d + d)) :=
  (fun pq : RPoint d × RPoint d => fun k =>
    TrackD.labelPt i₀ (TrackD.toC pq.1) (TrackD.toC pq.2) (finSumFinEquiv.symm k)) ''
    (Γ : Set (RPoint d × RPoint d))

/-- The irreducible components of dimension `h` of the degree-`L` label envelope,
including components that contain no label. -/
def commonLabelGroup (i₀ : Fin d) (Γ : Finset (RPoint d × RPoint d)) (L h : ℕ) :
    AffineFamily.Family (d + d) :=
  (Bridges.envelopeComponents (commonLabelPoints i₀ Γ) L).filter (fun V => V.dimension = h)

/-- Reindexing of the pair label set along `finSumFinEquiv`: the rank in pair
coordinates equals the affine Hilbert rank in `Fin (d+d)` coordinates. -/
private theorem commonLabelRank_eq_hilbertOfSet (d : ℕ) (i₀ : Fin d)
    (Γ : Finset (RPoint d × RPoint d)) (L : ℕ) :
    commonLabelRank i₀ Γ L = hilbertOfSet (commonLabelPoints i₀ Γ) L := by
  classical
  -- Pair-coordinate label set.
  let S : Set (Fin d ⊕ Fin d → ℂ) :=
    (fun pq : RPoint d × RPoint d =>
      TrackD.labelPt i₀ (TrackD.toC pq.1) (TrackD.toC pq.2)) '' (Γ : Set (RPoint d × RPoint d))
  have hS : S = (fun pq : RPoint d × RPoint d =>
      TrackD.labelPt i₀ (TrackD.toC pq.1) (TrackD.toC pq.2)) '' (Γ : Set (RPoint d × RPoint d)) := rfl
  have hRank : commonLabelRank i₀ Γ L = restrictionRank S L := by
    unfold commonLabelRank
    rfl
  have hPts : commonLabelPoints i₀ Γ =
      (fun x : Fin d ⊕ Fin d → ℂ => fun i => x (finSumFinEquiv.symm i)) '' S := by
    unfold commonLabelPoints S
    rw [Set.image_image]
  rw [hRank, hPts]
  -- Adapted from `Bridges.restrictionRank_eq_hilbertOfSet` with
  -- `e := finSumFinEquiv : Fin d ⊕ Fin d ≃ Fin (d + d)`.
  let e : (Fin d ⊕ Fin d) ≃ Fin (d + d) := finSumFinEquiv
  let T' : Set (Point (d + d)) :=
    (fun x : Fin d ⊕ Fin d → ℂ => fun i => x (e.symm i)) '' S
  let V := AffineVariety.closure T'
  let rename := MvPolynomial.renameEquiv ℂ e
  let q : MvPolynomial.restrictTotalDegree (Fin d ⊕ Fin d) ℂ L →ₗ[ℂ] (Poly (d + d) ⧸ V.ideal) :=
    (Ideal.Quotient.mkₐ ℂ V.ideal).toLinearMap.comp
      (rename.toLinearMap.comp (MvPolynomial.restrictTotalDegree (Fin d ⊕ Fin d) ℂ L).subtype)
  have hrange : LinearMap.range q = V.restrictionSpace L := by
    ext y
    change (∃ f, q f = y) ↔ ∃ f,
      f ∈ OAI.QuarticPowerFree.totalSpace L ∧
        (Ideal.Quotient.mkₐ ℂ V.ideal).toLinearMap f = y
    constructor
    · rintro ⟨f, rfl⟩
      refine ⟨rename f.val, OAI.QuarticPowerFree.mem_totalSpace.mpr ?_, rfl⟩
      rw [MvPolynomial.totalDegree_renameEquiv]
      exact (MvPolynomial.mem_restrictTotalDegree _ _ _).mp f.property
    · rintro ⟨f, hf, rfl⟩
      have hdegree : (rename.symm f).totalDegree ≤ L := by
        rw [MvPolynomial.renameEquiv_symm, MvPolynomial.totalDegree_renameEquiv]
        exact OAI.QuarticPowerFree.mem_totalSpace.mp hf
      let p : MvPolynomial.restrictTotalDegree (Fin d ⊕ Fin d) ℂ L :=
        ⟨rename.symm f, (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr hdegree⟩
      refine ⟨p, ?_⟩
      change Ideal.Quotient.mk V.ideal (rename (rename.symm f)) =
        Ideal.Quotient.mk V.ideal f
      rw [rename.apply_symm_apply]
  have hker : LinearMap.ker (restrictionMap S L) = LinearMap.ker q := by
    ext f
    change (restrictionMap S L f = 0) ↔
      Ideal.Quotient.mk V.ideal (rename f.val) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    change (restrictionMap S L f = 0) ↔
      ∀ x ∈ T', MvPolynomial.aeval x (rename f.val) = 0
    constructor
    · intro hf x hx
      obtain ⟨z, hz, rfl⟩ := hx
      have hzero := congrFun hf ⟨z, hz⟩
      change MvPolynomial.aeval z f.val = 0 at hzero
      simpa only [rename, MvPolynomial.renameEquiv_apply, MvPolynomial.aeval_rename,
        Function.comp_def, Equiv.symm_apply_apply] using hzero
    · intro hf
      funext z
      have hzero := hf (fun i => z.val (e.symm i)) ⟨z.val, z.property, rfl⟩
      change MvPolynomial.aeval z.val f.val = 0
      simpa only [rename, MvPolynomial.renameEquiv_apply, MvPolynomial.aeval_rename,
        Function.comp_def, Equiv.symm_apply_apply] using hzero
  have he := (restrictionMap S L).finrank_range_add_finrank_ker
  have hq := q.finrank_range_add_finrank_ker
  rw [← hker] at hq
  change Module.finrank ℂ (LinearMap.range (restrictionMap S L)) =
    Module.finrank ℂ (V.restrictionSpace L)
  rw [← hrange]
  exact Nat.add_right_cancel (he.trans hq.symm)

/-- The locus of a dimension group is a subvariety of the full envelope. -/
private theorem commonLabelGroup_subvariety (d : ℕ) (i₀ : Fin d)
    (Γ : Finset (RPoint d × RPoint d)) (L h : ℕ) :
    (AffineFamily.locus (commonLabelGroup i₀ Γ L h)).Subvariety
      (envelope (commonLabelPoints i₀ Γ) L) := by
  rw [AffineVariety.subvariety_iff_points_subset, AffineFamily.points_locus]
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨V, hVmem, hxV⟩ := hx
  -- `V` is a component of the envelope.
  have hVF : V ∈ Bridges.envelopeComponents (commonLabelPoints i₀ Γ) L :=
    Finset.mem_filter.mp hVmem |>.1
  obtain ⟨W, _, rfl⟩ := Finset.mem_image.mp hVF
  -- Its points lie in the envelope's points.
  have hsub : W.variety.points ⊆ (envelope (commonLabelPoints i₀ Γ) L).points := by
    intro y hy
    have hmem : y ∈ (envelope (commonLabelPoints i₀ Γ) L).points := by
      rw [AffineVariety.points_components]
      exact Set.mem_iUnion.mpr ⟨W, hy⟩
    exact hmem
  exact hsub hxV

/-- Closure is monotone under point inclusion. -/
private theorem closure_subvariety_of_subset {n : ℕ} (T : Set (Point n))
    (W : AffineVariety n) (h : T ⊆ W.points) :
    (AffineVariety.closure T).Subvariety W := by
  show W.ideal ≤ (AffineVariety.closure T).ideal
  have h1 : W.ideal = MvPolynomial.vanishingIdeal ℂ W.points := by
    rw [AffineVariety.vanishingIdeal_points]
  have h2 : (AffineVariety.closure T).ideal = MvPolynomial.vanishingIdeal ℂ T := rfl
  rw [h1, h2]
  exact MvPolynomial.vanishingIdeal_anti_mono (k := ℂ) h

/-- One constant, fixed before graphs and degrees: the lower Hilbert bound of a
dimension group at the defining degree is below the label rank, and every
graph whose labels lie on that group has rank at most its degree times
`(E+h).choose h` at every degree `E`. -/
theorem common_label_group_rank (d : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (i₀ : Fin d) (Γ : Finset (RPoint d × RPoint d)) (L : ℕ),
      1 ≤ L → ∀ h : ℕ,
        c * ((AffineFamily.degree (commonLabelGroup i₀ Γ L h) : ℚ) : ℝ) * (L : ℝ) ^ h ≤
          commonLabelRank i₀ Γ L ∧
        ∀ Γ'' : Finset (RPoint d × RPoint d),
          commonLabelPoints i₀ Γ'' ⊆
            (AffineFamily.locus (commonLabelGroup i₀ Γ L h)).points →
          ∀ E : ℕ, (commonLabelRank i₀ Γ'' E : ℝ) ≤
            ((AffineFamily.degree (commonLabelGroup i₀ Γ L h) : ℚ) : ℝ) *
              ((E + h).choose h : ℝ) := by
  classical
  obtain ⟨c0, hc0, hlow⟩ := TrackA.poly_hilbert_at_L (d + d)
  have hc0R : (0 : ℝ) < ((c0 : ℚ) : ℝ) := by exact_mod_cast hc0
  refine ⟨((c0 : ℚ) : ℝ), hc0R, ?_⟩
  intro i₀ Γ L hL h
  -- The dimension group and its envelope.
  set T0 := commonLabelPoints i₀ Γ with hT0def
  set G := commonLabelGroup i₀ Γ L h with hGdef
  set E0 := envelope T0 L with hE0def
  have hGsub : G ⊆ Bridges.envelopeComponents T0 L := by
    rw [hGdef, hT0def]
    unfold commonLabelGroup
    exact Finset.filter_subset _ _
  have hGirr : ∀ V ∈ G, V.IsIrreducible := by
    intro V hV
    have hVF : V ∈ Bridges.envelopeComponents T0 L := hGsub hV
    obtain ⟨W, _, rfl⟩ := Finset.mem_image.mp hVF
    exact W.irreducible
  have hGpure : AffineFamily.IsPure G h := by
    intro V hV
    obtain ⟨hVF, hdim⟩ := Finset.mem_filter.mp hV
    exact ⟨hGirr V hV, hdim⟩
  have hGdef : AffineFamily.ComponentsDefinedInDegree G L :=
    Bridges.envelope_components_defined T0 L G hGsub
  -- Lower Hilbert bound at the defining degree (in ℚ).
  have hlowQ := hlow G h L hGpure hL hGdef
  -- Transport to ℝ.
  have hlowR : ((c0 : ℚ) : ℝ) * ((AffineFamily.degree G : ℚ) : ℝ) * (L : ℝ) ^ h ≤
      ((AffineFamily.hilbert G L : ℕ) : ℝ) := by
    have hQ := hlowQ
    -- `hlowQ : c0 * degree * (L:ℚ)^h ≤ (hilbert:ℚ)`
    have hcast : (((AffineFamily.hilbert G L : ℕ) : ℚ) : ℝ) =
        ((AffineFamily.hilbert G L : ℕ) : ℝ) := by
      push_cast
      rfl
    have hdeg : (((AffineFamily.degree G : ℚ)) : ℝ) = ((AffineFamily.degree G : ℚ) : ℝ) := rfl
    -- Move the ℚ inequality to ℝ via monotonicity of `Rat.cast`.
    have hmove : ((c0 * AffineFamily.degree G * (L : ℚ) ^ h : ℚ) : ℝ) ≤
        ((((AffineFamily.hilbert G L : ℕ) : ℚ) : ℝ)) := by
      exact_mod_cast hQ
    simpa [mul_assoc, Rat.cast_pow, Rat.cast_natCast] using hmove
  -- Monotonicity: `hilbert G ≤ hilbert E0`.
  have hsubvar : (AffineFamily.locus G).Subvariety E0 :=
    commonLabelGroup_subvariety d i₀ Γ L h
  have hmonoNat : (AffineFamily.locus G).hilbert L ≤ E0.hilbert L :=
    AffineVariety.hilbert_mono _ _ hsubvar L
  have hmonoR : ((AffineFamily.hilbert G L : ℕ) : ℝ) ≤ ((E0.hilbert L : ℕ) : ℝ) := by
    have : AffineFamily.hilbert G L ≤ E0.hilbert L := by
      simpa [AffineFamily.hilbert] using hmonoNat
    exact_mod_cast this
  -- Envelope identity and reindexing.
  have henv : E0.hilbert L = hilbertOfSet T0 L := envelope_hilbert T0 L
  have hbridge : commonLabelRank i₀ Γ L = hilbertOfSet T0 L :=
    commonLabelRank_eq_hilbertOfSet d i₀ Γ L
  have hrankR : ((E0.hilbert L : ℕ) : ℝ) = ((commonLabelRank i₀ Γ L : ℕ) : ℝ) := by
    rw [henv, ← hbridge]
  -- Rewrite `G` back to the named group for the goal.
  have hG_eq : G = commonLabelGroup i₀ Γ L h := rfl
  have hdeg_eq : ((AffineFamily.degree G : ℚ) : ℝ) =
      ((AffineFamily.degree (commonLabelGroup i₀ Γ L h) : ℚ) : ℝ) := by rw [hG_eq]
  refine ⟨?_, ?_⟩
  · rw [hdeg_eq]
    calc ((c0 : ℚ) : ℝ) * ((AffineFamily.degree (commonLabelGroup i₀ Γ L h) : ℚ) : ℝ) * (L : ℝ) ^ h
        = ((c0 : ℚ) : ℝ) * ((AffineFamily.degree G : ℚ) : ℝ) * (L : ℝ) ^ h := by rw [← hdeg_eq]
      _ ≤ ((AffineFamily.hilbert G L : ℕ) : ℝ) := hlowR
      _ ≤ ((E0.hilbert L : ℕ) : ℝ) := hmonoR
      _ = ((commonLabelRank i₀ Γ L : ℕ) : ℝ) := hrankR
      _ = (commonLabelRank i₀ Γ L : ℝ) := by rfl
  · intro Γ'' hsub E
    -- Upper bound for the new graph.
    set T'' := commonLabelPoints i₀ Γ'' with hTdef
    have hbridge'' : commonLabelRank i₀ Γ'' E = hilbertOfSet T'' E :=
      commonLabelRank_eq_hilbertOfSet d i₀ Γ'' E
    have hclosure : (AffineVariety.closure T'').Subvariety (AffineFamily.locus G) :=
      closure_subvariety_of_subset T'' _ hsub
    have hmonoNat2 : (AffineVariety.closure T'').hilbert E ≤ (AffineFamily.locus G).hilbert E :=
      AffineVariety.hilbert_mono _ _ hclosure E
    have hmonoR2 : ((hilbertOfSet T'' E : ℕ) : ℝ) ≤ ((AffineFamily.hilbert G E : ℕ) : ℝ) := by
      have : hilbertOfSet T'' E ≤ AffineFamily.hilbert G E := by
        simpa [hilbertOfSet, AffineFamily.hilbert] using hmonoNat2
      exact_mod_cast this
    have hupperQ := TrackA.poly_hilbert_upper (n := d + d) G h hGpure E
    -- `hupperQ : (hilbert G E :ℚ) ≤ degree * choose`
    have hupperR : ((AffineFamily.hilbert G E : ℕ) : ℝ) ≤
        ((AffineFamily.degree G : ℚ) : ℝ) * (((E + h).choose h : ℕ) : ℝ) := by
      have hmove : ((((AffineFamily.hilbert G E : ℕ) : ℚ)) : ℝ) ≤
          ((AffineFamily.degree G * (((E + h).choose h : ℕ) : ℚ) : ℚ) : ℝ) := by
        exact_mod_cast hupperQ
      simpa [Rat.cast_natCast] using hmove
    calc (commonLabelRank i₀ Γ'' E : ℝ)
        = ((hilbertOfSet T'' E : ℕ) : ℝ) := by rw [hbridge'']
      _ ≤ ((AffineFamily.hilbert G E : ℕ) : ℝ) := hmonoR2
      _ ≤ ((AffineFamily.degree G : ℚ) : ℝ) * (((E + h).choose h : ℕ) : ℝ) := hupperR
      _ = ((AffineFamily.degree (commonLabelGroup i₀ Γ L h) : ℚ) : ℝ) *
          ((E + h).choose h : ℝ) := by rw [hG_eq]

end
end DistinctDistances.SparseCones
