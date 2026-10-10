import DistinctDistances.TrackE.DirectionEnvelope
import DistinctDistances.TrackE.RequestsDirectionComponents
import DistinctDistances.TrackA.Hilbert

/-! Literal dimension groups, direction rank and elementary interfaces for
`sc:separated-rank`, sparse-cones.tex:732–751. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- Include every envelope component of this dimension, even components
receiving no physical target. -/
def envelopeDimensionPart (F : ProjectiveFamily.Family d) (h : ℕ) :
    ProjectiveFamily.Family d := F.filter (fun C => C.dimension = h)

/-- The homogeneous restriction rank of the actual radial directions. -/
def rowDirectionRank (p : Point d) (Q : Finset (RPoint d)) (L : ℕ) : ℕ :=
  (ProjectiveVariety.closure (rowDirections p Q)).hilbert L

/-- An exact-degree envelope retains the direction set's rank in that degree. -/
theorem row_direction_rank_envelope (p : Point d) (Q : Finset (RPoint d)) (L : ℕ) :
    (rowDirectionEnvelope p Q L).hilbert L = rowDirectionRank p Q L := by
  classical
  let T : Set (ProjectivePoint d) := rowDirections p Q
  let V := rowDirectionEnvelope p Q L
  let C0 := ProjectiveVariety.closure T
  show V.hilbert L = C0.hilbert L
  have henv := (Bridges.projective_envelope d T L).choose_spec
  -- henv : V.points = ... ∧ (∀ f homogeneous → (f ∈ V.ideal ↔ ...)) ∧ ...
  have hVeq : V = (Bridges.projective_envelope d T L).choose := rfl
  -- Destructure: henv.1 : V.points = ..., henv.2.1 : ∀ f homogeneous → ..., henv.2.2 : ...
  have hpoints : V.points = {pp | ∀ f ∈ Bridges.homogeneousEquations T L,
      MvPolynomial.eval pp.rep f = 0} := henv.1
  have hideal : ∀ f : Poly d, f.IsHomogeneous L →
      (f ∈ V.ideal ↔ ∀ v ∈ ProjectiveVariety.nonzeroRepresentatives T,
        MvPolynomial.eval v f = 0) := henv.2.1
  have hC0ideal : C0.ideal = ProjectiveVariety.vanishingIdeal T := rfl
  have hTsubV : T ⊆ V.points := by
    intro pp hpp
    rw [hpoints]
    intro f hf
    obtain ⟨_, hfvan⟩ := hf
    apply hfvan
    refine ⟨pp.rep_nonzero, ?_⟩
    simpa using hpp
  have hIV : V.ideal ≤ C0.ideal := by
    intro f hf
    show f ∈ ProjectiveVariety.vanishingIdeal T
    have hmem : f ∈ MvPolynomial.vanishingIdeal ℂ
        (ProjectiveVariety.nonzeroRepresentatives T) := by
      rw [MvPolynomial.mem_vanishingIdeal_iff]
      rintro v ⟨hv, hp⟩
      have hpV : Projectivization.mk ℂ v hv ∈ V.points := hTsubV hp
      have hvZero : v ∈ MvPolynomial.zeroLocus ℂ V.ideal :=
        hpV v hv rfl
      exact MvPolynomial.mem_zeroLocus_iff.mp hvZero f hf
    simpa [ProjectiveVariety.vanishingIdeal] using hmem
  have hhom_eq : ∀ f : Poly d, f.IsHomogeneous L → (f ∈ C0.ideal ↔ f ∈ V.ideal) := by
    intro f hfhom
    constructor
    · intro hfC0
      have hvan : ∀ v ∈ ProjectiveVariety.nonzeroRepresentatives T,
          MvPolynomial.eval v f = 0 := by
        have hmem : f ∈ MvPolynomial.vanishingIdeal ℂ
            (ProjectiveVariety.nonzeroRepresentatives T) := by
          simpa [hC0ideal, ProjectiveVariety.vanishingIdeal] using hfC0
        exact MvPolynomial.mem_vanishingIdeal_iff.mp hmem
      exact (hideal f hfhom).mpr hvan
    · intro hfV
      exact hIV hfV
  let φ : (Poly d ⧸ V.ideal) →ₗ[ℂ] (Poly d ⧸ C0.ideal) :=
    (Ideal.Quotient.factorₐ ℂ hIV).toLinearMap
  have hφ_mk (q : Poly d) :
      φ ((Ideal.Quotient.mkₐ ℂ V.ideal).toLinearMap q) =
        (Ideal.Quotient.mkₐ ℂ C0.ideal).toLinearMap q := by
    simp [φ]
  let e : V.restrictionSpace L →ₗ[ℂ] C0.restrictionSpace L :=
    { toFun := fun x => ⟨φ x.val, by
        rcases x.property with ⟨q, hq, hqx⟩
        refine ⟨q, hq, ?_⟩
        calc
          (Ideal.Quotient.mkₐ ℂ C0.ideal).toLinearMap q =
              φ ((Ideal.Quotient.mkₐ ℂ V.ideal).toLinearMap q) := (hφ_mk q).symm
          _ = φ x.val := congrArg φ hqx
      ⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact φ.map_add x.val y.val
      map_smul' := by
        intro c x
        apply Subtype.ext
        exact φ.map_smul c x.val }
  have hzero : ∀ x : V.restrictionSpace L, e x = 0 → x = 0 := by
    intro x hx
    rcases x.property with ⟨q, hq, hqx⟩
    have hφzero : φ x.val = 0 := by
      simpa [e] using congrArg Subtype.val hx
    have hqzero : (Ideal.Quotient.mkₐ ℂ C0.ideal).toLinearMap q = 0 := by
      calc
        (Ideal.Quotient.mkₐ ℂ C0.ideal).toLinearMap q =
            φ ((Ideal.Quotient.mkₐ ℂ V.ideal).toLinearMap q) := (hφ_mk q).symm
        _ = φ x.val := congrArg φ hqx
        _ = 0 := hφzero
    have hqC0 : q ∈ C0.ideal := Ideal.Quotient.eq_zero_iff_mem.mp hqzero
    have hqhom : q.IsHomogeneous L :=
      (MvPolynomial.mem_homogeneousSubmodule L q).mp hq
    have hqV : q ∈ V.ideal := (hhom_eq q hqhom).mp hqC0
    apply Subtype.ext
    calc
      x.val = (Ideal.Quotient.mkₐ ℂ V.ideal).toLinearMap q := hqx.symm
      _ = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hqV
  have hinj : Function.Injective e := by
    intro x y hxy
    have heqzero : e (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hxy0 : x - y = 0 := hzero (x - y) heqzero
    exact sub_eq_zero.mp hxy0
  have hsurj : Function.Surjective e := by
    intro y
    obtain ⟨q, hq, hqy⟩ := y.property
    let x : V.restrictionSpace L :=
      ⟨(Ideal.Quotient.mkₐ ℂ V.ideal).toLinearMap q, ⟨q, hq, rfl⟩⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    calc
      φ ((Ideal.Quotient.mkₐ ℂ V.ideal).toLinearMap q) =
          (Ideal.Quotient.mkₐ ℂ C0.ideal).toLinearMap q := hφ_mk q
      _ = y.val := hqy
  have hfin : Module.finrank ℂ (V.restrictionSpace L)
      = Module.finrank ℂ (C0.restrictionSpace L) :=
    (LinearEquiv.ofBijective e ⟨hinj, hsurj⟩).finrank_eq
  unfold ProjectiveVariety.hilbert
  exact hfin

/-- Point containment bounds the actual direction rank at every degree. -/
theorem row_direction_rank_le (p : Point d) (Q : Finset (RPoint d))
    (V : ProjectiveVariety d) (hQV : rowDirections p Q ⊆ V.points) (L : ℕ) :
    rowDirectionRank p Q L ≤ V.hilbert L := by
  classical
  let C0 := ProjectiveVariety.closure (rowDirections p Q)
  show C0.hilbert L ≤ V.hilbert L
  have hrepSub : ProjectiveVariety.nonzeroRepresentatives (rowDirections p Q) ⊆
      ProjectiveVariety.nonzeroRepresentatives V.points := by
    rintro v ⟨hv, hp⟩
    exact ⟨hv, hQV hp⟩
  have hI : V.ideal ≤ C0.ideal := by
    have hV : V.ideal = ProjectiveVariety.vanishingIdeal V.points :=
      V.vanishingIdeal_points.symm
    have hC0 : C0.ideal = ProjectiveVariety.vanishingIdeal (rowDirections p Q) := rfl
    rw [hV, hC0]
    exact MvPolynomial.vanishingIdeal_anti_mono (k := ℂ) hrepSub
  let hfactor := OAI.PiExponentJets.W64.quotientSectionFactor V.ideal C0.ideal hI L
  have hsurj := OAI.PiExponentJets.W64.quotientSectionFactor_surjective V.ideal C0.ideal hI L
  have hsurj' : Function.Surjective hfactor := by simpa [hfactor] using hsurj
  have hrange : LinearMap.range hfactor = ⊤ := LinearMap.range_eq_top.mpr hsurj'
  have hle := hfactor.finrank_range_le
  rw [hrange, finrank_top] at hle
  -- hle : finrank (C0.restrictionSpace L) ≤ finrank (V.restrictionSpace L)
  show C0.hilbert L ≤ V.hilbert L
  unfold ProjectiveVariety.hilbert ProjectiveVariety.restrictionSpace
  exact hle

/-- Homogeneous restriction rank is monotone under containment of a complete
finite family; this is independent of the degree defining the envelope. -/
theorem projective_family_hilbert_mono (F : ProjectiveFamily.Family d)
    (V : ProjectiveVariety d) (hFV : ∀ C ∈ F, C.Subvariety V) (L : ℕ) :
    ProjectiveFamily.hilbert F L ≤ V.hilbert L := by
  classical
  let H := ProjectiveFamily.locus F
  show H.hilbert L ≤ V.hilbert L
  have hpointsSubset : H.points ⊆ V.points := by
    intro p hp
    rw [ProjectiveFamily.points_locus] at hp
    rcases Set.mem_iUnion.mp hp with ⟨C, hC⟩
    rcases Set.mem_iUnion.mp hC with ⟨hCF, hpC⟩
    have hsub := hFV C hCF
    -- hsub : V.ideal ≤ C.ideal, transfer point membership
    intro v hv heq
    have hvC : v ∈ MvPolynomial.zeroLocus ℂ C.ideal := hpC v hv heq
    exact MvPolynomial.zeroLocus_anti_mono hsub hvC
  have hrepSub : ProjectiveVariety.nonzeroRepresentatives H.points ⊆
      ProjectiveVariety.nonzeroRepresentatives V.points := by
    rintro v ⟨hv, hp⟩
    exact ⟨hv, hpointsSubset hp⟩
  have hI : V.ideal ≤ H.ideal := by
    have hV : V.ideal = ProjectiveVariety.vanishingIdeal V.points :=
      V.vanishingIdeal_points.symm
    have hH : H.ideal = ProjectiveVariety.vanishingIdeal H.points := by
      -- H = locus F, its ideal is vanishingIdeal of its points? Use vanishingIdeal_points
      have := H.vanishingIdeal_points
      -- this : vanishingIdeal H.points = H.ideal, so symm gives H.ideal = ...
      exact this.symm
    rw [hV, hH]
    exact MvPolynomial.vanishingIdeal_anti_mono (k := ℂ) hrepSub
  let hfactor := OAI.PiExponentJets.W64.quotientSectionFactor V.ideal H.ideal hI L
  have hsurj := OAI.PiExponentJets.W64.quotientSectionFactor_surjective V.ideal H.ideal hI L
  have hsurj' : Function.Surjective hfactor := by simpa [hfactor] using hsurj
  have hrange : LinearMap.range hfactor = ⊤ := LinearMap.range_eq_top.mpr hsurj'
  have hle := hfactor.finrank_range_le
  rw [hrange, finrank_top] at hle
  unfold ProjectiveVariety.hilbert ProjectiveVariety.restrictionSpace
  exact hle

/-- Degrees of irreducible varieties are nonnegative, so a subset has at most
the complete dimension group's degree. -/
theorem projective_degree_subset (F G : ProjectiveFamily.Family d) (hFG : F ⊆ G)
    (hG : ∀ C ∈ G, C.IsIrreducible) :
    ProjectiveFamily.degree F ≤ ProjectiveFamily.degree G := by
  classical
  apply Finset.sum_le_sum_of_subset_of_nonneg hFG
  intro C hC _
  have hirr : C.IsIrreducible := hG C hC
  have hNe : C.affineCone.ideal ≠ ⊤ := by
    -- affineCone.ideal is definitionally C.ideal
    show C.ideal ≠ ⊤
    exact hirr.ne_top
  have h1 : (1 : ℚ) ≤ C.affineCone.degree :=
    AffineVariety.one_le_degree _ hNe
  have hcone : C.affineCone.degree = C.degree :=
    ProjectiveVariety.degree_cone C
  rw [← hcone]
  linarith

/-- All physical row directions lie in the complete components containing
their unchanged owners' projections. No projective-direction injection is needed. -/
theorem assigned_row_directions_subset {j : ℕ}
    (D : TrackA.SeparatedDepthData regime j) (i : ℕ) (p : Point d)
    (Q : Finset (RPoint d)) (C : ProjectiveFamily.Family d)
    (hQ : Q.image TrackD.toC ⊆ D.targets i)
    (hneq : ∀ q ∈ Q, TrackD.toC q ≠ p)
    (hcover : ∀ q ∈ Q, ∃ W ∈ C,
      (radialImage p (D.owner i (TrackD.toC q))).Subvariety W) :
    rowDirections p Q ⊆ (ProjectiveFamily.locus C).points := by
  intro z hz
  obtain ⟨q, hq, hne, rfl⟩ := hz
  have htarget : TrackD.toC q ∈ D.targets i :=
    hQ (Finset.mem_image.mpr ⟨q, hq, rfl⟩)
  have hmemOwner : TrackD.toC q ∈ (D.owner i (TrackD.toC q)).points :=
    D.owner_contains i _ htarget
  have hdirMem : radialProjection p (TrackD.toC q) (hneq q hq)
      ∈ (radialImage p (D.owner i (TrackD.toC q))).points := by
    apply ProjectiveVariety.subset_closure
    exact ⟨TrackD.toC q, hmemOwner, hneq q hq, rfl⟩
  obtain ⟨W, hWC, hsub⟩ := hcover q hq
  have hWpoints : radialProjection p (TrackD.toC q) (hneq q hq) ∈ W.points := by
    -- hsub : W.ideal ≤ (radialImage ...).ideal, transfer zero-locus membership
    intro v hv heq
    have hvMem : v ∈ MvPolynomial.zeroLocus ℂ (radialImage p (D.owner i (TrackD.toC q))).ideal :=
      hdirMem v hv heq
    exact MvPolynomial.zeroLocus_anti_mono hsub hvMem
  rw [ProjectiveFamily.points_locus]
  exact Set.mem_iUnion.mpr ⟨W, Set.mem_iUnion.mpr ⟨hWC, hWpoints⟩⟩

/-- Pigeonhole the physical row by its inherited component dimension.
The multiplicative count avoids rounding a small positive density to zero. -/
theorem finite_dimension_row_pigeonhole (Q : Finset (RPoint d))
    (f : RPoint d → ℕ) (l : ℕ) (hl : l ≤ d)
    (hf : ∀ q ∈ Q, l ≤ f q ∧ f q ≤ d) :
    ∃ h : ℕ, l ≤ h ∧ h ≤ d ∧
      (Q.card : ℝ) ≤ (d + 1 : ℝ) * ((Q.filter (fun q => f q = h)).card : ℝ) := by
  classical
  let S := Finset.Icc l d
  have hmemS : ∀ q ∈ Q, f q ∈ S := fun q hq => Finset.mem_Icc.mpr (hf q hq)
  have hfilterSelf : Q.filter (fun q => f q ∈ S) = Q := by
    ext q
    simp only [Finset.mem_filter]
    constructor
    · intro h; exact h.1
    · intro hq; exact ⟨hq, hmemS q hq⟩
  have hsumR : ∑ h ∈ S, ((Q.filter (fun q => f q = h)).card : ℝ) = (Q.card : ℝ) := by
    have hfib := Finset.sum_fiberwise_eq_sum_filter Q S f (fun _ => (1 : ℝ))
    have hleft : (∑ h ∈ S, ((Q.filter (fun q => f q = h)).card : ℝ))
        = ∑ h ∈ S, ∑ q ∈ Q.filter (fun q => f q = h), (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro h _
      simp
    have hright : ((Q.card : ℝ)) = ∑ q ∈ Q.filter (fun q => f q ∈ S), (1 : ℝ) := by
      simp [hfilterSelf]
    rw [hleft, hright]
    exact hfib
  have hScard_le : (S.card : ℝ) ≤ (d + 1 : ℝ) := by
    have h1 : S.card = d + 1 - l := Nat.card_Icc l d
    have h2 : S.card ≤ d + 1 := by omega
    exact_mod_cast h2
  have hSne : S.Nonempty := by
    use l
    simp [S, Finset.mem_Icc, hl]
  by_contra hcon
  push Not at hcon
  have hlt_each : ∀ h ∈ S, (d + 1 : ℝ) * ((Q.filter (fun q => f q = h)).card : ℝ)
      < (Q.card : ℝ) := by
    intro h hh
    have hle1 : l ≤ h := (Finset.mem_Icc.mp hh).1
    have hle2 : h ≤ d := (Finset.mem_Icc.mp hh).2
    exact hcon h hle1 hle2
  have hsum_lt : ∑ h ∈ S, (d + 1 : ℝ) * ((Q.filter (fun q => f q = h)).card : ℝ)
      < ∑ h ∈ S, (Q.card : ℝ) :=
    Finset.sum_lt_sum_of_nonempty hSne hlt_each
  have hleft_eq : ∑ h ∈ S, (d + 1 : ℝ) * ((Q.filter (fun q => f q = h)).card : ℝ)
      = (d + 1 : ℝ) * (Q.card : ℝ) := by
    rw [← Finset.mul_sum, hsumR]
  have hright_eq : ∑ h ∈ S, (Q.card : ℝ) = (S.card : ℝ) * (Q.card : ℝ) := by
    simp [Finset.sum_const, nsmul_eq_mul]
  rw [hleft_eq, hright_eq] at hsum_lt
  by_cases hQ0 : (Q.card : ℝ) = 0
  · -- then each filter is empty, contradiction with strict inequality at l
    have hlS : l ∈ S := Finset.mem_Icc.mpr ⟨le_rfl, hl⟩
    have hlt_l := hlt_each l hlS
    rw [hQ0] at hlt_l
    have hfilter_le : ((Q.filter (fun q => f q = l)).card : ℝ) ≤ (Q.card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    rw [hQ0] at hfilter_le
    have hnonneg : (0 : ℝ) ≤ (d + 1 : ℝ) * ((Q.filter (fun q => f q = l)).card : ℝ) := by
      apply mul_nonneg (by positivity) (Nat.cast_nonneg _)
    linarith
  · -- Q.card > 0, contradict S.card ≤ d+1
    have hQpos : (0 : ℝ) < (Q.card : ℝ) := lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hQ0)
    have hle_mul : (S.card : ℝ) * (Q.card : ℝ) ≤ (d + 1 : ℝ) * (Q.card : ℝ) :=
      mul_le_mul_of_nonneg_right hScard_le hQpos.le
    linarith

/-- A later envelope chooses components once per distinct projected member.
The row is a physical subset of the original row and inherits that choice.
All components of the selected dimension remain available for the degree. -/
structure DirectionEnvelopeGroup {j : ℕ} (D : TrackA.SeparatedDepthData regime j)
    (i : ℕ) (p : Point d) (Q : Finset (RPoint d)) (L : ℕ)
    (bad : Finset (Point d × AffineVariety d)) where
  components : ProjectiveFamily.Family d
  components_spec : ∀ C ∈ components,
    C.IsIrreducible ∧ C.IsComponentOf (rowDirectionEnvelope p Q L) ∧ C.dimension ≤ d
  components_locus : ProjectiveFamily.locus components = rowDirectionEnvelope p Q L
  components_defined : ProjectiveFamily.ComponentsDefinedInDegree components L
  dimension : ℕ
  dimension_ge : d - j ≤ dimension
  dimension_le : dimension ≤ d
  choice : ProjectiveVariety d → ProjectiveVariety d
  row : Finset (RPoint d)
  row_subset : row ⊆ Q
  owner_retained : ∀ q ∈ row, D.owner i (TrackD.toC q) ∈ D.retained i bad p
  owner_dimension : ∀ q ∈ row, (radialImage p (D.owner i (TrackD.toC q))).dimension = d - j
  chosen_member : ∀ q ∈ row, choice (radialImage p (D.owner i (TrackD.toC q))) ∈
    envelopeDimensionPart components dimension
  chosen_contains : ∀ q ∈ row, (radialImage p (D.owner i (TrackD.toC q))).Subvariety
    (choice (radialImage p (D.owner i (TrackD.toC q))))
  chosen_equal : ∀ q ∈ row,
    (radialImage p (D.owner i (TrackD.toC q))).dimension = dimension →
    radialImage p (D.owner i (TrackD.toC q)) =
      choice (radialImage p (D.owner i (TrackD.toC q)))

end
end DistinctDistances.SparseCones
