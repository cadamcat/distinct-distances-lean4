import DistinctDistances.TrackE.SeparatedEndpoint
import DistinctDistances.TrackE.ProjectedMass

/-! The envelope of the entire covering family, sparse-cones.tex:809–857.
The physical row is chosen only after the original depth batch. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- The envelope is formed from every point of every original covering curve. -/
def coveringDirectionEnvelope (C : ProjectiveFamily.Family d) (L : ℕ) :
    ProjectiveVariety d :=
  (Bridges.projective_envelope d (ProjectiveFamily.locus C).points L).choose

/-- Retain the entire component family, including components without observed labels. -/
structure CoveringEnvelopeComponents (C : ProjectiveFamily.Family d) (L : ℕ) where
  components : ProjectiveFamily.Family d
  spec : ∀ V ∈ components,
    V.IsIrreducible ∧ V.IsComponentOf (coveringDirectionEnvelope C L) ∧ V.dimension ≤ d
  locus : ProjectiveFamily.locus components = coveringDirectionEnvelope C L
  defined : ProjectiveFamily.ComponentsDefinedInDegree components L

/-- Discard every actual label on a larger component, including a label lying
on both a larger component and a curve component. -/
def coveringEnvelopeLargeLabels {C : ProjectiveFamily.Family d} {L : ℕ}
    (G : CoveringEnvelopeComponents C L) (p : Point d) (Q : Finset (RPoint d)) :
    Finset (RPoint d) :=
  Q.filter fun q => ∃ h : TrackD.toC q ≠ p, ∃ V ∈ G.components,
    2 ≤ V.dimension ∧ radialProjection p (TrackD.toC q) h ∈ V.points

/-- Exact-degree homogeneous equations preserve the rank of the entire family
at their defining degree, rather than only the rank of observed incidences. -/
theorem covering_direction_envelope_rank (C : ProjectiveFamily.Family d) (L : ℕ) :
    (coveringDirectionEnvelope C L).hilbert L = ProjectiveFamily.hilbert C L := by
  classical
  let T := (ProjectiveFamily.locus C).points
  let E := Bridges.homogeneousEquations T L
  let V := coveringDirectionEnvelope C L
  let W := ProjectiveFamily.locus C
  have hspec := (Bridges.projective_envelope d T L).choose_spec
  have hVpoints : V.points = {z | ∀ f ∈ E, MvPolynomial.eval z.rep f = 0} := hspec.1
  have hTsub : T ⊆ V.points := by
    intro p hp
    rw [hVpoints]
    intro f hf
    have hrep : p.rep ∈ ProjectiveVariety.nonzeroRepresentatives T := by
      refine ⟨p.rep_nonzero, ?_⟩
      simpa [Projectivization.mk_rep] using hp
    have hvan := hf.2 p.rep hrep
    simpa [Projectivization.mk_rep] using hvan
  have hrep_sub : ProjectiveVariety.nonzeroRepresentatives T ⊆
      ProjectiveVariety.nonzeroRepresentatives V.points := by
    intro v hv
    obtain ⟨hv0, hp⟩ := hv
    exact ⟨hv0, hTsub hp⟩
  have hIdeal_le : V.ideal ≤ W.ideal := by
    have hVeq2 : V.ideal = ProjectiveVariety.vanishingIdeal V.points :=
      (ProjectiveVariety.vanishingIdeal_points V).symm
    have hWeq : W.ideal = ProjectiveVariety.vanishingIdeal T :=
      (ProjectiveVariety.vanishingIdeal_points W).symm
    rw [hVeq2, hWeq]
    exact MvPolynomial.vanishingIdeal_anti_mono (k := ℂ) hrep_sub
  have hmem : ∀ f : Poly d, f.IsHomogeneous L → (f ∈ W.ideal ↔ f ∈ V.ideal) := by
    intro f hf
    constructor
    · intro hfW
      have hvan : ∀ v ∈ ProjectiveVariety.nonzeroRepresentatives T,
          MvPolynomial.eval v f = 0 := by
        have hmem2 : f ∈ ProjectiveVariety.vanishingIdeal T := by
          have hWeq2 : W.ideal = ProjectiveVariety.vanishingIdeal T :=
            (ProjectiveVariety.vanishingIdeal_points W).symm
          rw [hWeq2] at hfW
          exact hfW
        intro v hv
        have hae := (MvPolynomial.mem_vanishingIdeal_iff.mp hmem2) v hv
        simpa [MvPolynomial.aeval_eq_eval] using hae
      exact (hspec.2.1 f hf).mpr hvan
    · intro hfV
      exact hIdeal_le hfV
  have hfin := TrackA.quotientSection_finrank_eq_of_homogeneous_agreement
    V.ideal W.ideal hIdeal_le L hmem
  have hfam : ProjectiveFamily.hilbert C L = W.hilbert L := rfl
  rw [hfam]
  show V.hilbert L = W.hilbert L
  simpa [ProjectiveVariety.hilbert, ProjectiveVariety.restrictionSpace] using hfin

/-- The existing homogeneous-envelope component transfer supplies one complete
finite component list and keeps the original degree-L equations. -/
theorem exists_covering_envelope_components (hd : 3 ≤ d)
    (C : ProjectiveFamily.Family d) (L : ℕ) :
    Nonempty (CoveringEnvelopeComponents C L) := by
  classical
  let E := Bridges.homogeneousEquations (ProjectiveFamily.locus C).points L
  let V := coveringDirectionEnvelope C L
  have hspec := (Bridges.projective_envelope d (ProjectiveFamily.locus C).points L).choose_spec
  have hpoints : V.points = {z | ∀ f ∈ E, MvPolynomial.eval z.rep f = 0} := hspec.1
  obtain ⟨F, hF, hlocus⟩ := Bridges.homogeneous_envelope_carriers d hd L E
    (fun f hf => hf.1) V hpoints
  have hdefined : ProjectiveFamily.ComponentsDefinedInDegree F L := by
    refine ⟨E, ?_, ?_⟩
    · intro f hf
      exact ⟨L, le_rfl, hf.1⟩
    · intro W hW
      exact hspec.2.2 W (hF W hW).2.1
  exact ⟨⟨F, hF, hlocus, hdefined⟩⟩

/-- Pigeonhole actual labels by a larger component's dimension. Points at
intersections choose a component once; no injectivity of directions is used. -/
theorem covering_large_labels_dimension_group (hd : 2 ≤ d)
    {C : ProjectiveFamily.Family d} {L : ℕ} (G : CoveringEnvelopeComponents C L)
    (p : Point d) (Q : Finset (RPoint d)) :
    ∃ h : ℕ, 2 ≤ h ∧ h ≤ d ∧ ∃ Q' : Finset (RPoint d),
      Q' ⊆ coveringEnvelopeLargeLabels G p Q ∧
      ((coveringEnvelopeLargeLabels G p Q).card : ℝ) ≤ (d + 1 : ℝ) * Q'.card ∧
      rowDirections p Q' ⊆ (ProjectiveFamily.locus (envelopeDimensionPart G.components h)).points := by
  classical
  let Large := coveringEnvelopeLargeLabels G p Q
  have hmem_large : ∀ q ∈ Large, ∃ V ∈ G.components,
      2 ≤ V.dimension ∧ V.dimension ≤ d ∧
      ∃ h : TrackD.toC q ≠ p, radialProjection p (TrackD.toC q) h ∈ V.points := by
    intro q hq
    obtain ⟨_, h, V, hV, hdim, hpt⟩ := Finset.mem_filter.mp hq
    exact ⟨V, hV, hdim, (G.spec V hV).2.2, h, hpt⟩
  have hex : ∀ q : {q // q ∈ Large}, ∃ V ∈ G.components,
      2 ≤ V.dimension ∧ V.dimension ≤ d ∧
      ∃ h : TrackD.toC q.val ≠ p, radialProjection p (TrackD.toC q.val) h ∈ V.points := by
    intro q
    exact hmem_large q.val q.property
  choose V hVmem hdim_ge hdim_le hpt using hex
  let f : RPoint d → ℕ := fun q =>
    if h : q ∈ Large then (V ⟨q, h⟩).dimension else 2
  have hf : ∀ q ∈ Large, 2 ≤ f q ∧ f q ≤ d := by
    intro q hq
    have heq : f q = (V ⟨q, hq⟩).dimension := dif_pos hq
    rw [heq]
    exact ⟨hdim_ge ⟨q, hq⟩, hdim_le ⟨q, hq⟩⟩
  obtain ⟨h, hlh, hhd, hcard⟩ := finite_dimension_row_pigeonhole Large f 2 hd hf
  let Q' := Large.filter (fun q => f q = h)
  refine ⟨h, hlh, hhd, Q', Finset.filter_subset _ _, hcard, ?_⟩
  intro z hz
  obtain ⟨q, hq, hneq, rfl⟩ := hz
  have hqLarge : q ∈ Large := (Finset.mem_filter.mp hq).1
  have hfh : f q = h := (Finset.mem_filter.mp hq).2
  have hVhV : V ⟨q, hqLarge⟩ ∈ G.components := hVmem ⟨q, hqLarge⟩
  have hdim_eq : (V ⟨q, hqLarge⟩).dimension = h := by
    have heq : f q = (V ⟨q, hqLarge⟩).dimension := dif_pos hqLarge
    rw [heq] at hfh
    exact hfh
  have hVpart : V ⟨q, hqLarge⟩ ∈ envelopeDimensionPart G.components h := by
    rw [envelopeDimensionPart, Finset.mem_filter]
    exact ⟨hVhV, hdim_eq⟩
  obtain ⟨hnep, hmem⟩ := (hpt ⟨q, hqLarge⟩)
  -- hmem : radialProjection with chosen proof lies in V; transfer to hneq by proof irrelevance.
  have hsame : radialProjection p (TrackD.toC q) hneq =
      radialProjection p (TrackD.toC q) hnep := rfl
  have hzV : radialProjection p (TrackD.toC q) hneq ∈ (V ⟨q, hqLarge⟩).points := by
    rw [hsame]
    exact hmem
  have hlocus := ProjectiveFamily.points_locus (envelopeDimensionPart G.components h)
  rw [hlocus]
  exact Set.mem_iUnion.mpr ⟨V ⟨q, hqLarge⟩,
    Set.mem_iUnion.mpr ⟨hVpart, hzV⟩⟩

end
end DistinctDistances.SparseCones
