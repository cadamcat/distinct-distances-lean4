import DistinctDistances.TrackE.FinalCurveInputs

/-! Identify the original owner projection with the covering curve at a regular
surviving label, sparse-cones.tex:920–928. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section

/-- sc:u-final-curve.identification: the complete covering curve and the
unchanged owner projection are the same member of the full envelope curve
family at a surviving regular actual label. -/
theorem regular_covering_label_projects_into {n j : ℕ} {regime : Regime (n + 1)}
    (D : TrackA.SeparatedDepthData regime j) (i : ℕ) (p : RPoint (n + 1))
    (Q : Finset (RPoint (n + 1))) (C : ProjectiveFamily.Family (n + 1))
    (hC : TrackD.IsDirectionalFamily C) (L : ℕ) (G : CoveringEnvelopeComponents C L)
    (bad : ProjectiveFamily.Family (n + 1)) (E : List (Poly (n + 1)))
    (g : Poly (n + 1)) (Creg Treg : ℕ)
    (hcert : CurveRegularityCertificate (envelopeDimensionPart G.components 1)
      bad E g Creg Treg)
    (q : RPoint (n + 1)) (hq : q ∈ Q) (hqD : TrackD.toC q ∈ D.targets i)
    (hneq : TrackD.toC q ≠ TrackD.toC p) (hcovered : TrackD.DirIn C p q)
    (hlarge : q ∉ coveringEnvelopeLargeLabels G (TrackD.toC p) Q)
    (hmember : radialImage (TrackD.toC p) (D.owner i (TrackD.toC q)) ∈
      envelopeDimensionPart G.components 1)
    (hg : MvPolynomial.eval (radialProjection (TrackD.toC p) (TrackD.toC q) hneq).rep g ≠ 0) :
    TrackD.ProjectsInto C p (D.owner i (TrackD.toC q)) := by
  classical
  let z := radialProjection (TrackD.toC p) (TrackD.toC q) hneq
  let W := radialImage (TrackD.toC p) (D.owner i (TrackD.toC q))
  obtain ⟨hne, hzC⟩ := hcovered
  obtain ⟨γ, hγ, hzγ⟩ := (by
    simpa only [z, TrackD.familyPoints, Set.mem_iUnion, exists_prop] using hzC :
      ∃ γ ∈ C, z ∈ γ.points)
  obtain ⟨V, hVG, hγV, hdim, hequal⟩ := Request.projective_irreducible_container
    _ G.components (fun V hV => (G.spec V hV).1) G.locus γ (hC γ hγ).1
    (covering_member_sub_envelope C L γ hγ)
  have hzV : z ∈ V.points := by
    intro x hx he f hf
    exact hzγ x hx he f (hγV hf)
  have hVsmall : ¬ 2 ≤ V.dimension := by
    intro hVlarge
    exact hlarge (Finset.mem_filter.mpr ⟨hq, hneq, V, hVG, hVlarge, hzV⟩)
  have hγdim : γ.dimension = 1 := (hC γ hγ).2.1
  have hVdim : V.dimension = 1 := by omega
  have hγVeq : γ = V := hequal (hγdim.trans hVdim.symm)
  have hγmember : γ ∈ envelopeDimensionPart G.components 1 := by
    rw [hγVeq]
    exact Finset.mem_filter.mpr ⟨hVG, hVdim⟩
  have hzW : z ∈ W.points := ProjectiveVariety.subset_closure _
    ⟨TrackD.toC q, D.owner_contains i _ hqD, hneq, rfl⟩
  have hzF : z ∈ (ProjectiveFamily.locus (envelopeDimensionPart G.components 1)).points := by
    rw [ProjectiveFamily.points_locus]
    exact Set.mem_iUnion.mpr ⟨W, Set.mem_iUnion.mpr ⟨hmember, hzW⟩⟩
  obtain ⟨_hbad, _hE, _hdeg, _hproper, hregular⟩ := hcert
  have hsame : W = γ := (hregular z hzF hg).2.2.2 W hmember γ hγmember hzW hzγ
  change W.points ⊆ TrackD.familyPoints C
  intro y hy
  simp only [TrackD.familyPoints, Set.mem_iUnion]
  exact ⟨γ, hγ, by rw [← hsame]; exact hy⟩

end
end DistinctDistances.SparseCones
