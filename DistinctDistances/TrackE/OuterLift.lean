import DistinctDistances.TrackE.OuterDiscard
import DistinctDistances.TrackE.OuterRoots
import DistinctDistances.TrackE.OuterLiftSpec
import DistinctDistances.TrackA.RadialGenericDegreeSupport
import DistinctDistances.TrackE.MOLiftAux
import DistinctDistances.TrackE.OuterTestAux

/-! The algebraic lift at the outer endpoint (sparse-cones.tex:580–629).

`outer_lift_curve` (sc:580–594): for `γ`
in the specialized label equations, a component of `Y ∩ π_p⁻¹(γ)` through `q`
is a curve (the label map is étale at `(p, q)`); it gives an algebraic curve
`C ⊂ Y` through `q` projecting onto `γ` with a generic map degree.
`outer_terminal_curve_resolution` (sc:596–599) resolves `k = 1` through
the global terminal assignment; `outer_lift_map_degree` (sc:601–629, impl)
pools the lifts over `γ` and applies `OuterRoots.lean` for `∑ deg ≤ 1`. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- One algebraic lift over `γ`: an irreducible curve through the marked point,
contained in the target carrier, projecting into `γ` with a generic map
degree. `X` is the (unique) source carrier at `p`. -/
structure OuterLiftData (i₀ : Fin d) (p q : Point d) (X Y : AffineVariety d)
    (γ : ProjectiveVariety d) where
  C : AffineVariety d
  r : ℕ
  hC : C.IsIrreducible ∧ C.dimension = 1 ∧ q ∈ C.points ∧ C.Subvariety Y
  hproj : (radialImage p C).points ⊆ γ.points
  hdeg : GenericallyFiniteRadialDegree p C r

/-- sc:outer-lift.curve (sparse-cones.tex:580–594). Near
the label the common equations give a smooth `2k`-fold (`hsys`, and they
vanish on the `2k`-dimensional image `Z_{X,Y}` through the label, `hvanish`),
and `ψ : X × Y → Z_{X,Y}` has full differential rank at `(p, q)` (`tdata`).
Since `γ` lies in the specialized equations (`hcontain`), `{p} × γ` lies in
the unique component `Z_{X,Y}` of the equation locus through the label; the
local inverse of `ψ` identifies the germ of `Y ∩ π_p⁻¹(γ)` at `q` with the germ
of `γ` at `π_p(q)`, which is pure one-dimensional; an algebraic irreducible
component of the preimage through a selected inverse branch is a curve
`C ⊆ Y` through `q`, projecting nonconstantly into `γ`, hence with a generic
radial map degree. -/
theorem outer_lift_curve {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (M : CommonPoolProfile T)
    (k : ℕ) (i₀ : Fin d)
    (p q : Point d) (γ : ProjectiveVariety d)
    (hγ : γ.IsIrreducible) (hγdim : γ.dimension = 1)
    (hdir : ∃ h : q ≠ p, radialProjection p q h ∈ γ.points)
    (X Y : AffineVariety d)
    (hX : X.IsIrreducible) (hY : Y.IsIrreducible)
    (hXd : X.dimension = k) (hYd : Y.dimension = k)
    (hpX : p ∈ X.points) (hqY : q ∈ Y.points)
    (Eqs : Finset (TrackD.PairPoly d))
    (tdata : OuterTangentData i₀ p q X Y k (outerLabelTangent Eqs i₀ p q))
    (hsys : Module.finrank ℂ (TrackD.jacKer (Eqs.image commonPairEquation)
      (fun kk => TrackD.labelPt i₀ p q (finSumFinEquiv.symm kk))) = 2 * k)
    (hvanish : ∀ G ∈ Eqs,
      commonPairEquation G ∈ (commonProductImage i₀ X Y).ideal)
    (hcontain : outerGammaInEqs i₀ Eqs p γ) :
    Nonempty (OuterLiftData i₀ p q X Y γ) := by
  obtain ⟨h2, h3⟩ := outer_spec_tangent i₀ p q X Y k Eqs tdata
  have h1 := outer_spec_vanish i₀ p X Y hpX Eqs hvanish
  have hT : Module.finrank ℂ (Y.tangentSpace q) = Y.dimension := by
    rw [← tdata.hTY, tdata.hdimY, hYd]
  have h4 : ∀ e ∈ Eqs.image (outerSpecEq p), ∀ z ∈ γ.points, z.rep i₀ ≠ 0 →
      MvPolynomial.eval ((z.rep i₀)⁻¹ • z.rep) e = 0 := by
    intro e he z hz hz0
    obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp he
    rw [outerSpecEq_eval]
    exact hcontain G hG z hz hz0
  obtain ⟨C, hCi, hCd, hqC, hCY, hproj, himage⟩ :=
    outer_curve_from_jets Y hY q hqY hT p i₀ tdata.hchart (Eqs.image (outerSpecEq p))
      h1 h2 (by rw [hYd]; exact h3) γ hγ hγdim hdir h4
  obtain ⟨r, hr⟩ := TrackA.radial_generic_degree_exists C hCi le_rfl hCd p himage
  exact ⟨⟨C, r, ⟨hCi, hCd, hqC, hCY⟩, hproj, hr⟩⟩

/-- sc:outer-lift.terminal (sparse-cones.tex:596–599). For
`k = 1` the lift is the target carrier `Y` itself (both irreducible curves,
`C ⊆ Y`: `TrackD.irreducible_subvariety_eq_of_pos_dimension_eq`, as cited in
item 185); with the terminal identification (188) this is an incidence removed
by `prof:pair-selection` (the `ProjectsInto` clause of `SelectedIncidence`,
obtained from `hproj`, `hCY` and `hγfam`), contradicting the pair's selected
incidence `hsel`. -/
theorem outer_terminal_curve_resolution {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F)
    (k : ℕ) (hk1 : k = 1) (i₀ : Fin d)
    (i : ℕ) (p q : RPoint d) (γ : ProjectiveVariety d)
    (X Y : AffineVariety d)
    (lift : OuterLiftData i₀ (TrackD.toC p) (TrackD.toC q) X Y γ)
    (hCY : lift.C = Y)
    (hterm : T.terminal i q = some Y)
    (P : Finset (TrackD.Pt d)) (Cf : TrackD.Pt d → ProjectiveFamily.Family d)
    (ρ : ℝ)
    (hsel : TrackD.SelectedIncidence P Cf (T.terminal i) ρ p q)
    (hγfam : γ.points ⊆ TrackD.familyPoints (Cf p)) :
    False := by
  apply hsel.2.2.1 Y hterm
  intro z hz
  have h := lift.hproj
  rw [hCY] at h
  exact hγfam (h hz)

/-- One lift with its marked point and target carrier packaged, sharing the
source point `p`, source carrier `X` and direction component `γ`. -/
structure OuterLiftBundle (i₀ : Fin d) (p : Point d) (X : AffineVariety d)
    (γ : ProjectiveVariety d) where
  q : Point d
  Y : AffineVariety d
  lift : OuterLiftData i₀ p q X Y γ

/-- sc:outer-lift.projection-bounds (sparse-cones.tex:589–594, 631–642). A curve projecting into the irreducible curve `γ` with a generic
radial map degree has radial image exactly of dimension one, contained in `γ`,
hence equal to `γ` (irreducible closed subsets of equal dimension), so of the
same degree. Dimension one: the image is irreducible of dimension `≤ 1`, and a
point image would make the generic fibre infinite (`hdeg`). -/
theorem outer_projection_image_bounds (p : Point d) (C : AffineVariety d)
    (γ : ProjectiveVariety d)
    (hC : C.IsIrreducible ∧ C.dimension = 1)
    (hγ : γ.IsIrreducible ∧ γ.dimension = 1)
    (hproj : (radialImage p C).points ⊆ γ.points)
    (r : ℕ) (hdeg : GenericallyFiniteRadialDegree p C r) :
    (radialImage p C).dimension = 1 ∧ (radialImage p C).degree ≤ γ.degree := by
  exact MOLiftAux.outer_projection_image_bounds_aux p C γ hC hγ hproj r hdeg

/-- sc:lift-map-degree (sparse-cones.tex:601–629). The lifts over
`γ` have pairwise distinct curves (`hCinj`; repeated physical curves are pooled
by the caller). Every marked lift point lies off the chart hyperplane
(`hchart`; lane sol-195: without it the statement is false — `γ` may avoid the
`i₀`-chart entirely while `himpl` holds vacuously, e.g. `γ = {[u:0:w]}` with
`i₀ = 1`). Each radial image is `γ` (187h). The test system `sys` is
nonzero at each marked point (`hsysnz`), hence off a finite subset of each
irreducible lift; choose one general direction `z ∈ γ` with `z_{i₀} ≠ 0`
avoiding those finite sets, the non-generic fibres of each lift (`hdeg`) and
the images of the finite pairwise intersections of distinct lifts. Each lift
then contributes exactly `r` roots on the ray of `z`, roots of distinct lifts
are distinct, and at every root `q'` the label `(p, z/z_{i₀})` (common to all
roots) lies in the complete product image (`hpX`, `q' ∈ Y`), so `himpl` gives
tangent data with the common label tangent space `outerLabelTangent Eqs i₀ p q'`
(equal for all roots), the common source space `X.tangentSpace p` and
`lam = proj i₀`. `outer_roots_card_le_one` bounds the roots by one and
`lift_map_degree_sum_le_one` (OuterRoots.lean) gives `∑ r ≤ 1`. -/
theorem outer_lift_map_degree {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F)
    (k : ℕ) (hk2 : 2 ≤ k) (i₀ : Fin d)
    (p : Point d) (γ : ProjectiveVariety d)
    (hγ : γ.IsIrreducible) (hγdim : γ.dimension = 1)
    (X : AffineVariety d) (hpX : p ∈ X.points)
    (Eqs : Finset (TrackD.PairPoly d))
    (lifts : Finset (OuterLiftBundle i₀ p X γ))
    (hCinj : ∀ l₁ ∈ lifts, ∀ l₂ ∈ lifts, l₁.lift.C = l₂.lift.C → l₁ = l₂)
    (hchart : ∀ l ∈ lifts, (l.q - p) i₀ ≠ 0)
    (sys : @OuterTestSystem d)
    (hsysnz : ∀ l ∈ lifts, OuterTestsNonvanishing sys p l.q)
    (himpl : ∀ l ∈ lifts, ∀ q' : Point d, q' ∈ l.Y.points →
      (q' - p) i₀ ≠ 0 →
      (fun kk => TrackD.labelPt i₀ p q' (finSumFinEquiv.symm kk)) ∈
        (commonProductImage i₀ X l.Y).points →
      OuterTestsNonvanishing sys p q' →
      Nonempty (OuterTangentData i₀ p q' X l.Y k (outerLabelTangent Eqs i₀ p q'))) :
    ∑ l ∈ lifts, l.lift.r ≤ 1 := by
  classical
  by_cases hlifts : lifts.Nonempty
  · have himage (l : OuterLiftBundle i₀ p X γ) (hl : l ∈ lifts) :
        radialImage p l.lift.C = γ := by
      have hdim := (outer_projection_image_bounds p l.lift.C γ
        ⟨l.lift.hC.1, l.lift.hC.2.1⟩ ⟨hγ, hγdim⟩ l.lift.hproj
        l.lift.r l.lift.hdeg).1
      exact OuterTestAux.radial_image_eq p l.lift.C γ l.lift.hC.1 hγ hγdim hdim
        l.lift.hproj (TrackA.radial_actual_of_generic _ p l.lift.hdeg)
    let f := OuterTestAux.testPolynomial sys i₀ p
    have hf (l : OuterLiftBundle i₀ p X γ) (hl : l ∈ lifts) : f ∉ l.lift.C.ideal := by
      intro hmem
      exact (OuterTestAux.testPolynomial_nonzero_iff sys i₀ p l.q).2
        ⟨hchart l hl, hsysnz l hl⟩ (l.lift.hC.2.2.1 f hmem)
    obtain ⟨z, hz, hcount, hgood, hdisj⟩ := OuterTestAux.common_fibers lifts
      (fun l => l.lift.C) (fun l => l.lift.r) p γ hγ hγdim
      (fun l _ => ⟨l.lift.hC.1, l.lift.hC.2.1⟩) himage
      (fun l _ => l.lift.hdeg) hCinj f hf
    let roots (l : OuterLiftBundle i₀ p X γ) : Finset (Point d) :=
      if hl : l ∈ lifts then (hcount l hl).1.toFinset else ∅
    have hmem (l : OuterLiftBundle i₀ p X γ) (hl : l ∈ lifts) (q : Point d) :
        q ∈ roots l ↔ q ∈ radialFiber p l.lift.C z := by
      simp only [roots, dif_pos hl, Set.Finite.mem_toFinset]
    have hcard (l : OuterLiftBundle i₀ p X γ) (hl : l ∈ lifts) :
        (roots l).card = l.lift.r := by
      simp only [roots, dif_pos hl]
      rw [← Set.ncard_eq_toFinset_card _ (hcount l hl).1]
      exact (hcount l hl).2
    have hdisjoint : (lifts : Set (OuterLiftBundle i₀ p X γ)).PairwiseDisjoint roots := by
      intro l hl l' hl' hne
      apply Finset.disjoint_left.mpr
      intro q hq hq'
      exact Set.disjoint_left.mp (hdisj l hl l' hl' hne)
        ((hmem l hl q).1 hq) ((hmem l' hl' q).1 hq')
    let Q := lifts.biUnion roots
    have hdir (q : Point d) (hq : q ∈ Q) :
        ∃ hqp : q ≠ p, radialProjection p q hqp = z := by
      obtain ⟨l, hl, hqroot⟩ := Finset.mem_biUnion.mp hq
      exact ((hmem l hl q).1 hqroot).2
    have hqchart (q : Point d) (hq : q ∈ Q) : (q-p) i₀ ≠ 0 := by
      obtain ⟨l, hl, hqroot⟩ := Finset.mem_biUnion.mp hq
      exact ((OuterTestAux.testPolynomial_nonzero_iff sys i₀ p q).1
        (hgood l hl q ((hmem l hl q).1 hqroot))).1
    have hline (q : Point d) (hq : q ∈ Q) (s : Point d) (hs : s ∈ Q) :
        ∃ c : ℂ, s-p = c • (q-p) := by
      obtain ⟨hqp, hqz⟩ := hdir q hq
      obtain ⟨hsp, hsz⟩ := hdir s hs
      obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ (s-p) (q-p)
        (sub_ne_zero.mpr hsp) (sub_ne_zero.mpr hqp)).mp (hsz.trans hqz.symm)
      exact ⟨c, hc.symm⟩
    obtain ⟨l₀, hl₀⟩ := hlifts
    obtain ⟨q₀, hq₀root⟩ := Finset.card_pos.mp
      (show 0 < (roots l₀).card by rw [hcard l₀ hl₀]; exact l₀.lift.hdeg.1)
    have hq₀ : q₀ ∈ Q := Finset.mem_biUnion.mpr ⟨l₀, hl₀, hq₀root⟩
    have hlabel (q : Point d) (hq : q ∈ Q) :
        outerLabelTangent Eqs i₀ p q = outerLabelTangent Eqs i₀ p q₀ := by
      obtain ⟨c, hc⟩ := hline q₀ hq₀ q hq
      have hc0 : c ≠ 0 := by
        intro he
        exact (hdir q hq).choose (sub_eq_zero.mp (by simpa [he] using hc))
      have hnorm : ((q-p) i₀)⁻¹ • (q-p) = ((q₀-p) i₀)⁻¹ • (q₀-p) := by
        change TrackD.dirChart (LinearMap.proj i₀) (q-p) =
          TrackD.dirChart (LinearMap.proj i₀) (q₀-p)
        rw [hc, TrackD.dirChart_smul _ _ c hc0 (hqchart q₀ hq₀)]
      have hpt : TrackD.labelPt i₀ p q = TrackD.labelPt i₀ p q₀ :=
        congrArg (TrackD.pairPt p) hnorm
      simp only [outerLabelTangent, hpt]
    have hdata (q : Point d) (hq : q ∈ Q) : ∃ Y : AffineVariety d,
        Nonempty (OuterTangentData i₀ p q X Y k (outerLabelTangent Eqs i₀ p q₀)) := by
      obtain ⟨l, hl, hqroot⟩ := Finset.mem_biUnion.mp hq
      have hqfiber := (hmem l hl q).1 hqroot
      have hqY := (AffineVariety.subvariety_iff_points_subset _ _).mp
        l.lift.hC.2.2.2 hqfiber.1
      have htests := ((OuterTestAux.testPolynomial_nonzero_iff sys i₀ p q).1
        (hgood l hl q hqfiber)).2
      refine ⟨l.Y, ?_⟩
      rw [← hlabel q hq]
      exact himpl l hl q hqY (hqchart q hq)
        (OuterTestAux.label_mem_image i₀ p q X l.Y hpX hqY (hqchart q hq)) htests
    choose Y hdata using hdata
    let t (q : Point d) (hq : q ∈ Q) := Classical.choice (hdata q hq)
    let TY (q : Point d) : Submodule ℂ (Point d) :=
      if hq : q ∈ Q then (t q hq).TY else ⊥
    have hTY (q : Point d) (hq : q ∈ Q) : TY q = (t q hq).TY := by
      simp only [TY, dif_pos hq]
    apply lift_map_degree_sum_le_one lifts roots (fun l => l.lift.r) hdisjoint hcard
    apply outer_roots_card_le_one (LinearMap.proj i₀) p Q (X.tangentSpace p) TY
      (outerLabelTangent Eqs i₀ p q₀) hqchart hline
    · intro q hq
      rw [← (t q hq).hTX]
      exact (t q hq).hsrc
    · intro q hq
      rw [hTY q hq]
      exact (t q hq).htgt
    · intro q hq
      rw [hTY q hq, ← (t q hq).hTX, (t q hq).hdimX, (t q hq).hdimY]
    · intro q hq
      rw [hTY q hq, ← (t q hq).hTX]
      exact (t q hq).hW
    · intro q hq
      rw [hTY q hq, ← (t q hq).hTX, (t q hq).hdimX, (t q hq).hdimY]
      exact (t q hq).hrank
    · intro q hq
      rw [hTY q hq, ← (t q hq).hTX, (t q hq).hdimX, (t q hq).hdimY]
      exact (t q hq).hdimW
    · intro q hq
      rw [hTY q hq, ← (t q hq).hTX]
      exact (t q hq).hneq hk2
  · simp [Finset.not_nonempty_iff_eq_empty.mp hlifts]

end
end DistinctDistances.SparseCones
