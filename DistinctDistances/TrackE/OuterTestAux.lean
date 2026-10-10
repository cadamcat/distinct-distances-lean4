import DistinctDistances.TrackE.OuterRegularity
import DistinctDistances.TrackE.MOLiftAux
import DistinctDistances.TrackA.SimultaneousRadialFiberSupport

namespace DistinctDistances.SparseCones.OuterTestAux

noncomputable section
open scoped Classical BigOperators
variable {d : ℕ}

/-- The chart condition and all retained tests, specialized at the source. -/
def testPolynomial (sys : @OuterTestSystem d) (i₀ : Fin d) (p : Point d) : Poly d :=
  (MvPolynomial.X i₀ - MvPolynomial.C (p i₀)) * sys.gph *
    (∏ G ∈ sys.srcTests, TrackD.pairFixLeft G p) *
    (∏ G ∈ sys.tgtTests, TrackD.pairFixLeft G p)

theorem testPolynomial_nonzero_iff (sys : @OuterTestSystem d) (i₀ : Fin d)
    (p q : Point d) :
    MvPolynomial.eval q (testPolynomial sys i₀ p) ≠ 0 ↔
      (q-p) i₀ ≠ 0 ∧ OuterTestsNonvanishing sys p q := by
  simp [testPolynomial, OuterTestsNonvanishing, TrackD.pairPt,
    mul_ne_zero_iff, Finset.prod_ne_zero_iff, and_assoc]

/-- Equal-dimensional irreducible projective curves in containment are equal. -/
theorem radial_image_eq (p : Point d) (C : AffineVariety d) (γ : ProjectiveVariety d)
    (hC : C.IsIrreducible) (hγ : γ.IsIrreducible)
    (hγdim : γ.dimension = 1) (himage : (radialImage p C).dimension = 1)
    (hproj : (radialImage p C).points ⊆ γ.points)
    (hactual : ∃ x ∈ C.points, x ≠ p) : radialImage p C = γ := by
  have hW := radialImage_irreducible p C hC hactual
  have hWne : (radialImage p C).points.Nonempty := by
    obtain ⟨x, hx, hxne⟩ := hactual
    exact ⟨_, ProjectiveVariety.subset_closure _ ⟨x, hx, hxne, rfl⟩⟩
  have hγne := ProjectiveFamily.irreducible_points_nonempty γ hγ
  have hdim : (radialImage p C).affineCone.dimension = γ.affineCone.dimension := by
    rw [ProjectiveVariety.dimension_cone _ hWne,
      ProjectiveVariety.dimension_cone _ hγne, himage, hγdim]
  exact ProjectiveVariety.ext (DistinctDistances.MReqAux.projective_ideal_eq_of_cone_dim_eq
    γ (radialImage p C) hγ hW
    (MOLiftAux.projectiveSubvariety_of_points_subset _ _ hproj) hdim).symm

/-- Choose a common generic fiber that avoids a proper source equation on
each curve, and whose roots on distinct curves are disjoint. -/
theorem common_fibers {ι : Type*} (I : Finset ι) (C : ι → AffineVariety d)
    (r : ι → ℕ) (p : Point d) (γ : ProjectiveVariety d)
    (hγ : γ.IsIrreducible) (hγdim : γ.dimension = 1)
    (hC : ∀ i ∈ I, (C i).IsIrreducible ∧ (C i).dimension = 1)
    (himage : ∀ i ∈ I, radialImage p (C i) = γ)
    (hgen : ∀ i ∈ I, GenericallyFiniteRadialDegree p (C i) (r i))
    (hinj : ∀ i ∈ I, ∀ j ∈ I, C i = C j → i = j)
    (f : Poly d) (hf : ∀ i ∈ I, f ∉ (C i).ideal) :
    ∃ z ∈ γ.points,
      (∀ i ∈ I, (radialFiber p (C i) z).Finite ∧
        (radialFiber p (C i) z).ncard = r i) ∧
      (∀ i ∈ I, ∀ x ∈ radialFiber p (C i) z, MvPolynomial.eval x f ≠ 0) ∧
      (∀ i ∈ I, ∀ j ∈ I, i ≠ j →
        Disjoint (radialFiber p (C i) z) (radialFiber p (C j) z)) := by
  letI : γ.ideal.IsPrime := hγ
  have hw (i : I) : ∃ (g : Poly d) (e : ℕ), g.IsHomogeneous e ∧ g ∉ γ.ideal ∧
      ∀ z ∈ γ.points, MvPolynomial.eval z.rep g ≠ 0 →
        ((radialFiber p (C i.val) z).Finite ∧
          (radialFiber p (C i.val) z).ncard = r i.val) ∧
        ∀ x ∈ radialFiber p (C i.val) z, MvPolynomial.eval x f ≠ 0 := by
    obtain ⟨_, g, e, hh, hn, hcount⟩ := hgen i.val i.property
    rw [himage i.val i.property] at hn hcount
    obtain ⟨H, D, hHhom, hHnot, havoid⟩ := TrackA.radial_fiber_avoids_proper_cut
      (C i.val) (hC i.val i.property).1 (hC i.val i.property).2 p
      (by rw [himage i.val i.property]; exact hγdim)
      (TrackA.radial_actual_of_generic (C i.val) p (hgen i.val i.property))
      f (hf i.val i.property)
    rw [himage i.val i.property] at hHnot
    refine ⟨g * H, e+D, hh.mul hHhom,
      fun h => (hγ.mem_or_mem h).elim hn hHnot, ?_⟩
    intro z hz hval
    have hparts : MvPolynomial.eval z.rep g ≠ 0 ∧ MvPolynomial.eval z.rep H ≠ 0 := by
      simpa only [map_mul, mul_ne_zero_iff] using hval
    exact ⟨hcount z hz hparts.1, havoid z hparts.2⟩
  choose g e hhom hnot hgood using hw
  let Pairs := {a : I × I // a.1 ≠ a.2}
  have hpw (a : Pairs) : ∃ (H : Poly d) (D : ℕ), H.IsHomogeneous D ∧ H ∉ γ.ideal ∧
      ∀ z : ProjectivePoint d, MvPolynomial.eval z.rep H ≠ 0 →
        Disjoint (radialFiber p (C a.val.1.val) z) (radialFiber p (C a.val.2.val) z) := by
    have hne : C a.val.1.val ≠ C a.val.2.val := by
      intro he
      exact a.property (Subtype.ext (hinj _ a.val.1.property _ a.val.2.property he))
    obtain ⟨H, D, hh, hn, hdisj⟩ := TrackA.radial_fibers_disjoint_open
      (C a.val.1.val) (C a.val.2.val)
      (hC _ a.val.1.property).1 (hC _ a.val.2.property).1 le_rfl
      (hC _ a.val.1.property).2 (hC _ a.val.2.property).2 hne p
      (by rw [himage _ a.val.1.property]; exact hγdim)
      (TrackA.radial_actual_of_generic _ p (hgen _ a.val.1.property))
    rw [himage _ a.val.1.property] at hn
    exact ⟨H, D, hh, hn, hdisj⟩
  choose H D hHhom hHnot hdisj using hpw
  let Q := (∏ i : I, g i) * ∏ a : Pairs, H a
  have hgnot : (∏ i : I, g i) ∉ γ.ideal := by
    intro h
    obtain ⟨i, _, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact hnot i hi
  have hHPnot : (∏ a : Pairs, H a) ∉ γ.ideal := by
    intro h
    obtain ⟨a, _, ha⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact hHnot a ha
  have hQnot : Q ∉ γ.ideal := fun h => (hγ.mem_or_mem h).elim hgnot hHPnot
  have hQhom : Q.IsHomogeneous ((∑ i : I, e i) + ∑ a : Pairs, D a) :=
    (MvPolynomial.IsHomogeneous.prod Finset.univ g e (fun i _ => hhom i)).mul
      (MvPolynomial.IsHomogeneous.prod Finset.univ H D (fun a _ => hHhom a))
  obtain ⟨z, hz, hzQ⟩ := TrackA.projective_homogeneous_nonzero_point γ Q hQhom hQnot
  have hparts : (∏ i : I, MvPolynomial.eval z.rep (g i)) ≠ 0 ∧
      (∏ a : Pairs, MvPolynomial.eval z.rep (H a)) ≠ 0 := by
    simpa only [Q, map_mul, map_prod, mul_ne_zero_iff] using hzQ
  have hi (i : I) := hgood i z hz
    ((Finset.prod_ne_zero_iff.mp hparts.1) i (Finset.mem_univ _))
  refine ⟨z, hz, fun i hiI => (hi ⟨i, hiI⟩).1,
    fun i hiI => (hi ⟨i, hiI⟩).2, ?_⟩
  intro i hiI j hjI hne
  let a : Pairs := ⟨(⟨i, hiI⟩, ⟨j, hjI⟩), fun h => hne (congrArg Subtype.val h)⟩
  exact hdisj a z ((Finset.prod_ne_zero_iff.mp hparts.2) a (Finset.mem_univ _))

/-- A chart label of an actual product point lies in the complete image. -/
theorem label_mem_image (i₀ : Fin d) (p q : Point d) (X Y : AffineVariety d)
    (hp : p ∈ X.points) (hq : q ∈ Y.points) (hchart : (q-p) i₀ ≠ 0) :
    (fun kk => TrackD.labelPt i₀ p q (finSumFinEquiv.symm kk)) ∈
      (commonProductImage i₀ X Y).points := by
  have hpt : TrackD.rationalPoint (TrackD.secantChartNumerator i₀)
      (TrackD.secantChartDenominator i₀) (TrackD.productPoint p q) =
      (fun kk => TrackD.labelPt i₀ p q (finSumFinEquiv.symm kk)) := by
    rw [TrackD.rational_secant_label i₀ p q hchart]
    rfl
  rw [← hpt]
  exact TrackD.rationalPoint_mem_image (TrackD.productVariety X Y)
    (TrackD.secantChartNumerator i₀) (TrackD.secantChartDenominator i₀)
    (TrackD.productPoint p q) (AffineVariety.subset_closure _ ⟨p, hp, q, hq, rfl⟩)
    (by rwa [TrackD.eval_secantChartDenominator])

end
end DistinctDistances.SparseCones.OuterTestAux
