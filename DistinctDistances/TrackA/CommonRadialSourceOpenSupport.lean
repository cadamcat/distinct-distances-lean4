import DistinctDistances.TrackA.RadialGenericDegreeSupport
import DistinctDistances.TrackA.RadialIntersectionSupport
import DistinctDistances.TrackA.DepthDefinitions

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical BigOperators

/-- The original polynomial pullback of a target direction equation. -/
def radialDirectionPullback {n : ℕ} (p : Point n) : Poly n →ₐ[ℂ] Poly n :=
  MvPolynomial.aeval (radialCoordinate p)

theorem radialDirectionPullback_eval {n : ℕ} (p x : Point n) (g : Poly n) :
    MvPolynomial.eval x (radialDirectionPullback p g) = MvPolynomial.eval (x-p) g := by
  change MvPolynomial.aeval x (MvPolynomial.aeval (radialCoordinate p) g) =
    MvPolynomial.aeval (x-p) g
  rw [MvPolynomial.comp_aeval_apply, radialCoordinate_eval]

/-- A proper homogeneous target equation pulls back to a proper equation
on the original source; no generic radial degree is assumed. -/
theorem radialDirectionPullback_not_mem {n e : ℕ} (Y : AffineVariety n)
    (p : Point n) (g : Poly n) (hhom : g.IsHomogeneous e)
    (hnot : g ∉ (radialImage p Y).ideal) : radialDirectionPullback p g ∉ Y.ideal := by
  intro hmem
  apply hnot
  change g ∈ MvPolynomial.vanishingIdeal ℂ (ProjectiveVariety.nonzeroRepresentatives
    {z | ∃ x ∈ Y.points, ∃ hx : x ≠ p, radialProjection p x hx = z})
  rw [MvPolynomial.mem_vanishingIdeal_iff]
  rintro v ⟨hv, x, hx, hxne, hproj⟩
  obtain ⟨t, ht⟩ := (Projectivization.mk_eq_mk_iff' ℂ v (x-p) hv
    (sub_ne_zero.mpr hxne)).mp hproj.symm
  have hz : MvPolynomial.eval (x-p) g = 0 := by
    rw [← radialDirectionPullback_eval]
    exact hx _ hmem
  simpa only [MvPolynomial.aeval_eq_eval, ← ht,
    Bridges.homogeneous_eval_smul g hhom, hz, mul_zero]

/-- Nonvanishing at a literal source point implies nonvanishing at its
original projective direction, with the chosen representative respected. -/
theorem radialDirectionPullback_nonzero {n e : ℕ} (p x : Point n) (hx : x ≠ p)
    (g : Poly n) (hhom : g.IsHomogeneous e)
    (hg : MvPolynomial.eval x (radialDirectionPullback p g) ≠ 0) :
    MvPolynomial.eval (radialProjection p x hx).rep g ≠ 0 := by
  intro h
  apply hg
  rw [radialDirectionPullback_eval]
  exact (Bridges.homogeneous_eval_zero_mk_iff g hhom (x-p) (sub_ne_zero.mpr hx)).mp h

/-- Positive-dimensional original sources admit a coordinate equation
proper on the source and vanishing at the supplied center. -/
theorem radial_center_coordinate_separator {n l : ℕ} (Y : AffineVariety n)
    (hY : Y.IsIrreducible) (hl : 1 ≤ l) (hd : Y.dimension = l) (p : Point n) :
    ∃ f : Poly n, f ∉ Y.ideal ∧ MvPolynomial.eval p f = 0 := by
  obtain ⟨x, hx, hxne⟩ := radial_actual_of_positive_dimension Y hY hl hd p
  obtain ⟨i, hi⟩ : ∃ i : Fin n, x i ≠ p i := by
    by_contra h
    push Not at h
    exact hxne (funext h)
  refine ⟨radialCoordinate p i, ?_, ?_⟩
  · intro hf
    have h := hx _ hf
    exact hi (sub_eq_zero.mp (by simpa [radialCoordinate] using h))
  · simp [radialCoordinate]

/-- One target direction open counts every member of its equal-image
group and separates each such fiber from every other original member. -/
theorem radial_group_fiber_open {n l : ℕ} (J : AffineFamily.Family n)
    (hl : 1 ≤ l) (hJ : AffineFamily.IsPure J l) (Y : AffineVariety n) (hY : Y ∈ J)
    (p : Point n) (himage : (radialImage p Y).dimension = l)
    (r : AffineVariety n → ℕ)
    (hgen : ∀ V ∈ J, radialImage p V = radialImage p Y → GenericallyFiniteRadialDegree p V (r V)) :
    ∃ (Q : Poly n) (e : ℕ), Q.IsHomogeneous e ∧ Q ∉ (radialImage p Y).ideal ∧
      ∀ z : ProjectivePoint n, MvPolynomial.eval z.rep Q ≠ 0 →
        (∀ V ∈ J, radialImage p V = radialImage p Y → z ∈ (radialImage p Y).points →
          (radialFiber p V z).Finite ∧ (radialFiber p V z).ncard = r V) ∧
        ∀ V ∈ J, radialImage p V = radialImage p Y →
          ∀ W ∈ J, V ≠ W → Disjoint (radialFiber p V z) (radialFiber p W z) := by
  let Z := radialImage p Y
  let G := J.filter (fun V => radialImage p V = Z)
  have hG (V : G) : V.val ∈ J ∧ radialImage p V.val = Z := Finset.mem_filter.mp V.property
  have hZ : Z.IsIrreducible := radialImage_irreducible p Y (hJ Y hY).1
    (radial_actual_of_generic Y p (hgen Y hY rfl))
  letI : Z.ideal.IsPrime := hZ
  have hgw (V : G) : ∃ (g : Poly n) (d : ℕ), g.IsHomogeneous d ∧ g ∉ Z.ideal ∧
      ∀ z ∈ Z.points, MvPolynomial.aeval z.rep g ≠ 0 →
        (radialFiber p V.val z).Finite ∧ (radialFiber p V.val z).ncard = r V.val := by
    obtain ⟨_, g, d, hh, hn, hc⟩ := hgen V.val (hG V).1 (hG V).2
    rw [(hG V).2] at hn hc
    exact ⟨g, d, hh, hn, hc⟩
  choose g d hh hn hc using hgw
  let Pairs := {a : G × J // a.1.val ≠ a.2.val}
  have hpw (a : Pairs) : ∃ (H : Poly n) (e : ℕ), H.IsHomogeneous e ∧ H ∉ Z.ideal ∧
      ∀ z : ProjectivePoint n, MvPolynomial.eval z.rep H ≠ 0 →
        Disjoint (radialFiber p a.val.1.val z) (radialFiber p a.val.2.val z) := by
    let V := a.val.1.val
    let W := a.val.2.val
    have hd : (radialImage p V).dimension = l := by rw [(hG a.val.1).2]; exact himage
    obtain ⟨H, e, hh, hn, hc⟩ := radial_fibers_disjoint_open V W
      (hJ V (hG a.val.1).1).1 (hJ W a.val.2.property).1 hl
      (hJ V (hG a.val.1).1).2 (hJ W a.val.2.property).2 a.property p hd
      (radial_actual_of_generic V p (hgen V (hG a.val.1).1 (hG a.val.1).2))
    rw [(hG a.val.1).2] at hn
    exact ⟨H, e, hh, hn, hc⟩
  choose H e hHhom hHnot hdisj using hpw
  let Q := (∏ V : G, g V) * ∏ a : Pairs, H a
  have hgnot : (∏ V : G, g V) ∉ Z.ideal := by
    intro h
    obtain ⟨V, _, hV⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact hn V hV
  have hHPnot : (∏ a : Pairs, H a) ∉ Z.ideal := by
    intro h
    obtain ⟨a, _, ha⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact hHnot a ha
  refine ⟨Q, (∑ V : G, d V) + ∑ a : Pairs, e a,
    (MvPolynomial.IsHomogeneous.prod Finset.univ g d (fun V _ => hh V)).mul
      (MvPolynomial.IsHomogeneous.prod Finset.univ H e (fun a _ => hHhom a)),
    (fun h => (hZ.mem_or_mem h).elim hgnot hHPnot), ?_⟩
  intro z hz
  have hparts : (∏ V : G, MvPolynomial.eval z.rep (g V)) ≠ 0 ∧
      (∏ a : Pairs, MvPolynomial.eval z.rep (H a)) ≠ 0 := by
    simpa only [Q, map_mul, map_prod, mul_ne_zero_iff] using hz
  constructor
  · intro V hV hVz hzZ
    let v : G := ⟨V, Finset.mem_filter.mpr ⟨hV, hVz⟩⟩
    apply hc v z hzZ
    exact (Finset.prod_ne_zero_iff.mp hparts.1) v (Finset.mem_univ _)
  · intro V hV hVz W hW hne
    let a : Pairs := ⟨(⟨V, Finset.mem_filter.mpr ⟨hV, hVz⟩⟩, ⟨W, hW⟩), hne⟩
    exact hdisj a z ((Finset.prod_ne_zero_iff.mp hparts.2) a (Finset.mem_univ _))

/-- One original source point simultaneously realizes every actual-center
generic count and avoids intersections with all other original carriers. -/
theorem simultaneous_radial_source_point {n l : ℕ} (J : AffineFamily.Family n)
    (hl : 1 ≤ l) (hJ : AffineFamily.IsPure J l) (Y : AffineVariety n) (hY : Y ∈ J)
    (S : Finset (Point n)) (himage : ∀ p ∈ S, (radialImage p Y).dimension = l)
    (r : Point n → AffineVariety n → ℕ)
    (hgen : ∀ p ∈ S, ∀ V ∈ J, radialImage p V = radialImage p Y →
      GenericallyFiniteRadialDegree p V (r p V)) :
    ∃ y ∈ Y.points, ∀ p ∈ S, ∃ hpy : y ≠ p,
      (∀ V ∈ J, radialImage p V = radialImage p Y →
        (radialFiber p V (radialProjection p y hpy)).Finite ∧
        (radialFiber p V (radialProjection p y hpy)).ncard = r p V) ∧
      ∀ V ∈ J, radialImage p V = radialImage p Y →
        ∀ W ∈ J, V ≠ W →
          Disjoint (radialFiber p V (radialProjection p y hpy))
            (radialFiber p W (radialProjection p y hpy)) := by
  letI : Y.ideal.IsPrime := (hJ Y hY).1
  have hw (p : S) : ∃ f : Poly n, f ∉ Y.ideal ∧ ∀ y ∈ Y.points,
      MvPolynomial.eval y f ≠ 0 → ∃ hpy : y ≠ p.val,
        (∀ V ∈ J, radialImage p.val V = radialImage p.val Y →
          (radialFiber p.val V (radialProjection p.val y hpy)).Finite ∧
          (radialFiber p.val V (radialProjection p.val y hpy)).ncard = r p.val V) ∧
        ∀ V ∈ J, radialImage p.val V = radialImage p.val Y →
          ∀ W ∈ J, V ≠ W →
            Disjoint (radialFiber p.val V (radialProjection p.val y hpy))
              (radialFiber p.val W (radialProjection p.val y hpy)) := by
    obtain ⟨Q, e, hhom, hnot, hopen⟩ := radial_group_fiber_open J hl hJ Y hY p.val
      (himage p.val p.property) (r p.val) (hgen p.val p.property)
    obtain ⟨a, ha, hap⟩ := radial_center_coordinate_separator Y (hJ Y hY).1 hl (hJ Y hY).2 p.val
    refine ⟨a * radialDirectionPullback p.val Q,
      (fun h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim ha
        (radialDirectionPullback_not_mem Y p.val Q hhom hnot)), ?_⟩
    intro y hy hval
    have hparts : MvPolynomial.eval y a ≠ 0 ∧
        MvPolynomial.eval y (radialDirectionPullback p.val Q) ≠ 0 := by
      simpa only [map_mul, mul_ne_zero_iff] using hval
    have hpy : y ≠ p.val := by intro he; exact hparts.1 (he ▸ hap)
    obtain ⟨hcount, hdisj⟩ := hopen (radialProjection p.val y hpy)
      (radialDirectionPullback_nonzero p.val y hpy Q hhom hparts.2)
    have hz : radialProjection p.val y hpy ∈ (radialImage p.val Y).points :=
      ProjectiveVariety.subset_closure _ ⟨y, hy, hpy, rfl⟩
    exact ⟨hpy, fun V hV hVz => hcount V hV hVz hz, hdisj⟩
  choose f hf hgood using hw
  have hprod : (∏ p : S, f p) ∉ Y.ideal := by
    intro h
    obtain ⟨p, _, hp⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact hf p hp
  rw [← Y.vanishingIdeal_points, MvPolynomial.mem_vanishingIdeal_iff] at hprod
  push Not at hprod
  obtain ⟨y, hy, hval⟩ := hprod
  refine ⟨y, hy, ?_⟩
  intro p hp
  apply hgood ⟨p, hp⟩ y hy
  have hval' : (∏ p : S, MvPolynomial.eval y (f p)) ≠ 0 := by
    simpa only [map_prod, MvPolynomial.aeval_eq_eval] using hval
  exact (Finset.prod_ne_zero_iff.mp hval') ⟨p,hp⟩ (Finset.mem_univ _)

end
end DistinctDistances.TrackA
