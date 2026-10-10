import DistinctDistances.TrackA.RadialIntersectionSupport
import DistinctDistances.TrackA.RadialRootCountSupport

namespace DistinctDistances.TrackA
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators Classical

theorem projective_homogeneous_nonzero_point {n e : ℕ} (Y : ProjectiveVariety n)
    (H : Poly n) (hh : H.IsHomogeneous e) (hn : H ∉ Y.ideal) :
    ∃ z ∈ Y.points, MvPolynomial.eval z.rep H ≠ 0 := by
  rw [← Y.vanishingIdeal_points] at hn
  change H ∉ MvPolynomial.vanishingIdeal ℂ (ProjectiveVariety.nonzeroRepresentatives Y.points) at hn
  rw [MvPolynomial.mem_vanishingIdeal_iff] at hn
  push Not at hn
  obtain ⟨v, ⟨hv0, hvY⟩, hvH⟩ := hn
  refine ⟨Projectivization.mk ℂ v hv0, hvY, ?_⟩
  intro hz
  apply hvH
  simpa only [MvPolynomial.aeval_eq_eval] using
    (Bridges.homogeneous_eval_zero_mk_iff H hh v hv0).1 hz

/-- Finite products choose one literal target fiber, simultaneously avoiding
all component intersections and every identically-zero ray restriction. -/
theorem simultaneous_radial_fibers {n l : ℕ} (J : AffineFamily.Family n)
    (hl : 1 ≤ l) (hJ : AffineFamily.IsPure J l) (Y : AffineVariety n) (hY : Y ∈ J)
    (p : Point n) (himage : (radialImage p Y).dimension = l)
    (himages : ∀ V ∈ J, radialImage p V = radialImage p Y)
    (r : AffineVariety n → ℕ)
    (hgen : ∀ V ∈ J, GenericallyFiniteRadialDegree p V (r V))
    (f : Poly n) (hfY : f ∈ Y.ideal)
    (hproper : ∃ y ∈ Y.points, ∃ t : ℂ, MvPolynomial.eval (p + t • (y-p)) f ≠ 0) :
    ∃ z ∈ (radialImage p Y).points, rayPolynomial p z.rep f ≠ 0 ∧
      (∀ V ∈ J, (radialFiber p V z).Finite ∧ (radialFiber p V z).ncard = r V) ∧
      ∀ V ∈ J, ∀ W ∈ J, V ≠ W → Disjoint (radialFiber p V z) (radialFiber p W z) := by
  let Z := radialImage p Y
  have hZprime : Z.IsIrreducible := radialImage_irreducible p Y (hJ Y hY).1
    (radial_actual_of_generic Y p (hgen Y hY))
  letI : Z.ideal.IsPrime := hZprime
  have hgw (V : J) : ∃ (g : Poly n) (d : ℕ), g.IsHomogeneous d ∧ g ∉ Z.ideal ∧
      ∀ z ∈ Z.points, MvPolynomial.aeval z.rep g ≠ 0 →
        (radialFiber p V.val z).Finite ∧ (radialFiber p V.val z).ncard = r V.val := by
    obtain ⟨_, g, d, hhom, hnot, hgeneric⟩ := hgen V.val V.property
    rw [himages V.val V.property] at hnot hgeneric
    exact ⟨g, d, hhom, hnot, hgeneric⟩
  choose g d hghom hgnot hgeneric using hgw
  let Pairs := {a : J × J // a.1 ≠ a.2}
  have hpw (a : Pairs) : ∃ (H : Poly n) (e : ℕ), H.IsHomogeneous e ∧ H ∉ Z.ideal ∧
      ∀ z : ProjectivePoint n, MvPolynomial.eval z.rep H ≠ 0 →
        Disjoint (radialFiber p a.val.1.val z) (radialFiber p a.val.2.val z) := by
    let V := a.val.1.val
    let W := a.val.2.val
    have hne : V ≠ W := fun he => a.property (Subtype.ext he)
    have hVdim : (radialImage p V).dimension = l := by
      rw [himages V a.val.1.property]
      exact himage
    obtain ⟨H, e, hh, hn, hdisj⟩ := radial_fibers_disjoint_open V W
      (hJ V a.val.1.property).1 (hJ W a.val.2.property).1 hl
      (hJ V a.val.1.property).2 (hJ W a.val.2.property).2 hne p hVdim
      (radial_actual_of_generic V p (hgen V a.val.1.property))
    rw [himages V a.val.1.property] at hn
    exact ⟨H, e, hh, hn, hdisj⟩
  choose H e hHhom hHnot hdisj using hpw
  obtain ⟨H0, e0, h0hom, h0not, h0ray⟩ := ray_nonzero_principal_open p Y f hfY hproper
  let Q := H0 * (∏ V : J, g V) * (∏ a : Pairs, H a)
  have hgp : (∏ V : J, g V) ∉ Z.ideal := by
    intro h
    obtain ⟨V, _, hV⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact hgnot V hV
  have hHp : (∏ a : Pairs, H a) ∉ Z.ideal := by
    intro h
    obtain ⟨a, _, ha⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact hHnot a ha
  have hQnot : Q ∉ Z.ideal := by
    intro h
    rcases hZprime.mem_or_mem h with h | h
    · exact (hZprime.mem_or_mem h).elim h0not hgp
    · exact hHp h
  have hQhom : Q.IsHomogeneous (e0 + (∑ V : J, d V) + ∑ a : Pairs, e a) :=
    (h0hom.mul (MvPolynomial.IsHomogeneous.prod Finset.univ g d (fun V _ => hghom V))).mul
      (MvPolynomial.IsHomogeneous.prod Finset.univ H e (fun a _ => hHhom a))
  obtain ⟨z, hz, hzQ⟩ := projective_homogeneous_nonzero_point Z Q hQhom hQnot
  have hzparts : MvPolynomial.eval z.rep H0 ≠ 0 ∧
      (∏ V : J, MvPolynomial.eval z.rep (g V)) ≠ 0 ∧
      (∏ a : Pairs, MvPolynomial.eval z.rep (H a)) ≠ 0 := by
    simpa only [Q, map_mul, map_prod, mul_ne_zero_iff, and_assoc] using hzQ
  refine ⟨z, hz, h0ray z hzparts.1, ?_, ?_⟩
  · intro V hV
    apply hgeneric ⟨V, hV⟩ z hz
    have h := (Finset.prod_ne_zero_iff.mp hzparts.2.1) ⟨V, hV⟩ (Finset.mem_univ _)
    simpa only [MvPolynomial.aeval_eq_eval] using h
  · intro V hV W hW hne
    let a : Pairs := ⟨(⟨V, hV⟩, ⟨W, hW⟩), fun he => hne (congrArg Subtype.val he)⟩
    exact hdisj a z ((Finset.prod_ne_zero_iff.mp hzparts.2.2) a (Finset.mem_univ _))

end
end DistinctDistances.TrackA
