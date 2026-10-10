import DistinctDistances.TrackA.RadialConePointSupport

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical

/-- A nonzero target cone point forces the original source away from the center. -/
theorem radialConePair_source_ne {n : ℕ} (V : AffineVariety n) (p v : Point n)
    (hv : v ≠ 0) (q : radialConePairs V p v) : q.1.1 ≠ p := by
  intro he
  have h := q.2.2
  rw [he, sub_self, smul_zero] at h
  exact hv h.symm

/-- Forgetting the unique cone scalar gives the literal radial fiber. -/
def radialConePairsEquivFiber {n : ℕ} (V : AffineVariety n) (p v : Point n)
    (hv : v ≠ 0) : radialConePairs V p v ≃
      radialFiber p V (Projectivization.mk ℂ v hv) := by
  let forget (q : radialConePairs V p v) : radialFiber p V (Projectivization.mk ℂ v hv) :=
    ⟨q.1.1, q.2.1, radialConePair_source_ne V p v hv q, by
      change Projectivization.mk ℂ (q.1.1-p) _ = Projectivization.mk ℂ v hv
      exact ((Projectivization.mk_eq_mk_iff' ℂ v (q.1.1-p) hv _).mpr ⟨q.1.2, q.2.2⟩).symm⟩
  apply Equiv.ofBijective forget
  constructor
  · intro q w he
    have hx : q.1.1 = w.1.1 := congrArg Subtype.val he
    apply Subtype.ext
    apply Prod.ext hx
    apply smul_left_injective ℂ (sub_ne_zero.mpr (radialConePair_source_ne V p v hv q))
    change q.1.2 • (q.1.1-p) = w.1.2 • (q.1.1-p)
    rw [q.2.2, hx, w.2.2]
  · intro x
    obtain ⟨hx, hxne, hproj⟩ := x.2
    change Projectivization.mk ℂ (x.1-p) _ = Projectivization.mk ℂ v hv at hproj
    obtain ⟨t, ht⟩ := (Projectivization.mk_eq_mk_iff' ℂ v (x.1-p) hv _).mp hproj.symm
    exact ⟨⟨(x.1,t), hx, ht⟩, Subtype.ext rfl⟩

/-- The original base-linear cone Hom count is the number of actual radial points. -/
theorem radialCone_hom_count_transfer {n : ℕ} (V : AffineVariety n) (p v : Point n)
    (hv : v ∈ (radialImage p V).affineCone.points) (hv0 : v ≠ 0) (r : ℕ) :
    letI := radialConeAlgebra V p
    letI := radialConePointAlgebra V p v hv
    Finite (Polynomial (Poly n ⧸ V.ideal) →ₐ[RadialConeBase V p] ℂ) →
    Nat.card (Polynomial (Poly n ⧸ V.ideal) →ₐ[RadialConeBase V p] ℂ) = r →
      (radialFiber p V (Projectivization.mk ℂ v hv0)).Finite ∧
      (radialFiber p V (Projectivization.mk ℂ v hv0)).ncard = r := by
  letI := radialConeAlgebra V p
  letI := radialConePointAlgebra V p v hv
  intro hfinite hcard
  letI := hfinite
  let e := (radialConeHomEquivPairs V p v hv).trans (radialConePairsEquivFiber V p v hv0)
  haveI : Finite (radialFiber p V (Projectivization.mk ℂ v hv0)) := Finite.of_equiv _ e
  exact ⟨Set.toFinite _, (Nat.card_congr e.symm).trans hcard⟩

/-- A nonzero original target polynomial gives a positive constant literal
radial fiber count wherever a nonzero cone representative avoids it. -/
theorem radial_generic_cone_fiber_count {n l : ℕ} (V : AffineVariety n)
    (hV : V.IsIrreducible) (hd : V.dimension = l) (p : Point n)
    (hactual : ∃ x ∈ V.points, x ≠ p) (himage : (radialImage p V).dimension = l) :
    ∃ H : Poly n, H ∉ (radialImage p V).ideal ∧ ∃ r : ℕ, 0 < r ∧
      ∀ (v : Point n) (hv0 : v ≠ 0), v ∈ (radialImage p V).affineCone.points →
        MvPolynomial.aeval v H ≠ 0 →
          (radialFiber p V (Projectivization.mk ℂ v hv0)).Finite ∧
          (radialFiber p V (Projectivization.mk ℂ v hv0)).ncard = r := by
  letI := radialConeAlgebra V p
  obtain ⟨g, hg, r, hr, hcount⟩ := radialCone_generic_field_hom_count V hV hd p hactual himage
  obtain ⟨H, hH⟩ := Ideal.Quotient.mk_surjective g
  have hHnot : H ∉ (radialImage p V).ideal := by
    rw [radialImage_ideal_eq_cone_ker V hV p hactual]
    intro hmem
    exact hg (hH.symm.trans (Ideal.Quotient.eq_zero_iff_mem.mpr hmem))
  refine ⟨H, hHnot, r, hr, ?_⟩
  intro v hv0 hv heval
  letI := radialConePointAlgebra V p v hv
  have hgval : algebraMap (RadialConeBase V p) ℂ g ≠ 0 := by
    change radialConePoint V p v hv g ≠ 0
    rw [← hH, radialConePoint_mk]
    exact heval
  obtain ⟨hfin, hcard⟩ := hcount ℂ hgval
  exact radialCone_hom_count_transfer V p v hv hv0 r hfin hcard

end
end DistinctDistances.TrackA
