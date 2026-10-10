import DistinctDistances.TrackA.RadialParameterFiberSupport

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical

/-- The literal cylinder over the supplied original affine carrier. -/
def lineCylinder {n : ℕ} (V : AffineVariety n) : AffineVariety (n+1) :=
  AffineVariety.closure {q | Fin.tail q ∈ V.points}

theorem lineCylinder_points {n : ℕ} (V : AffineVariety n) (q : Point (n+1)) :
    q ∈ (lineCylinder V).points ↔ Fin.tail q ∈ V.points := by
  constructor
  · intro hq f hf
    let F : Poly (n+1) := MvPolynomial.rename Fin.succ f
    have hF : F ∈ (lineCylinder V).ideal := by
      intro w hw
      change MvPolynomial.eval w (MvPolynomial.rename Fin.succ f) = 0
      rw [MvPolynomial.eval_rename]
      exact hw f hf
    have h := hq F hF
    change MvPolynomial.eval q (MvPolynomial.rename Fin.succ f) = 0 at h
    rw [MvPolynomial.eval_rename] at h
    exact h
  · intro hq
    exact AffineVariety.subset_closure _ hq

/-- Every counted original ray solution is an isolated point component of
the ORIGINAL cylinder plus pulled center equations. -/
theorem lineCylinder_isolated_parameter {n : ℕ} (V : AffineVariety n)
    (K : Ideal (Poly n)) (p y x : Point n) (hpy : y ≠ p) (hx : x ∈ V.points)
    (t : ℂ) (ht : p = y + t • (x-y))
    (hcenter : pointIdeal p ∈ K.minimalPrimes)
    (hfinite : (radialFiber p V (radialProjection p y hpy)).Finite) :
    pointIdeal (Fin.cons t x) ∈
      ((lineCylinder V).ideal ⊔ K.map
        (polynomialPointPullback (lineParameterCoordinate y)).toRingHom).minimalPrimes := by
  let q : Point (n+1) := Fin.cons t x
  have hmap : polynomialPoint (lineParameterCoordinate y) q = p := by
    rw [lineParameterCoordinate_eval]
    simpa only [q, lineParameterPoint, Fin.cons_zero, Fin.tail_cons] using ht.symm
  have hq : q ∈ (lineCylinder V).points := (lineCylinder_points V q).mpr (by simpa [q] using hx)
  have hmin : pointIdeal (polynomialPoint (lineParameterCoordinate y) q) ∈ K.minimalPrimes := by
    rwa [hmap]
  apply point_minimal_polynomial_preimage (lineCylinder V).ideal K (lineParameterCoordinate y) q hq hmin 1
  · simp
  · apply (lineParameter_fiber_finite V p y hpy hfinite).subset
    intro z hz
    refine ⟨(lineCylinder_points V z).mp hz.1, ?_⟩
    rw [← lineParameterCoordinate_eval, hz.2.2, hmap]

end
end DistinctDistances.TrackA
