import OAI.NumberTheory.PiExponent.Geometry.NormalizationGrowth
import DistinctDistances.TrackA.NarrowRadialCountSupport
import DistinctDistances.TrackA.IsolatedPolynomialPreimageSupport

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical

/-- The original source-times-line parametrization uses its literal coordinates. -/
def lineParameterPoint {n : ℕ} (y : Point n) (q : Point (n+1)) : Point n :=
  y + q 0 • (Fin.tail q - y)

/-- Its coordinate equations have degree at most two. -/
def lineParameterCoordinate {n : ℕ} (y : Point n) (i : Fin n) : Poly (n+1) :=
  MvPolynomial.C (y i) + MvPolynomial.X 0 * (MvPolynomial.X i.succ - MvPolynomial.C (y i))

theorem lineParameterCoordinate_eval {n : ℕ} (y : Point n) (q : Point (n+1)) :
    polynomialPoint (lineParameterCoordinate y) q = lineParameterPoint y q := by
  funext i
  simp [polynomialPoint, lineParameterCoordinate, lineParameterPoint, Pi.smul_apply, smul_eq_mul, Fin.tail]

theorem lineParameterCoordinate_degree {n : ℕ} (y : Point n) (i : Fin n) :
    (lineParameterCoordinate y i).totalDegree ≤ 2 := by
  have hs : (MvPolynomial.X i.succ - MvPolynomial.C (y i) : Poly (n+1)).totalDegree ≤ 1 :=
    (MvPolynomial.totalDegree_sub_C_le _ _).trans (by simp)
  have hm : (MvPolynomial.X 0 * (MvPolynomial.X i.succ - MvPolynomial.C (y i)) : Poly (n+1)).totalDegree ≤ 2 := by
    apply (MvPolynomial.totalDegree_mul _ _).trans
    simpa using Nat.add_le_add_left hs 1
  exact (MvPolynomial.totalDegree_add _ _).trans (by simpa using hm)

/-- Original center equations of degree L pull back to degree at most 2L.
This uses the original prebuilt OAI substitution degree theorem. -/
theorem lineParameter_pullback_degree {n : ℕ} (y : Point n) (f : Poly n) :
    (polynomialPointPullback (lineParameterCoordinate y) f).totalDegree ≤ 2 * f.totalDegree := by
  simpa only [polynomialPointPullback, Nat.mul_comm] using OAI.PiExponentJets.W24.totalDegree_aeval_le
    (lineParameterCoordinate y) 2 (lineParameterCoordinate_degree y) f

/-- Every literal solution over a center away from y has the original radial direction. -/
theorem lineParameter_radial_direction {n : ℕ} (p y x : Point n) (hpy : y ≠ p)
    (hxp : x ≠ p) (t : ℂ) (ht : p = y + t • (x-y)) :
    radialProjection p x hxp = radialProjection p y hpy := by
  have ht0 : t ≠ 0 := (radial_moving_parameter_endpoints p y x hpy hxp t ht).1
  apply (Projectivization.mk_eq_mk_iff' ℂ (x-p) (y-p)
    (sub_ne_zero.mpr hxp) (sub_ne_zero.mpr hpy)).mpr
  refine ⟨(t-1)*t⁻¹, ?_⟩
  funext i
  have h := congrFun ht i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at h ⊢
  field_simp [ht0]
  linear_combination h

/-- If the original radial fiber is finite, the literal parametrized fiber
on the original source-times-line set is finite, including its center endpoint. -/
theorem lineParameter_fiber_finite {n : ℕ} (V : AffineVariety n) (p y : Point n)
    (hpy : y ≠ p) (hfinite : (radialFiber p V (radialProjection p y hpy)).Finite) :
    {q : Point (n+1) | Fin.tail q ∈ V.points ∧ lineParameterPoint y q = p}.Finite := by
  let T : Set (Point (n+1)) := {q | Fin.tail q ∈ V.points ∧ lineParameterPoint y q = p}
  have hmaps : Set.MapsTo Fin.tail T (radialFiber p V (radialProjection p y hpy) ∪ {p}) := by
    intro q hq
    by_cases he : Fin.tail q = p
    · exact Or.inr he
    · exact Or.inl ⟨hq.1, he,
        lineParameter_radial_direction p y (Fin.tail q) hpy he (q 0) hq.2.symm⟩
  have hinj : Set.InjOn Fin.tail T := by
    intro q hq r hr he
    have hxny : Fin.tail q ≠ y := by
      intro hx
      have h := hq.2
      simp only [lineParameterPoint, hx, sub_self, smul_zero, add_zero] at h
      exact hpy h
    have hs : q 0 = r 0 := by
      apply smul_left_injective ℂ (sub_ne_zero.mpr hxny)
      change q 0 • (Fin.tail q-y) = r 0 • (Fin.tail q-y)
      apply add_left_cancel (a := y)
      simpa only [lineParameterPoint, ← he] using hq.2.trans hr.2.symm
    funext i
    cases i using Fin.cases with
    | zero => exact hs
    | succ i => exact congrFun he i
  exact (hfinite.union (Set.finite_singleton p)).of_injOn hmaps hinj

end
end DistinctDistances.TrackA
