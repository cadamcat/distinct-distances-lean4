import DistinctDistances.TrackB.ParameterImageSupport
import DistinctDistances.TrackB.IncidenceLinearSupport

namespace DistinctDistances.TrackB
noncomputable section

def rulingPairPolynomials {e : ℕ} (C : SkewCoordinates e) :
    Fin (e * (e + e)) → Poly (skewDim e + e) :=
  fun k => MvPolynomial.X (Fin.natAdd (skewDim e) (finProdFinEquiv.symm k).1) *
    rulingGraphPolynomials C (finProdFinEquiv.symm k).2

def rulingTriplePolynomials {e : ℕ} (C : SkewCoordinates e) :
    Fin ((e * (e + e)) * (skewDim e + 1)) → Poly (skewDim e + e) :=
  fun k => rulingPairPolynomials C (finProdFinEquiv.symm k).1 *
    (Fin.cons (MvPolynomial.C 1 : Poly (skewDim e + e))
      (fun i : Fin (skewDim e) => MvPolynomial.X (Fin.castAdd e i)) :
      Fin (skewDim e + 1) → Poly (skewDim e + e)) (finProdFinEquiv.symm k).2

theorem eval_rulingPairPolynomials {e : ℕ} (C : SkewCoordinates e)
    (w : Point (skewDim e + e)) :
    (fun k => MvPolynomial.aeval w (rulingPairPolynomials C k)) =
      segreVector (secondPoint w) (graphVector C (firstPoint w) (secondPoint w)) := by
  funext k
  have hgraph := congrFun (eval_rulingGraphPolynomials C w) (finProdFinEquiv.symm k).2
  simpa only [rulingPairPolynomials, map_mul, MvPolynomial.aeval_X, segreVector,
    secondPoint] using congrArg (fun a : ℂ => w (Fin.natAdd (skewDim e)
      (finProdFinEquiv.symm k).1) * a) hgraph

theorem eval_rulingTriplePolynomials {e : ℕ} (C : SkewCoordinates e)
    (w : Point (skewDim e + e)) :
    (fun k => MvPolynomial.aeval w (rulingTriplePolynomials C k)) =
      segreVector (segreVector (secondPoint w) (graphVector C (firstPoint w) (secondPoint w)))
        (Fin.cons 1 (firstPoint w)) := by
  funext k
  let a := (finProdFinEquiv.symm k).1
  let b := (finProdFinEquiv.symm k).2
  change MvPolynomial.aeval w (rulingPairPolynomials C a *
    (Fin.cons (MvPolynomial.C 1 : Poly (skewDim e + e))
      (fun i : Fin (skewDim e) => MvPolynomial.X (Fin.castAdd e i)) :
      Fin (skewDim e + 1) → Poly (skewDim e + e)) b) = _
  rw [map_mul, congrFun (eval_rulingPairPolynomials C w) a]
  have hlast : MvPolynomial.aeval w
      ((Fin.cons (MvPolynomial.C 1 : Poly (skewDim e + e))
        (fun i : Fin (skewDim e) => MvPolynomial.X (Fin.castAdd e i)) :
        Fin (skewDim e + 1) → Poly (skewDim e + e)) b) =
      (Fin.cons (1 : ℂ) (firstPoint (n := skewDim e) (m := e) w) :
        Point (skewDim e + 1)) b := by
    cases b using Fin.cases <;> simp [firstPoint]
  rw [hlast]
  rfl

section Ruling
variable {e j N : ℕ} (C : SkewCoordinates e)
  (V : AffineVariety (skewDim e)) (Γ : AffineVariety (skewDim e + e))
  (H : Poly (skewDim e)) (a : Fin e) (R : IsRulingIncidence C V Γ H a j N)
include R

theorem rulingPairPolynomials_nonzero (w : Point (skewDim e + e)) (hw : w ∈ Γ.points) :
    (fun k => MvPolynomial.aeval w (rulingPairPolynomials C k)) ≠ 0 := by
  have hv : secondPoint w ≠ 0 := by
    intro hzero
    have h := R.normalized w hw
    rw [hzero] at h
    exact zero_ne_one h
  rw [eval_rulingPairPolynomials]
  exact segreVector_ne_zero _ _ hv (graphVector_ne_zero C _ _ hv)

theorem rulingTriplePolynomials_nonzero (w : Point (skewDim e + e)) (hw : w ∈ Γ.points) :
    (fun k => MvPolynomial.aeval w (rulingTriplePolynomials C k)) ≠ 0 := by
  have hp := rulingPairPolynomials_nonzero C V Γ H a R w hw
  rw [eval_rulingPairPolynomials] at hp
  rw [eval_rulingTriplePolynomials]
  apply segreVector_ne_zero _ _ hp
  intro hz
  have h := congrFun hz 0
  exact (one_ne_zero : (1 : ℂ) ≠ 0) (by simpa using h)

end Ruling
end
end DistinctDistances.TrackB
