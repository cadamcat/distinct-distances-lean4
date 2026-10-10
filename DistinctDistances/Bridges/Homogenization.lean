import DistinctDistances.Bridges.ProjectiveEnvelope
import DistinctDistances.Foundations.Local
import Mathlib.Algebra.MvPolynomial.Funext

/-! Homogenization and dehomogenization in the distinguished affine chart. -/

namespace DistinctDistances.Bridges
open scoped BigOperators Classical
noncomputable section

 def homogenizedExponent {n : ℕ} (D : ℕ) (s : Fin n →₀ ℕ) : Fin (n+1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Fin.cons (D-s.degree) s)

 theorem homogenizedExponent_degree {n : ℕ} (D : ℕ) (s : Fin n →₀ ℕ)
    (hD : s.degree ≤ D) : (homogenizedExponent D s).degree = D := by
  have he : (homogenizedExponent D s).degree = D-s.degree+s.degree := by
    simp [Finsupp.degree_eq_sum, homogenizedExponent, Fin.sum_univ_succ]
  exact he.trans (Nat.sub_add_cancel hD)

 def homogenize {n : ℕ} (f : Poly n) : Poly (n+1) :=
  ∑ s ∈ f.support, MvPolynomial.monomial (homogenizedExponent f.totalDegree s) (f.coeff s)

 theorem homogenize_homogeneous {n : ℕ} (f : Poly n) :
    (homogenize f).IsHomogeneous f.totalDegree := by
  apply MvPolynomial.IsHomogeneous.sum
  intro s hs
  apply MvPolynomial.isHomogeneous_monomial
  exact homogenizedExponent_degree f.totalDegree s (MvPolynomial.le_totalDegree hs)

 theorem eval_homogenize_cons {n : ℕ} (f : Poly n) (x : Point n) :
    MvPolynomial.eval (Fin.cons 1 x) (homogenize f) = MvPolynomial.eval x f := by
  rw [MvPolynomial.eval_eq' _ f]
  simp only [homogenize, map_sum, MvPolynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro s hs
  congr 1
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_succ]
  simp [homogenizedExponent]

 theorem eval_chartPullback_zero {n : ℕ} (f : Poly (n+1)) (x : Point n) :
    MvPolynomial.eval x (chartPullback 0 f) = MvPolynomial.eval (Fin.cons 1 x) f := by
  change MvPolynomial.aeval x (chartPullback 0 f) = MvPolynomial.aeval (Fin.cons 1 x) f
  rw [chartPullback, MvPolynomial.comp_aeval_apply]
  apply congrArg (fun g : Point (n+1) => MvPolynomial.aeval g f)
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

 theorem chartPullback_homogenize {n : ℕ} (f : Poly n) :
    chartPullback 0 (homogenize f) = f := by
  apply MvPolynomial.funext
  intro x
  rw [eval_chartPullback_zero, eval_homogenize_cons]

end
end DistinctDistances.Bridges
