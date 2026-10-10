import DistinctDistances.TrackC.Basic

open scoped BigOperators

namespace DistinctDistances.TrackC

@[simp] theorem evalR_C (d : ℕ) (c : ℝ) :
    evalR (MvPolynomial.C c : Poly d) = (fun _ : E d => c) := by
  funext x
  simp [evalR]

@[simp] theorem evalR_add {d : ℕ} (f g : Poly d) :
    evalR (f + g) = evalR f + evalR g := by
  funext x
  simp [evalR]

@[simp] theorem evalR_mul_X {d : ℕ} (f : Poly d) (j : Fin d) :
    evalR (f * MvPolynomial.X j) = evalR f * (fun x : E d => x j) := by
  funext x
  simp [evalR]

/-- Coordinate functional on the Euclidean metric model. -/
noncomputable def coordinateL (d : ℕ) (i : Fin d) : E d →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).toContinuousLinearMap

@[simp] theorem coordinateL_apply (d : ℕ) (i : Fin d) (x : E d) :
    coordinateL d i x = x i := rfl

/-- Differential used by CI:188–206 and motions.tex:416–424. -/
noncomputable def polynomialDifferential {d : ℕ} (f : Poly d) (x : E d) : E d →L[ℝ] ℝ :=
  ∑ i : Fin d, evalR (MvPolynomial.pderiv i f) x • coordinateL d i

@[simp] theorem polynomialDifferential_apply {d : ℕ} (f : Poly d) (x v : E d) :
    polynomialDifferential f x v = ∑ i : Fin d, evalR (MvPolynomial.pderiv i f) x * v i := by
  simp [polynomialDifferential]

private theorem polynomialDifferential_add {d : ℕ} (f g : Poly d) (x : E d) :
    polynomialDifferential (f + g) x = polynomialDifferential f x + polynomialDifferential g x := by
  ext v
  simp [polynomialDifferential_apply, evalR, add_mul, Finset.sum_add_distrib]

private theorem polynomialDifferential_mul_X {d : ℕ} (f : Poly d) (j : Fin d) (x : E d) :
    polynomialDifferential (f * MvPolynomial.X j) x =
      x j • polynomialDifferential f x + evalR f x • coordinateL d j := by
  ext v
  simp [polynomialDifferential_apply, evalR, MvPolynomial.pderiv_X,
    Pi.single_apply, apply_ite, add_mul, Finset.sum_add_distrib, mul_ite, ite_mul,
    Finset.mul_sum, mul_assoc, add_comm]

/-- Polynomial evaluation has the expected first differential on Euclidean space. -/
theorem polynomial_hasFDerivAt (d : ℕ) (f : Poly d) (x : E d) :
    HasFDerivAt (evalR f) (polynomialDifferential f x) x := by
  induction f using MvPolynomial.induction_on generalizing x with
  | C c =>
    simpa [evalR, polynomialDifferential] using (hasFDerivAt_const c x :
      HasFDerivAt (fun _ : E d => c) (0 : E d →L[ℝ] ℝ) x)
  | add f g hf hg =>
    simpa [evalR_add, polynomialDifferential_add] using (hf x).add (hg x)
  | mul_X f j hf =>
    have hcoord : HasFDerivAt (fun z : E d => z j) (coordinateL d j) x :=
      (coordinateL d j).hasFDerivAt
    simpa [evalR_mul_X, polynomialDifferential_mul_X, evalR, add_comm] using (hf x).mul hcoord

/-- The smoothness input for the implicit surface chart. -/
theorem polynomial_contDiff (d : ℕ) (f : Poly d) (n : WithTop ℕ∞) :
    ContDiff ℝ n (evalR f) := by
  induction f using MvPolynomial.induction_on with
  | C c => simpa only [evalR_C] using (contDiff_const : ContDiff ℝ n (fun _ : E d => c))
  | add f g hf hg =>
    rw [evalR_add]
    change ContDiff ℝ n (fun z : E d => evalR f z + evalR g z)
    exact hf.add hg
  | mul_X f j hf =>
    have hcoord : ContDiff ℝ n (fun z : E d => z j) := (coordinateL d j).contDiff
    rw [evalR_mul_X]
    change ContDiff ℝ n (fun z : E d => evalR f z * z j)
    convert! hf.mul hcoord using 1

/-- Strict differentiability required by the implicit function theorem. -/
theorem polynomial_hasStrictFDerivAt (d : ℕ) (f : Poly d) (x : E d) :
    HasStrictFDerivAt (evalR f) (polynomialDifferential f x) x := by
  exact (polynomial_contDiff d f 1).contDiffAt.hasStrictFDerivAt'
    (polynomial_hasFDerivAt d f x) one_ne_zero

/-- Coordinate derivatives commute; used to identify the Hessian. -/
theorem polynomial_pderiv_commute (d : ℕ) (f : Poly d) (i j : Fin d) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j f) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i f) := by
  by_cases hij : i = j
  · subst j
    rfl
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp [hf, hg]
  | mul_X f k hf =>
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp_all [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X, Pi.single_apply,
        apply_ite, add_comm, add_left_comm, add_assoc]

/-- Differential evaluation on a coordinate basis vector. -/
theorem polynomialDifferential_single (d : ℕ) (f : Poly d) (x : E d) (i : Fin d) :
    polynomialDifferential f x (EuclideanSpace.single i 1) =
      evalR (MvPolynomial.pderiv i f) x := by
  simp [polynomialDifferential_apply, EuclideanSpace.single, Pi.single_apply]

/-- A regular hypersurface point has a surjective differential. -/
theorem regular_polynomial_differential_surjective (f : Poly 3) (x : E 3)
    (hx : regularPoint f x) : Function.Surjective (polynomialDifferential f x) := by
  obtain ⟨i, hi⟩ := hx.2
  change evalR (MvPolynomial.pderiv i f) x ≠ 0 at hi
  intro t
  refine ⟨(t / evalR (MvPolynomial.pderiv i f) x) • EuclideanSpace.single i 1, ?_⟩
  rw [map_smul, polynomialDifferential_single, smul_eq_mul, div_mul_cancel₀ _ hi]

end DistinctDistances.TrackC
