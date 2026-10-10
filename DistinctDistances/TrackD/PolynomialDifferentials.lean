import DistinctDistances.TrackD.ProductTangents

namespace DistinctDistances.TrackD
open scoped BigOperators Classical
noncomputable section
variable {d : ℕ}

@[simp] theorem differential_X (i : Fin d) (x : Point d) :
    differential (MvPolynomial.X i) x = LinearMap.proj i := by
  ext v
  simp [differential, Pi.single_apply]

theorem differential_sub (f g : Poly d) (x : Point d) :
    differential (f - g) x = differential f x - differential g x := by
  ext v
  simp [differential, sub_mul, Finset.sum_sub_distrib]

theorem differential_mul (f g : Poly d) (x : Point d) :
    differential (f * g) x = MvPolynomial.eval x g • differential f x +
      MvPolynomial.eval x f • differential g x := by
  apply LinearMap.ext
  intro v
  let φ : Poly d →ₐ[ℂ] ℂ := MvPolynomial.aeval x
  letI : Algebra (Poly d) ℂ := φ.toRingHom.toAlgebra
  letI : IsScalarTower ℂ (Poly d) ℂ := IsScalarTower.of_algHom φ
  let δ := MvPolynomial.mkDerivation ℂ v
  have hδ (p : Poly d) : δ p = differential p x v := by
    have hs := mk_derivation_sum ℂ v p
    simp only [Algebra.smul_def] at hs
    change δ p = ∑ i : Fin d, MvPolynomial.eval x (MvPolynomial.pderiv i p) * v i at hs
    simpa [differential, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.proj_apply, smul_eq_mul] using hs
  have hmul := δ.leibniz f g
  change δ (f * g) = MvPolynomial.eval x f * δ g + MvPolynomial.eval x g * δ f at hmul
  simpa only [hδ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, add_comm] using hmul

theorem differential_add (f g : Poly d) (x : Point d) :
    differential (f + g) x = differential f x + differential g x := by
  ext v
  simp [differential, add_mul, Finset.sum_add_distrib]

/-- The algebraic gradient is the actual complex derivative of polynomial evaluation. -/
theorem polynomial_eval_hasFDerivAt (q : Poly d) (x : Point d) :
    HasFDerivAt (fun z : Point d => MvPolynomial.eval z q)
      (LinearMap.toContinuousLinearMap (differential q x)) x := by
  induction q using MvPolynomial.induction_on with
  | C c => simpa using (hasFDerivAt_const (𝕜 := ℂ) c x)
  | add p q hp hq =>
    convert hp.add hq using 1
    · ext z
      simp
    · ext v
      simp [differential_add]
  | mul_X p i hp =>
    have hi : HasFDerivAt (fun z : Point d => z i)
        (LinearMap.toContinuousLinearMap (LinearMap.proj i : Point d →ₗ[ℂ] ℂ)) x :=
      (LinearMap.toContinuousLinearMap (LinearMap.proj i : Point d →ₗ[ℂ] ℂ)).hasFDerivAt
    convert hp.mul hi using 1
    · ext z
      simp
    · ext v
      simp [differential_mul]
      ring

end
end DistinctDistances.TrackD
