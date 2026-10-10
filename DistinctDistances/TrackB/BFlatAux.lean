import DistinctDistances.TrackB.TangentQuotientSupport
import DistinctDistances.TrackD.Requests

namespace DistinctDistances.TrackB
noncomputable section
open scoped BigOperators

set_option linter.unusedSimpArgs false

theorem bflat_differential_apply_sum {n : ℕ} (f : Poly n) (x d : Point n) :
    differential f x d = ∑ i : Fin n, MvPolynomial.aeval x (MvPolynomial.pderiv i f) * d i := by
  simp [differential, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]

theorem bflat_differential_X_apply {n : ℕ} (i : Fin n) (x d : Point n) :
    differential (MvPolynomial.X i : Poly n) x d = d i := by
  simp [bflat_differential_apply_sum, MvPolynomial.pderiv_X, Pi.single_apply]

theorem bflat_differential_C_apply {n : ℕ} (c : ℂ) (x d : Point n) :
    differential (MvPolynomial.C c : Poly n) x d = 0 := by
  simp [bflat_differential_apply_sum, MvPolynomial.pderiv_C]

theorem bflat_differential_sub_apply {n : ℕ} (f g : Poly n) (x d : Point n) :
    differential (f - g : Poly n) x d = differential f x d - differential g x d := by
  simp [bflat_differential_apply_sum, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem bflat_differential_X_sub_C_apply {n : ℕ} (a : Fin n) (c : ℂ) (x d : Point n) :
    differential (MvPolynomial.X a - MvPolynomial.C c : Poly n) x d = d a := by
  rw [bflat_differential_sub_apply, bflat_differential_X_apply, bflat_differential_C_apply,
    sub_zero]

theorem bflat_differential_C {n : ℕ} (c : ℂ) (x : Point n) :
    differential (MvPolynomial.C c : Poly n) x = 0 := by
  apply LinearMap.ext
  intro d
  exact bflat_differential_C_apply c x d

end
end DistinctDistances.TrackB
