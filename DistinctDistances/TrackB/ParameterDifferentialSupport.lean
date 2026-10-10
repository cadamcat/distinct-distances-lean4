import DistinctDistances.TrackB.RulingPolynomialImages
import DistinctDistances.TrackB.NormalizedImageSupport

namespace DistinctDistances.TrackB
noncomputable section
open scoped BigOperators

def rulingGraphDifferential {e : ℕ} (C : SkewCoordinates e) (w : Point (skewDim e + e)) :
    Point (skewDim e + e) →ₗ[ℂ] Point (e + e) :=
  LinearMap.pi (fun i => differential (rulingGraphPolynomials C i) w)

/-- Helper: differential of a coordinate variable is evaluation of the direction. -/
theorem bflat_pdiff_X {n : ℕ} (k : Fin n) (w δ : Point n) :
    differential (MvPolynomial.X k : Poly n) w δ = δ k := by
  simp only [differential, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul, MvPolynomial.pderiv_X]
  simp [Pi.single_apply]

/-- Helper: differential of a constant is zero. -/
theorem bflat_pdiff_C {n : ℕ} (c : ℂ) (w δ : Point n) :
    differential (MvPolynomial.C c : Poly n) w δ = 0 := by
  simp only [differential, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul, MvPolynomial.pderiv_C, map_zero, zero_mul,
    Finset.sum_const_zero]

/-- Helper: differential commutes with finite sums. -/
theorem bflat_pdiff_finset_sum {n : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → Poly n) (w δ : Point n) :
    differential (∑ i ∈ s, f i) w δ = ∑ i ∈ s, differential (f i) w δ := by
  classical
  simp only [differential, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul]
  simp_rw [map_sum, Finset.sum_mul]
  exact Finset.sum_comm

/-- Helper: product rule for a constant-scaled product of two variables. -/
theorem bflat_pdiff_C_mul_X_mul_X {n : ℕ} (c : ℂ) (a b : Fin n) (w δ : Point n) :
    differential (MvPolynomial.C c * MvPolynomial.X a * MvPolynomial.X b) w δ =
      c * (δ a * w b + w a * δ b) := by
  have hCa : differential (MvPolynomial.C c * MvPolynomial.X a : Poly n) w δ =
      c * δ a := by
    rw [differential_mul_X, bflat_pdiff_C]
    simp only [mul_zero, zero_add, MvPolynomial.aeval_C,
      Algebra.algebraMap_self, RingHom.id_apply]
  calc differential (MvPolynomial.C c * MvPolynomial.X a * MvPolynomial.X b) w δ
        = w b * differential (MvPolynomial.C c * MvPolynomial.X a : Poly n) w δ +
          MvPolynomial.aeval w (MvPolynomial.C c * MvPolynomial.X a) * δ b :=
        differential_mul_X _ _ _ _
      _ = w b * (c * δ a) + (c * w a) * δ b := by
        rw [hCa]
        simp only [map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
          Algebra.algebraMap_self, RingHom.id_apply]
      _ = c * (δ a * w b + w a * δ b) := by ring

/-- differentiate the actual polynomial map (z,v)↦(v,zv). -/
theorem rulingGraphDifferential_coordinates {e : ℕ} (C : SkewCoordinates e)
    (z dz : Point (skewDim e)) (v dv : Point e) :
    rulingGraphDifferential C (joinPoints z v) (joinPoints dz dv) =
      joinPoints dv (pointOfCovector ((C.decode dz).val v + (C.decode z).val dv)) := by
  ext i
  simp only [rulingGraphDifferential, LinearMap.pi_apply]
  cases i using Fin.addCases with
  | left j =>
      simp only [rulingGraphPolynomials, Fin.addCases_left]
      rw [bflat_pdiff_X]
      simp only [joinPoints, Fin.addCases_right, Fin.addCases_left]
  | right j =>
      simp only [rulingGraphPolynomials, Fin.addCases_right, bflat_pdiff_finset_sum]
      have hexpand (p : Point (skewDim e)) (r : Point e) :
          ((C.decode p).val r) (Pi.single j 1) =
            ∑ k : Fin (skewDim e), ∑ l : Fin e,
              (((C.decode (Pi.single k 1)).val (Pi.single l 1)) (Pi.single j 1)) *
              (p k * r l) := by
        have hp : p = ∑ k : Fin (skewDim e), p k • (Pi.single k (1 : ℂ) : Point (skewDim e)) := by
          simpa using ((Pi.basisFun ℂ (Fin (skewDim e))).sum_repr p).symm
        have hr : r = ∑ l : Fin e, r l • (Pi.single l (1 : ℂ) : Point e) := by
          simpa using ((Pi.basisFun ℂ (Fin e)).sum_repr r).symm
        conv_lhs => rw [hp, hr]
        simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul,
          LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro l _
        ring
      have hcov : pointOfCovector ((C.decode dz).val v + (C.decode z).val dv) j =
          ((C.decode dz).val v) (Pi.single j 1) + ((C.decode z).val dv) (Pi.single j 1) := by
        simp [pointOfCovector, LinearMap.add_apply]
      have hrhs : joinPoints dv (pointOfCovector ((C.decode dz).val v + (C.decode z).val dv))
          (Fin.natAdd e j) =
          ((C.decode dz).val v) (Pi.single j 1) + ((C.decode z).val dv) (Pi.single j 1) := by
        simp only [joinPoints, Fin.addCases_right]
        exact hcov
      rw [hrhs, hexpand dz v, hexpand z dv]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro l _
      rw [bflat_pdiff_C_mul_X_mul_X]
      simp only [joinPoints, Fin.addCases_left, Fin.addCases_right]
      ring

/-- a hyperplane containing the full evaluation kernel has one less
evaluation rank than the whole alternating-form space. -/
theorem alternating_hyperplane_evaluation_rank {e : ℕ} (he : 3 ≤ e)
    (v : Point e) (hv : v ≠ 0) (W : Submodule ℂ (alternatingForms (U := Point e)))
    (hdim : Module.finrank ℂ W + 1 = skewDim e)
    (hker : LinearMap.ker (alternatingEvaluation v) ≤ W) :
    Module.finrank ℂ (W.map (alternatingEvaluation v)) + 1 = e - 1 := by
  have hrange : W.map (alternatingEvaluation v) =
      LinearMap.range ((alternatingEvaluation v).domRestrict W) :=
    (LinearMap.range_domRestrict W _).symm
  have hkerW : Module.finrank ℂ (LinearMap.ker ((alternatingEvaluation v).domRestrict W)) =
      Module.finrank ℂ (LinearMap.ker (alternatingEvaluation v)) := by
    rw [LinearMap.ker_domRestrict]
    exact (Submodule.comapSubtypeEquivOfLe hker).finrank_eq
  letI : AddCommGroup ↥W := Module.addCommMonoidToAddCommGroup ℂ
  haveI : FiniteDimensional ℂ ↥W := Module.Finite.of_injective W.subtype Subtype.val_injective
  have hrn := LinearMap.finrank_range_add_finrank_ker ((alternatingEvaluation v).domRestrict W)
  have h1 : Module.finrank ℂ (W.map (alternatingEvaluation v)) +
      Module.finrank ℂ (LinearMap.ker (alternatingEvaluation v)) = Module.finrank ℂ W := by
    rw [hrange, ← hkerW]
    exact hrn
  have h2 := alternatingEvaluation_kernel_finrank v hv
  rw [Module.finrank_fin_fun] at h2
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
  have hchoose : (k + 1).choose 2 = k.choose 1 + k.choose 2 := Nat.choose_succ_succ k 1
  rw [Nat.choose_one_right] at hchoose
  rw [Nat.add_sub_cancel] at h2 ⊢
  unfold skewDim at hdim
  omega

end
end DistinctDistances.TrackB
