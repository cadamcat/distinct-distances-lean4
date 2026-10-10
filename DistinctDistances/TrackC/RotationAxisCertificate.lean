import DistinctDistances.TrackC.HomogeneousRotation
import DistinctDistances.TrackC.RotationDetWitness

open scoped BigOperators
open Classical

noncomputable section

namespace DistinctDistances.TrackC

def spatialIsometryMatrix (S : E 3 ≃ₗᵢ[ℝ] E 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  LinearMap.toMatrix homRotationStdBasis homRotationStdBasis S.toLinearMap

theorem spatialIsometryMatrix_orthogonal (S : E 3 ≃ₗᵢ[ℝ] E 3) :
    (spatialIsometryMatrix S).transpose*spatialIsometryMatrix S = 1 := by
  ext i j
  have h := S.inner_map_map (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial] at h
  simp only [spatialIsometryMatrix,Matrix.mul_apply,Matrix.transpose_apply]
  simp [LinearMap.toMatrix_apply,homRotationStdBasis,EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply,Matrix.one_apply]
  simpa [EuclideanSpace.single_apply,mul_comm,eq_comm] using h

theorem reversing_matrix_add_one_det_zero (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : A.transpose*A = 1) (hdet : Matrix.det A = -1) : Matrix.det (1+A) = 0 := by
  have hrow : A*A.transpose = 1 := (mul_eq_one_comm).mp hA
  have hprod : A*(1+A.transpose) = 1+A := by rw [Matrix.mul_add,Matrix.mul_one,hrow];abel
  have h := congrArg Matrix.det hprod
  rw [Matrix.det_mul,hdet] at h
  have ht : Matrix.det (1+A.transpose) = Matrix.det (1+A) := by
    have ht : (1+A).transpose = 1+A.transpose := by ext i j;simp [Matrix.transpose_apply,Matrix.one_apply,eq_comm]
    rw [← ht,Matrix.det_transpose]
  rw [ht] at h
  linarith

def spatialNormalFunctional (n : E 3) : E 3 →ₗ[ℝ] ℝ := (innerSL ℝ n).toLinearMap

def spatialAxisPerturbation (S : E 3 ≃ₗᵢ[ℝ] E 3) (n : E 3) : E 3 →ₗ[ℝ] E 3 :=
  S.toLinearMap+(LinearMap.id : E 3 →ₗ[ℝ] E 3)+(spatialNormalFunctional n).smulRight n

theorem spatialAxisPerturbation_toMatrix (S : E 3 ≃ₗᵢ[ℝ] E 3) (n : E 3) :
    LinearMap.toMatrix homRotationStdBasis homRotationStdBasis (spatialAxisPerturbation S n) =
      1+spatialIsometryMatrix S+normalOuterMatrix n := by
  ext i j
  simp [spatialAxisPerturbation,spatialIsometryMatrix,LinearMap.toMatrix_apply,
    homRotationStdBasis,EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply,
    spatialNormalFunctional,normalOuterMatrix,PiLp.inner_apply,Matrix.one_apply,mul_comm]
  ring

/-- A nonsingular normal perturbation certifies a one-dimensional reversing axis transverse to the normal plane. -/
theorem reversing_axis_certificate (S : E 3 ≃ₗᵢ[ℝ] E 3) (hS : LinearMap.det S.toLinearMap = -1)
    (n : E 3) (hM : Matrix.det (1+spatialIsometryMatrix S+normalOuterMatrix n) ≠ 0) :
    Module.finrank ℝ (LinearMap.ker (S.toLinearMap+(LinearMap.id : E 3 →ₗ[ℝ] E 3))) = 1 ∧
      LinearMap.ker (S.toLinearMap+(LinearMap.id : E 3 →ₗ[ℝ] E 3)) ⊓ LinearMap.ker (spatialNormalFunctional n) = ⊥ := by
  let A := LinearMap.ker (S.toLinearMap+(LinearMap.id : E 3 →ₗ[ℝ] E 3))
  let N := spatialNormalFunctional n
  have hMatS : Matrix.det (spatialIsometryMatrix S) = -1 :=
    (LinearMap.det_toMatrix homRotationStdBasis S.toLinearMap).trans hS
  have hzero : LinearMap.det (S.toLinearMap+(LinearMap.id : E 3 →ₗ[ℝ] E 3)) = 0 := by
    rw [← LinearMap.det_toMatrix homRotationStdBasis,map_add,LinearMap.toMatrix_id]
    simpa [spatialIsometryMatrix,add_comm] using
      reversing_matrix_add_one_det_zero _ (spatialIsometryMatrix_orthogonal S) hMatS
  have hAne : A ≠ ⊥ := LinearMap.det_eq_zero_iff_ker_ne_bot.mp hzero
  have hPert : LinearMap.det (spatialAxisPerturbation S n) ≠ 0 := by
    rw [← LinearMap.det_toMatrix homRotationStdBasis,spatialAxisPerturbation_toMatrix]
    exact hM
  have hKpert : LinearMap.ker (spatialAxisPerturbation S n) = ⊥ := by
    by_contra hn
    exact hPert (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hn)
  have hinj : Function.Injective (spatialAxisPerturbation S n) := LinearMap.ker_eq_bot.mp hKpert
  have hInf : A ⊓ LinearMap.ker N = ⊥ := by
    apply le_antisymm _ bot_le
    intro v hv
    change v = 0
    have hA : (S.toLinearMap+(LinearMap.id : E 3 →ₗ[ℝ] E 3)) v = 0 := hv.1
    have hN : N v = 0 := hv.2
    apply hinj
    rw [map_zero]
    change (S.toLinearMap+(LinearMap.id : E 3 →ₗ[ℝ] E 3)) v+N v • n = 0
    rw [hA,hN,zero_smul,add_zero]
  have hNinj : Function.Injective (N.domRestrict A) := by
    intro x y hxy
    apply Subtype.ext
    have hz : (x:E 3)-(y:E 3) ∈ A ⊓ LinearMap.ker N := by
      refine ⟨A.sub_mem x.property y.property,?_⟩
      change N ((x:E 3)-(y:E 3)) = 0
      rw [map_sub]
      change N x-N y = 0
      exact sub_eq_zero.mpr hxy
    rw [hInf] at hz
    exact sub_eq_zero.mp (by simpa using hz)
  have hupper : Module.finrank ℝ A ≤ 1 := by
    have h := LinearMap.finrank_le_finrank_of_injective hNinj
    simpa using h
  have hlower : 1 ≤ Module.finrank ℝ A := Submodule.one_le_finrank_iff.mpr hAne
  refine ⟨?_,hInf⟩
  change Module.finrank ℝ A = 1
  omega

end DistinctDistances.TrackC
