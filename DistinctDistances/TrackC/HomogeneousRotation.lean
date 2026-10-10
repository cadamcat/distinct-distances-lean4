import DistinctDistances.TrackC.Basic

open scoped BigOperators
open Classical

noncomputable section

namespace DistinctDistances.TrackC

def homRotationDenominator (a : ℝ) (w : E 3) : ℝ := a^2+w 0^2+w 1^2+w 2^2

theorem homRotationDenominator_nonneg (a : ℝ) (w : E 3) : 0 ≤ homRotationDenominator a w := by
  dsimp [homRotationDenominator]
  positivity

def homRotationNumerator (a : ℝ) (w : E 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![a^2+w 0^2-w 1^2-w 2^2, 2*(w 0*w 1+a*w 2), 2*(w 0*w 2-a*w 1);
     2*(w 0*w 1-a*w 2), a^2-w 0^2+w 1^2-w 2^2, 2*(w 1*w 2+a*w 0);
     2*(w 0*w 2+a*w 1), 2*(w 1*w 2-a*w 0), a^2-w 0^2-w 1^2+w 2^2]

def homRotationMatrix (a : ℝ) (w : E 3) : Matrix (Fin 3) (Fin 3) ℝ := (homRotationDenominator a w)⁻¹ • homRotationNumerator a w

def homRationalRotationLinear (a : ℝ) (w : E 3) : E 3 →ₗ[ℝ] E 3 where
  toFun v := WithLp.toLp 2 (fun i => ∑ j : Fin 3,homRotationMatrix a w i j*v j)
  map_add' v u := by ext i;simp [mul_add,Finset.sum_add_distrib]
  map_smul' a v := by ext i;simp [Finset.mul_sum,mul_left_comm,mul_assoc]

set_option maxHeartbeats 2000000 in
theorem homRationalRotation_norm_sq (a : ℝ) (w v : E 3) (hd : 0 < homRotationDenominator a w) : ‖homRationalRotationLinear a w v‖^2 = ‖v‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ),PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ)]
  simp [homRationalRotationLinear,homRotationMatrix,homRotationNumerator,Fin.sum_univ_three,Real.norm_eq_abs,sq_abs]
  field_simp [ne_of_gt hd]
  dsimp [homRotationDenominator]
  ring

def homRationalRotationIsometry (a : ℝ) (w : E 3) (hd : 0 < homRotationDenominator a w) : E 3 →ₗᵢ[ℝ] E 3 :=
  { homRationalRotationLinear a w with
    norm_map' := by intro v;nlinarith [homRationalRotation_norm_sq a w v hd,norm_nonneg (homRationalRotationLinear a w v),norm_nonneg v] }

def homRationalRotation (a : ℝ) (w : E 3) (hd : 0 < homRotationDenominator a w) : E 3 ≃ₗᵢ[ℝ] E 3 :=
  LinearIsometryEquiv.ofSurjective (homRationalRotationIsometry a w hd)
    (LinearMap.surjective_of_injective (homRationalRotationIsometry a w hd).injective)

theorem homRationalRotation_apply (a : ℝ) (w v : E 3) (hd : 0 < homRotationDenominator a w) : homRationalRotation a w hd v = homRationalRotationLinear a w v := rfl

theorem homRotationNumerator_det (a : ℝ) (w : E 3) : Matrix.det (homRotationNumerator a w) = homRotationDenominator a w^3 := by
  simp [homRotationNumerator,Matrix.det_fin_three,homRotationDenominator]
  ring

theorem homRotationMatrix_det (a : ℝ) (w : E 3) (hd : 0 < homRotationDenominator a w) : Matrix.det (homRotationMatrix a w) = 1 := by
  rw [homRotationMatrix,Matrix.det_smul,homRotationNumerator_det]
  simp only [Fintype.card_fin]
  field_simp [ne_of_gt hd]

def homRotationStdBasis : Module.Basis (Fin 3) ℝ (E 3) := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis

theorem homRationalRotation_toMatrix (a : ℝ) (w : E 3) :
    LinearMap.toMatrix homRotationStdBasis homRotationStdBasis (homRationalRotationLinear a w) = homRotationMatrix a w := by
  ext i j
  simp [LinearMap.toMatrix_apply,homRotationStdBasis,EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply,homRationalRotationLinear]

theorem homRationalRotation_det (a : ℝ) (w : E 3) (hd : 0 < homRotationDenominator a w) : LinearMap.det (homRationalRotation a w hd).toLinearEquiv.toLinearMap = 1 := by
  change LinearMap.det (homRationalRotationLinear a w) = 1
  rw [← LinearMap.det_toMatrix homRotationStdBasis,homRationalRotation_toMatrix,homRotationMatrix_det a w hd]

end DistinctDistances.TrackC
