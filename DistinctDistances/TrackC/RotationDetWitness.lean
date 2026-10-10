import DistinctDistances.TrackC.Basic

open scoped BigOperators
open Classical

noncomputable section

namespace DistinctDistances.TrackC

def coordinateEvenSigns (j : Fin 4) : Matrix (Fin 3) (Fin 3) ℝ :=
  match j.val with
  | 0 => !![1,0,0;0,1,0;0,0,1]
  | 1 => !![1,0,0;0,-1,0;0,0,-1]
  | 2 => !![-1,0,0;0,1,0;0,0,-1]
  | _ => !![-1,0,0;0,-1,0;0,0,1]

def normalOuterMatrix (v : E 3) : Matrix (Fin 3) (Fin 3) ℝ := fun i j => v i*v j

set_option maxHeartbeats 2000000 in
theorem coordinate_rotation_det_sum (S : Matrix (Fin 3) (Fin 3) ℝ) (v : E 3) :
    (∑ j : Fin 4,Matrix.det (1+coordinateEvenSigns j*S+normalOuterMatrix v)) =
      4*(1+Matrix.det S+∑ i : Fin 3,v i^2) := by
  simp [coordinateEvenSigns,normalOuterMatrix,Matrix.det_fin_three,Matrix.mul_apply,
    Fin.sum_univ_four,Fin.sum_univ_three,Matrix.one_apply]
  ring

theorem coordinate_rotation_det_witness (S : Matrix (Fin 3) (Fin 3) ℝ)
    (hS : Matrix.det S = -1) (v : E 3) (hv : v ≠ 0) :
    ∃ j : Fin 4,Matrix.det (1+coordinateEvenSigns j*S+normalOuterMatrix v) ≠ 0 := by
  have hsumpos : (0:ℝ) < ∑ i : Fin 3,v i^2 := by
    have hi : ∃ i : Fin 3,v i ≠ 0 := by
      by_contra! h
      apply hv
      ext i
      exact h i
    obtain ⟨i,hi⟩ := hi
    have hsq : 0 < v i^2 := sq_pos_of_ne_zero hi
    exact hsq.trans_le (Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i))
  by_contra! hzero
  have h := coordinate_rotation_det_sum S v
  simp only [hzero,Finset.sum_const_zero,hS] at h
  linarith

end DistinctDistances.TrackC
