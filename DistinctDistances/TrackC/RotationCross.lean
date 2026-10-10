import DistinctDistances.TrackC.MotionCoordinates

namespace DistinctDistances.TrackC

private theorem cross3_inner_det (x y z : E 3) :
    inner ℝ (cross3 x y) z = Matrix.det ![ (fun i => x i), (fun i => y i), (fun i => z i) ] := by
  have hcross : (fun i => cross3 x y i) =
      crossProduct (fun i => x i) (fun i => y i) := by
    funext i
    fin_cases i <;> simp [cross3, crossProduct]
  calc
    inner ℝ (cross3 x y) z =
        dotProduct (fun i => z i) (fun i => cross3 x y i) := by
      simp [PiLp.inner_apply, RCLike.inner_apply, dotProduct]
    _ = dotProduct (fun i => z i) (crossProduct (fun i => x i) (fun i => y i)) := by
      rw [hcross]
    _ = dotProduct (fun i => x i) (crossProduct (fun i => y i) (fun i => z i)) :=
      triple_product_permutation _ _ _
    _ = Matrix.det ![ (fun i => x i), (fun i => y i), (fun i => z i) ] :=
      triple_product_eq_det _ _ _

/-- Proper rotations preserve the physical cross product, motions.tex:342–346. -/
theorem cross3_rotation (R : E 3 ≃ₗᵢ[ℝ] E 3) (hR : LinearMap.det R.toLinearMap = 1)
    (u v : E 3) : R (cross3 u v) = cross3 (R u) (R v) := by
  let M : Matrix (Fin 3) (Fin 3) ℝ := spatialIsometryMatrix R
  let rows (x y z : E 3) : Matrix (Fin 3) (Fin 3) ℝ :=
    ![ (fun i => x i), (fun i => y i), (fun i => z i) ]
  have hMdet : Matrix.det M = 1 := by
    dsimp [M, spatialIsometryMatrix]
    exact (LinearMap.det_toMatrix homRotationStdBasis R.toLinearMap).trans hR
  have hmat (i j : Fin 3) : M i j = (R (EuclideanSpace.single j (1 : ℝ))) i := by
    simp [M, spatialIsometryMatrix, LinearMap.toMatrix_apply, homRotationStdBasis,
      EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
  have hsum (x : E 3) : x = ∑ j : Fin 3, x j • EuclideanSpace.single j (1 : ℝ) := by
    ext i
    fin_cases i <;> simp [Fin.sum_univ_three]
  have hcoord (x : E 3) : (fun i => R x i) = Matrix.mulVec M (fun i => x i) := by
    funext i
    calc
      R x i = R (∑ j : Fin 3, x j • EuclideanSpace.single j (1 : ℝ)) i :=
        congrArg (fun y : E 3 => (R y) i) (hsum x)
      _ = (∑ j : Fin 3, x j • R (EuclideanSpace.single j (1 : ℝ))) i := by
        simp only [map_sum, map_smul]
      _ = ∑ j : Fin 3, (R (EuclideanSpace.single j (1 : ℝ))) i * x j := by
        simp [Pi.smul_apply, smul_eq_mul, mul_comm]
      _ = Matrix.mulVec M (fun j => x j) i := by
        simp [Matrix.mulVec, dotProduct, hmat, mul_comm]
  have hrows : ∀ x y z : E 3, rows (R x) (R y) (R z) = rows x y z * M.transpose := by
    intro x y z
    ext i j
    fin_cases i
    · change (R x) j = ∑ k : Fin 3, x k * M j k
      have h := congrArg (fun f : Fin 3 → ℝ => f j) (hcoord x)
      simpa [Matrix.mulVec, dotProduct, mul_comm] using h
    · change (R y) j = ∑ k : Fin 3, y k * M j k
      have h := congrArg (fun f : Fin 3 → ℝ => f j) (hcoord y)
      simpa [Matrix.mulVec, dotProduct, mul_comm] using h
    · change (R z) j = ∑ k : Fin 3, z k * M j k
      have h := congrArg (fun f : Fin 3 → ℝ => f j) (hcoord z)
      simpa [Matrix.mulVec, dotProduct, mul_comm] using h
  have hdetRows (x y z : E 3) : Matrix.det (rows (R x) (R y) (R z)) =
      Matrix.det (rows x y z) := by
    rw [hrows, Matrix.det_mul, Matrix.det_transpose, hMdet]
    simp
  have hpair (z : E 3) : inner ℝ (R (cross3 u v)) (R z) =
      inner ℝ (cross3 (R u) (R v)) (R z) := by
    calc
      inner ℝ (R (cross3 u v)) (R z) = inner ℝ (cross3 u v) z :=
        R.inner_map_map _ _
      _ = Matrix.det (rows u v z) := cross3_inner_det _ _ _
      _ = Matrix.det (rows (R u) (R v) (R z)) := (hdetRows u v z).symm
      _ = inner ℝ (cross3 (R u) (R v)) (R z) := (cross3_inner_det _ _ _).symm
  ext i
  have h := hpair (R.symm (EuclideanSpace.single i (1 : ℝ)))
  simpa [PiLp.inner_apply, RCLike.inner_apply, PiLp.single_apply] using h

end DistinctDistances.TrackC
