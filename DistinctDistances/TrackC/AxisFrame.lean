import DistinctDistances.TrackC.MotionGeometry

namespace DistinctDistances.TrackC

private theorem spatial_isometry_det_sign (R : E 3 ≃ₗᵢ[ℝ] E 3) :
    LinearMap.det R.toLinearMap = 1 ∨ LinearMap.det R.toLinearMap = -1 := by
  have horth := congrArg Matrix.det (spatialIsometryMatrix_orthogonal R)
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at horth
  have hdet := LinearMap.det_toMatrix homRotationStdBasis R.toLinearMap
  have hdet' : Matrix.det (spatialIsometryMatrix R) = LinearMap.det R.toLinearMap := by
    simp [spatialIsometryMatrix, hdet]
  have hmatSq : (Matrix.det (spatialIsometryMatrix R))^2 = 1 := by
    simpa [pow_two] using horth
  have hsquare : (LinearMap.det R.toLinearMap)^2 = 1 := by
    rw [← hdet']
    exact hmatSq
  have hfactor : (LinearMap.det R.toLinearMap - 1) *
      (LinearMap.det R.toLinearMap + 1) = 0 := by nlinarith [hsquare]
  rcases mul_eq_zero.mp hfactor with h | h
  · left
    linarith
  · right
    linarith

/-- A proper axis frame, motions.tex:298–300; input to normalized_motion_flats. -/
theorem spatial_axis_frame (A : Submodule ℝ (E 3)) (hA : Module.finrank ℝ A = 1) :
    ∃ R : E 3 ≃ₗᵢ[ℝ] E 3,
      LinearMap.det R.toLinearMap = 1 ∧
      A.map R.toLinearMap = Submodule.span ℝ {EuclideanSpace.single (2 : Fin 3) (1 : ℝ)} := by
  obtain ⟨v, hvA, hv0⟩ := A.ne_bot_iff.mp (by
    intro hbot
    rw [hbot, finrank_bot] at hA
    norm_num at hA)
  have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  let n : E 3 := ‖v‖⁻¹ • v
  have hn : ‖n‖ = 1 := by simp [n, norm_smul, hpos.ne']
  have hn0 : n ≠ 0 := by
    intro hn0
    rw [hn0] at hn
    norm_num at hn
  have hnA : n ∈ A := by
    dsimp [n]
    exact A.smul_mem _ hvA
  have hspan_le : Submodule.span ℝ ({n} : Set (E 3)) ≤ A :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hnA)
  have hspanA : Submodule.span ℝ ({n} : Set (E 3)) = A :=
    Submodule.eq_of_le_of_finrank_eq hspan_le (by rw [finrank_span_singleton hn0, hA])
  have horth : Orthonormal ℝ (({2} : Set (Fin 3)).domRestrict (fun _ => n)) := by
    rw [orthonormal_subsingleton_iff]
    intro i
    exact hn
  obtain ⟨b, hb⟩ := horth.exists_orthonormalBasis_extension_of_card_eq
    (show Module.finrank ℝ (E 3) = Fintype.card (Fin 3) by simp [E])
  let R₀ : E 3 ≃ₗᵢ[ℝ] E 3 := b.repr
  let e : E 3 := EuclideanSpace.single (2 : Fin 3) (1 : ℝ)
  have hR₀n : R₀ n = e := by
    dsimp [R₀, e]
    have hx : n = b.repr.symm (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) := by
      rw [b.repr_symm_single, hb 2 (by simp)]
    rw [hx, b.repr.apply_symm_apply]
  let bStd : OrthonormalBasis (Fin 3) ℝ (E 3) := EuclideanSpace.basisFun (Fin 3) ℝ
  let σ : Fin 3 ≃ Fin 3 := Equiv.swap 0 1
  let P : E 3 ≃ₗᵢ[ℝ] E 3 := bStd.equiv bStd σ
  have hPe : P e = e := by
    have he : bStd 2 = e := by simp [bStd, e]
    rw [← he]
    change (bStd.equiv bStd σ) (bStd 2) = bStd 2
    rw [OrthonormalBasis.equiv_apply_basis]
    have hσ : σ (2 : Fin 3) = 2 := by decide
    rw [hσ]
  have hdetP : LinearMap.det P.toLinearMap = -1 := by
    rw [← LinearMap.det_toMatrix homRotationStdBasis P.toLinearMap]
    have hmat : LinearMap.toMatrix homRotationStdBasis homRotationStdBasis P.toLinearMap =
        !![0, 1, 0; 1, 0, 0; 0, 0, 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [P, bStd, σ, homRotationStdBasis, LinearMap.toMatrix_apply,
          OrthonormalBasis.equiv_apply, EuclideanSpace.basisFun_repr,
          EuclideanSpace.basisFun_apply, Equiv.swap_apply_def]
    rw [hmat]
    norm_num [Matrix.det_fin_three]
  let R : E 3 ≃ₗᵢ[ℝ] E 3 :=
    if LinearMap.det R₀.toLinearMap = 1 then R₀ else R₀.trans P
  have hRn : R n = e := by
    by_cases hR₀det : LinearMap.det R₀.toLinearMap = 1
    · simp [R, hR₀det, hR₀n]
    · simp [R, hR₀det, hR₀n, hPe]
  have hRdet : LinearMap.det R.toLinearMap = 1 := by
    by_cases hR₀det : LinearMap.det R₀.toLinearMap = 1
    · simp [R, hR₀det]
    · have hR₀neg := (spatial_isometry_det_sign R₀).resolve_left hR₀det
      have hcomp : LinearMap.det (R₀.trans P).toLinearMap = 1 := by
        change LinearMap.det (P.toLinearMap.comp R₀.toLinearMap) = 1
        rw [LinearMap.det_comp, hdetP, hR₀neg]
        norm_num
      simpa [R, hR₀det] using hcomp
  refine ⟨R, hRdet, ?_⟩
  rw [← hspanA, Submodule.map_span]
  simp [hRn, e]

end DistinctDistances.TrackC
