import DistinctDistances.TrackC.MotionCoordinates

namespace DistinctDistances.TrackC

theorem motionConjugate_linear (R : E 3 ≃ₗᵢ[ℝ] E 3) (g : Motion 3) :
    (motionConjugate R g).toAffineEquiv.linear.toLinearMap =
      R.toLinearMap.comp (g.toAffineEquiv.linear.toLinearMap.comp R.symm.toLinearMap) := rfl

theorem proper_rotation_symm (R : E 3 ≃ₗᵢ[ℝ] E 3) (hR : LinearMap.det R.toLinearMap = 1) :
    LinearMap.det R.symm.toLinearMap = 1 := by
  have heq : R.toLinearMap.comp R.symm.toLinearMap = LinearMap.id := by
    ext x
    simp
  have h := congrArg LinearMap.det heq
  rw [LinearMap.det_comp,hR,LinearMap.det_id,one_mul] at h
  exact h

theorem reverse_motion_conjugate (R : E 3 ≃ₗᵢ[ℝ] E 3)
    (hR : LinearMap.det R.toLinearMap = 1) (g : Motion 3) (hg : reverseMotion g) :
    reverseMotion (motionConjugate R g) := by
  unfold reverseMotion at hg ⊢
  rw [motionConjugate_linear,LinearMap.det_comp,LinearMap.det_comp,hR,hg,
    proper_rotation_symm R hR]
  norm_num

theorem axis_motionConjugate (R : E 3 ≃ₗᵢ[ℝ] E 3) (g : Motion 3) :
    axis (motionConjugate R g) = (axis g).map R.toLinearMap := by
  ext x
  constructor
  · intro hx
    change R (g.linearIsometryEquiv (R.symm x))+x = 0 at hx
    have hy : R.symm x ∈ axis g := by
      change g.linearIsometryEquiv (R.symm x)+R.symm x = 0
      apply R.injective
      simpa only [map_add,map_zero,R.apply_symm_apply] using hx
    exact Submodule.mem_map.mpr ⟨R.symm x,hy,R.apply_symm_apply x⟩
  · rintro ⟨y,hy,rfl⟩
    change g.linearIsometryEquiv y+y = 0 at hy
    change R (g.linearIsometryEquiv (R.symm (R y)))+R y = 0
    rw [R.symm_apply_apply,← map_add,hy,map_zero]

end DistinctDistances.TrackC
