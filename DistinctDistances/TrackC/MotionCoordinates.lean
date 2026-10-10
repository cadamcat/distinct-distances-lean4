import DistinctDistances.TrackC.MotionGeometry

open scoped BigOperators
open Classical

noncomputable section

namespace DistinctDistances.TrackC

def packSix (w c : E 3) : E 6 := WithLp.toLp 2 ![w 0,w 1,w 2,c 0,c 1,c 2]

@[simp] theorem wCoord_packSix (w c : E 3) : wCoord (packSix w c) = w := by
  ext i
  fin_cases i <;> simp [wCoord, packSix]

@[simp] theorem cCoord_packSix (w c : E 3) : cCoord (packSix w c) = c := by
  ext i
  fin_cases i <;> simp [cCoord, packSix]

@[simp] theorem wCoord_add (z z' : E 6) : wCoord (z + z') = wCoord z + wCoord z' := by
  ext i
  simp [wCoord]

@[simp] theorem cCoord_add (z z' : E 6) : cCoord (z + z') = cCoord z + cCoord z' := by
  ext i
  simp [cCoord]

@[simp] theorem wCoord_smul (a : ℝ) (z : E 6) : wCoord (a • z) = a • wCoord z := by
  ext i
  simp [wCoord]

@[simp] theorem cCoord_smul (a : ℝ) (z : E 6) : cCoord (a • z) = a • cCoord z := by
  ext i
  simp [cCoord]

theorem six_ext {z z' : E 6} (hw : wCoord z = wCoord z')
    (hc : cCoord z = cCoord z') : z = z' := by
  ext i
  fin_cases i
  all_goals first
    | exact congrArg (fun w : E 3 => w 0) hw
    | exact congrArg (fun w : E 3 => w 1) hw
    | exact congrArg (fun w : E 3 => w 2) hw
    | exact congrArg (fun c : E 3 => c 0) hc
    | exact congrArg (fun c : E 3 => c 1) hc
    | exact congrArg (fun c : E 3 => c 2) hc

@[simp] theorem packSix_coords (z : E 6) : packSix (wCoord z) (cCoord z) = z := by
  apply six_ext <;> simp

def sixRotate (R : E 3 ≃ₗᵢ[ℝ] E 3) : E 6 ≃ₗ[ℝ] E 6 where
  toFun z := packSix (R (wCoord z)) (R (cCoord z))
  invFun z := packSix (R.symm (wCoord z)) (R.symm (cCoord z))
  left_inv z := by simp
  right_inv z := by simp
  map_add' z z' := by
    apply six_ext
    · simp only [wCoord_packSix, wCoord_add, map_add]
    · simp only [cCoord_packSix, cCoord_add, map_add]
  map_smul' a z := by
    apply six_ext
    · simp only [wCoord_packSix, wCoord_smul, map_smul, RingHom.id_apply]
    · simp only [cCoord_packSix, cCoord_smul, map_smul, RingHom.id_apply]

@[simp] theorem wCoord_sixRotate (R : E 3 ≃ₗᵢ[ℝ] E 3) (z : E 6) :
    wCoord (sixRotate R z) = R (wCoord z) := wCoord_packSix _ _

@[simp] theorem cCoord_sixRotate (R : E 3 ≃ₗᵢ[ℝ] E 3) (z : E 6) :
    cCoord (sixRotate R z) = R (cCoord z) := cCoord_packSix _ _

@[simp] theorem sixRotate_symm (R : E 3 ≃ₗᵢ[ℝ] E 3) :
    (sixRotate R).symm = sixRotate R.symm := by
  ext z
  rfl

theorem sixRotate_quadratic (R : E 3 ≃ₗᵢ[ℝ] E 3) (z : E 6) :
    splitQuadratic (sixRotate R z) = splitQuadratic z := by
  have h := R.inner_map_map (wCoord z) (cCoord z)
  simpa only [splitQuadratic, wCoord_sixRotate, cCoord_sixRotate,
    PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mul_comm] using h

def motionConjugate (R : E 3 ≃ₗᵢ[ℝ] E 3) (g : Motion 3) : Motion 3 :=
  (R.symm.toAffineIsometryEquiv.trans g).trans R.toAffineIsometryEquiv

@[simp] theorem motionConjugate_apply (R : E 3 ≃ₗᵢ[ℝ] E 3) (g : Motion 3) (x : E 3) :
    motionConjugate R g x = R (g (R.symm x)) := rfl

@[simp] theorem motionConjugate_symm (R : E 3 ≃ₗᵢ[ℝ] E 3) (g : Motion 3) :
    motionConjugate R.symm (motionConjugate R g) = g := by
  ext x : 1
  simp

def canonicalPhysicalPoint (g : Motion 3) (x : E 3) : E 3 :=
  WithLp.toLp 2 ![((x + g x) 0) / 2, ((x + g x) 1) / 2, ((x - g x) 2) / 2]

end DistinctDistances.TrackC
