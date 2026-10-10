import DistinctDistances.TrackC.MotionGeometry

namespace DistinctDistances.TrackC

/-- Unit normals of an affine plane are unique up to simultaneous sign,
motions.tex:352–357; input to motion and section distinctness. -/
theorem unit_normal_planes_eq (a b : E 3) (ω ω' : ℝ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hplane : {w : E 3 | inner ℝ w a = ω} = {w : E 3 | inner ℝ w b = ω'}) :
    (a = b ∧ ω = ω') ∨ (a = -b ∧ ω = -ω') := by
  let t : ℝ := inner ℝ b a
  let v : E 3 := b - t • a
  have hva : inner ℝ v a = 0 := by
    simp [v, t, inner_sub_left, inner_smul_left, inner_self_eq_norm_sq_to_K, ha]
  have hbaseA : inner ℝ (ω • a) a = ω := by
    simp [inner_smul_left, inner_self_eq_norm_sq_to_K, ha]
  have hbaseB : inner ℝ (ω • a) b = ω' := by
    have hmA : ω • a ∈ {w : E 3 | inner ℝ w a = ω} := hbaseA
    have hmB : ω • a ∈ {w : E 3 | inner ℝ w b = ω'} := by
      rw [← hplane]
      exact hmA
    exact hmB
  have hshiftA : inner ℝ (ω • a + v) a = ω := by
    simp [inner_add_left, inner_smul_left, inner_self_eq_norm_sq_to_K, ha, hva]
  have hshiftB : inner ℝ (ω • a + v) b = ω' := by
    have hmA : ω • a + v ∈ {w : E 3 | inner ℝ w a = ω} := hshiftA
    have hmB : ω • a + v ∈ {w : E 3 | inner ℝ w b = ω'} := by
      rw [← hplane]
      exact hmA
    exact hmB
  have hvb : inner ℝ v b = 0 := by
    have hshift := hshiftB
    rw [inner_add_left, inner_smul_left] at hshift
    have hbase := hbaseB
    rw [inner_smul_left] at hbase
    linarith
  have hvv : inner ℝ v v = 0 := by
    calc
      inner ℝ v v = inner ℝ v (b - t • a) := by rfl
      _ = inner ℝ v b - inner ℝ v (t • a) := by rw [inner_sub_right]
      _ = 0 := by rw [inner_smul_right, hvb, hva]; ring
  have hvzero : v = 0 := inner_self_eq_zero.mp hvv
  have hba : b = t • a := by
    have h : b - t • a = 0 := by simpa [v] using hvzero
    exact sub_eq_zero.mp h
  have hbb : inner ℝ b b = 1 := by
    simpa [inner_self_eq_norm_sq_to_K, hb]
  have hscaled : inner ℝ (t • a) (t • a) = 1 := by
    simpa [hba] using hbb
  have htsq : t^2 = 1 := by
    have h := hscaled
    rw [inner_smul_left, inner_smul_right] at h
    rw [inner_self_eq_norm_sq_to_K] at h
    simp [ha] at h
    nlinarith
  have htsign : t = 1 ∨ t = -1 := by
    rcases lt_trichotomy t 0 with ht | ht | ht
    · right
      nlinarith
    · exfalso
      rw [ht] at htsq
      norm_num at htsq
    · left
      nlinarith
  have hω : ω * t = ω' := by
    have h := hbaseB
    simp [hba, inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K, ha] at h
    nlinarith
  rcases htsign with ht | ht
  · left
    exact ⟨by simpa [ht] using hba.symm, by simpa [ht] using hω⟩
  · right
    have hab : a = -b := by
      calc
        a = -(t • a) := by simp [ht]
        _ = -b := congrArg Neg.neg hba.symm
    have hω' : ω = -ω' := by
      have h := hω
      rw [ht] at h
      linarith
    exact ⟨hab, hω'⟩

end DistinctDistances.TrackC
