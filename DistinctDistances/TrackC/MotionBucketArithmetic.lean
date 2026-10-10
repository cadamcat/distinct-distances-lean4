import DistinctDistances.TrackC.Basic

namespace DistinctDistances.TrackC

noncomputable section

/-- A fixed lower bound on t ensures every local and ambient-line richness condition. -/
theorem motion_bucket_thresholds (η β C : ℝ) (hη : 0 < η) (hβ : 0 < β) (hC : 0 < C) :
    ∃ T : ℝ,4 < T ∧ ∀ t : ℝ,T ≤ t →
      C ≤ (β/4)*t^((9:ℝ)/14) ∧ 1 ≤ η*β*t^((3:ℝ)/7) ∧ 16 ≤ η*t := by
  let a := (4*C/β)^((14:ℝ)/9)
  let b := (1/(η*β))^((7:ℝ)/3)
  let T := 5+a+b+16/η
  have ha : 0 ≤ a := by dsimp [a];positivity
  have hb : 0 ≤ b := by dsimp [b];positivity
  have hT : 4 < T := by dsimp [T];nlinarith [div_pos (by norm_num : (0:ℝ) < 16) hη]
  refine ⟨T,hT,?_⟩
  intro t ht
  have htpos : 0 < t := by linarith
  have hat : a ≤ t := by dsimp [T] at ht;nlinarith [div_pos (by norm_num : (0:ℝ) < 16) hη]
  have hbt : b ≤ t := by dsimp [T] at ht;nlinarith [div_pos (by norm_num : (0:ℝ) < 16) hη]
  have hdt : 16/η ≤ t := by dsimp [T] at ht;linarith
  have hpa : a^((9:ℝ)/14) = 4*C/β := by
    dsimp [a]
    rw [← Real.rpow_mul (by positivity : 0 ≤ 4*C/β)]
    norm_num
  have hpb : b^((3:ℝ)/7) = 1/(η*β) := by
    dsimp [b]
    rw [← Real.rpow_mul (by positivity : 0 ≤ 1/(η*β))]
    norm_num
  refine ⟨?_,?_,?_⟩
  · have hp := Real.rpow_le_rpow ha hat (by norm_num : (0:ℝ) ≤ 9/14)
    rw [hpa] at hp
    have hm := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ β/4)
    have heq : (β/4)*(4*C/β) = C := by field_simp <;> ring
    rwa [heq] at hm
  · have hp := Real.rpow_le_rpow hb hbt (by norm_num : (0:ℝ) ≤ 3/7)
    rw [hpb] at hp
    have hm := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ η*β)
    have heq : (η*β)*(1/(η*β)) = 1 := by field_simp <;> ring
    rwa [heq] at hm
  · have hm := (div_le_iff₀ hη).mp hdt
    simpa [mul_comm] using hm

/-- Threshold times the number of overlap pairs is a fixed fraction of global richness. -/
theorem motion_region_threshold_identity (t A β : ℝ) (ht : 0 < t) :
    t^((15:ℝ)/14)*(β*A*t^((-1:ℝ)/14)) = β*(t*A) := by
  have hp : t^((15:ℝ)/14)*t^((-1:ℝ)/14) = t := by
    rw [← Real.rpow_add ht]
    norm_num
  calc
    _ = β*A*(t^((15:ℝ)/14)*t^((-1:ℝ)/14)) := by ring
    _ = _ := by rw [hp];ring

/-- The non-line contribution has the power-saving exponent consumed by the global bucket. -/
theorem motion_nonline_scale_identity (N t β : ℝ) (hN : 0 < N) (ht : 0 < t) (hβ : 0 < β) :
    let A := N^((2:ℝ)/3)
    let r := t^((15:ℝ)/14)
    let m := 8*N/r
    let k := t*A
    let b := β*A*t^((-1:ℝ)/14)
    k*r^2*m^3/Real.sqrt b = (512/Real.sqrt β)*(N^4/A*t^((-1:ℝ)/28)) := by
  let A := N^((2:ℝ)/3)
  let r := t^((15:ℝ)/14)
  let m := 8*N/r
  let k := t*A
  let b := β*A*t^((-1:ℝ)/14)
  have hA : 0 < A := by dsimp [A];positivity
  have hr : 0 < r := by dsimp [r];positivity
  have hb : 0 < b := by dsimp [b];positivity
  have hsqrtA : Real.sqrt A = N^((1:ℝ)/3) := by
    dsimp [A]
    rw [Real.sqrt_eq_rpow,← Real.rpow_mul hN.le]
    congr 1 <;> norm_num
  have hsqrtT : Real.sqrt (t^((-1:ℝ)/14)) = t^((-1:ℝ)/28) := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_mul ht.le]
    congr 1 <;> norm_num
  have hsqrtB : Real.sqrt b = Real.sqrt β*Real.sqrt A*t^((-1:ℝ)/28) := by
    dsimp [b]
    rw [Real.sqrt_mul (by positivity : 0 ≤ β*A),Real.sqrt_mul hβ.le,hsqrtT]
  have hNratio : N^3*A/Real.sqrt A = N^4/A := by
    have hleft : N^3*A/Real.sqrt A = N^((10:ℝ)/3) := by
      rw [hsqrtA]
      dsimp [A]
      rw [← Real.rpow_natCast,← Real.rpow_add hN,← Real.rpow_sub hN]
      congr 1 <;> norm_num
    have hright : N^4/A = N^((10:ℝ)/3) := by
      dsimp [A]
      rw [← Real.rpow_natCast,← Real.rpow_sub hN]
      congr 1 <;> norm_num
    exact hleft.trans hright.symm
  have hTratio : t/(r*t^((-1:ℝ)/28)) = t^((-1:ℝ)/28) := by
    have hp : r*t^((-1:ℝ)/28) = t^((29:ℝ)/28) := by
      dsimp [r]
      rw [← Real.rpow_add ht]
      congr 1 <;> norm_num
    rw [hp]
    calc
      _ = t^(1:ℝ)/t^((29:ℝ)/28) := by simp
      _ = t^((1:ℝ)-(29:ℝ)/28) := (Real.rpow_sub ht _ _).symm
      _ = _ := by congr 1 <;> norm_num
  calc
    _ = (512/Real.sqrt β)*(N^3*A/Real.sqrt A)*(t/(r*t^((-1:ℝ)/28))) := by
      change k*r^2*m^3/Real.sqrt b = _
      rw [hsqrtB]
      dsimp [k,m]
      field_simp <;> ring
    _ = _ := by rw [hNratio,hTratio];ring

end
end DistinctDistances.TrackC
