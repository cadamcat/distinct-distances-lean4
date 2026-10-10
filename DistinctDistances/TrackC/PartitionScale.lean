import DistinctDistances.TrackC.Basic

namespace DistinctDistances.TrackC

/-- Enough binary levels to achieve r^d sign classes. -/
def partitionLevelCount (d r : ℕ) : ℕ := Nat.log 2 (r^d) + 1

theorem partitionLevelCount_bounds (d r : ℕ) (hd : 1 ≤ d) (hr : 1 ≤ r) :
    r^d < 2^(partitionLevelCount d r) ∧
      2^(partitionLevelCount d r) ≤ 2*r^d ∧
      2^(partitionLevelCount d r / d) ≤ 2*r := by
  have hpow0 : r^d ≠ 0 := pow_ne_zero _ (by omega)
  have hlower : r^d < 2^(partitionLevelCount d r) :=
    Nat.lt_pow_succ_log_self (by norm_num) _
  have hupper : 2^(partitionLevelCount d r) ≤ 2*r^d := by
    unfold partitionLevelCount
    rw [pow_succ]
    nlinarith [Nat.pow_log_le_self 2 hpow0]
  refine ⟨hlower, hupper, ?_⟩
  have hquot : (partitionLevelCount d r / d)*d ≤ partitionLevelCount d r :=
    Nat.div_mul_le_self _ _
  have hsmall : (2^(partitionLevelCount d r / d))^d ≤ 2^(partitionLevelCount d r) := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) hquot
  have htwo : 2 ≤ (2 : ℕ)^d := by
    have := Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hd
    simpa using this
  have hlarge : 2*r^d ≤ (2*r)^d := by
    rw [mul_pow]
    exact Nat.mul_le_mul_right _ htwo
  by_contra! hbad
  have hstrict : (2*r)^d < (2^(partitionLevelCount d r / d))^d :=
    Nat.pow_lt_pow_left hbad (by omega)
  omega

end DistinctDistances.TrackC
