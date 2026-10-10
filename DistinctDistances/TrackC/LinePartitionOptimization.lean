import DistinctDistances.TrackC.PartitionCauchy

namespace DistinctDistances.TrackC

set_option maxHeartbeats 2000000 in
/-- Optimize the planar line partition scale, using the pair bound when m² ≤ n.
Consumer: `ci_st_planar`, classical-incidence.tex:48–73. -/
theorem line_partition_optimize (K n m I : ℝ) (hK : 0 < K)
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hpair : I ≤ n + m ^ 2)
    (hpart : ∀ r : ℕ, 1 ≤ r →
      I ≤ K * (n * Real.sqrt m / Real.sqrt r + m * r + n + (r : ℝ) ^ 2)) :
    I ≤ (8 * K + 2) * (n ^ ((2 : ℝ) / 3) * m ^ ((2 : ℝ) / 3) + n + m) := by
  let main : ℝ := n ^ ((2 : ℝ) / 3) * m ^ ((2 : ℝ) / 3)
  let target : ℝ := main + n + m
  let C : ℝ := 8 * K + 2
  have hnpos : 0 < n := by linarith
  have hmpos : 0 < m := by linarith
  have hmain : 0 ≤ main := by dsimp [main]; positivity
  have htarget : 0 ≤ target := by dsimp [target]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hCtwo : 2 ≤ C := by dsimp [C]; linarith
  have hCfour : 4 * K ≤ C := by dsimp [C]; linarith
  have hCfive : 5 * K ≤ C := by dsimp [C]; linarith
  by_cases hsmall : m ^ 2 ≤ n
  · have hI : I ≤ 2 * n := by linarith [hpair]
    have hnT : n ≤ target := by dsimp [target]; linarith
    calc
      I ≤ 2 * n := hI
      _ ≤ C * n := mul_le_mul_of_nonneg_right hCtwo hnpos.le
      _ ≤ C * target := mul_le_mul_of_nonneg_left hnT hC.le
  by_cases hlarge : n ^ 2 ≤ m
  · have hroot : n ≤ Real.sqrt m := by
      apply (Real.le_sqrt hnpos.le hmpos.le).2
      exact hlarge
    have hterm : n * Real.sqrt m ≤ m := by
      calc
        n * Real.sqrt m ≤ Real.sqrt m * Real.sqrt m :=
          mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg _)
        _ = m := Real.mul_self_sqrt hmpos.le
    have hnm : n ≤ m := by nlinarith [sq_nonneg (n - 1)]
    have hpartOne : I ≤ K * (n * Real.sqrt m + m + n + 1) := by
      simpa using hpart 1 (by norm_num)
    have hterms : n * Real.sqrt m + m + n + 1 ≤ 4 * m := by linarith
    have hmT : m ≤ target := by dsimp [target]; linarith
    calc
      I ≤ K * (n * Real.sqrt m + m + n + 1) := hpartOne
      _ ≤ K * (4 * m) := mul_le_mul_of_nonneg_left hterms hK.le
      _ = (4 * K) * m := by ring
      _ ≤ C * m := mul_le_mul_of_nonneg_right hCfour hmpos.le
      _ ≤ C * target := mul_le_mul_of_nonneg_left hmT hC.le
  have hnm2 : n ≤ m ^ 2 := (lt_of_not_ge hsmall).le
  have hmn2 : m < n ^ 2 := lt_of_not_ge hlarge
  let t : ℝ := n ^ ((2 : ℝ) / 3) / m ^ ((1 : ℝ) / 3)
  let rNat : ℕ := ⌊t⌋₊
  let r : ℝ := rNat
  have htpos : 0 < t := by dsimp [t]; positivity
  have ht3 : t ^ 3 = n ^ 2 / m := by
    dsimp [t]
    rw [div_pow, ← Real.rpow_natCast _ 3, ← Real.rpow_mul hnpos.le,
      ← Real.rpow_natCast _ 3, ← Real.rpow_mul hmpos.le]
    norm_num
  have htone : 1 < t := by
    have hratio : 1 < n ^ 2 / m := by
      apply (lt_div_iff₀ hmpos).2
      simpa only [one_mul] using hmn2
    have hpow : (1 : ℝ) ^ 3 < t ^ 3 := by simpa [ht3] using hratio
    exact (pow_lt_pow_iff_left₀ (n := 3) (by norm_num) htpos.le (by norm_num)).1 hpow
  have hrone : 1 ≤ rNat := (Nat.one_le_floor_iff t).2 htone.le
  have hrle : r ≤ t := Nat.floor_le htpos.le
  have hrpos : 0 < r := by dsimp [r]; exact_mod_cast (show 0 < rNat by omega)
  have hrhalf : t / 2 ≤ r := by
    by_cases ht2 : t < 2
    · have hrfloorlt : rNat < 2 := (Nat.floor_lt htpos.le).2 ht2
      have hreq : rNat = 1 := by omega
      dsimp [r]
      rw [hreq]
      linarith
    · have ht2' : 2 ≤ t := le_of_not_gt ht2
      have htfloor := Nat.lt_floor_add_one t
      dsimp [r, rNat]
      linarith
  have hmSplit : m ^ ((1 : ℝ) / 3) * m ^ ((2 : ℝ) / 3) = m := by
    rw [← Real.rpow_add hmpos]
    norm_num
  have hmDiv : m / m ^ ((1 : ℝ) / 3) = m ^ ((2 : ℝ) / 3) := by
    apply (div_eq_iff (Real.rpow_pos_of_pos hmpos ((1 : ℝ) / 3)).ne').2
    simpa [mul_comm] using hmSplit.symm
  have hMainEq : m * t = main := by
    dsimp [t, main]
    calc
      m * (n ^ ((2 : ℝ) / 3) / m ^ ((1 : ℝ) / 3)) =
          n ^ ((2 : ℝ) / 3) * (m / m ^ ((1 : ℝ) / 3)) := by ring
      _ = _ := by rw [hmDiv]
  have htle : t ≤ m := by
    apply (div_le_iff₀ (Real.rpow_pos_of_pos hmpos ((1 : ℝ) / 3))).2
    calc
      n ^ ((2 : ℝ) / 3) ≤ (m ^ 2) ^ ((2 : ℝ) / 3) :=
        Real.rpow_le_rpow hnpos.le hnm2 (by norm_num)
      _ = m * m ^ ((1 : ℝ) / 3) := by
        rw [← Real.rpow_natCast m 2, ← Real.rpow_mul hmpos.le]
        calc
          m ^ ((2 : ℝ) * (2 / 3)) = m ^ ((1 : ℝ) + 1 / 3) := by
            congr 1 <;> norm_num
          _ = m * m ^ ((1 : ℝ) / 3) := by rw [Real.rpow_add hmpos, Real.rpow_one]
  have htsq : t ^ 2 ≤ main := by nlinarith [htle, hMainEq]
  have hnSplit : n ^ ((1 : ℝ) / 3) * n ^ ((2 : ℝ) / 3) = n := by
    rw [← Real.rpow_add hnpos]
    norm_num
  have hnDiv : n / n ^ ((1 : ℝ) / 3) = n ^ ((2 : ℝ) / 3) := by
    apply (div_eq_iff (Real.rpow_pos_of_pos hnpos ((1 : ℝ) / 3)).ne').2
    simpa [mul_comm] using hnSplit.symm
  have hsqrtt : Real.sqrt t = n ^ ((1 : ℝ) / 3) / m ^ ((1 : ℝ) / 6) := by
    rw [Real.sqrt_eq_rpow]
    dsimp [t]
    rw [Real.div_rpow (by positivity) (by positivity),
      ← Real.rpow_mul hnpos.le, ← Real.rpow_mul hmpos.le]
    congr 1 <;> norm_num
  have hmSix : Real.sqrt m * m ^ ((1 : ℝ) / 6) = m ^ ((2 : ℝ) / 3) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hmpos]
    congr 1 <;> norm_num
  have hterm1id : n * Real.sqrt m / Real.sqrt t = main := by
    calc
      n * Real.sqrt m / Real.sqrt t =
          (n / n ^ ((1 : ℝ) / 3)) * (Real.sqrt m * m ^ ((1 : ℝ) / 6)) := by
        rw [hsqrtt]
        field_simp
        <;> ring
      _ = main := by rw [hnDiv, hmSix]
  have hden : Real.sqrt t / 2 ≤ Real.sqrt r := by
    have htwo : Real.sqrt 2 ≤ (2 : ℝ) := by norm_num
    calc
      Real.sqrt t / 2 ≤ Real.sqrt t / Real.sqrt 2 :=
        div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by positivity) htwo
      _ = Real.sqrt (t / 2) := (Real.sqrt_div htpos.le 2).symm
      _ ≤ Real.sqrt r := Real.sqrt_le_sqrt hrhalf
  have hterm1 : n * Real.sqrt m / Real.sqrt r ≤ 2 * main := by
    calc
      n * Real.sqrt m / Real.sqrt r ≤ n * Real.sqrt m / (Real.sqrt t / 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = 2 * (n * Real.sqrt m / Real.sqrt t) := by ring
      _ = 2 * main := by rw [hterm1id]
  have hterm2 : m * r ≤ main := by
    calc
      m * r ≤ m * t := mul_le_mul_of_nonneg_left hrle hmpos.le
      _ = main := hMainEq
  have hterm4 : r ^ 2 ≤ main :=
    (pow_le_pow_left₀ hrpos.le hrle 2).trans htsq
  have hterms : n * Real.sqrt m / Real.sqrt r + m * r + n + r ^ 2 ≤ 5 * target := by
    dsimp [target]
    linarith
  have hpartBound : I ≤ K * (n * Real.sqrt m / Real.sqrt r + m * r + n + r ^ 2) :=
    hpart rNat hrone
  calc
    I ≤ K * (n * Real.sqrt m / Real.sqrt r + m * r + n + r ^ 2) := hpartBound
    _ ≤ K * (5 * target) := mul_le_mul_of_nonneg_left hterms hK.le
    _ = (5 * K) * target := by ring
    _ ≤ C * target := mul_le_mul_of_nonneg_right hCfive htarget

end DistinctDistances.TrackC
