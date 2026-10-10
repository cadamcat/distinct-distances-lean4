import DistinctDistances.TrackC.LineImages
import DistinctDistances.TrackC.MotionBucketConstruct

open scoped BigOperators
open Classical

noncomputable section

namespace DistinctDistances.TrackC

/-- mot:subdivision-parameters, local-scale-check and rich-line-scale,
motions.tex:846–895. -/
theorem motion_scale_parameters (N t β : ℝ) (hN : 1 ≤ N) (ht : 1 ≤ t)
    (htN : t ≤ N ^ ((1 : ℝ) / 3)) (hβ : 0 < β) :
    let A := N ^ ((2 : ℝ) / 3)
    let r := t ^ ((15 : ℝ) / 14)
    let m := 8 * N / r
    let b := β * A * t ^ ((-1 : ℝ) / 14)
    1 ≤ r ∧ r ≤ N ∧ 1 ≤ m ∧
      b / m ^ ((2 : ℝ) / 3) = (β / 4) * t ^ ((9 : ℝ) / 14) ∧
      β * t ^ ((3 : ℝ) / 7) ≤ b / Real.sqrt N := by
  let A : ℝ := N ^ ((2 : ℝ) / 3)
  let r : ℝ := t ^ ((15 : ℝ) / 14)
  let m : ℝ := 8 * N / r
  let b : ℝ := β * A * t ^ ((-1 : ℝ) / 14)
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hApos : 0 < A := by dsimp [A]; positivity
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hrlo : 1 ≤ r := by
    dsimp [r]
    apply Real.one_le_rpow ht
    norm_num
  have hrhi : r ≤ N := by
    dsimp [r]
    calc
      t ^ ((15 : ℝ) / 14) ≤ (N ^ ((1 : ℝ) / 3)) ^ ((15 : ℝ) / 14) :=
        Real.rpow_le_rpow (by positivity) htN (by norm_num)
      _ = N ^ ((5 : ℝ) / 14) := by
        rw [← Real.rpow_mul hNpos.le]
        congr 1 <;> norm_num
      _ ≤ N := Real.rpow_le_self_of_one_le hN (by norm_num)
  have hmlo : 1 ≤ m := by
    dsimp [m]
    rw [le_div_iff₀ hrpos]
    nlinarith [hN, hrhi]
  have h8 : (8 : ℝ) ^ ((2 : ℝ) / 3) = 4 := by
    have hroot : (8 : ℝ) ^ ((1 : ℝ) / 3) = 2 := by
      rw [show (1 : ℝ) / 3 = (3 : ℝ)⁻¹ by norm_num]
      apply (Real.rpow_inv_eq (by norm_num) (by norm_num) (by norm_num)).2
      norm_num
    calc
      (8 : ℝ) ^ ((2 : ℝ) / 3) = ((8 : ℝ) ^ ((1 : ℝ) / 3)) ^ (2 : ℝ) := by
        rw [show (2 : ℝ) / 3 = ((1 : ℝ) / 3) * 2 by norm_num, Real.rpow_mul (by norm_num)]
      _ = 4 := by rw [hroot]; norm_num
  have hr23 : r ^ ((2 : ℝ) / 3) = t ^ ((5 : ℝ) / 7) := by
    dsimp [r]
    rw [← Real.rpow_mul htpos.le]
    congr 1 <;> norm_num
  have ht57pos : 0 < t ^ ((5 : ℝ) / 7) := Real.rpow_pos_of_pos htpos _
  have hm23 : m ^ ((2 : ℝ) / 3) = 4 * A / t ^ ((5 : ℝ) / 7) := by
    dsimp [m, A]
    calc
      (8 * N / (t ^ ((15 : ℝ) / 14))) ^ ((2 : ℝ) / 3) =
          (8 * N) ^ ((2 : ℝ) / 3) / (t ^ ((15 : ℝ) / 14)) ^ ((2 : ℝ) / 3) := by
            exact Real.div_rpow (by positivity) (by positivity) _
      _ = (8 : ℝ) ^ ((2 : ℝ) / 3) * N ^ ((2 : ℝ) / 3) /
          (t ^ ((15 : ℝ) / 14)) ^ ((2 : ℝ) / 3) := by
            rw [Real.mul_rpow (by norm_num) (by positivity)]
      _ = 4 * N ^ ((2 : ℝ) / 3) / t ^ ((5 : ℝ) / 7) := by rw [h8, hr23]
  have hneg : t ^ ((-1 : ℝ) / 14) = (t ^ ((1 : ℝ) / 14))⁻¹ := by
    rw [show (-1 : ℝ) / 14 = -((1 : ℝ) / 14) by norm_num]
    exact Real.rpow_neg htpos.le _
  have htProd : t ^ ((-1 : ℝ) / 14) * t ^ ((5 : ℝ) / 7) = t ^ ((9 : ℝ) / 14) := by
    rw [← Real.rpow_add htpos]
    congr 1 <;> norm_num
  have hfirst : b / m ^ ((2 : ℝ) / 3) = (β / 4) * t ^ ((9 : ℝ) / 14) := by
    rw [hm23]
    dsimp [b]
    calc
      β * A * t ^ ((-1 : ℝ) / 14) / (4 * A / t ^ ((5 : ℝ) / 7)) =
          (β / 4) * (t ^ ((-1 : ℝ) / 14) * t ^ ((5 : ℝ) / 7)) := by
            field_simp [ne_of_gt hApos, ne_of_gt ht57pos]
            <;> ring
      _ = (β / 4) * t ^ ((9 : ℝ) / 14) := by rw [htProd]
  have hhalf : 0 < t ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos htpos _
  have hrootBound : t ^ ((1 : ℝ) / 2) ≤ N ^ ((1 : ℝ) / 6) := by
    calc
      t ^ ((1 : ℝ) / 2) ≤ (N ^ ((1 : ℝ) / 3)) ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow (by positivity) htN (by norm_num)
      _ = N ^ ((1 : ℝ) / 6) := by
        rw [← Real.rpow_mul hNpos.le]
        congr 1 <;> norm_num
  have hratio : 1 ≤ N ^ ((1 : ℝ) / 6) / t ^ ((1 : ℝ) / 2) :=
    (le_div_iff₀ hhalf).2 (by simpa using hrootBound)
  have hAroot : A / Real.sqrt N = N ^ ((1 : ℝ) / 6) := by
    dsimp [A]
    rw [Real.sqrt_eq_rpow]
    calc
      N ^ ((2 : ℝ) / 3) / N ^ ((1 : ℝ) / 2) =
          N ^ ((2 : ℝ) / 3 - (1 : ℝ) / 2) := (Real.rpow_sub hNpos _ _).symm
      _ = N ^ ((1 : ℝ) / 6) := by congr 1 <;> norm_num
  have htRatio : t ^ ((3 : ℝ) / 7) / t ^ ((1 : ℝ) / 2) = t ^ ((-1 : ℝ) / 14) := by
    rw [← Real.rpow_sub htpos]
    congr 1 <;> norm_num
  have hsecond : β * t ^ ((3 : ℝ) / 7) ≤ b / Real.sqrt N := by
    calc
      β * t ^ ((3 : ℝ) / 7) ≤
          β * (N ^ ((1 : ℝ) / 6) / t ^ ((1 : ℝ) / 2)) * t ^ ((3 : ℝ) / 7) := by
            calc
              β * t ^ ((3 : ℝ) / 7) = β * 1 * t ^ ((3 : ℝ) / 7) := by ring
              _ ≤ β * (N ^ ((1 : ℝ) / 6) / t ^ ((1 : ℝ) / 2)) * t ^ ((3 : ℝ) / 7) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hratio hβ.le)
                  (Real.rpow_nonneg htpos.le _)
      _ = b / Real.sqrt N := by
        dsimp [b]
        rw [← htRatio]
        calc
          β * (N ^ ((1 : ℝ) / 6) / t ^ ((1 : ℝ) / 2)) * t ^ ((3 : ℝ) / 7) =
              β * N ^ ((1 : ℝ) / 6) * (t ^ ((3 : ℝ) / 7) / t ^ ((1 : ℝ) / 2)) := by
                field_simp [ne_of_gt hhalf]
                <;> ring
          _ = β * (A / Real.sqrt N) *
                (t ^ ((3 : ℝ) / 7) / t ^ ((1 : ℝ) / 2)) := by rw [← hAroot]
          _ = β * A * (t ^ ((3 : ℝ) / 7) / t ^ ((1 : ℝ) / 2)) / Real.sqrt N := by
            field_simp [ne_of_gt (Real.sqrt_pos.2 hNpos)]
            <;> ring
  change 1 ≤ r ∧ r ≤ N ∧ 1 ≤ m ∧
    b / m ^ ((2 : ℝ) / 3) = (β / 4) * t ^ ((9 : ℝ) / 14) ∧
      β * t ^ ((3 : ℝ) / 7) ≤ b / Real.sqrt N
  exact ⟨hrlo, hrhi, hmlo, hfirst, hsecond⟩

/-- The global bucket estimate after local mass splitting,
motions.tex:897–989. Constants are chosen before either cloud. -/
theorem motion_bucket_bound : ∃ C β K : ℝ, 4 < C ∧ 0 < β ∧ 0 < K ∧
    ∀ (N : ℕ) (X Y : Finset (E 3)) (t : ℝ), 2 ≤ N → X.card ≤ N → Y.card ≤ N →
      let A := (N : ℝ) ^ ((2 : ℝ) / 3)
      cloudLineCap X (2 * A) → cloudLineCap Y (2 * A) →
      C ≤ t → t ≤ (N : ℝ) ^ ((1 : ℝ) / 3) →
      let k := t * A
      let b := β * A * t ^ ((-1 : ℝ) / 14)
      FiniteCardBound (motionBucket X Y k)
        (K * ((N : ℝ) ^ 4 / A * t ^ ((-1 : ℝ) / 28) +
          A ^ 2 * ((N : ℝ) / b) ^ 4 + A ^ 3 * ((N : ℝ) / b) ^ ((7 : ℝ) / 2)) / k ^ 2) := by
  exact motion_bucket_construct motion_scale_parameters

/-- mot:nonparallel-exponent and parallel-exponent, motions.tex:997–1008. -/
theorem motion_line_exponents (N t β : ℝ) (hN : 0 < N) (ht : 0 < t) (hβ : 0 < β) :
    let A := N ^ ((2 : ℝ) / 3)
    let b := β * A * t ^ ((-1 : ℝ) / 14)
    A ^ 2 * (N / b) ^ 4 = β ^ (-4 : ℝ) * N ^ ((8 : ℝ) / 3) * t ^ ((2 : ℝ) / 7) ∧
      A ^ 3 * (N / b) ^ ((7 : ℝ) / 2) =
      β ^ ((-7 : ℝ) / 2) * N ^ ((19 : ℝ) / 6) * t ^ ((1 : ℝ) / 4) := by
  let A : ℝ := N ^ ((2 : ℝ) / 3)
  let b : ℝ := β * A * t ^ ((-1 : ℝ) / 14)
  have hN0 : 0 ≤ N := hN.le
  have hApos : 0 < A := by dsimp [A]; positivity
  have ht14pos : 0 < t ^ ((1 : ℝ) / 14) := Real.rpow_pos_of_pos ht _
  have hneg : t ^ ((-1 : ℝ) / 14) = (t ^ ((1 : ℝ) / 14))⁻¹ := by
    rw [show (-1 : ℝ) / 14 = -((1 : ℝ) / 14) by norm_num]
    exact Real.rpow_neg ht.le _
  have hNA : N / A = N ^ ((1 : ℝ) / 3) := by
    dsimp [A]
    calc
      N / N ^ ((2 : ℝ) / 3) = N ^ (1 : ℝ) / N ^ ((2 : ℝ) / 3) := by rw [Real.rpow_one]
      _ = N ^ ((1 : ℝ) - (2 : ℝ) / 3) := (Real.rpow_sub hN _ _).symm
      _ = N ^ ((1 : ℝ) / 3) := by congr 1 <;> norm_num
  have hquot : N / b = β⁻¹ * N ^ ((1 : ℝ) / 3) * t ^ ((1 : ℝ) / 14) := by
    dsimp [b]
    rw [hneg]
    calc
      N / (β * A * (t ^ ((1 : ℝ) / 14))⁻¹) = β⁻¹ * (N / A) * t ^ ((1 : ℝ) / 14) := by
        field_simp [ne_of_gt hβ, ne_of_gt hApos, ne_of_gt ht14pos]
        <;> ring
      _ = β⁻¹ * N ^ ((1 : ℝ) / 3) * t ^ ((1 : ℝ) / 14) := by rw [hNA]
  have hA2 : A ^ 2 = N ^ ((4 : ℝ) / 3) := by
    dsimp [A]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0]
    congr 1 <;> norm_num
  have hA3 : A ^ 3 = N ^ (2 : ℝ) := by
    dsimp [A]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0]
    congr 1 <;> norm_num
  have hβ4 : (β⁻¹) ^ (4 : ℝ) = β ^ (-4 : ℝ) := by
    rw [← Real.rpow_neg_one β, ← Real.rpow_mul hβ.le]
    congr 1 <;> norm_num
  have hN4 : (N ^ ((1 : ℝ) / 3)) ^ (4 : ℝ) = N ^ ((4 : ℝ) / 3) := by
    rw [← Real.rpow_mul hN0]
    congr 1 <;> norm_num
  have ht4 : (t ^ ((1 : ℝ) / 14)) ^ (4 : ℝ) = t ^ ((2 : ℝ) / 7) := by
    rw [← Real.rpow_mul ht.le]
    congr 1 <;> norm_num
  have hβ72 : (β⁻¹) ^ ((7 : ℝ) / 2) = β ^ ((-7 : ℝ) / 2) := by
    rw [← Real.rpow_neg_one β, ← Real.rpow_mul hβ.le]
    congr 1 <;> ring
  have hN72 : (N ^ ((1 : ℝ) / 3)) ^ ((7 : ℝ) / 2) = N ^ ((7 : ℝ) / 6) := by
    rw [← Real.rpow_mul hN0]
    congr 1 <;> ring
  have ht72 : (t ^ ((1 : ℝ) / 14)) ^ ((7 : ℝ) / 2) = t ^ ((1 : ℝ) / 4) := by
    rw [← Real.rpow_mul ht.le]
    congr 1 <;> ring
  have hD4 : (β⁻¹ * N ^ ((1 : ℝ) / 3) * t ^ ((1 : ℝ) / 14)) ^ (4 : ℝ) =
      β ^ (-4 : ℝ) * N ^ ((4 : ℝ) / 3) * t ^ ((2 : ℝ) / 7) := by
    rw [Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) (by positivity), hβ4, hN4, ht4]
  have hD72 : (β⁻¹ * N ^ ((1 : ℝ) / 3) * t ^ ((1 : ℝ) / 14)) ^ ((7 : ℝ) / 2) =
      β ^ ((-7 : ℝ) / 2) * N ^ ((7 : ℝ) / 6) * t ^ ((1 : ℝ) / 4) := by
    rw [Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) (by positivity), hβ72, hN72, ht72]
  constructor
  · calc
      A ^ 2 * (N / b) ^ 4 = N ^ ((4 : ℝ) / 3) *
          (β⁻¹ * N ^ ((1 : ℝ) / 3) * t ^ ((1 : ℝ) / 14)) ^ (4 : ℝ) := by
            rw [hA2, hquot]
            exact congrArg (fun z : ℝ => N ^ ((4 : ℝ) / 3) * z)
              (Real.rpow_natCast _ 4).symm
      _ = β ^ (-4 : ℝ) *
          (N ^ ((4 : ℝ) / 3) * N ^ ((4 : ℝ) / 3)) * t ^ ((2 : ℝ) / 7) := by
            rw [hD4]
            ring
      _ = β ^ (-4 : ℝ) * N ^ ((8 : ℝ) / 3) * t ^ ((2 : ℝ) / 7) := by
            rw [← Real.rpow_add hN]
            congr 1 <;> norm_num
  · calc
      A ^ 3 * (N / b) ^ ((7 : ℝ) / 2) = N ^ (2 : ℝ) *
          (β⁻¹ * N ^ ((1 : ℝ) / 3) * t ^ ((1 : ℝ) / 14)) ^ ((7 : ℝ) / 2) := by
            rw [hA3, hquot]
      _ = β ^ ((-7 : ℝ) / 2) *
          (N ^ (2 : ℝ) * N ^ ((7 : ℝ) / 6)) * t ^ ((1 : ℝ) / 4) := by
            rw [hD72]
            ring
      _ = β ^ ((-7 : ℝ) / 2) * N ^ ((19 : ℝ) / 6) * t ^ ((1 : ℝ) / 4) := by
            rw [← Real.rpow_add hN]
            congr 1 <;> norm_num

/-- Increasing and decreasing geometric bucket sums, motions.tex:1009–1026. -/
theorem dyadic_motion_sums : ∃ K : ℝ, 0 < K ∧
    ∀ (N C : ℝ) (J : Finset ℕ), 1 ≤ N → 1 ≤ C →
      (∀ j ∈ J, (2 : ℝ) ^ j * C ≤ N ^ ((1 : ℝ) / 3)) →
      (∑ j ∈ J,
        (N ^ ((10 : ℝ) / 3) * ((2 : ℝ) ^ j * C) ^ ((-1 : ℝ) / 28) +
          N ^ ((8 : ℝ) / 3) * ((2 : ℝ) ^ j * C) ^ ((2 : ℝ) / 7) +
          N ^ ((19 : ℝ) / 6) * ((2 : ℝ) ^ j * C) ^ ((1 : ℝ) / 4))) ≤
        K * N ^ ((10 : ℝ) / 3) := by
  let q1 : ℝ := (2 : ℝ) ^ ((-1 : ℝ) / 28)
  let q2 : ℝ := (2 : ℝ) ^ ((2 : ℝ) / 7)
  let q3 : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 4)
  let K1 : ℝ := (1 - q1)⁻¹
  let K2 : ℝ := q2 / (q2 - 1)
  let K3 : ℝ := q3 / (q3 - 1)
  let K : ℝ := K1 + K2 + K3
  have hq1pos : 0 < q1 := by dsimp [q1]; positivity
  have hq1lt : q1 < 1 := by
    dsimp [q1]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hq2pos : 0 < q2 := by dsimp [q2]; positivity
  have hq2gt : 1 < q2 := by
    dsimp [q2]
    exact Real.one_lt_rpow (by norm_num) (by norm_num)
  have hq3pos : 0 < q3 := by dsimp [q3]; positivity
  have hq3gt : 1 < q3 := by
    dsimp [q3]
    exact Real.one_lt_rpow (by norm_num) (by norm_num)
  have hK1pos : 0 < K1 := by dsimp [K1]; positivity
  have hK2pos : 0 < K2 := by dsimp [K2]; positivity
  have hK3pos : 0 < K3 := by dsimp [K3]; positivity
  have hKpos : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hKpos, ?_⟩
  intro N C J hN hC hbound
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  by_cases hJne : J.Nonempty
  · let n : ℕ := J.sup id
    have hnmem : n ∈ J := by
      have hmem := Finset.sup_mem_of_nonempty (f := id) hJne
      simpa [n] using hmem
    have hJrange : J ⊆ Finset.range (n + 1) := by
      intro j hj
      simp only [Finset.mem_range]
      exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hj)
    have hq1sum : (∑ j ∈ J, q1 ^ j) ≤ K1 := by
      calc
        (∑ j ∈ J, q1 ^ j) ≤ ∑ j ∈ Finset.range (n + 1), q1 ^ j :=
          Finset.sum_le_sum_of_subset_of_nonneg hJrange
            (fun j _ _ => pow_nonneg hq1pos.le _)
        _ ≤ (1 - q1)⁻¹ := by
          have hgeom := geom_sum_Ico_le_of_lt_one hq1pos.le hq1lt (m := 0) (n := n + 1)
          rw [Finset.range_eq_Ico]
          simpa only [pow_zero, one_div] using hgeom
        _ = K1 := by rfl
    have hq2sum : (∑ j ∈ J, q2 ^ j) ≤ q2 / (q2 - 1) * q2 ^ n := by
      calc
        (∑ j ∈ J, q2 ^ j) ≤ ∑ j ∈ Finset.range (n + 1), q2 ^ j :=
          Finset.sum_le_sum_of_subset_of_nonneg hJrange
            (fun j _ _ => pow_nonneg hq2pos.le _)
        _ = (q2 ^ (n + 1) - 1) / (q2 - 1) :=
          geom_sum_eq (ne_of_gt hq2gt) _
        _ ≤ q2 ^ (n + 1) / (q2 - 1) := by
          apply div_le_div_of_nonneg_right ?_ (le_of_lt (sub_pos.mpr hq2gt))
          exact sub_le_self _ (by norm_num)
        _ = q2 / (q2 - 1) * q2 ^ n := by
          rw [pow_succ]
          field_simp [ne_of_gt (sub_pos.mpr hq2gt)]
          <;> ring
    have hq3sum : (∑ j ∈ J, q3 ^ j) ≤ q3 / (q3 - 1) * q3 ^ n := by
      calc
        (∑ j ∈ J, q3 ^ j) ≤ ∑ j ∈ Finset.range (n + 1), q3 ^ j :=
          Finset.sum_le_sum_of_subset_of_nonneg hJrange
            (fun j _ _ => pow_nonneg hq3pos.le _)
        _ = (q3 ^ (n + 1) - 1) / (q3 - 1) :=
          geom_sum_eq (ne_of_gt hq3gt) _
        _ ≤ q3 ^ (n + 1) / (q3 - 1) := by
          apply div_le_div_of_nonneg_right ?_ (le_of_lt (sub_pos.mpr hq3gt))
          exact sub_le_self _ (by norm_num)
        _ = q3 / (q3 - 1) * q3 ^ n := by
          rw [pow_succ]
          field_simp [ne_of_gt (sub_pos.mpr hq3gt)]
          <;> ring
    have hterm (a q : ℝ) (hq : q = (2 : ℝ) ^ a) (j : ℕ) :
        ((2 : ℝ) ^ j * C) ^ a = C ^ a * q ^ j := by
      calc
        ((2 : ℝ) ^ j * C) ^ a = ((2 : ℝ) ^ j) ^ a * C ^ a :=
          Real.mul_rpow (by positivity) (by positivity)
        _ = ((2 : ℝ) ^ a) ^ j * C ^ a := by
          rw [← Real.rpow_pow_comm (by norm_num) a j]
        _ = C ^ a * q ^ j := by rw [← hq]; ring
    have hsum1eq :
        (∑ j ∈ J, N ^ ((10 : ℝ) / 3) * ((2 : ℝ) ^ j * C) ^ ((-1 : ℝ) / 28)) =
          N ^ ((10 : ℝ) / 3) * C ^ ((-1 : ℝ) / 28) * (∑ j ∈ J, q1 ^ j) := by
      calc
        _ = ∑ j ∈ J, (N ^ ((10 : ℝ) / 3) * C ^ ((-1 : ℝ) / 28)) * q1 ^ j := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hterm ((-1 : ℝ) / 28) q1 (by rfl) j]
          ring
        _ = N ^ ((10 : ℝ) / 3) * C ^ ((-1 : ℝ) / 28) * (∑ j ∈ J, q1 ^ j) := by
          rw [Finset.mul_sum]
    have hsum2eq :
        (∑ j ∈ J, N ^ ((8 : ℝ) / 3) * ((2 : ℝ) ^ j * C) ^ ((2 : ℝ) / 7)) =
          N ^ ((8 : ℝ) / 3) * C ^ ((2 : ℝ) / 7) * (∑ j ∈ J, q2 ^ j) := by
      calc
        _ = ∑ j ∈ J, (N ^ ((8 : ℝ) / 3) * C ^ ((2 : ℝ) / 7)) * q2 ^ j := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hterm ((2 : ℝ) / 7) q2 (by rfl) j]
          ring
        _ = N ^ ((8 : ℝ) / 3) * C ^ ((2 : ℝ) / 7) * (∑ j ∈ J, q2 ^ j) := by
          rw [Finset.mul_sum]
    have hsum3eq :
        (∑ j ∈ J, N ^ ((19 : ℝ) / 6) * ((2 : ℝ) ^ j * C) ^ ((1 : ℝ) / 4)) =
          N ^ ((19 : ℝ) / 6) * C ^ ((1 : ℝ) / 4) * (∑ j ∈ J, q3 ^ j) := by
      calc
        _ = ∑ j ∈ J, (N ^ ((19 : ℝ) / 6) * C ^ ((1 : ℝ) / 4)) * q3 ^ j := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hterm ((1 : ℝ) / 4) q3 (by rfl) j]
          ring
        _ = N ^ ((19 : ℝ) / 6) * C ^ ((1 : ℝ) / 4) * (∑ j ∈ J, q3 ^ j) := by
          rw [Finset.mul_sum]
    have hC1 : C ^ ((-1 : ℝ) / 28) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hC (by norm_num)
    have hsum1 :
        (∑ j ∈ J, N ^ ((10 : ℝ) / 3) * ((2 : ℝ) ^ j * C) ^ ((-1 : ℝ) / 28)) ≤
          K1 * N ^ ((10 : ℝ) / 3) := by
      rw [hsum1eq]
      calc
        N ^ ((10 : ℝ) / 3) * C ^ ((-1 : ℝ) / 28) * (∑ j ∈ J, q1 ^ j) =
            N ^ ((10 : ℝ) / 3) * (C ^ ((-1 : ℝ) / 28) * (∑ j ∈ J, q1 ^ j)) := by ring
        _ ≤ N ^ ((10 : ℝ) / 3) * (1 * K1) :=
          mul_le_mul_of_nonneg_left
            (calc
              C ^ ((-1 : ℝ) / 28) * (∑ j ∈ J, q1 ^ j) ≤ 1 * (∑ j ∈ J, q1 ^ j) :=
                mul_le_mul_of_nonneg_right hC1
                  (Finset.sum_nonneg fun j hj => pow_nonneg hq1pos.le _)
              _ ≤ 1 * K1 := mul_le_mul_of_nonneg_left hq1sum (by norm_num))
            (Real.rpow_nonneg (by exact_mod_cast (show 0 ≤ N by linarith)) _)
        _ = K1 * N ^ ((10 : ℝ) / 3) := by ring
    have hterminal2 : C ^ ((2 : ℝ) / 7) * q2 ^ n ≤ N ^ ((2 : ℝ) / 21) := by
      have hpow := Real.rpow_le_rpow (by positivity)
        (hbound n hnmem) (by norm_num : 0 ≤ (2 : ℝ) / 7)
      rw [hterm ((2 : ℝ) / 7) q2 (by rfl) n,
        ← Real.rpow_mul (by exact_mod_cast (show 0 ≤ N by linarith))] at hpow
      convert hpow using 1 <;> congr 1 <;> norm_num
    have hterminal3 : C ^ ((1 : ℝ) / 4) * q3 ^ n ≤ N ^ ((1 : ℝ) / 12) := by
      have hpow := Real.rpow_le_rpow (by positivity)
        (hbound n hnmem) (by norm_num : 0 ≤ (1 : ℝ) / 4)
      rw [hterm ((1 : ℝ) / 4) q3 (by rfl) n,
        ← Real.rpow_mul (by exact_mod_cast (show 0 ≤ N by linarith))] at hpow
      convert hpow using 1 <;> congr 1 <;> norm_num
    have hscaled2 : C ^ ((2 : ℝ) / 7) * (∑ j ∈ J, q2 ^ j) ≤
        K2 * N ^ ((2 : ℝ) / 21) := by
      calc
        C ^ ((2 : ℝ) / 7) * (∑ j ∈ J, q2 ^ j) ≤
            C ^ ((2 : ℝ) / 7) * (q2 / (q2 - 1) * q2 ^ n) :=
          mul_le_mul_of_nonneg_left hq2sum (Real.rpow_nonneg (by linarith) _)
        _ = q2 / (q2 - 1) * (C ^ ((2 : ℝ) / 7) * q2 ^ n) := by ring
        _ ≤ K2 * N ^ ((2 : ℝ) / 21) := by
          simpa [K2] using mul_le_mul_of_nonneg_left hterminal2
            (div_nonneg hq2pos.le (sub_nonneg.mpr hq2gt.le))
    have hscaled3 : C ^ ((1 : ℝ) / 4) * (∑ j ∈ J, q3 ^ j) ≤
        K3 * N ^ ((1 : ℝ) / 12) := by
      calc
        C ^ ((1 : ℝ) / 4) * (∑ j ∈ J, q3 ^ j) ≤
            C ^ ((1 : ℝ) / 4) * (q3 / (q3 - 1) * q3 ^ n) :=
          mul_le_mul_of_nonneg_left hq3sum (Real.rpow_nonneg (by linarith) _)
        _ = q3 / (q3 - 1) * (C ^ ((1 : ℝ) / 4) * q3 ^ n) := by ring
        _ ≤ K3 * N ^ ((1 : ℝ) / 12) := by
          simpa [K3] using mul_le_mul_of_nonneg_left hterminal3
            (div_nonneg hq3pos.le (sub_nonneg.mpr hq3gt.le))
    have hsum2 :
        (∑ j ∈ J, N ^ ((8 : ℝ) / 3) * ((2 : ℝ) ^ j * C) ^ ((2 : ℝ) / 7)) ≤
          K2 * N ^ ((10 : ℝ) / 3) := by
      rw [hsum2eq]
      calc
        N ^ ((8 : ℝ) / 3) * C ^ ((2 : ℝ) / 7) * (∑ j ∈ J, q2 ^ j) =
            N ^ ((8 : ℝ) / 3) * (C ^ ((2 : ℝ) / 7) * (∑ j ∈ J, q2 ^ j)) := by ring
        _ ≤ N ^ ((8 : ℝ) / 3) * (K2 * N ^ ((2 : ℝ) / 21)) :=
          mul_le_mul_of_nonneg_left hscaled2 (Real.rpow_nonneg (by exact_mod_cast (show 0 ≤ N by linarith)) _)
        _ = K2 * (N ^ ((8 : ℝ) / 3) * N ^ ((2 : ℝ) / 21)) := by ring
        _ = K2 * N ^ ((8 : ℝ) / 3 + (2 : ℝ) / 21) := by
          rw [← Real.rpow_add hNpos]
        _ = K2 * N ^ ((58 : ℝ) / 21) := by congr 1 <;> norm_num
        _ ≤ K2 * N ^ ((10 : ℝ) / 3) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hN (by norm_num)) hK2pos.le
    have hsum3 :
        (∑ j ∈ J, N ^ ((19 : ℝ) / 6) * ((2 : ℝ) ^ j * C) ^ ((1 : ℝ) / 4)) ≤
          K3 * N ^ ((10 : ℝ) / 3) := by
      rw [hsum3eq]
      calc
        N ^ ((19 : ℝ) / 6) * C ^ ((1 : ℝ) / 4) * (∑ j ∈ J, q3 ^ j) =
            N ^ ((19 : ℝ) / 6) * (C ^ ((1 : ℝ) / 4) * (∑ j ∈ J, q3 ^ j)) := by ring
        _ ≤ N ^ ((19 : ℝ) / 6) * (K3 * N ^ ((1 : ℝ) / 12)) :=
          mul_le_mul_of_nonneg_left hscaled3 (Real.rpow_nonneg (by exact_mod_cast (show 0 ≤ N by linarith)) _)
        _ = K3 * (N ^ ((19 : ℝ) / 6) * N ^ ((1 : ℝ) / 12)) := by ring
        _ = K3 * N ^ ((19 : ℝ) / 6 + (1 : ℝ) / 12) := by
          rw [← Real.rpow_add hNpos]
        _ = K3 * N ^ ((13 : ℝ) / 4) := by congr 1 <;> norm_num
        _ ≤ K3 * N ^ ((10 : ℝ) / 3) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hN (by norm_num)) hK3pos.le
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    calc
      (∑ j ∈ J, N ^ ((10 : ℝ) / 3) * ((2 : ℝ) ^ j * C) ^ ((-1 : ℝ) / 28)) +
          (∑ j ∈ J, N ^ ((8 : ℝ) / 3) * ((2 : ℝ) ^ j * C) ^ ((2 : ℝ) / 7)) +
          (∑ j ∈ J, N ^ ((19 : ℝ) / 6) * ((2 : ℝ) ^ j * C) ^ ((1 : ℝ) / 4)) ≤
        K1 * N ^ ((10 : ℝ) / 3) + K2 * N ^ ((10 : ℝ) / 3) + K3 * N ^ ((10 : ℝ) / 3) :=
          add_le_add (add_le_add hsum1 hsum2) hsum3
      _ = K * N ^ ((10 : ℝ) / 3) := by dsimp [K]; ring
  · have hJempty : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJne
    simp [hJempty]
    positivity

/-- Stronger two-cloud theorem, motions.tex:46–53, 801–1028. -/
theorem very_rich_two_clouds : ∃ C K : ℝ, 4 < C ∧ 0 < K ∧
    ∀ (N : ℕ) (X Y : Finset (E 3)), 2 ≤ N → X.card ≤ N → Y.card ≤ N →
      let A := (N : ℝ) ^ ((2 : ℝ) / 3)
      cloudLineCap X (2 * A) → cloudLineCap Y (2 * A) →
      FiniteSquareBound X Y (C * A) (K * (N : ℝ) ^ 4 / A) := by
  classical
  obtain ⟨C, β, K₀, hC, hβ, hK₀, hbucket⟩ := motion_bucket_bound
  obtain ⟨Ksum, hKsum, hdyadic⟩ := dyadic_motion_sums
  let Bbeta : ℝ := 1 + β ^ (-4 : ℝ) + β ^ ((-7 : ℝ) / 2)
  let K : ℝ := 4 * K₀ * Ksum * Bbeta
  have hCpos : 0 < C := by linarith
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨C, K, hC, hK, ?_⟩
  intro N X Y hN hX hY
  dsimp only
  let A : ℝ := (N : ℝ) ^ ((2 : ℝ) / 3)
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hNreal : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hApos : 0 < A := by dsimp [A]; positivity
  have hNdivA : (N : ℝ) / A = (N : ℝ) ^ ((1 : ℝ) / 3) := by
    dsimp [A]
    calc
      (N : ℝ) / (N : ℝ) ^ ((2 : ℝ) / 3) =
          (N : ℝ) ^ (1 : ℝ) / (N : ℝ) ^ ((2 : ℝ) / 3) := by rw [Real.rpow_one]
      _ = (N : ℝ) ^ ((1 : ℝ) - (2 : ℝ) / 3) := (Real.rpow_sub hNpos _ _).symm
      _ = (N : ℝ) ^ ((1 : ℝ) / 3) := by congr 1 <;> norm_num
  have hNfourA : (N : ℝ) ^ 4 / A = (N : ℝ) ^ ((10 : ℝ) / 3) := by
    dsimp [A]
    rw [← Real.rpow_natCast]
    calc
      (N : ℝ) ^ (4 : ℝ) / (N : ℝ) ^ ((2 : ℝ) / 3) =
          (N : ℝ) ^ ((4 : ℝ) - (2 : ℝ) / 3) := (Real.rpow_sub hNpos _ _).symm
      _ = (N : ℝ) ^ ((10 : ℝ) / 3) := by congr 1 <;> norm_num
  intro hcapX hcapY
  let J : Finset ℕ := (Finset.range (N + 1)).filter
    (fun j => (2 : ℝ) ^ j * C ≤ (N : ℝ) ^ ((1 : ℝ) / 3))
  have hJbound : ∀ j ∈ J, (2 : ℝ) ^ j * C ≤ (N : ℝ) ^ ((1 : ℝ) / 3) := by
    intro j hj
    exact (Finset.mem_filter.mp hj).2
  have hpowOne : ∀ j : ℕ, (1 : ℝ) ≤ (2 : ℝ) ^ j := by
    intro j
    induction j with
    | zero => norm_num
    | succ j ih =>
        rw [pow_succ]
        nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) j]
  have hNatPow : N ≤ 2 ^ N := by
    simpa using (Nat.choose_le_two_pow N 1)
  have hCN : (N : ℝ) ^ ((1 : ℝ) / 3) < (2 : ℝ) ^ N * C := by
    have hpow : (N : ℝ) ≤ (2 : ℝ) ^ N := by exact_mod_cast hNatPow
    have hN13 : (N : ℝ) ^ ((1 : ℝ) / 3) ≤ (N : ℝ) :=
      Real.rpow_le_self_of_one_le hNreal (by norm_num)
    have h4N : 4 * (N : ℝ) ≤ C * (2 : ℝ) ^ N := by
      calc
        4 * (N : ℝ) ≤ 4 * (2 : ℝ) ^ N := mul_le_mul_of_nonneg_left hpow (by norm_num)
        _ ≤ C * (2 : ℝ) ^ N := mul_le_mul_of_nonneg_right hC.le (pow_nonneg (by norm_num) N)
    nlinarith [hN13, h4N, hNreal]
  have hcover : ∀ g : Motion 3, g ∈ richMotions X Y (C * A) →
      ∃ j ∈ J, g ∈ motionBucket X Y (((2 : ℝ) ^ j * C) * A) := by
    intro g hg
    let m := matchCount X Y g
    let x := (m : ℝ) / A
    have hmX : m ≤ X.card := by
      dsimp [m, matchCount, matchPoints]
      exact Finset.card_filter_le _ _
    have hmN : m ≤ N := hmX.trans hX
    have hmcast : (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast hmN
    have hxhi : x ≤ (N : ℝ) ^ ((1 : ℝ) / 3) := by
      dsimp [x]
      calc
        (m : ℝ) / A ≤ (N : ℝ) / A := div_le_div_of_nonneg_right hmcast hApos.le
        _ = (N : ℝ) ^ ((1 : ℝ) / 3) := hNdivA
    have hmlow : C * A ≤ (m : ℝ) := by simpa [richMotions, m] using hg
    have hxlo : C ≤ x := (le_div_iff₀ hApos).2 (by simpa [mul_comm] using hmlow)
    let S : Finset ℕ := (Finset.range (N + 1)).filter (fun j => (2 : ℝ) ^ j * C ≤ x)
    have hS0 : 0 ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, by simpa [x] using hxlo⟩
    let j : ℕ := S.sup id
    have hjs : j ∈ S := by
      have hmem := Finset.sup_mem_of_nonempty (f := id) ⟨0, hS0⟩
      simpa [j] using hmem
    have hjs' := Finset.mem_filter.mp hjs
    have hjle : j ≤ N := by have := hjs'.1; simp only [Finset.mem_range] at this; omega
    have hjlt : j < N := by
      by_contra hn
      have hjeq : j = N := by omega
      have hmemj : (2 : ℝ) ^ j * C ≤ x := hjs'.2
      rw [hjeq] at hmemj
      subst j
      linarith [hCN, hxhi, hmemj]
    have hxupper : x < (2 : ℝ) ^ (j + 1) * C := by
      by_contra hn
      have hnext : (2 : ℝ) ^ (j + 1) * C ≤ x := le_of_not_gt hn
      have hnextmem : j + 1 ∈ S := by
        apply Finset.mem_filter.mpr
        exact ⟨by simp only [Finset.mem_range]; omega, hnext⟩
      have hmax : j + 1 ≤ j := Finset.le_sup (f := id) hnextmem
      omega
    have hjJ : j ∈ J := by
      apply Finset.mem_filter.mpr
      exact ⟨hjs'.1, hjs'.2.trans hxhi⟩
    have hlo : ((2 : ℝ) ^ j * C) * A ≤ (m : ℝ) :=
      (le_div_iff₀ hApos).1 (by simpa [x] using hjs'.2)
    have hxt : x < 2 * ((2 : ℝ) ^ j * C) := by
      have heq : (2 : ℝ) ^ (j + 1) * C = 2 * ((2 : ℝ) ^ j * C) := by
        rw [pow_succ]
        ring
      rw [heq] at hxupper
      exact hxupper
    have hhi : (m : ℝ) < 2 * (((2 : ℝ) ^ j * C) * A) := by
      calc
        (m : ℝ) < (2 * ((2 : ℝ) ^ j * C)) * A := (div_lt_iff₀ hApos).1 (by simpa [x] using hxt)
        _ = 2 * (((2 : ℝ) ^ j * C) * A) := by ring
    refine ⟨j, ?_, ?_⟩
    · exact hjJ
    · change ((2 : ℝ) ^ j * C) * A ≤ (matchCount X Y g : ℝ) ∧
        (matchCount X Y g : ℝ) < 2 * (((2 : ℝ) ^ j * C) * A)
      exact ⟨hlo, hhi⟩
  have hBucket (j : ℕ) (hj : j ∈ J) :
      FiniteCardBound (motionBucket X Y (((2 : ℝ) ^ j * C) * A))
        (K₀ * ((N : ℝ) ^ 4 / A * ((2 : ℝ) ^ j * C) ^ ((-1 : ℝ) / 28) +
          A ^ 2 * ((N : ℝ) / (β * A * ((2 : ℝ) ^ j * C) ^ ((-1 : ℝ) / 14))) ^ 4 +
          A ^ 3 * ((N : ℝ) / (β * A * ((2 : ℝ) ^ j * C) ^ ((-1 : ℝ) / 14))) ^ ((7 : ℝ) / 2)) /
          (((2 : ℝ) ^ j * C) * A) ^ 2) := by
    have htlo : C ≤ (2 : ℝ) ^ j * C := by
      calc
        C = 1 * C := by ring
        _ ≤ (2 : ℝ) ^ j * C :=
          mul_le_mul_of_nonneg_right (hpowOne j) (le_trans (by norm_num) hC.le)
    have hthi : (2 : ℝ) ^ j * C ≤ (N : ℝ) ^ ((1 : ℝ) / 3) := hJbound j hj
    have hraw := hbucket N X Y ((2 : ℝ) ^ j * C) hN hX hY hcapX hcapY htlo hthi
    simpa [A] using hraw
  have hRichFinite : (richMotions X Y (C * A)).Finite := by
    have hUnion : (⋃ j ∈ (J : Set ℕ), motionBucket X Y (((2 : ℝ) ^ j * C) * A)).Finite := by
      apply (Finset.finite_toSet J).biUnion
      intro j hj
      exact (hBucket j hj).1
    apply hUnion.subset
    intro g hg
    rcases hcover g hg with ⟨j, hj, hgj⟩
    exact Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨hj, hgj⟩⟩
  refine ⟨hRichFinite, ?_⟩
  intro G hG
  let idx : Motion 3 → ℕ := fun g =>
    if hg : g ∈ richMotions X Y (C * A) then Classical.choose (hcover g hg) else 0
  have hidxSpec (g : Motion 3) (hg : g ∈ G) :
      idx g ∈ J ∧ g ∈ motionBucket X Y (((2 : ℝ) ^ idx g * C) * A) := by
    have hrich : g ∈ richMotions X Y (C * A) := hG g hg
    have hspec := Classical.choose_spec (hcover g hrich)
    dsimp [idx]
    rw [dif_pos hrich]
    exact hspec
  let W (j : ℕ) : ℝ :=
    (N : ℝ) ^ 4 / A * ((2 : ℝ) ^ j * C) ^ ((-1 : ℝ) / 28) +
      A ^ 2 * ((N : ℝ) / (β * A * ((2 : ℝ) ^ j * C) ^ ((-1 : ℝ) / 14))) ^ 4 +
      A ^ 3 * ((N : ℝ) / (β * A * ((2 : ℝ) ^ j * C) ^ ((-1 : ℝ) / 14))) ^ ((7 : ℝ) / 2)
  have hlineEq (j : ℕ) (hj : j ∈ J) : W j =
      (N : ℝ) ^ ((10 : ℝ) / 3) * ((2 : ℝ) ^ j * C) ^ ((-1 : ℝ) / 28) +
        β ^ (-4 : ℝ) * (N : ℝ) ^ ((8 : ℝ) / 3) * ((2 : ℝ) ^ j * C) ^ ((2 : ℝ) / 7) +
        β ^ ((-7 : ℝ) / 2) * (N : ℝ) ^ ((19 : ℝ) / 6) * ((2 : ℝ) ^ j * C) ^ ((1 : ℝ) / 4) := by
    have htpos : 0 < (2 : ℝ) ^ j * C := mul_pos (pow_pos (by norm_num) j) hCpos
    have hline := motion_line_exponents (N : ℝ) ((2 : ℝ) ^ j * C) β hNpos htpos hβ
    have hline1 : A ^ 2 * ((N : ℝ) / (β * A * ((2 : ℝ) ^ j * C) ^ ((-1 : ℝ) / 14))) ^ 4 =
        β ^ (-4 : ℝ) * (N : ℝ) ^ ((8 : ℝ) / 3) * ((2 : ℝ) ^ j * C) ^ ((2 : ℝ) / 7) := by
      simpa [A] using hline.1
    have hline2 : A ^ 3 * ((N : ℝ) / (β * A * ((2 : ℝ) ^ j * C) ^ ((-1 : ℝ) / 14))) ^ ((7 : ℝ) / 2) =
        β ^ ((-7 : ℝ) / 2) * (N : ℝ) ^ ((19 : ℝ) / 6) * ((2 : ℝ) ^ j * C) ^ ((1 : ℝ) / 4) := by
      simpa [A] using hline.2
    dsimp [W]
    rw [hNfourA, hline1, hline2]
  have hWsum : (∑ j ∈ J, W j) ≤ Bbeta * (Ksum * (N : ℝ) ^ ((10 : ℝ) / 3)) := by
    have hβ4 : 0 ≤ β ^ (-4 : ℝ) := Real.rpow_nonneg hβ.le _
    have hβ72 : 0 ≤ β ^ ((-7 : ℝ) / 2) := Real.rpow_nonneg hβ.le _
    have hBpos : 0 < Bbeta := by dsimp [Bbeta]; positivity
    have hB1 : 1 ≤ Bbeta := by dsimp [Bbeta]; linarith
    have hB4 : β ^ (-4 : ℝ) ≤ Bbeta := by dsimp [Bbeta]; linarith
    have hB72 : β ^ ((-7 : ℝ) / 2) ≤ Bbeta := by dsimp [Bbeta]; linarith
    let F1 (j : ℕ) := (N : ℝ) ^ ((10 : ℝ) / 3) * ((2 : ℝ) ^ j * C) ^ ((-1 : ℝ) / 28)
    let F2 (j : ℕ) := (N : ℝ) ^ ((8 : ℝ) / 3) * ((2 : ℝ) ^ j * C) ^ ((2 : ℝ) / 7)
    let F3 (j : ℕ) := (N : ℝ) ^ ((19 : ℝ) / 6) * ((2 : ℝ) ^ j * C) ^ ((1 : ℝ) / 4)
    have hWterm (j : ℕ) (hj : j ∈ J) :
        W j = F1 j + β ^ (-4 : ℝ) * F2 j + β ^ ((-7 : ℝ) / 2) * F3 j := by
      calc
        W j = (N : ℝ) ^ ((10 : ℝ) / 3) * ((2 : ℝ) ^ j * C) ^ ((-1 : ℝ) / 28) +
            β ^ (-4 : ℝ) * (N : ℝ) ^ ((8 : ℝ) / 3) * ((2 : ℝ) ^ j * C) ^ ((2 : ℝ) / 7) +
            β ^ ((-7 : ℝ) / 2) * (N : ℝ) ^ ((19 : ℝ) / 6) * ((2 : ℝ) ^ j * C) ^ ((1 : ℝ) / 4) :=
          hlineEq j hj
        _ = F1 j + β ^ (-4 : ℝ) * F2 j + β ^ ((-7 : ℝ) / 2) * F3 j := by
          simp [F1, F2, F3]
          ring
    have hcoeff (j : ℕ) :
        F1 j + β ^ (-4 : ℝ) * F2 j + β ^ ((-7 : ℝ) / 2) * F3 j ≤
          Bbeta * (F1 j + F2 j + F3 j) := by
      have hF1 : 0 ≤ F1 j := by dsimp [F1]; positivity
      have hF2 : 0 ≤ F2 j := by dsimp [F2]; positivity
      have hF3 : 0 ≤ F3 j := by dsimp [F3]; positivity
      have hterm1 : F1 j ≤ Bbeta * F1 j := by
        simpa using mul_le_mul_of_nonneg_right hB1 hF1
      calc
        F1 j + β ^ (-4 : ℝ) * F2 j + β ^ ((-7 : ℝ) / 2) * F3 j ≤
            Bbeta * F1 j + Bbeta * F2 j + Bbeta * F3 j := by
          exact add_le_add (add_le_add hterm1
            (mul_le_mul_of_nonneg_right hB4 hF2))
            (mul_le_mul_of_nonneg_right hB72 hF3)
        _ = Bbeta * (F1 j + F2 j + F3 j) := by ring
    have hweighted : (∑ j ∈ J, W j) ≤ Bbeta * (∑ j ∈ J, (F1 j + F2 j + F3 j)) := by
      calc
        (∑ j ∈ J, W j) = ∑ j ∈ J, (F1 j + β ^ (-4 : ℝ) * F2 j + β ^ ((-7 : ℝ) / 2) * F3 j) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact hWterm j hj
        _ ≤ Bbeta * (∑ j ∈ J, (F1 j + F2 j + F3 j)) := by
          calc
            (∑ j ∈ J, (F1 j + β ^ (-4 : ℝ) * F2 j + β ^ ((-7 : ℝ) / 2) * F3 j)) ≤
                ∑ j ∈ J, Bbeta * (F1 j + F2 j + F3 j) :=
              Finset.sum_le_sum fun j hj => hcoeff j
            _ = Bbeta * (∑ j ∈ J, (F1 j + F2 j + F3 j)) := by rw [Finset.mul_sum]
    have hplain : (∑ j ∈ J, (F1 j + F2 j + F3 j)) ≤ Ksum * (N : ℝ) ^ ((10 : ℝ) / 3) := by
      calc
        (∑ j ∈ J, (F1 j + F2 j + F3 j)) = ∑ j ∈ J,
            ((N : ℝ) ^ ((10 : ℝ) / 3) * ((2 : ℝ) ^ j * C) ^ ((-1 : ℝ) / 28) +
              (N : ℝ) ^ ((8 : ℝ) / 3) * ((2 : ℝ) ^ j * C) ^ ((2 : ℝ) / 7) +
              (N : ℝ) ^ ((19 : ℝ) / 6) * ((2 : ℝ) ^ j * C) ^ ((1 : ℝ) / 4)) := by
                apply Finset.sum_congr rfl
                intro j hj
                rfl
        _ ≤ Ksum * (N : ℝ) ^ ((10 : ℝ) / 3) :=
          hdyadic (N : ℝ) C J hNreal (le_trans (by norm_num) hC.le) hJbound
    exact le_trans hweighted (mul_le_mul_of_nonneg_left hplain hBpos.le)
  have hfilter : G.filter (fun g => idx g ∈ J) = G := by
    apply Finset.filter_eq_self.mpr
    intro g hg
    exact (hidxSpec g hg).1
  have hsumPartition :
      (∑ g ∈ G, (matchCount X Y g : ℝ) ^ 2) =
        ∑ j ∈ J, ∑ g ∈ G.filter (fun g => idx g = j), (matchCount X Y g : ℝ) ^ 2 := by
    calc
      (∑ g ∈ G, (matchCount X Y g : ℝ) ^ 2) =
          ∑ g ∈ G.filter (fun g => idx g ∈ J), (matchCount X Y g : ℝ) ^ 2 := by rw [hfilter]
      _ = ∑ j ∈ J, ∑ g ∈ G.filter (fun g => idx g = j), (matchCount X Y g : ℝ) ^ 2 :=
          (Finset.sum_fiberwise_eq_sum_filter G J idx (fun g => (matchCount X Y g : ℝ) ^ 2)).symm
  have hfiber (j : ℕ) (hj : j ∈ J) :
      (∑ g ∈ G.filter (fun g => idx g = j), (matchCount X Y g : ℝ) ^ 2) ≤ 4 * K₀ * W j := by
    let Gj := G.filter (fun g => idx g = j)
    let kj : ℝ := ((2 : ℝ) ^ j * C) * A
    have hkj : 0 < kj := mul_pos (mul_pos (pow_pos (by norm_num) j) hCpos) hApos
    have hbb := hBucket j hj
    change (motionBucket X Y (((2 : ℝ) ^ j * C) * A)).Finite ∧
      ((motionBucket X Y (((2 : ℝ) ^ j * C) * A)).ncard : ℝ) ≤
        K₀ * W j / kj ^ 2 at hbb
    have hGsubset : Gj ⊆ hbb.1.toFinset := by
      intro g hg
      have hg' := Finset.mem_filter.mp hg
      have hidx := (hidxSpec g hg'.1).2
      rw [hg'.2] at hidx
      exact hbb.1.mem_toFinset.mpr hidx
    have hcard : (Gj.card : ℝ) ≤ K₀ * W j / kj ^ 2 := by
      calc
        (Gj.card : ℝ) ≤ (hbb.1.toFinset.card : ℝ) := by exact_mod_cast Finset.card_le_card hGsubset
        _ = (motionBucket X Y (((2 : ℝ) ^ j * C) * A)).ncard := by
          have hcardSet := Set.ncard_eq_toFinset_card
            (motionBucket X Y (((2 : ℝ) ^ j * C) * A)) hbb.1
          exact_mod_cast hcardSet.symm
        _ ≤ K₀ * W j / kj ^ 2 := by simpa [W, kj] using hbb.2
    have hsumBound : (∑ g ∈ Gj, (matchCount X Y g : ℝ) ^ 2) ≤
        (Gj.card : ℝ) * (2 * kj) ^ 2 := by
      calc
        (∑ g ∈ Gj, (matchCount X Y g : ℝ) ^ 2) ≤ Gj.card • (2 * kj) ^ 2 :=
          Finset.sum_le_card_nsmul Gj (fun g => (matchCount X Y g : ℝ) ^ 2) ((2 * kj) ^ 2) fun g hg => by
            have hg' := Finset.mem_filter.mp hg
            have hbg := (hidxSpec g hg'.1).2
            rw [hg'.2] at hbg
            have hupper : (matchCount X Y g : ℝ) < 2 * kj := by
              simpa [motionBucket, kj] using hbg.2
            have hcount : 0 ≤ (matchCount X Y g : ℝ) := Nat.cast_nonneg _
            have hprod : 0 ≤ (2 * kj - (matchCount X Y g : ℝ)) *
                (2 * kj + (matchCount X Y g : ℝ)) :=
              mul_nonneg (sub_nonneg.mpr hupper.le)
                (add_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hkj.le) hcount)
            nlinarith [hprod]
        _ = (Gj.card : ℝ) * (2 * kj) ^ 2 := by simp
    calc
      (∑ g ∈ Gj, (matchCount X Y g : ℝ) ^ 2) ≤ (Gj.card : ℝ) * (2 * kj) ^ 2 := hsumBound
      _ ≤ (K₀ * W j / kj ^ 2) * (2 * kj) ^ 2 := mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
      _ = 4 * K₀ * W j := by field_simp [ne_of_gt hkj]; ring
  have hsumFib :
      (∑ j ∈ J, ∑ g ∈ G.filter (fun g => idx g = j), (matchCount X Y g : ℝ) ^ 2) ≤
        4 * K₀ * (∑ j ∈ J, W j) := by
    calc
      (∑ j ∈ J, ∑ g ∈ G.filter (fun g => idx g = j), (matchCount X Y g : ℝ) ^ 2) ≤
          ∑ j ∈ J, 4 * K₀ * W j := Finset.sum_le_sum fun j hj => hfiber j hj
      _ = 4 * K₀ * (∑ j ∈ J, W j) := by rw [Finset.mul_sum]
  calc
    (∑ g ∈ G, (matchCount X Y g : ℝ) ^ 2) =
        ∑ j ∈ J, ∑ g ∈ G.filter (fun g => idx g = j), (matchCount X Y g : ℝ) ^ 2 := hsumPartition
    _ ≤ 4 * K₀ * (∑ j ∈ J, W j) := hsumFib
    _ ≤ 4 * K₀ * (Bbeta * (Ksum * (N : ℝ) ^ ((10 : ℝ) / 3))) :=
      mul_le_mul_of_nonneg_left hWsum (by positivity)
    _ = K * ((N : ℝ) ^ 4 / A) := by
      rw [hNfourA]
      dsimp [K]
      ring
    _ = K * (N : ℝ) ^ 4 / A := by ring

/-- mot:rich, including every congruent copy, motions.tex:15–32. -/
theorem mot_rich : ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
    ∀ P : Finset (E 3), 2 ≤ P.card →
      let A := (P.card : ℝ) ^ ((2 : ℝ) / 3)
      let M := 1 + ((positiveDistances P).card : ℝ)
      M ≤ A → ∀ Q : Finset (E 3),
        (∃ h : Motion 3, P.image h = Q) →
        FiniteSquareBound P Q (C * A) (K * (P.card : ℝ) ^ 4 / A) := by
  classical
  obtain ⟨C, K, hC, hK, htwo⟩ := very_rich_two_clouds
  refine ⟨C, K, lt_trans (by norm_num) hC, hK, ?_⟩
  intro P hP letA M hM Q hQ
  obtain ⟨h, hPQ⟩ := hQ
  have hdist : positiveDistances Q = positiveDistances P := by
    ext d
    constructor
    · intro hd
      rcases Finset.mem_image.mp hd with ⟨⟨q₁, q₂⟩, hq, hdq⟩
      rcases Finset.mem_offDiag.mp hq with ⟨hq₁, hq₂, hqne⟩
      have hq₁' : q₁ ∈ P.image h := by simpa [hPQ] using hq₁
      have hq₂' : q₂ ∈ P.image h := by simpa [hPQ] using hq₂
      rcases Finset.mem_image.mp hq₁' with ⟨p₁, hp₁, rfl⟩
      rcases Finset.mem_image.mp hq₂' with ⟨p₂, hp₂, rfl⟩
      have hpne : p₁ ≠ p₂ := by
        intro heq
        apply hqne
        simpa [heq]
      apply Finset.mem_image.mpr ⟨(p₁, p₂), Finset.mem_offDiag.mpr ⟨hp₁, hp₂, hpne⟩, ?_⟩
      simpa [h.isometry.dist_eq p₁ p₂] using hdq
    · intro hd
      rcases Finset.mem_image.mp hd with ⟨⟨p₁, p₂⟩, hp, hdp⟩
      rcases Finset.mem_offDiag.mp hp with ⟨hp₁, hp₂, hpne⟩
      have hq₁ : h p₁ ∈ Q := by
        rw [← hPQ]
        exact Finset.mem_image.mpr ⟨p₁, hp₁, rfl⟩
      have hq₂ : h p₂ ∈ Q := by
        rw [← hPQ]
        exact Finset.mem_image.mpr ⟨p₂, hp₂, rfl⟩
      have hqne : h p₁ ≠ h p₂ := fun heq => hpne (h.injective heq)
      apply Finset.mem_image.mpr
        ⟨(h p₁, h p₂), Finset.mem_offDiag.mpr ⟨hq₁, hq₂, hqne⟩, ?_⟩
      simpa [h.isometry.dist_eq p₁ p₂] using hdp
  have hQcard : Q.card = P.card := by
    rw [← hPQ, Finset.card_image_of_injective _ h.injective]
  have hcapP : cloudLineCap P (2 * letA) := by
    have hphysical := physical_line_cap P
    have hbound : (1 : ℝ) + 2 * (positiveDistances P).card ≤ 2 * letA := by
      dsimp [M] at hM
      nlinarith [hM]
    intro l
    exact (hphysical l).trans hbound
  have hcapQ : cloudLineCap Q (2 * letA) := by
    have hphysical := physical_line_cap Q
    have hbound : (1 : ℝ) + 2 * (positiveDistances Q).card ≤ 2 * letA := by
      rw [hdist]
      dsimp [M] at hM
      nlinarith [hM]
    intro l
    exact (hphysical l).trans hbound
  have hresult := htwo P.card P Q hP (show P.card ≤ P.card from le_rfl)
    (by simpa [hQcard]) hcapP hcapQ
  simpa using hresult

/-- Vertices of the equal-distance graph are matched source-target point pairs. -/
def motionDeletedEdges (P Q : Finset (E 3)) (k : ℝ) :
    Finset ((E 3 × E 3) × (E 3 × E 3)) :=
  (P ×ˢ Q).offDiag.filter (fun vv' => ∃ g : Motion 3,
    g ∈ richMotions P Q k ∧ g vv'.1.1 = vv'.1.2 ∧ g vv'.2.1 = vv'.2.2)

/-- Ordered graph-edge version of mot:scope's deletion cost, motions.tex:1037–1046;
consumed by reduction.tex:275–290. -/
theorem mot_rich_deletion : ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
    ∀ P : Finset (E 3), 2 ≤ P.card →
      let A := (P.card : ℝ) ^ ((2 : ℝ) / 3)
      (1 + ((positiveDistances P).card : ℝ)) ≤ A →
      ∀ Q : Finset (E 3), (∃ h : Motion 3, P.image h = Q) →
      ((motionDeletedEdges P Q (C * A)).card : ℝ) ≤ K * (P.card : ℝ) ^ 4 / A := by
  classical
  obtain ⟨C, K, hC, hK, hmot⟩ := mot_rich
  refine ⟨C, K, hC, hK, ?_⟩
  intro P hP A hA Q hQ
  have hbound := hmot P hP hA Q hQ
  let G : Finset (Motion 3) := hbound.1.toFinset
  have hGmem (g : Motion 3) : g ∈ G ↔ g ∈ richMotions P Q (C * A) := by
    constructor
    · exact hbound.1.mem_toFinset.mp
    · exact hbound.1.mem_toFinset.mpr
  let edgesFor : Motion 3 → Finset ((E 3 × E 3) × (E 3 × E 3)) := fun g =>
    (P ×ˢ Q).offDiag.filter (fun vv' =>
      g vv'.1.1 = vv'.1.2 ∧ g vv'.2.1 = vv'.2.2)
  have hUnion : motionDeletedEdges P Q (C * A) = G.biUnion edgesFor := by
    ext e
    constructor
    · intro he
      rcases Finset.mem_filter.mp he with ⟨he, ⟨g, hg, hmatch⟩⟩
      exact Finset.mem_biUnion.mpr
        ⟨g, (hGmem g).mpr hg, Finset.mem_filter.mpr ⟨he, hmatch⟩⟩
    · intro he
      rcases Finset.mem_biUnion.mp he with ⟨g, hg, he⟩
      rcases Finset.mem_filter.mp he with ⟨he, hmatch⟩
      exact Finset.mem_filter.mpr ⟨he, ⟨g, (hGmem g).mp hg, hmatch⟩⟩
  have hcount (g : Motion 3) :
      (edgesFor g).card ≤ (matchCount P Q g) ^ 2 := by
    let S := matchPoints P Q g
    have hle : (edgesFor g).card ≤ (S ×ˢ S).card := by
      refine Finset.card_le_card_of_injOn
        (fun e : ((E 3 × E 3) × (E 3 × E 3)) => (e.1.1, e.2.1)) ?_ ?_
      · intro e he
        change e ∈ (P ×ˢ Q).offDiag.filter (fun vv' =>
          g vv'.1.1 = vv'.1.2 ∧ g vv'.2.1 = vv'.2.2) at he
        rcases Finset.mem_filter.mp he with ⟨heoff, hmatch⟩
        rcases Finset.mem_offDiag.mp heoff with ⟨he₁, he₂, _⟩
        rcases Finset.mem_product.mp he₁ with ⟨hp, hq⟩
        rcases Finset.mem_product.mp he₂ with ⟨hp', hq'⟩
        have hm : e.1.1 ∈ matchPoints P Q g := by
          dsimp [matchPoints]
          exact Finset.mem_filter.mpr ⟨hp, by rw [hmatch.1]; exact hq⟩
        have hm' : e.2.1 ∈ matchPoints P Q g := by
          dsimp [matchPoints]
          exact Finset.mem_filter.mpr ⟨hp', by rw [hmatch.2]; exact hq'⟩
        exact Finset.mem_product.mpr ⟨hm, hm'⟩
      · intro e he e' he' heq
        change e ∈ (P ×ˢ Q).offDiag.filter (fun vv' =>
          g vv'.1.1 = vv'.1.2 ∧ g vv'.2.1 = vv'.2.2) at he
        change e' ∈ (P ×ˢ Q).offDiag.filter (fun vv' =>
          g vv'.1.1 = vv'.1.2 ∧ g vv'.2.1 = vv'.2.2) at he'
        have hmatch := (Finset.mem_filter.mp he).2
        have hmatch' := (Finset.mem_filter.mp he').2
        rcases e with ⟨⟨p, q⟩, ⟨p', q'⟩⟩
        rcases e' with ⟨⟨r, s⟩, ⟨r', s'⟩⟩
        change ((p, p') = (r, r')) at heq
        have hpr : p = r := congrArg Prod.fst heq
        have hp'r' : p' = r' := congrArg Prod.snd heq
        subst r
        subst r'
        have hqs : q = s := hmatch.1.symm.trans hmatch'.1
        have hq's' : q' = s' := hmatch.2.symm.trans hmatch'.2
        subst s
        subst s'
        rfl
    calc
      (edgesFor g).card ≤ (S ×ˢ S).card := hle
      _ = S.card * S.card := Finset.card_product _ _
      _ = (matchCount P Q g) ^ 2 := by simp [S, matchCount, pow_two]
  have hsum :
      (∑ g ∈ G, (edgesFor g).card : ℝ) ≤
        ∑ g ∈ G, (matchCount P Q g : ℝ) ^ 2 := by
    exact Finset.sum_le_sum fun g hg => by exact_mod_cast hcount g
  have hsumBound := hbound.2 G fun g hg => (hGmem g).mp hg
  calc
    ((motionDeletedEdges P Q (C * A)).card : ℝ) =
        ((G.biUnion edgesFor).card : ℝ) := by rw [hUnion]
    _ ≤ (∑ g ∈ G, (edgesFor g).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le (s := G) (t := edgesFor))
    _ ≤ ∑ g ∈ G, (matchCount P Q g : ℝ) ^ 2 := hsum
    _ ≤ K * (P.card : ℝ) ^ 4 / A := hsumBound

end DistinctDistances.TrackC
