import DistinctDistances.TrackE.CommonEndpoint
import DistinctDistances.TrackE.OuterPool

/-! Final-plateau selection and budget identities at the outer endpoint
(sparse-cones.tex:350–354).

The limiting profile has at least two cuts below one (`b_0, b_1 < 1`, from
balance and `b ≥ -1`) and its last cut at one (`outer_profile_last_eq_one`).
The final open plateau starts at the largest cut below one; all later cuts
are exactly one (sortedness + maximality), so with `k + j + 1 = d` the first
`j + 1` cuts sum to `-k` and `eScale = B^{d-2k}`, `N / eScale = A^k`
(sparse-cones.tex:352) hold exactly. The deletion ratio
`eScale · B^{k+1} / N = e^{s(1-k)}` vanishes for `k ≥ 2`. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- The first two limiting cuts lie below one (balance against `b ≥ -1`). -/
theorem outer_first_two_cuts_below_one {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} (M : CommonPoolProfile T) :
    M.b ⟨0, by have := regime.dimension_ge_three; omega⟩ < 1 ∧
    M.b ⟨1, by have := regime.dimension_ge_three; omega⟩ < 1 := by
  obtain ⟨c, hc0, hb0, _, h01⟩ := M.balance
  have h0 : -1 ≤ M.b ⟨0, by have := regime.dimension_ge_three; omega⟩ :=
    common_profile_time_lower M _
  have h1 : -1 ≤ M.b ⟨1, by have := regime.dimension_ge_three; omega⟩ :=
    common_profile_time_lower M _
  refine ⟨by linarith, ?_⟩
  by_contra hcon
  simp only [not_lt] at hcon
  linarith

/-- The final open plateau: `k + j + 1 = d` with `1 ≤ k`, `k + 1 < d`, the
cut `β = M.b j` below one, and every later cut exactly one. -/
theorem outer_final_plateau_exists {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} (M : CommonPoolProfile T) :
    ∃ (k j : ℕ) (hj : j < d), k + j + 1 = d ∧ 1 ≤ k ∧ k + 1 < d ∧
      M.b ⟨j, hj⟩ < 1 ∧
      ∀ a : Fin d, j < a.val → M.b a = 1 := by
  have hd := regime.dimension_ge_three
  have h01 := outer_first_two_cuts_below_one M
  have hlast : M.b ⟨d - 1, by omega⟩ = 1 := by
    have h := outer_profile_last_eq_one _ M
    rwa [commonLastTime] at h
  classical
  let S : Finset (Fin d) :=
    Finset.univ.filter (fun a : Fin d => M.b a < 1)
  have h0mem : (⟨0, by omega⟩ : Fin d) ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h01.1
  have h1mem : (⟨1, by omega⟩ : Fin d) ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h01.2
  have hne : S.Nonempty := ⟨_, h0mem⟩
  have hlt' : (S.max' hne).val < d := (S.max' hne).isLt
  refine ⟨d - ((S.max' hne).val + 1), (S.max' hne).val, hlt', ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · have hmax1 : (⟨1, by omega⟩ : Fin d) ≤ S.max' hne :=
      Finset.le_max' S _ h1mem
    have hlt : (S.max' hne).val ≤ d - 2 := by
      by_contra hcon
      simp only [not_le] at hcon
      have hmax : (S.max' hne).val = d - 1 := by omega
      have hmem := Finset.max'_mem S hne
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      have hlast' : M.b (S.max' hne) = 1 := by
        have : (S.max' hne) = (⟨d - 1, by omega⟩ : Fin d) := Fin.ext hmax
        rw [this]; exact hlast
      linarith
    omega
  · have hmax1 : (⟨1, by omega⟩ : Fin d) ≤ S.max' hne :=
      Finset.le_max' S _ h1mem
    simp only [Fin.le_def] at hmax1
    omega
  · have hmem := Finset.max'_mem S hne
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    exact hmem
  · intro a ha
    have hnotmem : a ∉ S := by
      intro hmem
      have hle := Finset.le_max' S a hmem
      simp only [Fin.le_def] at hle
      omega
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and,
      not_lt] at hnotmem
    have hle : M.b a ≤ M.b ⟨d - 1, by omega⟩ :=
      M.sorted (by simp only [Fin.le_def]; omega)
    linarith

/-- The first `j + 1` cuts sum to `-k` (the top `k` cuts are all one). -/
theorem outer_first_cuts_sum {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} (M : CommonPoolProfile T)
    (k j : ℕ) (hkj : k + j + 1 = d)
    (htop : ∀ a : Fin d, j < a.val → M.b a = 1) :
    ∑ a ∈ Finset.univ.filter (fun a : Fin d => a.val < j + 1), M.b a = -(k : ℝ) := by
  have hsum := M.sum_zero
  have hsplit : ∑ a : Fin d, M.b a =
      (∑ a ∈ Finset.univ.filter (fun a : Fin d => a.val < j + 1), M.b a) +
      (∑ a ∈ Finset.univ.filter (fun a : Fin d => ¬ a.val < j + 1), M.b a) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun a : Fin d => a.val < j + 1) M.b]
  have htop_sum : ∑ a ∈ Finset.univ.filter (fun a : Fin d => ¬ a.val < j + 1), M.b a
      = (k : ℝ) := by
    have hcard : (Finset.univ.filter (fun a : Fin d => ¬ a.val < j + 1)).card = k := by
      have hkj' : j + 1 + k = d := by omega
      have : Finset.univ.filter (fun a : Fin d => ¬ a.val < j + 1) =
          Finset.Ioi (⟨j, by have h := regime.dimension_ge_three; omega⟩ : Fin d) := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ioi,
          Fin.lt_def, not_lt]
        omega
      rw [this, Fin.card_Ioi]
      show d - 1 - j = k
      omega
    have h1 : ∀ a ∈ Finset.univ.filter (fun a : Fin d => ¬ a.val < j + 1),
        M.b a = 1 := by
      intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      exact htop a (by omega)
    rw [Finset.sum_congr rfl h1]
    simp only [Finset.sum_const, hcard, nsmul_eq_mul, mul_one]
  linarith

/-- `N = B^d` from the regime normalization. -/
theorem outer_N_eq_B_pow {d : ℕ} {regime : Regime d} (i : ℕ) :
    regime.N i = (regime.B i) ^ d := by
  have hN := regime.N_pos i
  have hd : d ≠ 0 := by
    have h := regime.dimension_ge_three
    omega
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  have hB : regime.B i = (regime.N i) ^ (1 / (d : ℝ)) := rfl
  rw [hB]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hN)]
  have : (1 / (d : ℝ)) * (d : ℝ) = 1 := by rw [one_div, inv_mul_cancel₀ hd']
  rw [this, Real.rpow_one]

/-- Helper: `exp` of a negated diverging sequence tends to zero. -/
theorem tendsto_zero_of_exp_neg_tendsto_atTop (f : ℕ → ℝ)
    (hf : Tendsto f atTop atTop) :
    Tendsto (fun i => Real.exp (-(f i))) atTop (𝓝 0) :=
  Real.tendsto_exp_neg_atTop_nhds_zero.comp hf

/-- The deletion ratio vanishes for `k ≥ 2` (sparse-cones.tex:382–390,
outer budgets 352): with `s = log B`,
`eScale · B^{k+1} / N = e^{s(1-k)} → 0`. -/
theorem outer_deletion_ratio_vanishes {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} (M : CommonPoolProfile T)
    (hs : ∀ i : ℕ, M.s i = Real.log (regime.B i))
    (k j : ℕ) (hkj : k + j + 1 = d) (hk2 : 2 ≤ k)
    (hsum : ∑ a ∈ Finset.univ.filter (fun a : Fin d => a.val < j + 1),
      M.b a = -(k : ℝ)) :
    Tendsto (fun i => TrackD.eScale (regime.B i) (M.s i) M.b (j + 1) *
      (regime.B i) ^ (k + 1) / (regime.N i)) atTop (𝓝 0) := by
  have hBpos : ∀ i : ℕ, 0 < regime.B i := fun i => regime.B_pos i
  have hN : ∀ i : ℕ, regime.N i = (regime.B i) ^ d := fun i => outer_N_eq_B_pow i
  have hexp : ∀ i : ℕ, TrackD.eScale (regime.B i) (M.s i) M.b (j + 1) *
      (regime.B i) ^ (k + 1) / (regime.N i) =
      Real.exp ((1 - (k : ℝ)) * M.s i) := by
    intro i
    have hcard : (Finset.univ.filter (fun a : Fin d => a.val < j + 1)).card
        = j + 1 := by
      have : Finset.univ.filter (fun a : Fin d => a.val < j + 1) =
          Finset.Iio (⟨j + 1, by have h := regime.dimension_ge_three; omega⟩ : Fin d) := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio,
          Fin.lt_def]
      rw [this, Fin.card_Iio]
    have hesum := hsum
    simp only [TrackD.eScale, TrackD.cutScale, TrackD.testDeg]
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const, hcard]
    rw [← Real.exp_sum]
    have hBne : regime.B i ≠ 0 := ne_of_gt (hBpos i)
    rw [hN i]
    have hpow : (regime.B i) ^ (j + 1) * Real.exp (∑ x ∈ Finset.univ.filter
        (fun a : Fin d => a.val < j + 1), M.b x * M.s i) * (regime.B i) ^ (k + 1) /
        (regime.B i) ^ d = regime.B i * Real.exp (∑ x ∈ Finset.univ.filter
        (fun a : Fin d => a.val < j + 1), M.b x * M.s i) := by
      have hinner : (regime.B i) ^ (j + 1) * (regime.B i) ^ (k + 1) /
          (regime.B i) ^ d = regime.B i := by
        have : j + 1 + (k + 1) = d + 1 := by omega
        rw [← pow_add, this, pow_succ']
        field_simp
      have hrw : (regime.B i) ^ (j + 1) * Real.exp (∑ x ∈ Finset.univ.filter
          (fun a : Fin d => a.val < j + 1), M.b x * M.s i) * (regime.B i) ^ (k + 1) /
          (regime.B i) ^ d =
          ((regime.B i) ^ (j + 1) * (regime.B i) ^ (k + 1) / (regime.B i) ^ d) *
            Real.exp (∑ x ∈ Finset.univ.filter
              (fun a : Fin d => a.val < j + 1), M.b x * M.s i) := by
        ring
      rw [hrw, hinner]
    rw [hpow]
    have hexpsum : ∑ x ∈ Finset.univ.filter (fun a : Fin d => a.val < j + 1),
        M.b x * M.s i =
        (∑ x ∈ Finset.univ.filter (fun a : Fin d => a.val < j + 1), M.b x) *
          M.s i := by
      rw [Finset.sum_mul]
    rw [hexpsum, hesum, hs i]
    nth_rewrite 1 [← Real.exp_log (hBpos i)]
    have : Real.exp (Real.log (regime.B i)) *
        Real.exp (-(k : ℝ) * Real.log (regime.B i))
        = Real.exp ((1 - (k : ℝ)) * Real.log (regime.B i)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    exact this
  simp only [hexp]
  have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by
    have h2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
    linarith
  have hpos : Tendsto (fun i => ((k : ℝ) - 1) * M.s i) atTop atTop :=
    M.width_grows.const_mul_atTop hk1
  have heq' : (fun i => Real.exp ((1 - (k : ℝ)) * M.s i)) =
      (fun i => Real.exp (-(((k : ℝ) - 1) * M.s i))) := by
    funext i
    congr 1
    ring
  rw [heq']
  exact tendsto_zero_of_exp_neg_tendsto_atTop _ hpos

end
end DistinctDistances.SparseCones
