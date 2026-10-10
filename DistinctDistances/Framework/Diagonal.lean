import DistinctDistances.Framework.Asymptotics
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Nat.Find

open Filter
open scoped Topology

namespace DistinctDistances.Framework

/-- `FW.diag`: combine all fixed-precision eventual conditions while precision
increases slowly. The stronger conclusion includes every smaller precision.
Further conditions and rate caps can be conjoined into `Q` before application. -/
theorem exists_slow_diagonal (Q : ℕ → ℕ → Prop)
    (hQ : ∀ h, ∀ᶠ k in atTop, Q h k) :
    ∃ h : ℕ → ℕ, Monotone h ∧ Tendsto h atTop atTop ∧
      ∀ᶠ k in atTop, ∀ j ≤ h k, Q j k := by
  classical
  let good (k n : ℕ) : Prop := ∀ j ≤ n, ∀ l, k ≤ l → Q j l
  have hfinite (n : ℕ) : ∀ᶠ k in atTop, ∀ j ≤ n, Q j k := by
    filter_upwards [eventually_finite (Finset.range (n + 1)) Q (fun j _ => hQ j)]
      with k hk
    intro j hj
    exact hk j (Finset.mem_range.mpr (by omega))
  have hgood (n : ℕ) : ∀ᶠ k in atTop, good k n := by
    filter_upwards [eventually_forall_ge_atTop.mpr (hfinite n)] with k hk
    exact fun j hj l hl => hk l hl j hj
  let h : ℕ → ℕ := fun k => Nat.findGreatest (good k) k
  refine ⟨h, ?_, ?_, ?_⟩
  · intro k l hkl
    apply Nat.findGreatest_mono ?_ hkl
    exact fun n hn j hj m hm => hn j hj m (hkl.trans hm)
  · refine tendsto_atTop.2 fun n => ?_
    filter_upwards [hgood n, eventually_ge_atTop n] with k hk hkn
    exact Nat.le_findGreatest hkn hk
  · filter_upwards [hgood 0] with k hk
    have hg : good k (h k) := Nat.findGreatest_spec (Nat.zero_le k) hk
    exact fun j hj => hg j hj k le_rfl

/-- The error version of `FW.diag`, profiles.tex:570–618. For every fixed
precision each error converges; the selected precision preserves convergence
and any countable collection of further fixed-precision conditions. -/
theorem diagonal_errors (err : ℕ → ℕ → ℝ)
    (herr : ∀ h, Tendsto (err h) atTop (𝓝 0))
    (Q : ℕ → ℕ → ℕ → Prop) (hQ : ∀ h j, ∀ᶠ k in atTop, Q h j k) :
    ∃ h : ℕ → ℕ, Monotone h ∧ Tendsto h atTop atTop ∧
      Tendsto (fun k => err (h k) k) atTop (𝓝 0) ∧
      ∀ j, ∀ᶠ k in atTop, Q (h k) j k := by
  have he (h : ℕ) : ∀ᶠ k in atTop, |err h k| ≤ 1 / ((h : ℝ) + 1) := by
    have hh : LittleO (err h) (fun _ => 1) :=
      (Asymptotics.isLittleO_one_iff ℝ).mpr (herr h)
    simpa only [Real.norm_eq_abs, abs_one, mul_one] using
      hh.def (show (0 : ℝ) < 1 / ((h : ℝ) + 1) by positivity)
  let R (h k : ℕ) : Prop :=
    |err h k| ≤ 1 / ((h : ℝ) + 1) ∧ ∀ j ≤ h, Q h j k
  have hR (h : ℕ) : ∀ᶠ k in atTop, R h k := by
    filter_upwards [he h,
      eventually_finite (Finset.range (h + 1)) (Q h) (fun j _ => hQ h j)] with k hk hq
    exact ⟨hk, fun j hj => hq j (Finset.mem_range.mpr (by omega))⟩
  obtain ⟨h, hmono, hgrows, hchosen⟩ := exists_slow_diagonal R hR
  refine ⟨h, hmono, hgrows, ?_, ?_⟩
  · rw [tendsto_zero_iff_abs_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun k => abs_nonneg (err (h k) k))
      (hchosen.mono fun k hk => (hk (h k) le_rfl).1)
    exact tendsto_one_div_add_atTop_nhds_zero_nat.comp hgrows
  · intro j
    filter_upwards [hchosen, hgrows.eventually (eventually_ge_atTop j)] with k hk hj
    exact (hk (h k) le_rfl).2 j hj

/-- Compactness supplies honest limits for bounded finite profiles. A diagonal
choice making two profiles close does not by itself prove either converges. -/
theorem exists_profile_subsequence {m : ℕ} (times : ℕ → Fin m → ℝ)
    (a b : ℝ) (hbounds : ∀ᶠ k in atTop, ∀ j, a ≤ times k j ∧ times k j ≤ b) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ limits : Fin m → ℝ,
      ProfileConverges (fun k => times (φ k)) limits := by
  have hc : IsCompact {x : Fin m → ℝ | ∀ j, x j ∈ Set.Icc a b} :=
    isCompact_pi_infinite (fun _ => isCompact_Icc)
  have hmem : ∃ᶠ k in atTop, times k ∈ {x : Fin m → ℝ | ∀ j, x j ∈ Set.Icc a b} := by
    simpa only [Set.mem_setOf_eq, Set.mem_Icc] using hbounds.frequently
  obtain ⟨limits, _, φ, hφ, hlim⟩ := hc.tendsto_subseq' hmem
  exact ⟨φ, hφ, limits, tendsto_pi_nhds.mp hlim⟩

end DistinctDistances.Framework
