import DistinctDistances.TrackE.CommonRankAlternativeData
import DistinctDistances.TrackE.CommonLabelGroup
import DistinctDistances.TrackD.Profiles.RankCore
import DistinctDistances.TrackD.Profiles.RegularityZero
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Sym.Card
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Rename

/-! Shared scalar helpers for the common-rank plateau step (182) and initial
interval (183): sigma factorization, floor/choose bounds, width absorption,
rank-one convention. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

theorem common_cutScale_ge_one {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} (M : CommonPoolProfile T) (i : ℕ)
    (a : Fin d) : 1 ≤ TrackD.cutScale (regime.B i) (M.s i) M.b a := by
  have hb := common_profile_time_lower M a
  have hs := common_pool_width_le_logB M i
  have hB := regime.B_pos i
  unfold TrackD.cutScale TrackD.testDeg
  rw [← Real.exp_log hB, ← Real.exp_add]
  apply Real.one_le_exp
  nlinarith [M.width_pos i]

theorem common_sigma_plateau_eq {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} (M : CommonPoolProfile T)
    (j : ℕ) (hj : j + 1 < d) (τ : ℝ)
    (hτ : M.b ⟨j, by omega⟩ < τ ∧ τ < M.b ⟨j + 1, hj⟩) (i : ℕ) :
    TrackD.sigma (regime.B i) (M.s i) M.b τ =
      TrackD.eScale (regime.B i) (M.s i) M.b (j + 1) *
        (TrackD.testDeg (regime.B i) (M.s i) τ) ^ (d - (j + 1)) := by
  classical
  have hspos := M.width_pos i
  have hBnn := (regime.B_pos i).le
  have hfactor : ∀ a : Fin d,
      min (TrackD.testDeg (regime.B i) (M.s i) τ)
        (TrackD.cutScale (regime.B i) (M.s i) M.b a) =
        (if a.val < j + 1 then TrackD.cutScale (regime.B i) (M.s i) M.b a
         else TrackD.testDeg (regime.B i) (M.s i) τ) := by
    intro a
    by_cases ha : a.val < j + 1
    · rw [if_pos ha]
      apply min_eq_right
      have hval : a.val ≤ j := by omega
      have hle : M.b a ≤ M.b ⟨j, by omega⟩ :=
        M.sorted (Fin.le_def.mpr hval)
      exact TrackD.RankCore.testDeg_mono hBnn hspos.le
        (le_trans hle hτ.1.le)
    · rw [if_neg ha]
      apply min_eq_left
      have hval : j + 1 ≤ a.val := by omega
      have hle : M.b ⟨j + 1, hj⟩ ≤ M.b a :=
        M.sorted (Fin.le_def.mpr hval)
      exact TrackD.RankCore.testDeg_mono hBnn hspos.le
        (le_trans hτ.2.le hle)
  unfold TrackD.sigma TrackD.eScale
  simp_rw [hfactor]
  rw [Finset.prod_ite]
  congr 1
  have hcard : (Finset.univ.filter (fun x : Fin d => ¬ x.val < j + 1)).card =
      d - (j + 1) := by
    have hcomp : Finset.univ.filter (fun x : Fin d => ¬ x.val < j + 1) =
        Finset.univ.filter (fun x : Fin d => j + 1 ≤ x.val) := by
      apply Finset.filter_congr
      intro a _
      exact Nat.not_lt
    rw [hcomp]
    exact TrackD.RankCore.card_after (j + 1) (by omega)
  rw [Finset.prod_const, hcard]

theorem common_floor_ge_half {T : ℝ} (hT : 1 ≤ T) :
    T / 2 ≤ (⌊T⌋₊ : ℝ) := by
  have hT0 : 0 ≤ T := le_trans zero_le_one hT
  by_cases h2 : 2 ≤ T
  · have hfl : T - 1 ≤ (⌊T⌋₊ : ℝ) := by
      have hlt := Nat.lt_floor_add_one T
      linarith
    linarith
  · push Not at h2
    have hfl1 : (1 : ℝ) ≤ (⌊T⌋₊ : ℝ) := by
      have h1 : 1 ≤ ⌊T⌋₊ := Nat.le_floor (by simpa using hT)
      exact_mod_cast h1
    linarith

private theorem choose_succ_mul (E h : ℕ) :
    (E + (h + 1)).choose (h + 1) * (h + 1) =
      (E + h).choose h * (E + h + 1) := by
  have h1 : h ≤ E + h := Nat.le_add_left _ _
  have h2 : h + 1 ≤ E + (h + 1) := Nat.le_add_left _ _
  have hsub1 : (E + h) - h = E := by omega
  have hsub2 : (E + (h + 1)) - (h + 1) = E := by omega
  have e1 : (E + h).choose h * (Nat.factorial h * Nat.factorial E) =
      Nat.factorial (E + h) := by
    have e := Nat.choose_eq_factorial_div_factorial h1
    rw [hsub1] at e
    have dvd : Nat.factorial h * Nat.factorial E ∣ Nat.factorial (E + h) := by
      have := Nat.factorial_mul_factorial_dvd_factorial h1
      rwa [hsub1] at this
    rw [e]
    exact Nat.div_mul_cancel dvd
  have e2 : (E + (h + 1)).choose (h + 1) *
      (Nat.factorial (h + 1) * Nat.factorial E) =
      Nat.factorial (E + (h + 1)) := by
    have e := Nat.choose_eq_factorial_div_factorial h2
    rw [hsub2] at e
    have dvd : Nat.factorial (h + 1) * Nat.factorial E ∣ Nat.factorial (E + (h + 1)) := by
      have := Nat.factorial_mul_factorial_dvd_factorial h2
      rwa [hsub2] at this
    rw [e]
    exact Nat.div_mul_cancel dvd
  have f1 : Nat.factorial (E + (h + 1)) = (E + h + 1) * Nat.factorial (E + h) := by
    have heq : E + (h + 1) = (E + h) + 1 := by omega
    rw [heq, Nat.factorial_succ]
  have f2 : Nat.factorial (h + 1) = (h + 1) * Nat.factorial h := Nat.factorial_succ _
  have hC1pos : 0 < Nat.factorial h * Nat.factorial E :=
    Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  have hEq : (E + (h + 1)).choose (h + 1) * (h + 1) * (Nat.factorial h * Nat.factorial E) =
      (E + h).choose h * (E + h + 1) * (Nat.factorial h * Nat.factorial E) := by
    calc (E + (h + 1)).choose (h + 1) * (h + 1) * (Nat.factorial h * Nat.factorial E)
        = (E + (h + 1)).choose (h + 1) * ((h + 1) * (Nat.factorial h * Nat.factorial E)) := by
          ring
      _ = (E + (h + 1)).choose (h + 1) * (Nat.factorial (h + 1) * Nat.factorial E) := by
          rw [f2]; ring
      _ = Nat.factorial (E + (h + 1)) := e2
      _ = (E + h + 1) * Nat.factorial (E + h) := f1
      _ = (E + h + 1) * ((E + h).choose h * (Nat.factorial h * Nat.factorial E)) := by
          rw [← e1]
      _ = (E + h).choose h * (E + h + 1) * (Nat.factorial h * Nat.factorial E) := by
          ring
  exact Nat.mul_right_cancel hC1pos hEq

theorem common_choose_le_pow (E h : ℕ) :
    ((E + h).choose h : ℝ) ≤ ((E + 1 : ℕ) : ℝ) ^ h := by
  classical
  induction h generalizing E with
  | zero => simp
  | succ h ih =>
    have hnat : (E + (h + 1)).choose (h + 1) * (h + 1) =
        (E + h).choose h * (E + h + 1) := choose_succ_mul E h
    have hratio : ((((E + (h + 1)).choose (h + 1) : ℕ)) : ℝ) =
        ((((E + h).choose h : ℕ)) : ℝ) * (((E + h + 1 : ℕ)) : ℝ) /
          (((h + 1 : ℕ)) : ℝ) := by
      have hnatR : ((((E + (h + 1)).choose (h + 1) : ℕ)) : ℝ) *
          ((((h + 1 : ℕ))) : ℝ) =
          ((((E + h).choose h : ℕ)) : ℝ) * ((((E + h + 1 : ℕ))) : ℝ) := by
        exact_mod_cast hnat
      have hpos : (0 : ℝ) < ((((h + 1 : ℕ))) : ℝ) := by positivity
      rw [eq_div_iff hpos.ne']
      linarith [hnatR]
    have hle : ((((E + h + 1 : ℕ))) : ℝ) / ((((h + 1 : ℕ))) : ℝ) ≤
        ((((E + 1 : ℕ))) : ℝ) := by
      have hpos : (0 : ℝ) < ((((h + 1 : ℕ))) : ℝ) := by positivity
      rw [div_le_iff₀ hpos]
      have hexpand : ((((E + 1 : ℕ))) : ℝ) * ((((h + 1 : ℕ))) : ℝ) =
          ((E : ℕ) : ℝ) * ((h : ℕ) : ℝ) + ((h : ℕ) : ℝ) + ((E : ℕ) : ℝ) + 1 := by
        push_cast
        ring
      have hcast : ((((E + h + 1 : ℕ))) : ℝ) =
          ((E : ℕ) : ℝ) + ((h : ℕ) : ℝ) + 1 := by
        push_cast
        ring
      have hEi : (0 : ℝ) ≤ ((E : ℕ) : ℝ) * ((h : ℕ) : ℝ) :=
        mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      rw [hcast, hexpand]
      linarith
    calc ((((E + (h + 1)).choose (h + 1) : ℕ)) : ℝ)
        = ((((E + h).choose h : ℕ)) : ℝ) * (((E + h + 1 : ℕ)) : ℝ) /
            (((h + 1 : ℕ)) : ℝ) := hratio
      _ = ((((E + h).choose h : ℕ)) : ℝ) *
          (((((E + h + 1 : ℕ))) : ℝ) / ((((h + 1 : ℕ))) : ℝ)) := by ring
      _ ≤ ((E + 1 : ℕ) : ℝ) ^ h * (((E + 1 : ℕ))) :=
        mul_le_mul (ih E) hle (by positivity) (by positivity)
      _ = ((E + 1 : ℕ) : ℝ) ^ (h + 1) := by ring

theorem common_absorb_eventually {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} (M : CommonPoolProfile T)
    (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∀ᶠ i in atTop, C ≤ Real.exp (ε * M.s i) := by
  obtain ⟨s₀, hs₀⟩ := TrackD.RankCore.absorb_constant hC hε
  filter_upwards [M.width_grows.eventually_ge_atTop s₀] with i hi
  exact hs₀ _ hi

theorem commonLabelRank_zero_ge_one (d : ℕ) (i₀ : Fin d)
    (Γ : Finset (RPoint d × RPoint d)) (hne : Γ.Nonempty) :
    1 ≤ commonLabelRank i₀ Γ 0 := by
  classical
  let S : Set (Fin d ⊕ Fin d → ℂ) :=
    (fun pq : RPoint d × RPoint d =>
      TrackD.labelPt i₀ (TrackD.toC pq.1) (TrackD.toC pq.2)) '' (Γ : Set (RPoint d × RPoint d))
  have hRank : commonLabelRank i₀ Γ 0 = restrictionRank S 0 := rfl
  rw [hRank]
  have hneS : S.Nonempty := by
    obtain ⟨pq, hpq⟩ := hne
    exact ⟨_, Set.mem_image_of_mem _ (Finset.mem_coe.mpr hpq)⟩
  obtain ⟨z0, hz0⟩ := hneS
  let p0 : MvPolynomial.restrictTotalDegree (Fin d ⊕ Fin d) ℂ 0 :=
    ⟨MvPolynomial.C 1, (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr (by simp)⟩
  have himg : restrictionMap S 0 p0 ≠ 0 := by
    intro h0
    have h0z := congrFun h0 ⟨z0, hz0⟩
    have h1 : (1 : ℂ) = 0 := by simpa [restrictionMap, p0] using h0z
    exact one_ne_zero h1
  have hmem : restrictionMap S 0 p0 ∈ LinearMap.range (restrictionMap S 0) :=
    LinearMap.mem_range_self _ _
  have hpos : 0 < Module.finrank ℂ (LinearMap.range (restrictionMap S 0)) := by
    rw [Module.finrank_pos_iff_exists_ne_zero]
    refine ⟨⟨_, hmem⟩, ?_⟩
    intro hzero
    apply himg
    have hval := congrArg Subtype.val hzero
    simpa using hval
  unfold restrictionRank
  omega

/-- Equal-dimension final combination: `target ≤ lower·T^h`, `rank ≥ c·lower·e^{-(θ/2)s}·L^h`,
`L ≥ T/2`, `4^h/c ≤ e^{(θ/2)s}` give `target·e^{-θs} ≤ rank`. -/
theorem common_rank_equal_dim_final
    (lower T L : ℝ) (h : ℕ) (c θ s target rank : ℝ)
    (hlower_pos : 0 < lower) (hTpos : 0 < T)
    (hLge : T / 2 ≤ L)
    (htarg : target ≤ lower * T ^ h)
    (hlow : c * lower * Real.exp (-(θ / 2) * s) * L ^ h ≤ rank)
    (hcpos : 0 < c)
    (habs : 4 ^ h / c ≤ Real.exp ((θ / 2) * s)) :
    target * Real.exp (-θ * s) ≤ rank := by
  have hTnn : (0 : ℝ) ≤ T := hTpos.le
  have hLnn : (0 : ℝ) ≤ L := le_trans (by positivity) hLge
  have hexp_half : Real.exp (-(θ / 2) * s) * Real.exp (-(θ / 2) * s) =
      Real.exp (-θ * s) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h2h : (2 : ℝ) ^ h ≤ 4 ^ h :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hpos2 : (0 : ℝ) < (2 : ℝ) ^ h := by positivity
  have hpos4 : (0 : ℝ) < (4 : ℝ) ^ h := by positivity
  have hposE : (0 : ℝ) < Real.exp ((θ / 2) * s) := Real.exp_pos _
  have hpowL : (T / 2) ^ h ≤ L ^ h :=
    pow_le_pow_left₀ (by positivity) hLge _
  have hdiv : (T / 2) ^ h = T ^ h / 2 ^ h := div_pow _ _ _
  -- `1/exp ≤ c/4^h` from `4^h/c ≤ exp`.
  have hle : (1 : ℝ) / Real.exp ((θ / 2) * s) ≤ c / 4 ^ h := by
    rw [div_le_div_iff₀ hposE hpos4]
    have h2 : (4 : ℝ) ^ h ≤ Real.exp ((θ / 2) * s) * c := by
      rw [div_le_iff₀ hcpos] at habs
      linarith [habs]
    calc 1 * (4 : ℝ) ^ h = (4 : ℝ) ^ h := one_mul _
      _ ≤ Real.exp ((θ / 2) * s) * c := h2
      _ = c * Real.exp ((θ / 2) * s) := mul_comm _ _
  have hle2 : (1 : ℝ) / Real.exp ((θ / 2) * s) ≤ c / 2 ^ h := by
    calc 1 / Real.exp ((θ / 2) * s) ≤ c / 4 ^ h := hle
      _ ≤ c / 2 ^ h := by gcongr
  have hexp_neg : Real.exp (-(θ / 2) * s) = 1 / Real.exp ((θ / 2) * s) := by
    simp [neg_mul, Real.exp_neg]
  have hc2 : Real.exp (-(θ / 2) * s) ≤ c / 2 ^ h := by
    rw [hexp_neg]
    exact hle2
  -- Final chain.
  have hnn : (0 : ℝ) ≤ lower * T ^ h := by positivity
  have hexp_nonneg : (0 : ℝ) ≤ Real.exp (-(θ / 2) * s) := Real.exp_nonneg _
  have hpow_eq : (T / 2) ^ h = T ^ h / 2 ^ h := div_pow _ _ _
  calc target * Real.exp (-θ * s)
      ≤ lower * T ^ h * Real.exp (-θ * s) :=
        mul_le_mul_of_nonneg_right htarg (Real.exp_nonneg _)
    _ = lower * T ^ h * (Real.exp (-(θ / 2) * s) * Real.exp (-(θ / 2) * s)) := by
        rw [hexp_half]
    _ ≤ lower * T ^ h * (c / 2 ^ h * Real.exp (-(θ / 2) * s)) := by
        apply mul_le_mul_of_nonneg_left _ hnn
        apply mul_le_mul_of_nonneg_right hc2 hexp_nonneg
    _ = c * lower * Real.exp (-(θ / 2) * s) * (T ^ h / 2 ^ h) := by
        ring
    _ = c * lower * Real.exp (-(θ / 2) * s) * (T / 2) ^ h := by
        rw [hpow_eq]
    _ ≤ c * lower * Real.exp (-(θ / 2) * s) * L ^ h := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact hpowL
    _ ≤ rank := hlow

/-- Borrowing final combination when `T' ≥ 1`: `c·rank'·L^h ≤ rank·C`,
`rank' ≥ target'·e^{-(θ/4)s}`, `C ≤ (E+1)^h ≤ (2T')^h`, `L ≥ T/2`, `T ≥ T'`,
`h ≥ 2k+1`, `target ≤ target'·(T/T')^{2k+1}·e^{2dκs}`,
`e^{(3θ/4-2dκ)s} ≥ 4^h/c` give `target·e^{-θs} ≤ rank`. -/
theorem common_rank_borrow_ge_one
    (T T' L : ℝ) (E h k : ℕ) (d : ℕ) (c θ s κ target target' rank rank' : ℝ)
    (hTpos : 0 < T) (hT'pos : 0 < T') (hTge1 : 1 ≤ T) (hT'ge1 : 1 ≤ T')
    (hLge : T / 2 ≤ L) (hE1le : ((E + 1 : ℕ) : ℝ) ≤ 2 * T')
    (hTle : T' ≤ T) (hkh : 2 * k + 1 ≤ h) (hd2 : h ≤ 2 * d)
    (hchoose : ((E + h).choose h : ℝ) ≤ ((E + 1 : ℕ) : ℝ) ^ h)
    (hborrow : c * rank' * L ^ h ≤ rank * ((E + h).choose h : ℝ))
    (hprev : target' * Real.exp (-(θ / 4) * s) ≤ rank')
    (htarg_growth : target ≤ target' * (T / T') ^ (2 * k + 1) * Real.exp (2 * d * κ * s))
    (hcpos : 0 < c)
    (habs : 4 ^ h / c ≤ Real.exp ((3 * θ / 4 - 2 * d * κ) * s))
    (htarget_nn : 0 ≤ target') (hrank_nn : 0 ≤ rank')
    (hTnn' : 0 ≤ target) :
    target * Real.exp (-θ * s) ≤ rank := by
  have hTnn : (0 : ℝ) ≤ T := hTpos.le
  have hT'nn : (0 : ℝ) ≤ T' := hT'pos.le
  have hLpos : (0 : ℝ) < L := lt_of_lt_of_le (by positivity) hLge
  have hCpos : (0 : ℝ) < ((E + h).choose h : ℝ) := by
    have hposNat : 0 < (E + h).choose h := Nat.choose_pos (Nat.le_add_left _ _)
    exact_mod_cast hposNat
  have hTTpos : (0 : ℝ) < T / T' := div_pos hTpos hT'pos
  have hTTge1 : (1 : ℝ) ≤ T / T' := (le_div_iff₀ hT'pos).mpr (by simpa using hTle)
  have hpowTT : (T / T') ^ (2 * k + 1) ≤ (T / T') ^ h :=
    pow_le_pow_right₀ hTTge1 hkh
  have hE1pow : (((E + 1 : ℕ) : ℝ) ^ h) ≤ (2 * T') ^ h :=
    pow_le_pow_left₀ (by positivity) hE1le _
  have hCup : ((E + h).choose h : ℝ) ≤ (2 * T') ^ h :=
    hchoose.trans hE1pow
  have hpowL : (T / 2) ^ h ≤ L ^ h :=
    pow_le_pow_left₀ (by positivity) hLge _
  have hdivL : (T / 2) ^ h = T ^ h / 2 ^ h := div_pow _ _ _
  have hpos2 : (0 : ℝ) < (2 : ℝ) ^ h := by positivity
  have hpos4 : (0 : ℝ) < (4 : ℝ) ^ h := by positivity
  have h2h : (2 : ℝ) ^ h ≤ 4 ^ h :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  -- `L^h / C ≥ (T/T')^h / 4^h`? Since `L^h ≥ (T/2)^h = T^h/2^h` and `C ≤ (2T')^h = 2^h*T'^h`,
  -- so `L^h/C ≥ (T^h/2^h)/(2^h*T'^h) = (T/T')^h/4^h` (using `2^h*2^h = 4^h`).
  have h44 : (2 : ℝ) ^ h * 2 ^ h = 4 ^ h := by
    have h42 : (4 : ℝ) = 2 * 2 := by norm_num
    rw [h42, mul_pow]
  have hexp_add1 : Real.exp (-(θ / 4) * s) * Real.exp ((3 * θ / 4 - 2 * d * κ) * s) =
      Real.exp ((θ / 2 - 2 * d * κ) * s) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hexp_add2 : Real.exp ((θ / 2 - 2 * d * κ) * s) * Real.exp ((2 * d * κ) * s) =
      Real.exp ((θ / 2) * s) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hexp_split : Real.exp (-θ * s) =
      Real.exp (-(θ / 4) * s) * (Real.exp (-(θ / 4) * s) *
        (Real.exp (-(θ / 4) * s) * Real.exp (-(θ / 4) * s))) := by
    have h4 : (-θ : ℝ) * s = (-(θ / 4) * s) + (-(θ / 4) * s + (-(θ / 4) * s + -(θ / 4) * s)) := by
      ring
    rw [h4, Real.exp_add, Real.exp_add, Real.exp_add]
  -- `C > 0`, `L > 0`, etc.
  have hCpos' : (0 : ℝ) < ((E + h).choose h : ℝ) := hCpos
  have hLpos'' : (0 : ℝ) < L := hLpos
  have hexp4_pos : (0 : ℝ) < Real.exp (-(θ / 4) * s) := Real.exp_pos _
  have hT'ne : T' ≠ 0 := ne_of_gt hT'pos
  have hTne : T ≠ 0 := ne_of_gt hTpos
  have hLnn : (0 : ℝ) ≤ L := hLpos.le
  have hT'pow_pos1 : (0 : ℝ) < T' ^ (2 * k + 1) := pow_pos hT'pos _
  have hT'pow_nn1 : (0 : ℝ) ≤ T' ^ (2 * k + 1) := hT'pow_pos1.le
  have hTpow_nn : (0 : ℝ) ≤ T ^ (2 * k + 1) := pow_nonneg hTnn _
  have hRpow_nn : (0 : ℝ) ≤ (T / T') ^ (2 * k + 1) := pow_nonneg hTTpos.le _
  have hTp_le : T' ^ (h - (2 * k + 1)) ≤ T ^ (h - (2 * k + 1)) :=
    pow_le_pow_left₀ hT'nn hTle _
  have hhp : (2 * k + 1) + (h - (2 * k + 1)) = h := by omega
  have hTh_eq : T ^ h = T ^ (2 * k + 1) * T ^ (h - (2 * k + 1)) := by
    conv_lhs => rw [← hhp]
    rw [pow_add]
  have hT'h_eq : T' ^ h = T' ^ (2 * k + 1) * T' ^ (h - (2 * k + 1)) := by
    conv_lhs => rw [← hhp]
    rw [pow_add]
  have hRpow_eq : (T / T') ^ (2 * k + 1) = T ^ (2 * k + 1) / T' ^ (2 * k + 1) :=
    div_pow _ _ _
  have h2T'mul : (2 * T') ^ h = (2 : ℝ) ^ h * T' ^ h := mul_pow _ _ _
  have hTh_le : T ^ h ≤ L ^ h * (2 : ℝ) ^ h := by
    have hle := hpowL
    rw [hdivL] at hle
    exact (div_le_iff₀ hpos2).mp hle
  have hTh2 : T ^ h * (2 : ℝ) ^ h ≤ (4 : ℝ) ^ h * L ^ h := by
    calc T ^ h * (2 : ℝ) ^ h ≤ (L ^ h * (2 : ℝ) ^ h) * (2 : ℝ) ^ h :=
          mul_le_mul_of_nonneg_right hTh_le (le_of_lt hpos2)
      _ = L ^ h * ((2 : ℝ) ^ h * (2 : ℝ) ^ h) := by ring
      _ = L ^ h * (4 : ℝ) ^ h := by rw [h44]
      _ = (4 : ℝ) ^ h * L ^ h := mul_comm _ _
  have hmid_le : T ^ (2 * k + 1) * (2 : ℝ) ^ h * T' ^ (h - (2 * k + 1)) ≤
      (4 : ℝ) ^ h * L ^ h := by
    have h1 : T ^ (2 * k + 1) * (2 : ℝ) ^ h * T' ^ (h - (2 * k + 1)) ≤
        T ^ (2 * k + 1) * (2 : ℝ) ^ h * T ^ (h - (2 * k + 1)) :=
      mul_le_mul_of_nonneg_left hTp_le (mul_nonneg hTpow_nn (le_of_lt hpos2))
    have h2 : T ^ (2 * k + 1) * (2 : ℝ) ^ h * T ^ (h - (2 * k + 1)) =
        T ^ h * (2 : ℝ) ^ h := by
      rw [hTh_eq]; ring
    calc T ^ (2 * k + 1) * (2 : ℝ) ^ h * T' ^ (h - (2 * k + 1))
        ≤ T ^ (2 * k + 1) * (2 : ℝ) ^ h * T ^ (h - (2 * k + 1)) := h1
      _ = T ^ h * (2 : ℝ) ^ h := h2
      _ ≤ (4 : ℝ) ^ h * L ^ h := hTh2
  have hbig_le : T ^ (2 * k + 1) * (2 * T') ^ h ≤
      (4 : ℝ) ^ h * L ^ h * T' ^ (2 * k + 1) := by
    have h2T'h : (2 * T') ^ h = (2 : ℝ) ^ h * (T' ^ (2 * k + 1) * T' ^ (h - (2 * k + 1))) := by
      rw [h2T'mul, hT'h_eq]
    have heq1 : T ^ (2 * k + 1) * (2 * T') ^ h =
        T' ^ (2 * k + 1) * (T ^ (2 * k + 1) * (2 : ℝ) ^ h * T' ^ (h - (2 * k + 1))) := by
      rw [h2T'h]; ring
    have heq2 : (4 : ℝ) ^ h * L ^ h * T' ^ (2 * k + 1) =
        T' ^ (2 * k + 1) * ((4 : ℝ) ^ h * L ^ h) := by ring
    rw [heq1, heq2]
    exact mul_le_mul_of_nonneg_left hmid_le hT'pow_nn1
  have hTC_le : T ^ (2 * k + 1) * ((E + h).choose h : ℝ) ≤
      (4 : ℝ) ^ h * L ^ h * T' ^ (2 * k + 1) := by
    have hCup' : T ^ (2 * k + 1) * ((E + h).choose h : ℝ) ≤
        T ^ (2 * k + 1) * (2 * T') ^ h :=
      mul_le_mul_of_nonneg_left hCup hTpow_nn
    exact hCup'.trans hbig_le
  have hkey : (T / T') ^ (2 * k + 1) * ((E + h).choose h : ℝ) ≤ (4 : ℝ) ^ h * L ^ h := by
    have hR_eq : (T / T') ^ (2 * k + 1) * ((E + h).choose h : ℝ) =
        (T ^ (2 * k + 1) * ((E + h).choose h : ℝ)) / T' ^ (2 * k + 1) := by
      rw [hRpow_eq, div_mul_eq_mul_div]
    rw [hR_eq]
    exact (div_le_iff₀ hT'pow_pos1).mpr hTC_le
  have hEeq : Real.exp (2 * (d : ℝ) * κ * s) * Real.exp (-θ * s) =
      Real.exp (-(θ / 4) * s) * Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hexp_inv : Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s)) *
      Real.exp (((3 * θ / 4 - 2 * (d : ℝ) * κ) * s)) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have habs' : (4 : ℝ) ^ h ≤ c * Real.exp (((3 * θ / 4 - 2 * (d : ℝ) * κ) * s)) := by
    have habs_le := (div_le_iff₀ hcpos).mp habs
    calc (4 : ℝ) ^ h ≤ Real.exp (((3 * θ / 4 - 2 * (d : ℝ) * κ) * s)) * c := habs_le
      _ = c * Real.exp (((3 * θ / 4 - 2 * (d : ℝ) * κ) * s)) := mul_comm _ _
  have hE4_nn : (0 : ℝ) ≤ Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s)) :=
    Real.exp_nonneg _
  have hRE4_nn : (0 : ℝ) ≤ (T / T') ^ (2 * k + 1) *
      Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s)) :=
    mul_nonneg hRpow_nn hE4_nn
  have hRC_le : (T / T') ^ (2 * k + 1) * ((E + h).choose h : ℝ) *
      Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s)) ≤ c * L ^ h := by
    have h1 : (T / T') ^ (2 * k + 1) * ((E + h).choose h : ℝ) *
        Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s)) ≤
        (4 : ℝ) ^ h * L ^ h * Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s)) :=
      mul_le_mul_of_nonneg_right hkey hE4_nn
    have h2 : (4 : ℝ) ^ h * L ^ h * Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s)) ≤
        c * Real.exp (((3 * θ / 4 - 2 * (d : ℝ) * κ) * s)) * L ^ h *
        Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right habs' (pow_nonneg hLnn _)) hE4_nn
    have heq : c * Real.exp (((3 * θ / 4 - 2 * (d : ℝ) * κ) * s)) * L ^ h *
        Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s)) = c * L ^ h := by
      calc c * Real.exp (((3 * θ / 4 - 2 * (d : ℝ) * κ) * s)) * L ^ h *
            Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s))
          = c * L ^ h * (Real.exp (((3 * θ / 4 - 2 * (d : ℝ) * κ) * s)) *
            Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s))) := by ring
        _ = c * L ^ h * (Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s)) *
            Real.exp (((3 * θ / 4 - 2 * (d : ℝ) * κ) * s))) := by ring
        _ = c * L ^ h * 1 := by rw [hexp_inv]
        _ = c * L ^ h := mul_one _
    calc (T / T') ^ (2 * k + 1) * ((E + h).choose h : ℝ) *
          Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s))
        ≤ (4 : ℝ) ^ h * L ^ h * Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s)) := h1
      _ ≤ c * Real.exp (((3 * θ / 4 - 2 * (d : ℝ) * κ) * s)) * L ^ h *
          Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s)) := h2
      _ = c * L ^ h := heq
  have htarget_le1 : target * Real.exp (-θ * s) ≤
      (target' * (T / T') ^ (2 * k + 1) * Real.exp (2 * (d : ℝ) * κ * s)) *
      Real.exp (-θ * s) :=
    mul_le_mul_of_nonneg_right htarg_growth (Real.exp_nonneg _)
  have htarget_eq : (target' * (T / T') ^ (2 * k + 1) * Real.exp (2 * (d : ℝ) * κ * s)) *
      Real.exp (-θ * s) =
      (target' * Real.exp (-(θ / 4) * s)) * ((T / T') ^ (2 * k + 1) *
      Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s))) := by
    calc (target' * (T / T') ^ (2 * k + 1) * Real.exp (2 * (d : ℝ) * κ * s)) *
          Real.exp (-θ * s)
        = target' * (T / T') ^ (2 * k + 1) *
          (Real.exp (2 * (d : ℝ) * κ * s) * Real.exp (-θ * s)) := by ring
      _ = target' * (T / T') ^ (2 * k + 1) *
          (Real.exp (-(θ / 4) * s) * Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s))) := by
          rw [hEeq]
      _ = (target' * Real.exp (-(θ / 4) * s)) * ((T / T') ^ (2 * k + 1) *
          Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s))) := by ring
  have htarget_le2 : (target' * (T / T') ^ (2 * k + 1) * Real.exp (2 * (d : ℝ) * κ * s)) *
      Real.exp (-θ * s) ≤ rank' * ((T / T') ^ (2 * k + 1) *
      Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s))) := by
    rw [htarget_eq]
    exact mul_le_mul_of_nonneg_right hprev hRE4_nn
  have htarget_mid : target * Real.exp (-θ * s) ≤
      rank' * ((T / T') ^ (2 * k + 1) *
      Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s))) :=
    htarget_le1.trans htarget_le2
  have hfinal : rank' * ((T / T') ^ (2 * k + 1) *
      Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s))) ≤ rank := by
    have h1 : rank' * ((T / T') ^ (2 * k + 1) *
        Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s))) * ((E + h).choose h : ℝ) ≤
        rank * ((E + h).choose h : ℝ) := by
      have ha : rank' * ((T / T') ^ (2 * k + 1) *
          Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s))) * ((E + h).choose h : ℝ) =
          rank' * ((T / T') ^ (2 * k + 1) * ((E + h).choose h : ℝ) *
          Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s))) := by ring
      have hb : rank' * ((T / T') ^ (2 * k + 1) * ((E + h).choose h : ℝ) *
          Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s))) ≤ rank' * (c * L ^ h) :=
        mul_le_mul_of_nonneg_left hRC_le hrank_nn
      have hc : rank' * (c * L ^ h) = c * rank' * L ^ h := by ring
      calc rank' * ((T / T') ^ (2 * k + 1) *
            Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s))) * ((E + h).choose h : ℝ)
          = rank' * ((T / T') ^ (2 * k + 1) * ((E + h).choose h : ℝ) *
            Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s))) := ha
        _ ≤ rank' * (c * L ^ h) := hb
        _ = c * rank' * L ^ h := hc
        _ ≤ rank * ((E + h).choose h : ℝ) := hborrow
    exact le_of_mul_le_mul_right h1 hCpos
  exact htarget_mid.trans hfinal

/-- Borrowing final combination when `T' < 1` (`E = 0`, `C = 1`, `rank' ≥ 1`):
`c·L^h ≤ rank`, `target ≤ e^{2dκs}·T^{2k+1}`, `L ≥ T/2`, `T ≥ 1`, `h ≥ 2k+1`,
`h ≤ 2d`, `e^{(θ-2dκ)s} ≥ (2^{2d}/c)·T^{2k+1}/(T/2)^h` (via `hi_abs2` + `T ≥ 1`)
give `target·e^{-θs} ≤ rank`. Simplified to absorption of `4^(2d)/c` as in the
`T' ≥ 1` case with `(T/T')` replaced by `T` (since `T' < 1` implies `T/T' > T`). -/
theorem common_rank_borrow_lt_one
    (T L : ℝ) (h k : ℕ) (d : ℕ) (c θ s κ target rank : ℝ)
    (hTpos : 0 < T) (hTge1 : 1 ≤ T)
    (hLge : T / 2 ≤ L) (hkh : 2 * k + 1 ≤ h) (hd2 : h ≤ 2 * d)
    (hborrow0 : c * 1 * L ^ h ≤ rank * 1)
    (htarg0 : target ≤ Real.exp (2 * d * κ * s) * T ^ (2 * k + 1))
    (hcpos : 0 < c)
    (habs : 4 ^ h / c ≤ Real.exp ((3 * θ / 4 - 2 * d * κ) * s))
    (htarget_nn : 0 ≤ target) (hs : 0 ≤ s) (hθ : 0 ≤ θ) :
    target * Real.exp (-θ * s) ≤ rank := by
  have hTnn : (0 : ℝ) ≤ T := hTpos.le
  have hLpos : (0 : ℝ) < L := lt_of_lt_of_le (by positivity) hLge
  have hLnn : (0 : ℝ) ≤ L := hLpos.le
  have hpos2 : (0 : ℝ) < (2 : ℝ) ^ h := by positivity
  have hpos4 : (0 : ℝ) < (4 : ℝ) ^ h := by positivity
  have h2h : (2 : ℝ) ^ h ≤ 4 ^ h :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have h44 : (2 : ℝ) ^ h * 2 ^ h = 4 ^ h := by
    have h42 : (4 : ℝ) = 2 * 2 := by norm_num
    rw [h42, mul_pow]
  have hpowL : (T / 2) ^ h ≤ L ^ h :=
    pow_le_pow_left₀ (by positivity) hLge _
  have hdivL : (T / 2) ^ h = T ^ h / 2 ^ h := div_pow _ _ _
  have hTh_le : T ^ h ≤ L ^ h * (2 : ℝ) ^ h := by
    have hle := hpowL
    rw [hdivL] at hle
    exact (div_le_iff₀ hpos2).mp hle
  have hTh2 : T ^ h * (2 : ℝ) ^ h ≤ (4 : ℝ) ^ h * L ^ h := by
    calc T ^ h * (2 : ℝ) ^ h ≤ (L ^ h * (2 : ℝ) ^ h) * (2 : ℝ) ^ h :=
          mul_le_mul_of_nonneg_right hTh_le (le_of_lt hpos2)
      _ = L ^ h * ((2 : ℝ) ^ h * (2 : ℝ) ^ h) := by ring
      _ = L ^ h * (4 : ℝ) ^ h := by rw [h44]
      _ = (4 : ℝ) ^ h * L ^ h := mul_comm _ _
  have hTpow_le : T ^ (2 * k + 1) ≤ T ^ h := pow_le_pow_right₀ hTge1 hkh
  have hkey_lt : T ^ (2 * k + 1) ≤ (4 : ℝ) ^ h * L ^ h := by
    have h2h_le : L ^ h * (2 : ℝ) ^ h ≤ L ^ h * (4 : ℝ) ^ h :=
      mul_le_mul_of_nonneg_left h2h (pow_nonneg hLnn _)
    calc T ^ (2 * k + 1) ≤ T ^ h := hTpow_le
      _ ≤ L ^ h * (2 : ℝ) ^ h := hTh_le
      _ ≤ L ^ h * (4 : ℝ) ^ h := h2h_le
      _ = (4 : ℝ) ^ h * L ^ h := mul_comm _ _
  have hEeq : Real.exp (2 * (d : ℝ) * κ * s) * Real.exp (-θ * s) =
      Real.exp (-(θ / 4) * s) * Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hexp_inv : Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s)) *
      Real.exp (((3 * θ / 4 - 2 * (d : ℝ) * κ) * s)) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have habs' : (4 : ℝ) ^ h ≤ c * Real.exp (((3 * θ / 4 - 2 * (d : ℝ) * κ) * s)) := by
    have habs_le := (div_le_iff₀ hcpos).mp habs
    calc (4 : ℝ) ^ h ≤ Real.exp (((3 * θ / 4 - 2 * (d : ℝ) * κ) * s)) * c := habs_le
      _ = c * Real.exp (((3 * θ / 4 - 2 * (d : ℝ) * κ) * s)) := mul_comm _ _
  have hTpow_nn : (0 : ℝ) ≤ T ^ (2 * k + 1) := pow_nonneg hTnn _
  have hE4_nn : (0 : ℝ) ≤ Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s)) :=
    Real.exp_nonneg _
  have hθ4_nn : (0 : ℝ) ≤ θ / 4 := div_nonneg hθ (by norm_num)
  have hθs_nn : (0 : ℝ) ≤ (θ / 4) * s := mul_nonneg hθ4_nn hs
  have hE1_le : Real.exp (-(θ / 4) * s) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have heq : -(θ / 4) * s = -((θ / 4) * s) := by ring
    rw [heq]
    exact neg_nonpos.mpr hθs_nn
  have hTE4_nn : (0 : ℝ) ≤ T ^ (2 * k + 1) *
      Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s)) :=
    mul_nonneg hTpow_nn hE4_nn
  have hE1E4_le : T ^ (2 * k + 1) * Real.exp (-(θ / 4) * s) *
      Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s)) ≤
      T ^ (2 * k + 1) * Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s)) := by
    have hle : Real.exp (-(θ / 4) * s) * (T ^ (2 * k + 1) *
        Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s))) ≤
        1 * (T ^ (2 * k + 1) *
        Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s))) :=
      mul_le_mul_of_nonneg_right hE1_le hTE4_nn
    calc T ^ (2 * k + 1) * Real.exp (-(θ / 4) * s) *
          Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s))
        = Real.exp (-(θ / 4) * s) * (T ^ (2 * k + 1) *
          Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s))) := by ring
      _ ≤ 1 * (T ^ (2 * k + 1) *
          Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s))) := hle
      _ = T ^ (2 * k + 1) * Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s)) := one_mul _
  have hTE4_le : T ^ (2 * k + 1) *
      Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s)) ≤ c * L ^ h := by
    have h1 : T ^ (2 * k + 1) *
        Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s)) ≤
        (4 : ℝ) ^ h * L ^ h * Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s)) :=
      mul_le_mul_of_nonneg_right hkey_lt hE4_nn
    have h2 : (4 : ℝ) ^ h * L ^ h * Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s)) ≤
        c * Real.exp (((3 * θ / 4 - 2 * (d : ℝ) * κ) * s)) * L ^ h *
        Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right habs' (pow_nonneg hLnn _)) hE4_nn
    have heq : c * Real.exp (((3 * θ / 4 - 2 * (d : ℝ) * κ) * s)) * L ^ h *
        Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s)) = c * L ^ h := by
      calc c * Real.exp (((3 * θ / 4 - 2 * (d : ℝ) * κ) * s)) * L ^ h *
            Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s))
          = c * L ^ h * (Real.exp (((3 * θ / 4 - 2 * (d : ℝ) * κ) * s)) *
            Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s))) := by ring
        _ = c * L ^ h * (Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s)) *
            Real.exp (((3 * θ / 4 - 2 * (d : ℝ) * κ) * s))) := by ring
        _ = c * L ^ h * 1 := by rw [hexp_inv]
        _ = c * L ^ h := mul_one _
    calc T ^ (2 * k + 1) * Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s))
        ≤ (4 : ℝ) ^ h * L ^ h * Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s)) := h1
      _ ≤ c * Real.exp (((3 * θ / 4 - 2 * (d : ℝ) * κ) * s)) * L ^ h *
          Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s)) := h2
      _ = c * L ^ h := heq
  have hborrow0' : c * L ^ h ≤ rank := by simpa using hborrow0
  have htarget_le1 : target * Real.exp (-θ * s) ≤
      (Real.exp (2 * (d : ℝ) * κ * s) * T ^ (2 * k + 1)) * Real.exp (-θ * s) :=
    mul_le_mul_of_nonneg_right htarg0 (Real.exp_nonneg _)
  have htarget_eq : (Real.exp (2 * (d : ℝ) * κ * s) * T ^ (2 * k + 1)) *
      Real.exp (-θ * s) =
      T ^ (2 * k + 1) * Real.exp (-(θ / 4) * s) *
      Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s)) := by
    calc (Real.exp (2 * (d : ℝ) * κ * s) * T ^ (2 * k + 1)) * Real.exp (-θ * s)
        = T ^ (2 * k + 1) * (Real.exp (2 * (d : ℝ) * κ * s) * Real.exp (-θ * s)) := by
          ring
      _ = T ^ (2 * k + 1) * (Real.exp (-(θ / 4) * s) *
          Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s))) := by rw [hEeq]
      _ = T ^ (2 * k + 1) * Real.exp (-(θ / 4) * s) *
          Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s)) := by ring
  have htarget_mid : target * Real.exp (-θ * s) ≤
      T ^ (2 * k + 1) * Real.exp (-(θ / 4) * s) *
      Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s)) := by
    calc target * Real.exp (-θ * s)
        ≤ (Real.exp (2 * (d : ℝ) * κ * s) * T ^ (2 * k + 1)) * Real.exp (-θ * s) :=
          htarget_le1
      _ = T ^ (2 * k + 1) * Real.exp (-(θ / 4) * s) *
          Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s)) := htarget_eq
  have htarget_le : T ^ (2 * k + 1) * Real.exp (-(θ / 4) * s) *
      Real.exp (-((3 * θ / 4 - 2 * (d : ℝ) * κ) * s)) ≤ c * L ^ h :=
    hE1E4_le.trans hTE4_le
  exact htarget_mid.trans (htarget_le.trans hborrow0')

/-- Initial sigma factorization: for `τ < b₀`, every `min (T, D_a) = T`,
so `σ = T^d`. -/
theorem common_sigma_initial_eq {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} (M : CommonPoolProfile T) (τ : ℝ)
    (hτ : τ < M.b ⟨0, by have := regime.dimension_ge_three; omega⟩) (i : ℕ) :
    TrackD.sigma (regime.B i) (M.s i) M.b τ =
      (TrackD.testDeg (regime.B i) (M.s i) τ) ^ d := by
  classical
  have hspos := M.width_pos i
  have hBnn := (regime.B_pos i).le
  have hle : ∀ a : Fin d, τ ≤ M.b a := by
    intro a
    have h0le : (⟨0, by have := regime.dimension_ge_three; omega⟩ : Fin d) ≤ a :=
      Fin.le_def.mpr (Nat.zero_le _)
    have hba : M.b ⟨0, by have := regime.dimension_ge_three; omega⟩ ≤ M.b a :=
      M.sorted h0le
    exact le_of_lt (lt_of_lt_of_le hτ hba)
  have hfactor : ∀ a : Fin d,
      min (TrackD.testDeg (regime.B i) (M.s i) τ)
        (TrackD.cutScale (regime.B i) (M.s i) M.b a) =
        TrackD.testDeg (regime.B i) (M.s i) τ := by
    intro a
    apply min_eq_left
    exact TrackD.RankCore.testDeg_mono hBnn hspos.le (hle a)
  unfold TrackD.sigma
  simp_rw [hfactor]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Initial plateau margin: `τ` lies on the `0`-plateau with margin
`(b₀-τ)/2`. -/
theorem common_initial_OnPlateau {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} (M : CommonPoolProfile T) (τ : ℝ)
    (hτ : τ < M.b ⟨0, by have := regime.dimension_ge_three; omega⟩) :
    TrackD.OnPlateau M.b 0 ((M.b ⟨0, by have := regime.dimension_ge_three; omega⟩ - τ) / 2) τ := by
  intro a
  constructor
  · intro hlt
    omega
  · intro _
    have h0le : (⟨0, by have := regime.dimension_ge_three; omega⟩ : Fin d) ≤ a :=
      Fin.le_def.mpr (Nat.zero_le _)
    have hba : M.b ⟨0, by have := regime.dimension_ge_three; omega⟩ ≤ M.b a :=
      M.sorted h0le
    linarith

/-- Zero-cut carriers: every pool point can be assigned the whole space,
which is a carrier of the empty (`0`-cut) system and contains the point. -/
theorem common_zero_carrier_assignment (pl : Finset (TrackD.Piece d)) :
    ∃ α : TrackD.Pt d → AffineVariety d, TrackD.CarrierAssignment pl 0 α := by
  classical
  have hrad : (⊥ : Ideal (Poly d)).IsRadical :=
    (inferInstance : (⊥ : Ideal (Poly d)).IsPrime).isRadical
  refine ⟨fun _ => ⟨⊥, hrad⟩, ?_⟩
  intro X hX p hp
  constructor
  · show (⟨⊥, hrad⟩ : AffineVariety d).ideal ∈ (X.path.system 0).minimalPrimes
    have hs : X.path.system 0 = ⊥ := by simp [TrackD.CutPath.system]
    rw [hs, Ideal.minimalPrimes_eq_subsingleton_self]
    rfl
  · show TrackD.toC p ∈ (⟨⊥, hrad⟩ : AffineVariety d).points
    intro f hf
    rw [Ideal.mem_bot.mp hf]
    simp

/-- Choose lower bound: `L^h ≤ h! * (L+h).choose h` in `ℕ`
(via `choose_succ_mul`, dual to `common_choose_le_pow`). -/
theorem common_pow_le_factorial_mul_choose (L h : ℕ) :
    L ^ h ≤ Nat.factorial h * (L + h).choose h := by
  induction h generalizing L with
  | zero => simp
  | succ h ih =>
    have hnat : (L + (h + 1)).choose (h + 1) * (h + 1) =
        (L + h).choose h * (L + h + 1) := choose_succ_mul L h
    have hfac : Nat.factorial (h + 1) = (h + 1) * Nat.factorial h :=
      Nat.factorial_succ _
    have hpow : L ^ (h + 1) = L ^ h * L := pow_succ _ _
    have hge : L ≤ L + h + 1 := by omega
    -- Work in ℕ directly via `hnat` to avoid division.
    have hEq : Nat.factorial (h + 1) * (L + (h + 1)).choose (h + 1) =
        Nat.factorial h * (L + h).choose h * (L + h + 1) := by
      calc Nat.factorial (h + 1) * (L + (h + 1)).choose (h + 1)
          = ((h + 1) * Nat.factorial h) * (L + (h + 1)).choose (h + 1) := by
            rw [hfac]
        _ = Nat.factorial h * ((L + (h + 1)).choose (h + 1) * (h + 1)) := by ring
        _ = Nat.factorial h * ((L + h).choose h * (L + h + 1)) := by rw [hnat]
        _ = Nat.factorial h * (L + h).choose h * (L + h + 1) := by ring
    have hle : L ^ h * L ≤ Nat.factorial h * (L + h).choose h * (L + h + 1) :=
      (mul_le_mul_of_nonneg_right (ih L) (Nat.zero_le _)).trans
        (mul_le_mul_of_nonneg_left (Nat.le_add_right L (h + 1)) (Nat.zero_le _))
    calc L ^ (h + 1) = L ^ h * L := hpow
      _ ≤ Nat.factorial h * (L + h).choose h * (L + h + 1) := hle
      _ = Nat.factorial (h + 1) * (L + (h + 1)).choose (h + 1) := hEq.symm

private lemma finsupp_sum_id_eq_sum_self_aux {σ : Type*} [Fintype σ] (f : σ →₀ ℕ) :
    f.sum (fun _ e => e) = f.sum (fun _ => id) := by
  rw [Finsupp.sum_fintype _ _ (by simp), Finsupp.sum_fintype _ _ (by simp)]
  simp

private lemma finite_restrictTotalDegreeExponents_aux (σ : Type*) [Fintype σ] (D : ℕ) :
    Finite {m : σ →₀ ℕ // m.sum (fun _ e => e) ≤ D} := by
  classical
  have hbounded : Finite {m : σ →₀ ℕ // ∀ a, m a ≤ D} :=
    ((Set.Finite.pi' fun _ => Set.finite_le_nat D).preimage
      DFunLike.coe_injective.injOn).to_subtype
  letI : Finite {m : σ →₀ ℕ // ∀ a, m a ≤ D} := hbounded
  refine Finite.of_injective (fun m : {m : σ →₀ ℕ // m.sum (fun _ e => e) ≤ D} =>
    (⟨m.1, fun a => ?_⟩ : {m : σ →₀ ℕ // ∀ a, m a ≤ D})) ?_
  · by_cases ha : m.1 a = 0
    · exact ha ▸ Nat.zero_le _
    · exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finsupp.mem_support_iff.mpr ha)).trans m.2
  · intro a b h
    apply Subtype.ext
    exact congrArg (fun x : {m : σ →₀ ℕ // ∀ a, m a ≤ D} => x.1) h

theorem common_finrank_restrictTotalDegree_eq_choose (σ : Type*) [Fintype σ]
    [DecidableEq σ] (D : ℕ) :
    Module.finrank ℂ (MvPolynomial.restrictTotalDegree σ ℂ D) =
      Nat.choose (D + Fintype.card σ) (Fintype.card σ) := by
  classical
  let S : Set (σ →₀ ℕ) := {m | m.sum (fun _ e => e) ≤ D}
  have hfinite := finite_restrictTotalDegreeExponents_aux σ D
  letI : Finite S := by
    change Finite {m : σ →₀ ℕ // m.sum (fun _ e => e) ≤ D}
    exact hfinite
  letI : Fintype S := Fintype.ofFinite S
  letI : Fintype {m : σ →₀ ℕ // m.sum (fun _ e => e) ≤ D} := Fintype.ofFinite _
  have hdim : Module.finrank ℂ (MvPolynomial.restrictTotalDegree σ ℂ D) =
      Fintype.card {m : σ →₀ ℕ // m.sum (fun _ e => e) ≤ D} := by
    change Module.finrank ℂ (MvPolynomial.restrictSupport ℂ S) = _
    rw [Module.finrank_eq_card_basis (MvPolynomial.basisRestrictSupport ℂ S)]
    rfl
  let E := {m : σ →₀ ℕ // m.sum (fun _ e => e) ≤ D}
  let total (m : E) : Fin (D + 1) := ⟨m.1.sum (fun _ e => e), Nat.lt_succ_of_le m.2⟩
  let fiberEquiv (k : Fin (D + 1)) : {m : E // total m = k} ≃
      {m : σ →₀ ℕ // m.sum (fun _ => id) = k.val} := {
    toFun := fun m => ⟨m.1.1, by
      have h := congrArg Fin.val m.2
      exact (finsupp_sum_id_eq_sum_self_aux m.1.1).symm.trans h⟩
    invFun := fun m => ⟨⟨m.1, by
      have hsum : m.1.sum (fun _ e => e) = k.val :=
        (finsupp_sum_id_eq_sum_self_aux m.1).trans m.2
      rw [hsum]
      exact Nat.lt_succ_iff.mp k.isLt⟩, by
      apply Fin.ext
      have hsum : m.1.sum (fun _ e => e) = k.val :=
        (finsupp_sum_id_eq_sum_self_aux m.1).trans m.2
      exact hsum⟩
    left_inv := by intro m; apply Subtype.ext; apply Subtype.ext; rfl
    right_inv := by intro m; apply Subtype.ext; rfl
  }
  let F := (Equiv.sigmaFiberEquiv total).symm
  letI : Finite E := hfinite
  letI : Fintype E := Fintype.ofFinite E
  letI : ∀ k : Fin (D + 1), Fintype {m : E // total m = k} := fun _ => Fintype.ofFinite _
  have hcard : Fintype.card E = Nat.choose (D + Fintype.card σ) (Fintype.card σ) := by
    calc
      Fintype.card E = ∑ k : Fin (D + 1),
          Fintype.card {m : E // total m = k} := by
        rw [Fintype.card_congr F, Fintype.card_sigma]
      _ = ∑ k : Fin (D + 1), Nat.multichoose (Fintype.card σ) k.val := by
        congr 1
        funext k
        letI : Finite {P : σ →₀ ℕ // P.sum (fun _ => id) = k.val} := by
          apply Finite.of_injective (fiberEquiv k).symm
          exact Equiv.injective (fiberEquiv k).symm
        letI : Fintype {P : σ →₀ ℕ // P.sum (fun _ => id) = k.val} := Fintype.ofFinite _
        rw [Fintype.card_congr (fiberEquiv k)]
        rw [Fintype.card_congr (Sym.equivNatSum σ k.val).symm]
        simp [Sym.card_sym_eq_multichoose]
      _ = ∑ k ∈ Finset.range (D + 1), Nat.multichoose (Fintype.card σ) k := by
        rw [← Fin.sum_univ_eq_sum_range]
      _ = Nat.choose (D + Fintype.card σ) (Fintype.card σ) := by
        rw [Nat.sum_range_multichoose]
  rw [hdim]
  exact hcard

end
end DistinctDistances.SparseCones
