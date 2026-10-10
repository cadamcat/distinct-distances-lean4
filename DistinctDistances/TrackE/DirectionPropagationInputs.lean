import DistinctDistances.TrackE.DirectionRank
import DistinctDistances.TrackE.InitialNoCapture
import Mathlib.Data.Nat.Choose.Bounds

/-! Initial direction rank, floor losses and strict limiting-profile margins
consumed by `sc:separated-rank`, sparse-cones.tex:711–781. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- The exact limiting-profile target σ(b)T_s(b)/A. -/
def profileDirectionRankTarget (S : LimitingSeparatedProfile regime) (i : ℕ) (b : ℝ) : ℝ :=
  TrackD.sigma (regime.B i) (S.sequence.target i).width S.b b *
    TrackD.testDeg (regime.B i) (S.sequence.target i).width b / regime.A i

/-- Every nonfinal positive-dimensional plateau is eligible. On the final
curve plateau the strict-rank argument applies to wider centers. -/
def StrictPlateauEligible (S : LimitingSeparatedProfile regime) (u : ProfilePlateau S) : Prop :=
  u.val.val + 1 < d ∨ Tendsto (fun i => (S.sequence.target i).width /
    (S.sequence.source i).width) atTop (𝓝 0)

/-- The three literal endpoint logarithms in sc:strict-margins, with paper
cut indices translated to zero-based Fin d indices. -/
def profileRateEndpointLog (S : LimitingSeparatedProfile regime) (u : ProfilePlateau S)
    (kind : DepthRateKind) : ℝ :=
  match kind with
  | .first => S.b ⟨0, by have := regime.dimension_ge_three; omega⟩ + S.b u.val
  | .narrow => -∑ t ∈ (Finset.univ : Finset (Fin d)).filter
      (fun t => u.val.val < t.val), S.b t
  | .wide => S.b u.val - 2

/-- Choose a fixed positive initial plateau margin before testing any later
row or center, and transfer it to the actual target path. -/
theorem target_initial_plateau_margin (S : LimitingSeparatedProfile regime) (τ : ℝ)
    (hτ : τ < S.b ⟨0, by have := regime.dimension_ge_three; omega⟩) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ᶠ i in atTop,
      TrackD.OnPlateau (S.sequence.target i).path.time 0 ξ τ := by
  have hd3 := regime.dimension_ge_three
  let b0 : ℝ := S.b ⟨0, by omega⟩
  have hb0_eq : b0 = S.b ⟨0, by have := regime.dimension_ge_three; omega⟩ := rfl
  have hτ' : τ < b0 := by rw [hb0_eq]; exact hτ
  refine ⟨(b0 - τ) / 2, by linarith, ?_⟩
  have hgap : ∀ t : Fin d, τ + (b0 - τ) / 2 < S.b t := by
    intro t
    have h0le : (⟨0, by omega⟩ : Fin d) ≤ t := Fin.le_def.mpr (Nat.zero_le _)
    have hle : b0 ≤ S.b t := S.sorted h0le
    linarith
  have hev : ∀ t : Fin d, ∀ᶠ i in atTop,
      τ + (b0 - τ) / 2 ≤ (S.sequence.target i).path.time t := by
    intro t
    exact Filter.Tendsto.eventually_const_le (hgap t) (S.target_limit t)
  have hall : ∀ᶠ i in atTop, ∀ t ∈ (Finset.univ : Finset (Fin d)),
      τ + (b0 - τ) / 2 ≤ (S.sequence.target i).path.time t :=
    Framework.eventually_finite _ _ (fun t _ => hev t)
  filter_upwards [hall] with i hi
  intro t
  constructor
  · intro hlt
    omega
  · intro _
    have h := hi t (Finset.mem_univ _)
    linarith [h]

/-- A nonzero homogeneous direction polynomial has a nonzero physical
pullback of the same degree bound, uniformly over all complex centers. -/
theorem nonzero_direction_pullback {L : ℕ} (p : Point d) (f : Poly d)
    (hf : f.IsHomogeneous L) (hfnz : f ≠ 0) :
    ∃ g : Poly d, g.totalDegree ≤ L ∧ g ≠ 0 ∧
      ∀ x : Point d, MvPolynomial.eval x g = MvPolynomial.eval (x - p) f := by
  obtain ⟨g, hg_deg, _, hg_eval⟩ :=
    Request.bounded_radial_pullback p AffineVariety.whole f hf
  refine ⟨g, hg_deg, ?_, hg_eval⟩
  intro hg0
  have hvanish : ∀ y : Point d, MvPolynomial.eval y f = 0 := by
    intro y
    have hx := hg_eval (y + p)
    have hsub : (y + p) - p = y := by simp
    rw [hsub] at hx
    have hzero : MvPolynomial.eval (y + p) g = 0 := by
      rw [hg0]
      simp
    rw [hzero] at hx
    exact hx.symm
  have hfone : f = 0 := hf.eq_zero_of_forall_eval_eq_zero hvanish
  exact hfnz hfone

/-- If the degree-L envelope kernel is zero, its homogeneous restriction
space is the full degree-L space. This includes degree zero. -/
theorem row_direction_rank_full (hd : 1 ≤ d) (p : Point d)
    (Q : Finset (RPoint d)) (L : ℕ)
    (hzero : ∀ f : Poly d, f.IsHomogeneous L →
      f ∈ (rowDirectionEnvelope p Q L).ideal → f = 0) :
    rowDirectionRank p Q L = (L + (d - 1)).choose (d - 1) := by
  classical
  let V := rowDirectionEnvelope p Q L
  have hEnv : V.hilbert L = rowDirectionRank p Q L :=
    row_direction_rank_envelope p Q L
  rw [← hEnv]
  -- Reduce to finrank of the envelope quotient section.
  have hBot : Module.finrank ℂ
      (OAI.PiExponentJets.W64.quotientSection (⊥ : Ideal (Poly d)) L) =
      (L + (d - 1)).choose (d - 1) := by
    have h1 := OAI.PiExponentJets.W64.quotientSection_bot_finrank_multichoose
      (σ := Fin d) (k := ℂ) L
    rw [Fintype.card_fin] at h1
    rw [Nat.multichoose_eq] at h1
    have hadd : d + L - 1 = L + (d - 1) := by omega
    rw [hadd] at h1
    have hsymm : (L + (d - 1)).choose L = (L + (d - 1)).choose (d - 1) :=
      Nat.choose_symm_add
    rw [hsymm] at h1
    -- h1 : finrank bot = (L+(d-1)).choose (d-1); need to rewrite goal which is same
    -- The goal's LHS is finrank bot, RHS is choose; h1 is exactly that after rewrites?
    -- Actually h1 after rewrites is finrank bot = choose (d-1); that's the goal.
    exact h1
  -- Bijective factor from bot to V.
  let I := V.ideal
  have hIJ : (⊥ : Ideal (Poly d)) ≤ I := bot_le
  let φ := OAI.PiExponentJets.W64.quotientSectionFactor
    (⊥ : Ideal (Poly d)) I hIJ L
  have hsurj : Function.Surjective φ :=
    OAI.PiExponentJets.W64.quotientSectionFactor_surjective _ _ hIJ L
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot]
    apply le_antisymm _ bot_le
    intro x hx
    have hxv : φ x = 0 := LinearMap.mem_ker.mp hx
    have hval : (Ideal.Quotient.factorₐ ℂ hIJ) x.1 = 0 := congrArg Subtype.val hxv
    obtain ⟨q, hq, hqx⟩ := Submodule.mem_map.mp x.2
    have hqx' : (Ideal.Quotient.mkₐ ℂ (⊥ : Ideal (Poly d))).toLinearMap q = x.1 := hqx
    have hmem : q ∈ I := by
      have h0 : (Ideal.Quotient.factorₐ ℂ hIJ)
          ((Ideal.Quotient.mkₐ ℂ (⊥ : Ideal (Poly d))).toLinearMap q) = 0 := by
        rw [hqx']
        exact hval
      have hmk : (Ideal.Quotient.mkₐ ℂ I) q = 0 := by
        have h1 : ((Ideal.Quotient.factorₐ ℂ hIJ).comp
          (Ideal.Quotient.mkₐ ℂ (⊥ : Ideal (Poly d)))) q = 0 := by
          rw [AlgHom.comp_apply]
          exact h0
        rw [Ideal.Quotient.factorₐ_comp_mk] at h1
        exact h1
      have : Ideal.Quotient.mk I q = 0 := by
        simpa only [Ideal.Quotient.mkₐ_eq_mk] using hmk
      exact Ideal.Quotient.eq_zero_iff_mem.mp this
    have hhom : q.IsHomogeneous L := (MvPolynomial.mem_homogeneousSubmodule L q).mp hq
    have hq0 : q = 0 := hzero q hhom hmem
    have hx1 : x.1 = 0 := by
      rw [← hqx']
      rw [hq0]
      simp
    exact Subtype.ext hx1
  let e := LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩
  have hfin : Module.finrank ℂ
      (OAI.PiExponentJets.W64.quotientSection I L) =
      Module.finrank ℂ
        (OAI.PiExponentJets.W64.quotientSection (⊥ : Ideal (Poly d)) L) :=
    e.finrank_eq.symm
  -- V.hilbert is finrank of its quotient section by definition.
  have hV : V.hilbert L = Module.finrank ℂ
      (OAI.PiExponentJets.W64.quotientSection I L) := rfl
  rw [hV, hfin]
  exact hBot

/-- On the initial interval σ=T^d and A=B². Half the exponent margin
-2τ survives the fixed floor and factorial costs in the full rank. -/
theorem initial_profile_rank_margin (S : LimitingSeparatedProfile regime) (τ : ℝ)
    (hτ : τ < S.b ⟨0, by have := regime.dimension_ge_three; omega⟩) :
    ∀ᶠ i in atTop,
      profileDirectionRankTarget S i τ * Real.exp ((-τ) * (S.sequence.target i).width) ≤
        ( (⌊TrackD.testDeg (TrackD.cfgB (regime.P i))
          (S.sequence.target i).width τ⌋₊ + (d - 1)).choose (d - 1) : ℝ) := by
  classical
  have hd3 := regime.dimension_ge_three
  have hd1 : 1 ≤ d := by omega
  let b0 : ℝ := S.b ⟨0, by omega⟩
  have hb0_eq : b0 = S.b ⟨0, by have := regime.dimension_ge_three; omega⟩ := rfl
  have hτ' : τ < b0 := by rw [hb0_eq]; exact hτ
  obtain ⟨c, hcpos, hb0_le, _, _⟩ := S.balance
  have hb0_neg : b0 < 0 := by linarith
  have hτ_neg : τ < 0 := lt_trans hτ' hb0_neg
  have hξpos : 0 < (b0 - τ) / 2 := by linarith
  -- OnPlateau for the limiting profile itself.
  have hplat : TrackD.OnPlateau S.b 0 ((b0 - τ) / 2) τ := by
    intro t
    constructor
    · intro hlt
      omega
    · intro _
      have h0le : (⟨0, by omega⟩ : Fin d) ≤ t := Fin.le_def.mpr (Nat.zero_le _)
      have hle : b0 ≤ S.b t := S.sorted h0le
      linarith
  -- Exponential decay of exp(τs).
  have hwidth_grows := S.sequence.target_grows
  have hτw_bot : Tendsto (fun i => τ * (S.sequence.target i).width) atTop atBot :=
    (tendsto_const_mul_atBot_of_neg hτ_neg).mpr hwidth_grows
  have hexp_tend : Tendsto (fun i => Real.exp (τ * (S.sequence.target i).width))
      atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hτw_bot
  have hfact_pos : 0 < ((Nat.factorial (d - 1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  have hCpos : 0 < 1 / ((Nat.factorial (d - 1) : ℕ) : ℝ) :=
    one_div_pos.mpr hfact_pos
  have hexp_ev : ∀ᶠ i in atTop,
      Real.exp (τ * (S.sequence.target i).width) ≤
        1 / ((Nat.factorial (d - 1) : ℕ) : ℝ) := by
    have hmem : Set.Iio (1 / ((Nat.factorial (d - 1) : ℕ) : ℝ)) ∈ 𝓝 (0 : ℝ) :=
      Iio_mem_nhds hCpos
    filter_upwards [hexp_tend.eventually hmem] with i hi
    exact le_of_lt hi
  -- Combine with the pointwise sigma identity and choose lower bound.
  filter_upwards [hexp_ev] with i hi
  -- Setup per-index data.
  let B := regime.B i
  let w := (S.sequence.target i).width
  let T := TrackD.testDeg B w τ
  have hBpos : 0 < B := regime.B_pos i
  have hBnonneg : 0 ≤ B := le_of_lt hBpos
  have hwpos : 0 < w := (S.sequence.width_pos i).2
  have hwnonneg : 0 ≤ w := le_of_lt hwpos
  have hBne : B ≠ 0 := ne_of_gt hBpos
  have hTpos : 0 < T := TrackD.RankCore.testDeg_pos hBpos w τ
  have hTnonneg : 0 ≤ T := le_of_lt hTpos
  have hBeq : B = TrackD.cfgB (regime.P i) := rfl
  have hTdef : T = B * Real.exp (τ * w) := rfl
  have hA : regime.A i = B ^ 2 := regime.A_eq_B_sq i
  -- Sigma is T^d on the initial plateau (limiting profile).
  have hsigma : TrackD.sigma B w S.b τ = T ^ d :=
    TrackD.RankCore.plateau_zero_sigma B w τ hBnonneg hwnonneg S.b
      ((b0 - τ) / 2) (le_of_lt hξpos) hplat
  -- Unfold the target.
  have htarget : profileDirectionRankTarget S i τ = T ^ d * T / regime.A i := by
    unfold profileDirectionRankTarget
    rw [hsigma]
  have hLHS_eq : profileDirectionRankTarget S i τ * Real.exp ((-τ) * w) =
      T ^ (d - 1) * Real.exp (τ * w) := by
    have hB2ne : B ^ 2 ≠ 0 := pow_ne_zero 2 hBne
    have hadd : (d - 1) + 2 = d + 1 := by omega
    have hpow_eq : T ^ d * T = T ^ (d - 1) * T ^ 2 := by
      calc T ^ d * T = T ^ (d + 1) := (pow_succ T d).symm
        _ = T ^ ((d - 1) + 2) := by rw [hadd]
        _ = T ^ (d - 1) * T ^ 2 := pow_add T (d - 1) 2
    have hT2 : T ^ 2 / B ^ 2 * Real.exp ((-τ) * w) = Real.exp (τ * w) := by
      rw [hTdef, mul_pow]
      have hcancel : (B ^ 2 * (Real.exp (τ * w)) ^ 2) / B ^ 2 =
          (Real.exp (τ * w)) ^ 2 := by field_simp
      rw [hcancel]
      rw [pow_two]
      have h1 : Real.exp (τ * w) * Real.exp (τ * w) * Real.exp ((-τ) * w) =
          Real.exp (τ * w) * (Real.exp (τ * w) * Real.exp ((-τ) * w)) := by ring
      rw [h1]
      have h2 : Real.exp (τ * w) * Real.exp ((-τ) * w) = 1 := by
        rw [← Real.exp_add]
        have heq : τ * w + (-τ) * w = 0 := by ring
        rw [heq, Real.exp_zero]
      rw [h2, mul_one]
    calc profileDirectionRankTarget S i τ * Real.exp ((-τ) * w)
        = (T ^ d * T / B ^ 2) * Real.exp ((-τ) * w) := by
          rw [htarget, hA]
      _ = (T ^ d * T * Real.exp ((-τ) * w)) / B ^ 2 := by
          rw [div_mul_eq_mul_div]
      _ = ((T ^ (d - 1) * T ^ 2) * Real.exp ((-τ) * w)) / B ^ 2 := by
          rw [hpow_eq]
      _ = T ^ (d - 1) * ((T ^ 2 * Real.exp ((-τ) * w)) / B ^ 2) := by
          rw [mul_assoc, mul_div_assoc]
      _ = T ^ (d - 1) * (T ^ 2 / B ^ 2 * Real.exp ((-τ) * w)) := by
          rw [← div_mul_eq_mul_div]
      _ = T ^ (d - 1) * Real.exp (τ * w) := by rw [hT2]
  rw [hLHS_eq]
  -- Lower bound for the choose RHS.
  let F := ⌊TrackD.testDeg (TrackD.cfgB (regime.P i)) w τ⌋₊
  have hFeq : F = ⌊T⌋₊ := rfl
  have hTle : T ≤ (F : ℝ) + 1 := by
    rw [hFeq]
    exact le_of_lt (Nat.lt_floor_add_one T)
  have hpow_le : T ^ (d - 1) ≤ ((F : ℝ) + 1) ^ (d - 1) :=
    pow_le_pow_left₀ hTnonneg hTle _
  have hchoose_ge : ((F : ℝ) + 1) ^ (d - 1) / ((Nat.factorial (d - 1) : ℕ) : ℝ) ≤
      ((F + (d - 1)).choose (d - 1) : ℝ) := by
    have h := Nat.pow_le_choose (α := ℝ) (d - 1) (F + (d - 1))
    have heq : F + (d - 1) + 1 - (d - 1) = F + 1 := by omega
    rw [heq] at h
    have hcast : ((F + 1 : ℕ) : ℝ) = (F : ℝ) + 1 := by
      simp [Nat.cast_add, Nat.cast_one]
    rw [hcast] at h
    exact h
  -- Final combination: T^{d-1}*exp ≤ T^{d-1}/fact ≤ ((F+1)^{d-1})/fact ≤ choose.
  have hTpow_nonneg : 0 ≤ T ^ (d - 1) := pow_nonneg hTnonneg _
  have h1 : T ^ (d - 1) * Real.exp (τ * w) ≤
      T ^ (d - 1) * (1 / ((Nat.factorial (d - 1) : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_left hi hTpow_nonneg
  have h2 : T ^ (d - 1) * (1 / ((Nat.factorial (d - 1) : ℕ) : ℝ)) =
      T ^ (d - 1) / ((Nat.factorial (d - 1) : ℕ) : ℝ) := by
    rw [mul_one_div]
  have h3 : T ^ (d - 1) / ((Nat.factorial (d - 1) : ℕ) : ℝ) ≤
      ((F : ℝ) + 1) ^ (d - 1) / ((Nat.factorial (d - 1) : ℕ) : ℝ) :=
    div_le_div_of_nonneg_right hpow_le (le_of_lt hfact_pos)
  calc T ^ (d - 1) * Real.exp (τ * w)
      ≤ T ^ (d - 1) * (1 / ((Nat.factorial (d - 1) : ℕ) : ℝ)) := h1
    _ = T ^ (d - 1) / ((Nat.factorial (d - 1) : ℕ) : ℝ) := h2
    _ ≤ ((F : ℝ) + 1) ^ (d - 1) / ((Nat.factorial (d - 1) : ℕ) : ℝ) := h3
    _ ≤ ((F + (d - 1)).choose (d - 1) : ℝ) := hchoose_ge

/-- The common 4^d loss dominates the floor cost for any selected dimension
h≤d in the equal-dimension branch. -/
theorem same_dimension_floor_growth (d h : ℕ) (hh : h ≤ d)
    (c U V x : ℝ) (hc : 0 ≤ c) (hU : 0 ≤ U) (hx : 1 ≤ x)
    (hbound : c * U * (⌊x⌋₊ : ℝ)^h ≤ V) :
    (c / (4 : ℝ)^d) * U * x^h ≤ V := by
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx
  have hfloor1 : 1 ≤ ⌊x⌋₊ := by
    have h := Nat.floor_mono hx
    simpa using h
  have hfloorR1 : (1 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hfloor1
  have hFnonneg : 0 ≤ (⌊x⌋₊ : ℝ) := Nat.cast_nonneg _
  have hx_lt : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  have hx_le : x ≤ 2 * (⌊x⌋₊ : ℝ) := by linarith
  have hpow : x ^ h ≤ (2 * (⌊x⌋₊ : ℝ)) ^ h := pow_le_pow_left₀ hx0 hx_le h
  have h2pow : (2 * (⌊x⌋₊ : ℝ)) ^ h = (2 : ℝ) ^ h * (⌊x⌋₊ : ℝ) ^ h := mul_pow _ _ _
  have h2h_le : (2 : ℝ) ^ h ≤ (4 : ℝ) ^ d := by
    calc (2 : ℝ) ^ h ≤ (4 : ℝ) ^ h := pow_le_pow_left₀ (by norm_num) (by norm_num) h
      _ ≤ (4 : ℝ) ^ d := pow_le_pow_right₀ (by norm_num) hh
  have h4pos : 0 < (4 : ℝ) ^ d := by positivity
  have hCU : 0 ≤ c * U := mul_nonneg hc hU
  have hCUF : 0 ≤ c * U * (⌊x⌋₊ : ℝ) ^ h :=
    mul_nonneg hCU (pow_nonneg hFnonneg _)
  have hVnonneg : 0 ≤ V := le_trans hCUF hbound
  have hcoeff_nonneg : 0 ≤ (c / (4 : ℝ) ^ d) * U := by
    apply mul_nonneg
    · exact div_nonneg hc (le_of_lt h4pos)
    · exact hU
  have hstep : (c / (4 : ℝ) ^ d) * U * x ^ h ≤
      (c / (4 : ℝ) ^ d) * U * ((2 * (⌊x⌋₊ : ℝ)) ^ h) :=
    mul_le_mul_of_nonneg_left hpow hcoeff_nonneg
  rw [h2pow] at hstep
  have heq : (c / (4 : ℝ) ^ d) * U * ((2 : ℝ) ^ h * (⌊x⌋₊ : ℝ) ^ h) =
      (c * U * (⌊x⌋₊ : ℝ) ^ h) * ((2 : ℝ) ^ h / (4 : ℝ) ^ d) := by ring
  rw [heq] at hstep
  have hfrac_nonneg : 0 ≤ (2 : ℝ) ^ h / (4 : ℝ) ^ d :=
    div_nonneg (pow_nonneg (by norm_num) _) (le_of_lt h4pos)
  have hfrac_le_one : (2 : ℝ) ^ h / (4 : ℝ) ^ d ≤ 1 :=
    (div_le_one h4pos).mpr h2h_le
  have hmid : (c * U * (⌊x⌋₊ : ℝ) ^ h) * ((2 : ℝ) ^ h / (4 : ℝ) ^ d) ≤
      V * ((2 : ℝ) ^ h / (4 : ℝ) ^ d) :=
    mul_le_mul_of_nonneg_right hbound hfrac_nonneg
  have hfinal : V * ((2 : ℝ) ^ h / (4 : ℝ) ^ d) ≤ V := by
    calc V * ((2 : ℝ) ^ h / (4 : ℝ) ^ d) ≤ V * 1 :=
          mul_le_mul_of_nonneg_left hfrac_le_one hVnonneg
      _ = V := mul_one _
  exact le_trans (le_trans hstep hmid) hfinal

/-- Nat.choose_add_le_add_one_pow and the two floor comparisons turn the
literal borrowed Hilbert inequality into rank growth with exponent h. -/
theorem borrowed_floor_growth (d h : ℕ) (hh : h ≤ d)
    (c U V x y : ℝ) (hc : 0 ≤ c) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hbound : c * U * (⌊x⌋₊ : ℝ)^h ≤ V * ((⌊y⌋₊ + h).choose h : ℝ)) :
    (c / (4 : ℝ)^d) * U * (x / y)^h ≤ V := by
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx
  have hy0 : 0 ≤ y := le_trans (by norm_num) hy
  have hypos : 0 < y := lt_of_lt_of_le (by norm_num) hy
  have hfloorX1 : 1 ≤ ⌊x⌋₊ := by
    have h := Nat.floor_mono hx
    simpa using h
  have hfloorY1 : 1 ≤ ⌊y⌋₊ := by
    have h := Nat.floor_mono hy
    simpa using h
  have hFXnonneg : 0 ≤ (⌊x⌋₊ : ℝ) := Nat.cast_nonneg _
  have hFYnonneg : 0 ≤ (⌊y⌋₊ : ℝ) := Nat.cast_nonneg _
  have hfloorX_R1 : (1 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hfloorX1
  have hfloorY_R1 : (1 : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast hfloorY1
  have hx_lt : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  have hy_lt : y < (⌊y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one y
  have hYle : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy0
  have hx_le : x ≤ 2 * (⌊x⌋₊ : ℝ) := by linarith
  have hYadd_le : (⌊y⌋₊ : ℝ) + 1 ≤ 2 * y := by linarith
  have hpowX : x ^ h ≤ (2 * (⌊x⌋₊ : ℝ)) ^ h := pow_le_pow_left₀ hx0 hx_le h
  have h2powX : (2 * (⌊x⌋₊ : ℝ)) ^ h = (2 : ℝ) ^ h * (⌊x⌋₊ : ℝ) ^ h := mul_pow _ _ _
  have hchoose_nat : (⌊y⌋₊ + h).choose h ≤ (⌊y⌋₊ + 1) ^ h :=
    Nat.choose_add_le_add_one_pow _ _
  have hchooseR : ((⌊y⌋₊ + h).choose h : ℝ) ≤ ((⌊y⌋₊ + 1 : ℕ) : ℝ) ^ h := by
    exact_mod_cast hchoose_nat
  have hcast_add : ((⌊y⌋₊ + 1 : ℕ) : ℝ) = (⌊y⌋₊ : ℝ) + 1 := by
    simp [Nat.cast_add, Nat.cast_one]
  rw [hcast_add] at hchooseR
  have hpowY : ((⌊y⌋₊ : ℝ) + 1) ^ h ≤ (2 * y) ^ h := by
    apply pow_le_pow_left₀ _ hYadd_le h
    linarith
  have h2powY : (2 * y) ^ h = (2 : ℝ) ^ h * y ^ h := mul_pow _ _ _
  rw [h2powY] at hpowY
  have hchoose_le : ((⌊y⌋₊ + h).choose h : ℝ) ≤ (2 : ℝ) ^ h * y ^ h :=
    le_trans hchooseR hpowY
  have h4pos : 0 < (4 : ℝ) ^ d := by positivity
  have h2h_nonneg : 0 ≤ (2 : ℝ) ^ h := pow_nonneg (by norm_num) _
  have hyh_nonneg : 0 ≤ y ^ h := pow_nonneg hy0 _
  have h2h_le_4d : (2 : ℝ) ^ h ≤ (4 : ℝ) ^ d := by
    calc (2 : ℝ) ^ h ≤ (4 : ℝ) ^ h := pow_le_pow_left₀ (by norm_num) (by norm_num) h
      _ ≤ (4 : ℝ) ^ d := pow_le_pow_right₀ (by norm_num) hh
  have h4h_le_4d : (4 : ℝ) ^ h ≤ (4 : ℝ) ^ d := pow_le_pow_right₀ (by norm_num) hh
  have hCU_nonneg : 0 ≤ c * U := mul_nonneg hc hU
  -- Main product bound: c*U*x^h ≤ V*4^d*y^h
  have hXstep : c * U * x ^ h ≤ c * U * ((2 : ℝ) ^ h * (⌊x⌋₊ : ℝ) ^ h) := by
    have hle : x ^ h ≤ (2 : ℝ) ^ h * (⌊x⌋₊ : ℝ) ^ h := by
      calc x ^ h ≤ (2 * (⌊x⌋₊ : ℝ)) ^ h := hpowX
        _ = (2 : ℝ) ^ h * (⌊x⌋₊ : ℝ) ^ h := h2powX
    exact mul_le_mul_of_nonneg_left hle hCU_nonneg
  have hXeq : c * U * ((2 : ℝ) ^ h * (⌊x⌋₊ : ℝ) ^ h) =
      (c * U * (⌊x⌋₊ : ℝ) ^ h) * (2 : ℝ) ^ h := by ring
  have hbound_mul : (c * U * (⌊x⌋₊ : ℝ) ^ h) * (2 : ℝ) ^ h ≤
      (V * ((⌊y⌋₊ + h).choose h : ℝ)) * (2 : ℝ) ^ h :=
    mul_le_mul_of_nonneg_right hbound h2h_nonneg
  have hchoose_mul : (V * ((⌊y⌋₊ + h).choose h : ℝ)) * (2 : ℝ) ^ h ≤
      V * ((4 : ℝ) ^ d * y ^ h) := by
    have h1 : V * ((⌊y⌋₊ + h).choose h : ℝ) * (2 : ℝ) ^ h ≤
        V * ((2 : ℝ) ^ h * y ^ h) * (2 : ℝ) ^ h := by
      apply mul_le_mul_of_nonneg_right _ h2h_nonneg
      exact mul_le_mul_of_nonneg_left hchoose_le hV
    have h2 : V * ((2 : ℝ) ^ h * y ^ h) * (2 : ℝ) ^ h =
        V * (((2 : ℝ) ^ h * (2 : ℝ) ^ h) * y ^ h) := by ring
    have h3 : (2 : ℝ) ^ h * (2 : ℝ) ^ h = (4 : ℝ) ^ h := by
      rw [← mul_pow]
      norm_num
    have h4 : V * (((2 : ℝ) ^ h * (2 : ℝ) ^ h) * y ^ h) ≤ V * ((4 : ℝ) ^ d * y ^ h) := by
      apply mul_le_mul_of_nonneg_left _ hV
      apply mul_le_mul_of_nonneg_right _ hyh_nonneg
      calc (2 : ℝ) ^ h * (2 : ℝ) ^ h = (4 : ℝ) ^ h := h3
        _ ≤ (4 : ℝ) ^ d := h4h_le_4d
    calc V * ((⌊y⌋₊ + h).choose h : ℝ) * (2 : ℝ) ^ h
        ≤ V * ((2 : ℝ) ^ h * y ^ h) * (2 : ℝ) ^ h := h1
      _ = V * (((2 : ℝ) ^ h * (2 : ℝ) ^ h) * y ^ h) := h2
      _ ≤ V * ((4 : ℝ) ^ d * y ^ h) := h4
  have hmain : c * U * x ^ h ≤ V * ((4 : ℝ) ^ d * y ^ h) := by
    calc c * U * x ^ h ≤ c * U * ((2 : ℝ) ^ h * (⌊x⌋₊ : ℝ) ^ h) := hXstep
      _ = (c * U * (⌊x⌋₊ : ℝ) ^ h) * (2 : ℝ) ^ h := hXeq
      _ ≤ (V * ((⌊y⌋₊ + h).choose h : ℝ)) * (2 : ℝ) ^ h := hbound_mul
      _ ≤ V * ((4 : ℝ) ^ d * y ^ h) := hchoose_mul
  have hyh_pos : 0 < y ^ h := pow_pos hypos h
  have hdenom_pos : 0 < (4 : ℝ) ^ d * y ^ h := mul_pos h4pos hyh_pos
  have heq : (c / (4 : ℝ) ^ d) * U * (x / y) ^ h =
      (c * U * x ^ h) / ((4 : ℝ) ^ d * y ^ h) := by
    rw [div_pow]
    field_simp
  rw [heq]
  exact (div_le_iff₀ hdenom_pos).mpr hmain

theorem limiting_profile_time_upper (S : LimitingSeparatedProfile regime) :
    ∀ t : Fin d, S.b t ≤ 1 := by
  intro t
  have hlim := S.target_limit t
  have hle_all : ∀ ε : ℝ, 0 < ε → S.b t ≤ 1 + ε := by
    intro ε hε
    have hev : ∀ᶠ i in atTop,
        (S.sequence.target i).path.time t ≤ 1 + ε := by
      filter_upwards [S.sequence.good ε hε 1 (by norm_num) 1 le_rfl] with i hi
      have hrange := hi.2.time_range t
      linarith [hrange.2]
    exact le_of_tendsto hlim hev
  by_contra hcon
  have hlt : 1 < S.b t := lt_of_not_ge hcon
  have hpos : 0 < (S.b t - 1) / 2 := by linarith
  have hle := hle_all ((S.b t - 1) / 2) hpos
  linarith

/-- After a positive nonfinal endpoint there is a nonempty tail of positive
limiting cut times, giving the narrow-center strict margin. -/
theorem positive_later_profile_sum (S : LimitingSeparatedProfile regime)
    (u : ProfilePlateau S) (hpos : 0 < S.b u.val) (hfinal : u.val.val + 1 < d) :
    0 < ∑ t ∈ (Finset.univ : Finset (Fin d)).filter
      (fun t => u.val.val < t.val), S.b t := by
  classical
  let s : Finset (Fin d) :=
    (Finset.univ : Finset (Fin d)).filter (fun t => u.val.val < t.val)
  have hwit : (⟨u.val.val + 1, hfinal⟩ : Fin d) ∈ s := by
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Nat.lt_succ_self _
  have hne : s.Nonempty := ⟨_, hwit⟩
  apply Finset.sum_pos _ hne
  intro t ht
  simp only [s, Finset.mem_filter, Finset.mem_univ, true_and] at ht
  have hle : u.val ≤ t := Fin.le_def.mpr (Nat.le_of_lt ht)
  have hmono := S.sorted hle
  linarith

/-- Remove the B² convention algebraically, and split the narrow tail at
the current endpoint. The literal rate has exactly the stated endpoint log. -/
theorem profile_rate_endpoint_identity (S : LimitingSeparatedProfile regime)
    (u : ProfilePlateau S) (kind : DepthRateKind) (i : ℕ) :
    profileDepthRate S u.val.val kind i *
      TrackD.testDeg (regime.B i) (S.sequence.target i).width (S.b u.val) / regime.A i =
      Real.exp (profileRateEndpointLog S u kind * (S.sequence.target i).width) := by
  classical
  cases u with
  | mk j hj =>
    have hA : regime.A i = (regime.B i) ^ 2 := regime.A_eq_B_sq i
    have hBne : regime.B i ≠ 0 := ne_of_gt (regime.B_pos i)
    cases kind with
    | first =>
      simp only [profileDepthRate, profileRateEndpointLog]
      unfold TrackD.testDeg
      rw [hA]
      have hexp : Real.exp (S.b ⟨0, by have := regime.dimension_ge_three; omega⟩ *
          (S.sequence.target i).width) *
          Real.exp (S.b j * (S.sequence.target i).width) =
          Real.exp ((S.b ⟨0, by have := regime.dimension_ge_three; omega⟩ + S.b j) *
            (S.sequence.target i).width) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc regime.B i * Real.exp (S.b ⟨0, by have := regime.dimension_ge_three; omega⟩ *
              (S.sequence.target i).width) *
              (regime.B i * Real.exp (S.b j * (S.sequence.target i).width)) /
              (regime.B i) ^ 2
          = Real.exp (S.b ⟨0, by have := regime.dimension_ge_three; omega⟩ *
              (S.sequence.target i).width) *
            Real.exp (S.b j * (S.sequence.target i).width) := by
            field_simp
        _ = _ := hexp
    | narrow =>
      simp only [profileDepthRate, profileRateEndpointLog]
      unfold TrackD.testDeg
      rw [hA]
      have hsum : ∑ t ∈ (Finset.univ : Finset (Fin d)).filter
            (fun t => j.val ≤ t.val), S.b t =
          S.b j + ∑ t ∈ (Finset.univ : Finset (Fin d)).filter
            (fun t => j.val < t.val), S.b t := by
        have hset : (Finset.univ : Finset (Fin d)).filter
              (fun t => j.val ≤ t.val) =
            insert j ((Finset.univ : Finset (Fin d)).filter
              (fun t => j.val < t.val)) := by
          ext t
          simp only [Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_insert]
          constructor
          · intro hle
            by_cases heq : t.val = j.val
            · left
              exact Fin.ext heq
            · right
              omega
          · rintro (rfl | hlt)
            · omega
            · omega
        have hnotmem : j ∉ (Finset.univ : Finset (Fin d)).filter
            (fun t => j.val < t.val) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          omega
        rw [hset, Finset.sum_insert hnotmem]
      have hexp : Real.exp (-(S.sequence.target i).width * ∑ t ∈
              (Finset.univ : Finset (Fin d)).filter
              (fun t => j.val ≤ t.val), S.b t) *
          Real.exp (S.b j * (S.sequence.target i).width) =
          Real.exp ((-∑ t ∈ (Finset.univ : Finset (Fin d)).filter
              (fun t => j.val < t.val), S.b t) *
            (S.sequence.target i).width) := by
        rw [← Real.exp_add]
        congr 1
        rw [hsum]
        ring
      calc regime.B i * Real.exp (-(S.sequence.target i).width * ∑ t ∈
                (Finset.univ : Finset (Fin d)).filter
                (fun t => j.val ≤ t.val), S.b t) *
              (regime.B i * Real.exp (S.b j * (S.sequence.target i).width)) /
              (regime.B i) ^ 2
          = Real.exp (-(S.sequence.target i).width * ∑ t ∈
                (Finset.univ : Finset (Fin d)).filter
                (fun t => j.val ≤ t.val), S.b t) *
            Real.exp (S.b j * (S.sequence.target i).width) := by
            field_simp
        _ = _ := hexp
    | wide =>
      simp only [profileDepthRate, profileRateEndpointLog]
      unfold TrackD.testDeg
      rw [hA]
      have hexp : Real.exp (-2 * (S.sequence.target i).width) *
          Real.exp (S.b j * (S.sequence.target i).width) =
          Real.exp ((S.b j - 2) * (S.sequence.target i).width) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc regime.B i * Real.exp (-2 * (S.sequence.target i).width) *
              (regime.B i * Real.exp (S.b j * (S.sequence.target i).width)) /
              (regime.B i) ^ 2
          = Real.exp (-2 * (S.sequence.target i).width) *
            Real.exp (S.b j * (S.sequence.target i).width) := by
            field_simp
        _ = _ := hexp


end
end DistinctDistances.SparseCones
