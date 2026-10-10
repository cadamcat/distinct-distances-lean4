import OAI.RingTheory.Multiplicity.LinearNormalizationDimension
import OAI.NumberTheory.PiExponent.Polynomials.PolynomialGrowthRanks
import OAI.NumberTheory.PowerFree.HilbertGrowth
import OAI.RingTheory.Multiplicity.LechHilbertSerre
import OAI.RingTheory.Multiplicity.SubalgebraStageFromBase
import OAI.RingTheory.Multiplicity.LechLengthLe

open scoped Pointwise

namespace DistinctDistances.AffineVariety

/-- Any graded-independent size bounds the degree of an eventual colength polynomial. -/
theorem le_degree_of_independent {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (P : Polynomial ℚ)
    (hP : ∀ᶠ t : ℕ in Filter.atTop,
      ((OAI.Lech.colength R (t+1) : ℕ) : ℚ) = P.eval (t : ℚ))
    {s : ℕ}
    (z : Fin s → OAI.Lech.IdealGraded.Ring (IsLocalRing.maximalIdeal R))
    (hz : ∀ i, z i ∈ OAI.Lech.IdealGraded.grade (IsLocalRing.maximalIdeal R) 1)
    (hi : Function.Injective
      (MvPolynomial.aeval (R := R ⧸ IsLocalRing.maximalIdeal R) z)) :
    s ≤ P.natDegree := by
  classical
  have hlow : ∀ t : ℕ,
      ((t + s).choose s : ℚ) ≤ ((OAI.Lech.colength R (t+1) : ℕ) : ℚ) := by
    intro t
    have hle := OAI.Lech.LinearNormalization.polynomial_rank_le_colength (R := R)
      z hz hi (t+1)
    have hsum : ∑ n ∈ Finset.range (t+1), s.multichoose n = (t + s).choose s := by
      have h := Nat.sum_range_multichoose t s
      simpa [add_comm] using h
    have hle2 : (t + s).choose s ≤ OAI.Lech.colength R (t+1) := by
      rw [← hsum]
      exact hle
    exact_mod_cast hle2
  have hlow_poly : ∀ᶠ t : ℕ in Filter.atTop,
      (OAI.PiExponentJets.W32.polynomialGrowth s).eval (t : ℚ) ≤ P.eval (t : ℚ) := by
    filter_upwards [hP] with t ht
    rw [OAI.PiExponentJets.W32.polynomialGrowth_eval]
    rw [← ht]
    exact hlow t
  have hnonneg : ∀ᶠ t : ℕ in Filter.atTop,
      0 ≤ (OAI.PiExponentJets.W32.polynomialGrowth s).eval (t : ℚ) := by
    filter_upwards with t
    rw [OAI.PiExponentJets.W32.polynomialGrowth_eval]
    positivity
  have hdeg := OAI.QuarticPowerFree.natDegree_le_of_eventually_nat_eval_bounds
    (OAI.PiExponentJets.W32.polynomialGrowth s) P hnonneg hlow_poly
  rw [OAI.PiExponentJets.W32.polynomialGrowth_natDegree] at hdeg
  exact hdeg

/-- Base case: constant Hilbert-Samuel polynomial forces Krull dimension zero.
If colength is eventually constant, then m^N stabilizes, Nakayama gives m^N=0,
hence every prime equals the maximal ideal, so Krull dimension is zero. -/
theorem dimension_eq_zero_of_natDegree_eq_zero {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] [Nontrivial R]
    (P : Polynomial ℚ)
    (hP : ∀ᶠ N : ℕ in Filter.atTop,
      ((OAI.Lech.colength R N : ℕ) : ℚ) = P.eval (N : ℚ))
    (hdeg : P.natDegree = 0) : OAI.Lech.dimension R = 0 := by
  classical
  -- P constant (unused for stability, but records degree-zero shape)
  have hPconst : P = Polynomial.C (P.coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero hdeg
  -- colength eventually constant Nat k
  have hstab : ∃ k : ℕ, ∃ N1 : ℕ, ∀ N ≥ N1,
      OAI.Lech.colength R N = k := by
    obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp hP
    refine ⟨OAI.Lech.colength R N1, N1, fun N hN => ?_⟩
    have h1 := hN1 N hN
    have h2 := hN1 N1 le_rfl
    have heq : ((OAI.Lech.colength R N : ℕ) : ℚ) =
        ((OAI.Lech.colength R N1 : ℕ) : ℚ) := by
      rw [h1, h2, hPconst]
      simp
    exact Nat.cast_injective heq
  obtain ⟨k, N1, hk⟩ := hstab
  -- lengths eventually constant as ℕ∞
  have hlen_const : ∃ N1 : ℕ, ∀ N ≥ N1,
      Module.length R (R ⧸ IsLocalRing.maximalIdeal R ^ N) =
        ((k : ℕ) : ℕ∞) := by
    refine ⟨N1, fun N hN => ?_⟩
    have hcol := hk N hN
    have hcast := OAI.Lech.colength_cast R N
    rw [hcol] at hcast
    exact hcast.symm
  obtain ⟨N2, hN2⟩ := hlen_const
  -- pick N ≥ max N2 1 with equal successive lengths to get m^N = m^{N+1}
  obtain ⟨N, hNge, hNpos⟩ : ∃ N : ℕ, N ≥ N2 ∧ 0 < N := ⟨max N2 1, le_max_left _ _, lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)⟩
  have hlen_eq : Module.length R (R ⧸ IsLocalRing.maximalIdeal R ^ N) =
      Module.length R (R ⧸ IsLocalRing.maximalIdeal R ^ (N+1)) := by
    have h1 := hN2 N hNge
    have h2 := hN2 (N+1) (le_trans hNge (Nat.le_succ _))
    rw [h1, h2]
  -- m^{N+1} ≤ m^N, so quotient m^N/m^{N+1} has length 0
  have hle_pow : IsLocalRing.maximalIdeal R ^ (N+1) ≤ IsLocalRing.maximalIdeal R ^ N := by
    calc IsLocalRing.maximalIdeal R ^ (N+1)
        = IsLocalRing.maximalIdeal R ^ N * IsLocalRing.maximalIdeal R := by rw [pow_succ]
      _ ≤ IsLocalRing.maximalIdeal R ^ N * ⊤ := by gcongr; exact le_top
      _ = IsLocalRing.maximalIdeal R ^ N := by rw [Ideal.mul_top]
  -- finiteness of both lengths
  have hfin1 : Module.length R (R ⧸ IsLocalRing.maximalIdeal R ^ N) ≠ ⊤ :=
    OAI.Lech.quotient_length_ne_top R N
  have hfin2 : Module.length R (R ⧸ IsLocalRing.maximalIdeal R ^ (N+1)) ≠ ⊤ :=
    OAI.Lech.quotient_length_ne_top R (N+1)
  -- surjection R/m^{N+1} → R/m^N gives length additivity with kernel m^N/m^{N+1}
  -- hence m^N = m^{N+1} since successive lengths equal and finite
  have hpow_eq : IsLocalRing.maximalIdeal R ^ N = IsLocalRing.maximalIdeal R ^ (N+1) := by
    classical
    let mN := IsLocalRing.maximalIdeal R ^ N
    let mN1 := IsLocalRing.maximalIdeal R ^ (N+1)
    have hle : mN1 ≤ mN := hle_pow
    let F : (R ⧸ mN1) →ₐ[R] (R ⧸ mN) := Ideal.Quotient.factorₐ R hle
    have hFsurj : Function.Surjective F := by
      intro y
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact ⟨Ideal.Quotient.mk mN1 r, rfl⟩
    -- F as linear map is surjective with equal finite lengths, hence injective
    have hFsurj_lin : Function.Surjective F.toLinearMap := hFsurj
    have hker_eq : Module.length R (LinearMap.ker F.toLinearMap) = 0 := by
      have hexact : Function.Exact (LinearMap.ker F.toLinearMap).subtype F.toLinearMap :=
        LinearMap.exact_subtype_ker_map F.toLinearMap
      have hadd := Module.length_eq_add_of_exact (LinearMap.ker F.toLinearMap).subtype
        F.toLinearMap (Submodule.subtype_injective _) hFsurj_lin hexact
      -- hadd : length(R/mN1) = length(ker) + length(R/mN)
      -- hlen_eq : length(R/mN) = length(R/mN1), hfin1 : length(R/mN) ≠ ⊤
      have h_eq : Module.length R (R ⧸ mN) =
          Module.length R (LinearMap.ker F.toLinearMap) + Module.length R (R ⧸ mN) := by
        rw [← hadd, ← hlen_eq]
      have h0 : Module.length R (R ⧸ mN) + Module.length R (LinearMap.ker F.toLinearMap) =
          Module.length R (R ⧸ mN) + 0 := by
        rw [add_comm (Module.length R (R ⧸ mN)) _, add_zero]
        exact h_eq.symm
      have hcancel := WithTop.add_left_cancel hfin1 h0
      exact hcancel
    -- kernel trivial hence F injective hence ideals equal
    have hker_bot : LinearMap.ker F.toLinearMap = ⊥ := by
      have hsub : Subsingleton (LinearMap.ker F.toLinearMap) := by
        rwa [Module.length_eq_zero_iff] at hker_eq
      haveI := hsub
      exact Submodule.eq_bot_of_subsingleton
    have hFinj : Function.Injective F := by
      have hlinj : Function.Injective F.toLinearMap := by
        rw [← LinearMap.ker_eq_bot]
        exact hker_bot
      exact hlinj
    -- mN ⊆ mN1 via injectivity + factor Mk
    have hsup : mN ≤ mN1 := by
      intro x hx
      have hmk : F (Ideal.Quotient.mk mN1 x) = 0 := by
        have h1 : F (Ideal.Quotient.mk mN1 x) = Ideal.Quotient.mk mN x := rfl
        rw [h1]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
      have h0 : (0 : R ⧸ mN1) = Ideal.Quotient.mk mN1 0 := rfl
      have hmem : Ideal.Quotient.mk mN1 x = 0 := by
        have h2 : F (Ideal.Quotient.mk mN1 x) = F 0 := by
          rw [hmk]
          simp
        exact hFinj h2
      exact Ideal.Quotient.eq_zero_iff_mem.mp hmem
    exact le_antisymm hsup hle
  -- Nakayama: m^N = m • m^N with m^N FG and m ≤ Jacobson gives m^N = ⊥
  have hsmul : (↑(IsLocalRing.maximalIdeal R ^ N) : Submodule R R) =
      IsLocalRing.maximalIdeal R • (↑(IsLocalRing.maximalIdeal R ^ N) : Submodule R R) := by
    have h1 : IsLocalRing.maximalIdeal R ^ N = IsLocalRing.maximalIdeal R ^ (N+1) := hpow_eq
    have h2 : IsLocalRing.maximalIdeal R ^ (N+1) =
        IsLocalRing.maximalIdeal R ^ N * IsLocalRing.maximalIdeal R := by rw [pow_succ]
    have h3 : (↑(IsLocalRing.maximalIdeal R ^ N * IsLocalRing.maximalIdeal R) : Submodule R R) =
        IsLocalRing.maximalIdeal R • (↑(IsLocalRing.maximalIdeal R ^ N) : Submodule R R) := by
      rw [mul_comm]
      exact Ideal.smul_eq_mul _ _
    calc (↑(IsLocalRing.maximalIdeal R ^ N) : Submodule R R)
        = ↑(IsLocalRing.maximalIdeal R ^ (N+1)) := by rw [h1]
      _ = ↑(IsLocalRing.maximalIdeal R ^ N * IsLocalRing.maximalIdeal R) := by rw [h2]
      _ = IsLocalRing.maximalIdeal R • (↑(IsLocalRing.maximalIdeal R ^ N) : Submodule R R) := h3
  -- Nakayama gives the submodule is ⊥
  have hbot_sub : (↑(IsLocalRing.maximalIdeal R ^ N) : Submodule R R) ≤ ⊥ := by
    apply Submodule.le_of_le_smul_of_le_jacobson_bot
      (IsNoetherian.noetherian (IsLocalRing.maximalIdeal R ^ N))
      (IsLocalRing.maximalIdeal_le_jacobson ⊥)
    conv_lhs => rw [hsmul]
    exact le_sup_right
  -- hence every prime equals the maximal ideal
  have hall : ∀ p : Ideal R, p.IsPrime → p = IsLocalRing.maximalIdeal R := by
    intro p hp
    have hle : IsLocalRing.maximalIdeal R ≤ p := by
      intro a ha
      have hpowmem : a ^ N ∈ (↑(IsLocalRing.maximalIdeal R ^ N) : Submodule R R) :=
        Ideal.pow_mem_pow ha N
      have hbotmem : a ^ N ∈ (⊥ : Submodule R R) := hbot_sub hpowmem
      have hzero : a ^ N = 0 := by simpa using hbotmem
      have hmem : a ^ N ∈ p := by
        rw [hzero]
        exact p.zero_mem
      exact hp.mem_of_pow_mem _ hmem
    have hmax : (IsLocalRing.maximalIdeal R).IsMaximal := inferInstance
    exact (hmax.eq_of_le hp.ne_top hle).symm
  have hkle : Ring.KrullDimLE 0 R :=
    Ring.KrullDimLE.mk₀ (fun I hI => by
      rw [hall I hI]
      infer_instance)
  have hkrull : ringKrullDim R = 0 :=
    ringKrullDimZero_iff_ringKrullDim_eq_zero.mp hkle
  have hcast := OAI.Lech.dimension_cast R
  rw [hkrull] at hcast
  have h0 : ((OAI.Lech.dimension R : ℕ) : WithBot ℕ∞) = ((0 : ℕ) : WithBot ℕ∞) := by
    rw [hcast]
    norm_cast
  exact Nat.cast_injective (WithBot.coe_injective h0)

/-- Krull dimension drops by exactly one when quotienting a Noetherian local ring
by an element outside every minimal prime (Atiyah–Macdonald 11.14, Krull half).
No regularity hypothesis is needed. -/
theorem krullDim_span_singleton_avoidance {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {x : R}
    (hn : ∀ p ∈ minimalPrimes R, x ∉ p)
    (hx : x ∈ IsLocalRing.maximalIdeal R) :
    ringKrullDim (R ⧸ Ideal.span {x}) + 1 = ringKrullDim R := by
  have hann : Module.annihilator R R = ⊥ :=
    Module.annihilator_eq_bot.mpr
      ((faithfulSMul_iff_algebraMap_injective R R).mpr fun {a₁ a₂} a ↦ a)
  have hn' : ∀ p ∈ (Module.annihilator R R).minimalPrimes, x ∉ p := by
    rw [hann]
    exact hn
  have h : Ideal.span {x} = x • (⊤ : Ideal R) := by
    simp [← Submodule.ideal_span_singleton_smul]
  rw [ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquivAlgOfEq R h).toRingEquiv,
    ← Module.supportDim_quotient_eq_ringKrullDim,
    ← Module.supportDim_self_eq_ringKrullDim]
  exact Module.supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_maximalIdeal
    hn' hx

/-- An element of the maximal ideal outside every minimal prime exists as soon
as the maximal ideal itself is not minimal (prime avoidance). -/
theorem exists_mem_maximal_outside_minimal {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] [Nontrivial R]
    (h : IsLocalRing.maximalIdeal R ∉ minimalPrimes R) :
    ∃ x : R, x ∈ IsLocalRing.maximalIdeal R ∧ ∀ p ∈ minimalPrimes R, x ∉ p := by
  classical
  have hfin : (minimalPrimes R).Finite := minimalPrimes.finite_of_isNoetherianRing R
  have hmem := Ideal.subset_iUnion_iff_mem_of_isMaximal_of_finite
    (M := IsLocalRing.maximalIdeal R) hfin (⊥ : Ideal R) (⊥ : Ideal R)
    (fun I hI _ _ => Ideal.IsMinimalPrime.isPrime hI) bot_ne_top bot_ne_top
  have hsub : ¬ ((IsLocalRing.maximalIdeal R : Set R) ⊆ ⋃ I ∈ minimalPrimes R, I) :=
    mt hmem.mp h
  rw [Set.not_subset] at hsub
  obtain ⟨x, hxm, hxo⟩ := hsub
  exact ⟨x, hxm, fun p hp hxp =>
    hxo (Set.mem_iUnion_of_mem p (Set.mem_iUnion_of_mem hp hxp))⟩

/-- If the maximal ideal is itself minimal, the local ring has dimension zero.
Used in the induction step when no quotient element can be picked. -/
theorem dimension_eq_zero_of_maximal_minimal {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] [Nontrivial R]
    (h : IsLocalRing.maximalIdeal R ∈ minimalPrimes R) :
    OAI.Lech.dimension R = 0 := by
  have hall : ∀ p : Ideal R, p.IsPrime → p = IsLocalRing.maximalIdeal R := by
    intro p hp
    haveI := hp
    obtain ⟨q, hqmin, hqp⟩ :=
      Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R)) (J := p) bot_le
    have hqm : q ≤ IsLocalRing.maximalIdeal R :=
      hqp.trans (IsLocalRing.le_maximalIdeal_of_isPrime p)
    have hPq : q.IsPrime ∧ (⊥ : Ideal R) ≤ q := ⟨hqmin.isPrime, bot_le⟩
    have hmin : Minimal (fun q : Ideal R => q.IsPrime ∧ (⊥ : Ideal R) ≤ q)
        (IsLocalRing.maximalIdeal R) := h
    have hqeq : q = IsLocalRing.maximalIdeal R := Minimal.eq_of_le hmin hPq hqm
    have hpm : IsLocalRing.maximalIdeal R ≤ p := hqeq ▸ hqp
    have hmp : p ≤ IsLocalRing.maximalIdeal R :=
      IsLocalRing.le_maximalIdeal_of_isPrime p
    exact le_antisymm hmp hpm
  have hkle : Ring.KrullDimLE 0 R :=
    Ring.KrullDimLE.mk₀ (fun I hI => by
      rw [hall I hI]
      infer_instance)
  have hkrull : ringKrullDim R = 0 :=
    ringKrullDimZero_iff_ringKrullDim_eq_zero.mp hkle
  have hcast := OAI.Lech.dimension_cast R
  rw [hkrull] at hcast
  have h0 : ((OAI.Lech.dimension R : ℕ) : WithBot ℕ∞) = ((0 : ℕ) : WithBot ℕ∞) := by
    rw [hcast]
    norm_cast
  exact Nat.cast_injective (WithBot.coe_injective h0)

/-- The principal quotient by an element of the maximal ideal is nontrivial. -/
theorem quot_span_nontrivial {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {x : R} (hx : x ∈ IsLocalRing.maximalIdeal R) :
    Nontrivial (R ⧸ Ideal.span {x}) := by
  have hle : Ideal.span {x} ≤ IsLocalRing.maximalIdeal R :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx)
  have hmax : (IsLocalRing.maximalIdeal R).IsMaximal := inferInstance
  have hne : Ideal.span {x} ≠ ⊤ := ne_top_of_le_ne_top hmax.ne_top hle
  exact Ideal.Quotient.nontrivial_iff.mpr hne

/-- The principal quotient by an element of the maximal ideal is local. -/
theorem quot_span_isLocalRing {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {x : R} [Nontrivial (R ⧸ Ideal.span {x})] :
    IsLocalRing (R ⧸ Ideal.span {x}) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

/-- The principal quotient carries an eventual colength polynomial. -/
theorem quot_span_eventual {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {x : R} [IsLocalRing (R ⧸ Ideal.span {x})] :
    ∃ Q : Polynomial ℚ, ∀ᶠ N in Filter.atTop,
      ((OAI.Lech.colength (R ⧸ Ideal.span {x}) N : ℕ) : ℚ) =
        Q.eval (N : ℚ) := by
  obtain ⟨Q, hQ⟩ := OAI.Lech.IdealGraded.eventuallyPolynomial_length
    (IsLocalRing.maximalIdeal (R ⧸ Ideal.span {x}))
  exact ⟨Q, hQ⟩

/-- Colength does not increase under quotient by an ideal below the
maximal ideal (surjection of the `m`-adic quotients). -/
theorem colength_quotient_le_general {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (J : Ideal R) (hle : J ≤ IsLocalRing.maximalIdeal R)
    [Nontrivial (R ⧸ J)] [IsLocalRing (R ⧸ J)] (N : ℕ) :
    OAI.Lech.colength (R ⧸ J) N ≤ OAI.Lech.colength R N := by
  classical
  have hmax_img : ((IsLocalRing.maximalIdeal R).map
      (Ideal.Quotient.mk J)).IsMaximal := by
    apply Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
    rw [Ideal.mk_ker]
    exact hle
  have hmax : IsLocalRing.maximalIdeal (R ⧸ J) =
      (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk J) :=
    (IsLocalRing.eq_maximalIdeal hmax_img).symm
  have hbridge := OAI.Lech.FrobeniusGrowth.quotient_power_length
    (IsLocalRing.maximalIdeal R) J N
  have hlen_eq : Module.length (R ⧸ J) ((R ⧸ J) ⧸
      (IsLocalRing.maximalIdeal (R ⧸ J)) ^ N) =
      Module.length R (R ⧸ (IsLocalRing.maximalIdeal R ^ N ⊔ J)) := by
    rw [hmax]
    exact hbridge
  have hle_pow : IsLocalRing.maximalIdeal R ^ N ≤
      IsLocalRing.maximalIdeal R ^ N ⊔ J := le_sup_left
  let F : (R ⧸ IsLocalRing.maximalIdeal R ^ N) →ₐ[R]
      (R ⧸ (IsLocalRing.maximalIdeal R ^ N ⊔ J)) :=
    Ideal.Quotient.factorₐ R hle_pow
  have hFsurj : Function.Surjective F.toLinearMap := by
    intro y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk _ r, rfl⟩
  have hle_len : Module.length R
      (R ⧸ (IsLocalRing.maximalIdeal R ^ N ⊔ J)) ≤
      Module.length R (R ⧸ IsLocalRing.maximalIdeal R ^ N) :=
    Module.length_le_of_surjective F.toLinearMap hFsurj
  have hB := OAI.Lech.colength_cast (R ⧸ J) N
  have hA := OAI.Lech.colength_cast R N
  have hBeq : ((OAI.Lech.colength (R ⧸ J) N : ℕ) : ℕ∞) =
      Module.length R (R ⧸ (IsLocalRing.maximalIdeal R ^ N ⊔ J)) := by
    rw [hB, hlen_eq]
  have hAeq : ((OAI.Lech.colength R N : ℕ) : ℕ∞) =
      Module.length R (R ⧸ IsLocalRing.maximalIdeal R ^ N) := hA
  have hle_cast : ((OAI.Lech.colength (R ⧸ J) N : ℕ) : ℕ∞) ≤
      ((OAI.Lech.colength R N : ℕ) : ℕ∞) := by
    rw [hBeq, hAeq]
    exact hle_len
  exact_mod_cast hle_cast

/-- Eventual Hilbert–Samuel degree does not increase under such quotients. -/
theorem natDegree_le_of_quotient {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (J : Ideal R) (hle : J ≤ IsLocalRing.maximalIdeal R)
    [Nontrivial (R ⧸ J)] [IsLocalRing (R ⧸ J)]
    (P Q : Polynomial ℚ)
    (hP : ∀ᶠ N in Filter.atTop,
      ((OAI.Lech.colength R N : ℕ) : ℚ) = P.eval (N : ℚ))
    (hQ : ∀ᶠ N in Filter.atTop,
      ((OAI.Lech.colength (R ⧸ J) N : ℕ) : ℚ) = Q.eval (N : ℚ)) :
    Q.natDegree ≤ P.natDegree := by
  classical
  have hQnonneg : ∀ᶠ N : ℕ in Filter.atTop, 0 ≤ Q.eval (N : ℚ) := by
    filter_upwards [hQ] with N hN
    rw [← hN]
    positivity
  have hQPle : ∀ᶠ N : ℕ in Filter.atTop,
      Q.eval (N : ℚ) ≤ P.eval (N : ℚ) := by
    filter_upwards [hP, hQ] with N hPN hQN
    rw [← hQN, ← hPN]
    have hleN := colength_quotient_le_general J hle N
    exact_mod_cast hleN
  exact OAI.QuarticPowerFree.natDegree_le_of_eventually_nat_eval_bounds
    Q P hQnonneg hQPle

/-- Colength of the principal quotient equals the ambient length by the
imaged maximal power (bridge for the degree-drop analysis). -/
theorem colength_quot_span_eq_length {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {x : R} (hx : x ∈ IsLocalRing.maximalIdeal R)
    [IsLocalRing (R ⧸ Ideal.span {x})] (N : ℕ) :
    OAI.Lech.colength (R ⧸ Ideal.span {x}) N =
      (Module.length R
        (R ⧸ (IsLocalRing.maximalIdeal R ^ N ⊔ Ideal.span {x}))).toNat := by
  have hle : Ideal.span {x} ≤ IsLocalRing.maximalIdeal R :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx)
  have hmax_img : ((IsLocalRing.maximalIdeal R).map
      (Ideal.Quotient.mk (Ideal.span {x}))).IsMaximal := by
    apply Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
    rw [Ideal.mk_ker]
    exact hle
  have hmax : IsLocalRing.maximalIdeal (R ⧸ Ideal.span {x}) =
      (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {x})) :=
    (IsLocalRing.eq_maximalIdeal hmax_img).symm
  have hbridge := OAI.Lech.FrobeniusGrowth.quotient_power_length
    (IsLocalRing.maximalIdeal R) (Ideal.span {x}) N
  calc OAI.Lech.colength (R ⧸ Ideal.span {x}) N
      = (Module.length (R ⧸ Ideal.span {x})
          ((R ⧸ Ideal.span {x}) ⧸
            (IsLocalRing.maximalIdeal (R ⧸ Ideal.span {x})) ^ N)).toNat := rfl
    _ = (Module.length R
          (R ⧸ (IsLocalRing.maximalIdeal R ^ N ⊔ Ideal.span {x}))).toNat := by
        rw [hmax, hbridge]

/-- Artin–Rees containment for a principal submodule: some `k` works for all
`n ≥ k`. This packages Mathlib `Ideal.exists_pow_inf_eq_pow_smul` (prebuilt)
in Ideal language. -/
theorem artinRees_containment {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {x : R} :
    ∃ k : ℕ, ∀ n ≥ k, (Ideal.span {x} ⊓ IsLocalRing.maximalIdeal R ^ n) ≤
      IsLocalRing.maximalIdeal R ^ (n - k) * Ideal.span {x} := by
  classical
  obtain ⟨k, hk⟩ := (IsLocalRing.maximalIdeal R).exists_pow_inf_eq_pow_smul
    (↑(Ideal.span {x}) : Submodule R R)
  refine ⟨k, fun n hn => ?_⟩
  have heq := hk n hn
  -- Translate the Submodule equality to the Ideal inequality via defeq
  -- (Ideal is Submodule definitionally) and `Ideal.smul_eq_mul` (`rfl`).
  have hleft : ((Ideal.span {x} ⊓ IsLocalRing.maximalIdeal R ^ n : Ideal R) :
      Submodule R R) ≤
      (IsLocalRing.maximalIdeal R ^ n • (⊤ : Submodule R R) ⊓
        ↑(Ideal.span {x})) := by
    have hpow : ((IsLocalRing.maximalIdeal R ^ n : Ideal R) : Submodule R R) ≤
        IsLocalRing.maximalIdeal R ^ n • (⊤ : Submodule R R) := by
      intro a ha
      have hmem : a • (1 : R) ∈ IsLocalRing.maximalIdeal R ^ n •
          (⊤ : Submodule R R) :=
        Submodule.smul_mem_smul ha (Submodule.mem_top (R := R) (M := R))
      simpa using hmem
    exact inf_le_inf le_rfl hpow |>.trans (inf_comm _ _).le
  have hright : (IsLocalRing.maximalIdeal R ^ (n - k) •
      (IsLocalRing.maximalIdeal R ^ k • (⊤ : Submodule R R) ⊓
        ↑(Ideal.span {x}))) ≤
      ((IsLocalRing.maximalIdeal R ^ (n - k) * Ideal.span {x} : Ideal R) :
        Submodule R R) := by
    have hmul : IsLocalRing.maximalIdeal R ^ (n - k) •
        (↑(Ideal.span {x}) : Submodule R R) ≤
        ((IsLocalRing.maximalIdeal R ^ (n - k) * Ideal.span {x} : Ideal R) :
          Submodule R R) := by
      apply Submodule.smul_le.mpr
      intro a ha b hb
      rw [smul_eq_mul]
      exact Ideal.mul_mem_mul ha hb
    exact (smul_mono_right _ inf_le_right).trans hmul
  have hle_sub : ((Ideal.span {x} ⊓ IsLocalRing.maximalIdeal R ^ n : Ideal R) :
      Submodule R R) ≤
      ((IsLocalRing.maximalIdeal R ^ (n - k) * Ideal.span {x} : Ideal R) :
        Submodule R R) := by
    calc ((Ideal.span {x} ⊓ IsLocalRing.maximalIdeal R ^ n : Ideal R) :
          Submodule R R)
        ≤ (IsLocalRing.maximalIdeal R ^ n • (⊤ : Submodule R R) ⊓
          ↑(Ideal.span {x})) := hleft
      _ = (IsLocalRing.maximalIdeal R ^ (n - k) •
          (IsLocalRing.maximalIdeal R ^ k • (⊤ : Submodule R R) ⊓
            ↑(Ideal.span {x}))) := heq
      _ ≤ ((IsLocalRing.maximalIdeal R ^ (n - k) * Ideal.span {x} : Ideal R) :
            Submodule R R) := hright
  exact hle_sub

/-- Colon by a regular element is controlled by the Artin–Rees shift:
`(m^n : x) ≤ m^(n-k)` for `n ≥ k`. Regularity cancels `x`. -/
theorem colon_le_shift {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {x : R} (hx_reg : x ∈ nonZeroDivisors R) (k : ℕ)
    (hAR : ∀ n ≥ k, (Ideal.span {x} ⊓ IsLocalRing.maximalIdeal R ^ n) ≤
      IsLocalRing.maximalIdeal R ^ (n - k) * Ideal.span {x})
    {n : ℕ} (hn : n ≥ k) :
    (IsLocalRing.maximalIdeal R ^ n).colon {x} ≤
      IsLocalRing.maximalIdeal R ^ (n - k) := by
  classical
  intro r hr
  have hmem_smul : r • x ∈ ((IsLocalRing.maximalIdeal R ^ n : Ideal R) :
      Submodule R R) := (Submodule.mem_colon_singleton).mp hr
  have hrx_mem : r * x ∈ IsLocalRing.maximalIdeal R ^ n := hmem_smul
  have hrx_span : r * x ∈ Ideal.span {x} :=
    Ideal.mem_span_singleton'.mpr ⟨r, rfl⟩
  have hinter : r * x ∈ Ideal.span {x} ⊓ IsLocalRing.maximalIdeal R ^ n :=
    Submodule.mem_inf.mpr ⟨hrx_span, hrx_mem⟩
  have hmul_mem : r * x ∈ IsLocalRing.maximalIdeal R ^ (n - k) *
      Ideal.span {x} := hAR n hn hinter
  obtain ⟨s, hs_mem, hs_eq⟩ := (Ideal.mem_mul_span_singleton).mp hmul_mem
  have hcancel : (r - s) * x = 0 := by
    have h1 : r * x = s * x := hs_eq.symm
    calc (r - s) * x = r * x - s * x := by ring
      _ = 0 := by rw [h1, sub_self]
  have hzero : r - s = 0 :=
    (mem_nonZeroDivisors_iff_right.mp hx_reg) _ hcancel
  have hrs : r = s := by
    have h2 : r - s = 0 := hzero
    calc r = (r - s) + s := by ring
      _ = s := by rw [h2, zero_add]
  rw [hrs]
  exact hs_mem

/-- Length additivity for the regular-element exact sequence
`0 → R/(m^n:x) → R/m^n → R/(m^n+(x)) → 0` gives
`length(R/D) + length(R/m^(n-k)) ≤ length(R/m^n)` when `(m^n:x) ≤ m^(n-k)`. -/
theorem length_le_of_regular {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {x : R} {n k : ℕ}
    (hC_le : (IsLocalRing.maximalIdeal R ^ n).colon {x} ≤
      IsLocalRing.maximalIdeal R ^ (n - k)) :
    Module.length R (R ⧸ (IsLocalRing.maximalIdeal R ^ n ⊔ Ideal.span {x})) +
      Module.length R (R ⧸ IsLocalRing.maximalIdeal R ^ (n - k)) ≤
      Module.length R (R ⧸ IsLocalRing.maximalIdeal R ^ n) := by
  classical
  let m := IsLocalRing.maximalIdeal R
  let C : Ideal R := (m ^ n).colon {x}
  let D : Ideal R := m ^ n ⊔ Ideal.span {x}
  have hmnD : m ^ n ≤ D := le_sup_left
  have hleC : m ^ n ≤ C := Ideal.le_colon
  -- mult-x map f : R/C → R/m^n
  let φ : R →ₗ[R] R := LinearMap.lsmul R R x
  have hφ : (C : Submodule R R) ≤ Submodule.comap φ ((m ^ n : Ideal R) : Submodule R R) := by
    intro r hr
    have hmem : r • x ∈ ((m ^ n : Ideal R) : Submodule R R) :=
      (Submodule.mem_colon_singleton).mp hr
    have h1 : φ r = r • x := by
      simp [φ, LinearMap.lsmul_apply, mul_comm]
    rw [Submodule.mem_comap, h1]
    exact hmem
  let f : (R ⧸ C) →ₗ[R] (R ⧸ (m ^ n : Ideal R)) :=
    Submodule.mapQ _ _ φ hφ
  -- quotient map g : R/m^n → R/D
  let g : (R ⧸ (m ^ n : Ideal R)) →ₗ[R] (R ⧸ D) :=
    Submodule.factor hmnD
  have hf_inj : Function.Injective f := by
    intro a b hab
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hfrs : Ideal.Quotient.mk (m ^ n) (φ r) =
        Ideal.Quotient.mk (m ^ n) (φ s) := hab
    have hsub : φ r - φ s ∈ (m ^ n : Ideal R) :=
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hfrs
    have hdiff : (r - s) • x ∈ ((m ^ n : Ideal R) : Submodule R R) := by
      have h1 : (r - s) • x = φ r - φ s := by
        simp [φ, LinearMap.lsmul_apply, smul_eq_mul, mul_comm, sub_mul]
        ring
      rw [h1]
      exact hsub
    have hrsC : r - s ∈ C :=
      (Submodule.mem_colon_singleton).mpr hdiff
    have heq : Ideal.Quotient.mk C r = Ideal.Quotient.mk C s :=
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr hrsC
    exact heq
  have hg_surj : Function.Surjective g := Submodule.factor_surjective _
  have hexact : Function.Exact ⇑f ⇑g := by
    rw [LinearMap.exact_iff]
    have h_range_φ : LinearMap.range φ =
        ((Ideal.span {x} : Ideal R) : Submodule R R) := by
      apply SetLike.ext
      intro y
      constructor
      · rintro ⟨r, rfl⟩
        have h1 : φ r = r * x := by
          simp [φ, LinearMap.lsmul_apply, smul_eq_mul, mul_comm]
        rw [h1]
        exact Ideal.mem_span_singleton'.mpr ⟨r, rfl⟩
      · intro hy
        obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp hy
        refine ⟨s, ?_⟩
        have h1 : φ s = s * x := by
          simp [φ, LinearMap.lsmul_apply, smul_eq_mul, mul_comm]
        rw [h1]
        exact hs
    have h_range_f : LinearMap.range f =
        Submodule.map (Submodule.mkQ ((m ^ n : Ideal R) : Submodule R R))
          (((Ideal.span {x} : Ideal R) : Submodule R R)) := by
      have h1 := Submodule.range_mapQ
        (p := (C : Submodule R R)) (q := ((m ^ n : Ideal R) : Submodule R R))
        φ hφ
      have h2 : LinearMap.range f = Submodule.map
          (Submodule.mkQ ((m ^ n : Ideal R) : Submodule R R))
            (LinearMap.range φ) := h1
      rw [h2, h_range_φ]
    have h_ker_g : LinearMap.ker g =
        Submodule.map (Submodule.mkQ ((m ^ n : Ideal R) : Submodule R R))
          (((Ideal.span {x} : Ideal R) : Submodule R R)) := by
      have h1 := Submodule.ker_mapQ
        (p := ((m ^ n : Ideal R) : Submodule R R))
        (q := (D : Submodule R R)) (LinearMap.id) hmnD
      have h2 : LinearMap.ker g =
          Submodule.map
            (Submodule.mkQ ((m ^ n : Ideal R) : Submodule R R))
            (Submodule.comap LinearMap.id (D : Submodule R R)) := h1
      have hcomap : Submodule.comap LinearMap.id (D : Submodule R R) =
          (D : Submodule R R) := by
        simp
      have hDmap : Submodule.map
          (Submodule.mkQ ((m ^ n : Ideal R) : Submodule R R))
            (D : Submodule R R) =
          Submodule.map (Submodule.mkQ ((m ^ n : Ideal R) : Submodule R R))
            (((Ideal.span {x} : Ideal R) : Submodule R R)) := by
        have hDdef : (D : Submodule R R) =
            ((m ^ n : Ideal R) : Submodule R R) ⊔
              ((Ideal.span {x} : Ideal R) : Submodule R R) := rfl
        rw [hDdef, Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq]
      rw [h2, hcomap, hDmap]
    rw [h_ker_g, h_range_f]
  have hadd := Module.length_eq_add_of_exact f g hf_inj hg_surj hexact
  -- c ≥ a' via C ≤ m^(n-k)
  have hsurjC : Function.Surjective
      (Submodule.factor hC_le : (R ⧸ C) →ₗ[R] (R ⧸ (m ^ (n - k) : Ideal R))) :=
    Submodule.factor_surjective _
  have hleC_len : Module.length R (R ⧸ (m ^ (n - k) : Ideal R)) ≤
      Module.length R (R ⧸ C) :=
    Module.length_le_of_surjective _ hsurjC
  calc Module.length R (R ⧸ D) + Module.length R (R ⧸ (m ^ (n - k) : Ideal R))
      ≤ Module.length R (R ⧸ D) + Module.length R (R ⧸ C) := by
        gcongr
    _ = Module.length R (R ⧸ C) + Module.length R (R ⧸ D) := by
        rw [add_comm]
    _ = Module.length R (R ⧸ (m ^ n : Ideal R)) := hadd.symm

/-- Strict Hilbert–Samuel degree drop for a regular element in the maximal
ideal. From `b_n + a_{n-k} ≤ a_n` with `a=ˢP`, `b=ˢQ`, the difference
`S = P − P.comp(X−Ck)` has degree `< P.degree`, so `Q.degree < P.degree`. -/
theorem natDegree_lt_of_regular {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {x : R} (hx_mem : x ∈ IsLocalRing.maximalIdeal R)
    (hx_reg : x ∈ nonZeroDivisors R) [IsLocalRing (R ⧸ Ideal.span {x})]
    (P Q : Polynomial ℚ)
    (hP : ∀ᶠ N in Filter.atTop,
      ((OAI.Lech.colength R N : ℕ) : ℚ) = P.eval (N : ℚ))
    (hQ : ∀ᶠ N in Filter.atTop,
      ((OAI.Lech.colength (R ⧸ Ideal.span {x}) N : ℕ) : ℚ) = Q.eval (N : ℚ))
    (hPpos : 0 < P.natDegree) :
    Q.natDegree < P.natDegree := by
  classical
  -- Artin–Rees index and per-n Nat inequality b_n + a_{n-k} ≤ a_n
  obtain ⟨k, hAR⟩ := artinRees_containment (R := R) (x := x)
  have hNat : ∀ n ≥ k, OAI.Lech.colength (R ⧸ Ideal.span {x}) n +
      OAI.Lech.colength R (n - k) ≤ OAI.Lech.colength R n := by
    intro n hn
    have hC_le_n : (IsLocalRing.maximalIdeal R ^ n).colon {x} ≤
        IsLocalRing.maximalIdeal R ^ (n - k) :=
      colon_le_shift hx_reg k (hAR) hn
    have hlen := length_le_of_regular (R := R) (x := x) (n := n) (k := k) hC_le_n
    -- Identify the three lengths with colengths via bridges + finiteness
    have hbridge := colength_quot_span_eq_length (R := R) hx_mem n
    have hA := OAI.Lech.colength_cast R n
    have hA' := OAI.Lech.colength_cast R (n - k)
    have hfinA : Module.length R (R ⧸ IsLocalRing.maximalIdeal R ^ n) ≠ ⊤ :=
      OAI.Lech.quotient_length_ne_top R n
    have hleD : Module.length R
        (R ⧸ (IsLocalRing.maximalIdeal R ^ n ⊔ Ideal.span {x})) ≤
        Module.length R (R ⧸ IsLocalRing.maximalIdeal R ^ n) := by
      apply Module.length_le_of_surjective
        (Ideal.Quotient.factorₐ R (le_sup_left (a := IsLocalRing.maximalIdeal R ^ n)
          (b := Ideal.span {x}))).toLinearMap
      intro y
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact ⟨Ideal.Quotient.mk _ r, rfl⟩
    have hfinD : Module.length R
        (R ⧸ (IsLocalRing.maximalIdeal R ^ n ⊔ Ideal.span {x})) ≠ ⊤ :=
      ne_top_of_le_ne_top hfinA hleD
    have hBeq : ((OAI.Lech.colength (R ⧸ Ideal.span {x}) n : ℕ) : ℕ∞) =
        Module.length R
          (R ⧸ (IsLocalRing.maximalIdeal R ^ n ⊔ Ideal.span {x})) := by
      rw [hbridge]
      exact ENat.natCast_toNat hfinD
    have hAeq : ((OAI.Lech.colength R n : ℕ) : ℕ∞) =
        Module.length R (R ⧸ IsLocalRing.maximalIdeal R ^ n) := hA
    have hA'eq : ((OAI.Lech.colength R (n - k) : ℕ) : ℕ∞) =
        Module.length R (R ⧸ IsLocalRing.maximalIdeal R ^ (n - k)) := hA'
    have hle_cast : ((OAI.Lech.colength (R ⧸ Ideal.span {x}) n : ℕ) : ℕ∞) +
        ((OAI.Lech.colength R (n - k) : ℕ) : ℕ∞) ≤
        ((OAI.Lech.colength R n : ℕ) : ℕ∞) := by
      rw [hBeq, hA'eq, hAeq]
      exact hlen
    have hcast_add : ((OAI.Lech.colength (R ⧸ Ideal.span {x}) n +
        OAI.Lech.colength R (n - k) : ℕ) : ℕ∞) =
        ((OAI.Lech.colength (R ⧸ Ideal.span {x}) n : ℕ) : ℕ∞) +
          ((OAI.Lech.colength R (n - k) : ℕ) : ℕ∞) := by
      push_cast
      ring
    have hle_natCast : ((OAI.Lech.colength (R ⧸ Ideal.span {x}) n +
        OAI.Lech.colength R (n - k) : ℕ) : ℕ∞) ≤
        ((OAI.Lech.colength R n : ℕ) : ℕ∞) := by
      rw [hcast_add]
      exact hle_cast
    exact_mod_cast hle_natCast
  -- Unpack eventual equalities to thresholds
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hP
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp hQ
  set Nstar := max (N₀ + k) N₁ with hNstar
  have hNstar_k : k ≤ Nstar := le_trans (Nat.le_add_left k N₀) (Nat.le_max_left _ _)
  -- Shifted evaluation: (P.comp (X − C k)).eval n = P.eval (n−k) for n ≥ k
  have hshift : ∀ n ≥ k, (P.comp (Polynomial.X - Polynomial.C (k : ℚ))).eval
      (n : ℚ) = P.eval (((n - k : ℕ) : ℚ)) := by
    intro n hn
    rw [Polynomial.eval_comp]
    have hqeval : (Polynomial.X - Polynomial.C (k : ℚ)).eval (n : ℚ) =
        (((n - k : ℕ) : ℚ)) := by
      rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      have hcast : (((n - k : ℕ) : ℚ)) = (n : ℚ) - (k : ℚ) := by
        rw [Nat.cast_sub hn]
      rw [hcast]
    rw [hqeval]
  -- Eventual bound Q.eval ≤ S.eval
  set S : Polynomial ℚ := P - P.comp (Polynomial.X - Polynomial.C (k : ℚ)) with hS
  have hQleS : ∀ᶠ N : ℕ in Filter.atTop,
      Q.eval (N : ℚ) ≤ S.eval (N : ℚ) := by
    apply Filter.eventually_atTop.mpr
    refine ⟨Nstar, fun n hn => ?_⟩
    have hnk : n ≥ k := le_trans hNstar_k hn
    have hn₀ : n ≥ N₀ := le_trans (le_trans (Nat.le_add_right N₀ k)
      (Nat.le_max_left _ _)) hn
    have hnk₀ : n - k ≥ N₀ := by
      have h1 : N₀ + k ≤ n := le_trans (Nat.le_max_left _ _) hn
      omega
    have hn₁ : n ≥ N₁ := le_trans (Nat.le_max_right _ _) hn
    have hPn := hN₀ n hn₀
    have hPnk := hN₀ (n - k) hnk₀
    have hQn := hN₁ n hn₁
    have hnat := hNat n hnk
    have hleQ : ((OAI.Lech.colength (R ⧸ Ideal.span {x}) n : ℕ) : ℚ) +
        ((OAI.Lech.colength R (n - k) : ℕ) : ℚ) ≤
        ((OAI.Lech.colength R n : ℕ) : ℚ) := by
      exact_mod_cast hnat
    rw [hPn, hPnk, hQn] at hleQ
    have hSeq : S.eval (n : ℚ) =
        P.eval (n : ℚ) - P.eval (((n - k : ℕ) : ℚ)) := by
      rw [hS, Polynomial.eval_sub, hshift n hnk]
    rw [hSeq]
    linarith
  have hQnonneg : ∀ᶠ N : ℕ in Filter.atTop, 0 ≤ Q.eval (N : ℚ) := by
    filter_upwards [hQ] with N hN
    rw [← hN]
    positivity
  have hQleS_deg : Q.natDegree ≤ S.natDegree :=
    OAI.QuarticPowerFree.natDegree_le_of_eventually_nat_eval_bounds
      Q S hQnonneg hQleS
  -- Strict drop S.natDegree < P.natDegree via leading cancellation
  have hSlt : S.natDegree < P.natDegree := by
    have hPne : P ≠ 0 := by
      intro h0
      rw [h0, Polynomial.natDegree_zero] at hPpos
      exact lt_irrefl 0 hPpos
    have hq_deg : (Polynomial.X - Polynomial.C (k : ℚ)).natDegree = 1 :=
      Polynomial.natDegree_X_sub_C _
    have hq_lead : (Polynomial.X - Polynomial.C (k : ℚ)).leadingCoeff = 1 :=
      Polynomial.leadingCoeff_X_sub_C _
    have hcomp_deg : (P.comp
        (Polynomial.X - Polynomial.C (k : ℚ))).natDegree = P.natDegree := by
      rw [Polynomial.natDegree_comp, hq_deg, mul_one]
    have hcomp_lead : (P.comp
        (Polynomial.X - Polynomial.C (k : ℚ))).leadingCoeff = P.leadingCoeff := by
      rw [Polynomial.leadingCoeff_comp (by rw [hq_deg]; norm_num), hq_lead,
        one_pow, mul_one]
    have hcomp_ne : P.comp (Polynomial.X - Polynomial.C (k : ℚ)) ≠ 0 := by
      intro h0
      have h1 : (P.comp (Polynomial.X - Polynomial.C (k : ℚ))).natDegree = 0 := by
        rw [h0, Polynomial.natDegree_zero]
      rw [hcomp_deg] at h1
      omega
    have hdeg_eq : P.degree =
        (P.comp (Polynomial.X - Polynomial.C (k : ℚ))).degree := by
      rw [Polynomial.degree_eq_natDegree hPne,
        Polynomial.degree_eq_natDegree hcomp_ne, hcomp_deg]
    have hdrop : (P - P.comp
        (Polynomial.X - Polynomial.C (k : ℚ))).degree < P.degree :=
      Polynomial.degree_sub_lt_left hdeg_eq hPne hcomp_lead.symm
    have hSeq : S = P - P.comp (Polynomial.X - Polynomial.C (k : ℚ)) := rfl
    by_cases hS0 : S = 0
    · rw [hS0, Polynomial.natDegree_zero]
      exact hPpos
    · have hdegS := Polynomial.degree_eq_natDegree hS0
      have hdegP := Polynomial.degree_eq_natDegree hPne
      have hlt : (S.natDegree : WithBot ℕ) < (P.natDegree : WithBot ℕ) := by
        rw [← hdegS, ← hdegP]
        rw [hSeq]
        exact hdrop
      exact WithBot.coe_lt_coe.mp hlt
  exact lt_of_le_of_lt hQleS_deg hSlt

/-- An Ideal prime chain yields an LTSeries in the prime spectrum. -/
def idealChain_to_LTSeries {R : Type*} [CommSemiring R] {r : ℕ}
    (ps : Fin (r + 1) → Ideal R) (hprime : ∀ i, (ps i).IsPrime)
    (hlt : StrictMono ps) : LTSeries (PrimeSpectrum R) :=
  ⟨r, fun i => ⟨ps i, hprime i⟩, fun i => by
    have hltI : ps i.castSucc < ps i.succ := hlt Fin.castSucc_lt_succ
    exact (PrimeSpectrum.asIdeal_lt_asIdeal _ _).mp hltI⟩

theorem dimension_le_natDegree_of_eventual_aux : ∀ (d : ℕ) (R : Type) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] [Nontrivial R]
    (P : Polynomial ℚ)
    (hP : ∀ᶠ N in Filter.atTop,
      ((OAI.Lech.colength R N : ℕ) : ℚ) = P.eval (N : ℚ))
    (hdeg : P.natDegree ≤ d),
    OAI.Lech.dimension R ≤ P.natDegree := by
  intro d
  induction d with
  | zero =>
    intro R _ _ _ _ P hP hdeg
    have h0 : P.natDegree = 0 := Nat.le_zero.mp hdeg
    have hdim := dimension_eq_zero_of_natDegree_eq_zero P hP h0
    omega
  | succ d ih =>
    intro R _ _ _ _ P hP hdeg
    by_cases hle : P.natDegree ≤ d
    · exact ih R P hP hle
    · have hPd : P.natDegree = d + 1 := by omega
      -- It suffices to show KrullDimLE, then convert via dimension_cast
      have hKrull : Ring.KrullDimLE P.natDegree R := by
        rw [Ring.krullDimLE_iff]
        unfold ringKrullDim Order.krullDim
        apply iSup_le_iff.mpr
        intro p
        -- Show p.length ≤ P.natDegree as Nat, then cast
        have hNat : p.length ≤ P.natDegree := by
          by_cases hr : p.length = 0
          · omega
          · -- Extract Ideal chain ps from p (no cast needed: indices match)
            set ps : Fin (p.length + 1) → Ideal R := fun i =>
              (p i).asIdeal with hps
            have hprime : ∀ i, (ps i).IsPrime := fun i => (p i).isPrime
            have hlt : StrictMono ps := by
              intro a b hab
              exact (PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr
                (p.strictMono hab)
            -- p0 < p1 gives x ∈ p1 \ p0
            have hpos : 0 < p.length := Nat.pos_of_ne_zero hr
            have hi01 : (⟨0, by omega⟩ : Fin (p.length + 1)) <
                ⟨1, by omega⟩ :=
              Fin.mk_lt_mk.mpr (by norm_num)
            have hp01 : ps ⟨0, by omega⟩ < ps ⟨1, by omega⟩ :=
              hlt hi01
            have hle01 : ps ⟨0, by omega⟩ ≤ ps ⟨1, by omega⟩ :=
              le_of_lt hp01
            have hnge : ¬ ps ⟨1, by omega⟩ ≤ ps ⟨0, by omega⟩ :=
              not_le_of_gt hp01
            have hex : ∃ x : R, x ∈ ps ⟨1, by omega⟩ ∧
                x ∉ ps ⟨0, by omega⟩ := by
              rw [SetLike.le_def] at hnge
              push_neg at hnge
              exact hnge
            obtain ⟨x, hx1, hx0⟩ := hex
            -- R' = R ⧸ ps 0 (local domain) with eventual Q'
            set p0 : Ideal R := ps ⟨0, by omega⟩ with hp0
            have hp0prime : p0.IsPrime := hprime _
            haveI : p0.IsPrime := hp0prime
            have hp0_le : p0 ≤ IsLocalRing.maximalIdeal R :=
              IsLocalRing.le_maximalIdeal_of_isPrime p0
            have hp0_ne : p0 ≠ ⊤ := hp0prime.ne_top
            haveI : Nontrivial (R ⧸ p0) :=
              Ideal.Quotient.nontrivial_iff.mpr hp0_ne
            haveI : IsLocalRing (R ⧸ p0) :=
              IsLocalRing.of_surjective' (Ideal.Quotient.mk _)
                Ideal.Quotient.mk_surjective
            haveI : IsDomain (R ⧸ p0) := Ideal.Quotient.isDomain p0
            obtain ⟨Q', hQ'⟩ := OAI.Lech.IdealGraded.eventuallyPolynomial_length
              (IsLocalRing.maximalIdeal (R ⧸ p0))
            have hQ'event : ∀ᶠ N in Filter.atTop,
                ((OAI.Lech.colength (R ⧸ p0) N : ℕ) : ℚ) =
                  Q'.eval (N : ℚ) := hQ'
            have hQ'le : Q'.natDegree ≤ P.natDegree :=
              natDegree_le_of_quotient p0 hp0_le P Q' hP hQ'event
            -- x' in R' nonzero, in maximalIdeal, regular
            set x' : (R ⧸ p0) := Ideal.Quotient.mk p0 x with hx'
            have hx'ne : x' ≠ 0 := by
              intro h0
              have hmem : x ∈ p0 :=
                Ideal.Quotient.eq_zero_iff_mem.mp h0
              exact hx0 hmem
            have hxm : x ∈ IsLocalRing.maximalIdeal R := by
              have hp1_le : ps ⟨1, by omega⟩ ≤ IsLocalRing.maximalIdeal R :=
                IsLocalRing.le_maximalIdeal_of_isPrime _
              exact hp1_le hx1
            have hx'mem : x' ∈ IsLocalRing.maximalIdeal (R ⧸ p0) := by
              have himg : x' ∈ (IsLocalRing.maximalIdeal R).map
                  (Ideal.Quotient.mk p0) :=
                Ideal.mem_map_of_mem _ hxm
              have hmax_img : ((IsLocalRing.maximalIdeal R).map
                  (Ideal.Quotient.mk p0)).IsMaximal := by
                apply Ideal.IsMaximal.map_of_surjective_of_ker_le
                  Ideal.Quotient.mk_surjective
                rw [Ideal.mk_ker]
                exact hp0_le
              have hmax : IsLocalRing.maximalIdeal (R ⧸ p0) =
                  (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk p0) :=
                (IsLocalRing.eq_maximalIdeal hmax_img).symm
              rw [hmax]
              exact himg
            have hx'reg : x' ∈ nonZeroDivisors (R ⧸ p0) :=
              mem_nonZeroDivisors_iff_ne_zero.mpr hx'ne
            -- R'' = R' ⧸ span{x'} with eventual Q''
            haveI : Nontrivial ((R ⧸ p0) ⧸ Ideal.span {x'}) :=
              quot_span_nontrivial hx'mem
            haveI : IsLocalRing ((R ⧸ p0) ⧸ Ideal.span {x'}) :=
              quot_span_isLocalRing
            obtain ⟨Q'', hQ''⟩ := OAI.Lech.IdealGraded.eventuallyPolynomial_length
              (IsLocalRing.maximalIdeal ((R ⧸ p0) ⧸ Ideal.span {x'}))
            have hQ''event : ∀ᶠ N in Filter.atTop,
                ((OAI.Lech.colength ((R ⧸ p0) ⧸ Ideal.span {x'}) N : ℕ) : ℚ) =
                  Q''.eval (N : ℚ) := hQ''
            -- Q' has positive degree (else R' would be a field, contradicting x')
            have hQ'pos : 0 < Q'.natDegree := by
              by_contra hcon
              push_neg at hcon
              have hQ'zero : Q'.natDegree = 0 := Nat.le_zero.mp hcon
              have hdim0 : OAI.Lech.dimension (R ⧸ p0) = 0 :=
                dimension_eq_zero_of_natDegree_eq_zero Q' hQ'event hQ'zero
              have hkrull0 : ringKrullDim (R ⧸ p0) = 0 := by
                have hcast := OAI.Lech.dimension_cast (R ⧸ p0)
                rw [hdim0, Nat.cast_zero] at hcast
                exact hcast.symm
              have hKrull0 : Ring.KrullDimLE 0 (R ⧸ p0) :=
                Ring.krullDimLE_iff.mpr (by simp [hkrull0])
              haveI : Ring.KrullDimLE 0 (R ⧸ p0) := hKrull0
              have hfield : IsField (R ⧸ p0) :=
                Ring.KrullDimLE.isField_of_isDomain
              have hmax_bot : IsLocalRing.maximalIdeal (R ⧸ p0) = ⊥ :=
                IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield
              have hx'bot : x' ∈ (⊥ : Ideal (R ⧸ p0)) := by
                rw [← hmax_bot]
                exact hx'mem
              have hx'zero : x' = 0 := by simpa using hx'bot
              exact hx'ne hx'zero
            have hQ''lt : Q''.natDegree < Q'.natDegree :=
              natDegree_lt_of_regular hx'mem hx'reg Q' Q'' hQ'event hQ''event hQ'pos
            have hQ''le_d : Q''.natDegree ≤ d := by omega
            have hdimR'' : OAI.Lech.dimension ((R ⧸ p0) ⧸ Ideal.span {x'}) ≤
                Q''.natDegree :=
              ih _ Q'' hQ''event hQ''le_d
            have hKrullR'' : Ring.KrullDimLE Q''.natDegree
                ((R ⧸ p0) ⧸ Ideal.span {x'}) := by
              rw [Ring.krullDimLE_iff]
              have hcast := OAI.Lech.dimension_cast ((R ⧸ p0) ⧸ Ideal.span {x'})
              have hle2 : (OAI.Lech.dimension ((R ⧸ p0) ⧸ Ideal.span {x'}) :
                  WithBot ℕ∞) ≤ (Q''.natDegree : WithBot ℕ∞) :=
                by exact_mod_cast hdimR''
              rw [hcast] at hle2
              exact hle2
            -- Tail chain in R'' of length p.length-1 gives p.length-1 ≤ Q''.deg
            have htail : p.length - 1 ≤ Q''.natDegree := by
              have hpos1 : 1 ≤ p.length := hpos
              -- Index map from tail to original
              -- qs : Fin ((p.length-1)+1) → Ideal R'' via double quotient maps
              let mk1 : R →+* (R ⧸ p0) := Ideal.Quotient.mk p0
              let mk2 : (R ⧸ p0) →+* ((R ⧸ p0) ⧸ Ideal.span {x'}) :=
                Ideal.Quotient.mk _
              have hmk1_surj : Function.Surjective mk1 :=
                Ideal.Quotient.mk_surjective
              have hmk2_surj : Function.Surjective mk2 :=
                Ideal.Quotient.mk_surjective
              have hker1 : RingHom.ker mk1 = p0 := Ideal.mk_ker
              have hker2 : RingHom.ker mk2 = Ideal.span {x'} := Ideal.mk_ker
              set qs : Fin ((p.length - 1) + 1) → Ideal ((R ⧸ p0) ⧸ Ideal.span {x'}) :=
                fun i =>
                  (((ps ⟨i.val + 1, by omega⟩).map mk1).map mk2) with hqs
              have hqs_prime : ∀ i, (qs i).IsPrime := by
                intro i
                -- p0 ≤ ps j and span{x'} ≤ (ps j).map mk1
                have hj_le : p0 ≤ ps ⟨i.val + 1, by omega⟩ := by
                  have h0le : (⟨0, by omega⟩ : Fin (p.length + 1)) ≤
                      ⟨i.val + 1, by omega⟩ := by
                    rw [Fin.mk_le_mk]
                    omega
                  exact hlt.monotone h0le
                have hker_le1 : RingHom.ker mk1 ≤ ps ⟨i.val + 1, by omega⟩ := by
                  rw [hker1]
                  exact hj_le
                have hprime1 : ((ps ⟨i.val + 1, by omega⟩).map mk1).IsPrime :=
                  Ideal.map_isPrime_of_surjective hmk1_surj hker_le1
                have hx'_mem : x' ∈ (ps ⟨i.val + 1, by omega⟩).map mk1 := by
                  have hx_mem : x ∈ ps ⟨i.val + 1, by omega⟩ := by
                    have h1le : (⟨1, by omega⟩ : Fin (p.length + 1)) ≤
                        ⟨i.val + 1, by omega⟩ := by
                      rw [Fin.mk_le_mk]
                      omega
                    exact hlt.monotone h1le hx1
                  have hmem := Ideal.mem_map_of_mem mk1 hx_mem
                  exact hmem
                have hspan_le : Ideal.span {x'} ≤
                    (ps ⟨i.val + 1, by omega⟩).map mk1 :=
                  Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx'_mem)
                have hker_le2 : RingHom.ker mk2 ≤
                    (ps ⟨i.val + 1, by omega⟩).map mk1 := by
                  rw [hker2]
                  exact hspan_le
                exact Ideal.map_isPrime_of_surjective hmk2_surj hker_le2
              have hqs_lt : StrictMono qs := by
                intro a b hab
                -- a < b in Fin gives ja < jb in original, hence ps ja < ps jb
                have hab_val : a.val < b.val := Fin.lt_def.mp hab
                have hjab : (⟨a.val + 1, by omega⟩ : Fin (p.length + 1)) <
                    ⟨b.val + 1, by omega⟩ := by
                  rw [Fin.mk_lt_mk]
                  omega
                have hps_lt : ps ⟨a.val + 1, by omega⟩ <
                    ps ⟨b.val + 1, by omega⟩ := hlt hjab
                -- qs a ≤ qs b via monotone maps
                have hle : qs a ≤ qs b := by
                  have hle_idx : (⟨a.val + 1, by omega⟩ : Fin (p.length + 1)) ≤
                      ⟨b.val + 1, by omega⟩ :=
                    le_of_lt hjab
                  have hps_le : ps ⟨a.val + 1, by omega⟩ ≤
                      ps ⟨b.val + 1, by omega⟩ :=
                    hlt.monotone hle_idx
                  have h1 : ((ps ⟨a.val + 1, by omega⟩).map mk1) ≤
                      ((ps ⟨b.val + 1, by omega⟩).map mk1) :=
                    Ideal.map_mono hps_le
                  exact Ideal.map_mono h1
                -- qs b ≤ qs a would imply ps jb ≤ ps ja, contradicting strict
                have hnge : ¬ qs b ≤ qs a := by
                  intro hge
                  -- comap mk2 gives I'_b ≤ I'_a via absorption
                  have hcomap2 := Ideal.comap_mono (f := mk2) hge
                  have hcm2a : Ideal.comap mk2 (qs a) =
                      (ps ⟨a.val + 1, by omega⟩).map mk1 ⊔ Ideal.comap mk2 ⊥ := by
                    show Ideal.comap mk2
                      (Ideal.map mk2 ((ps _).map mk1)) = _
                    rw [Ideal.comap_map_of_surjective (f := mk2) hmk2_surj]
                  have hcm2b : Ideal.comap mk2 (qs b) =
                      (ps ⟨b.val + 1, by omega⟩).map mk1 ⊔ Ideal.comap mk2 ⊥ := by
                    show Ideal.comap mk2
                      (Ideal.map mk2 ((ps _).map mk1)) = _
                    rw [Ideal.comap_map_of_surjective (f := mk2) hmk2_surj]
                  have hcomap_bot2 : Ideal.comap mk2 (⊥ : Ideal _) =
                      Ideal.span {x'} := by
                    rw [← RingHom.ker_eq_comap_bot, hker2]
                  -- span ≤ each I' (same argument as in hqs_prime, for a and b)
                  have hspan_a : Ideal.span {x'} ≤
                      (ps ⟨a.val + 1, by omega⟩).map mk1 := by
                    have hx_mem : x ∈ ps ⟨a.val + 1, by omega⟩ := by
                      have h1le : (⟨1, by omega⟩ : Fin (p.length + 1)) ≤
                          ⟨a.val + 1, by omega⟩ := by
                        rw [Fin.mk_le_mk]
                        omega
                      exact hlt.monotone h1le hx1
                    have hmem := Ideal.mem_map_of_mem mk1 hx_mem
                    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmem)
                  have hspan_b : Ideal.span {x'} ≤
                      (ps ⟨b.val + 1, by omega⟩).map mk1 := by
                    have hx_mem : x ∈ ps ⟨b.val + 1, by omega⟩ := by
                      have h1le : (⟨1, by omega⟩ : Fin (p.length + 1)) ≤
                          ⟨b.val + 1, by omega⟩ := by
                        rw [Fin.mk_le_mk]
                        omega
                      exact hlt.monotone h1le hx1
                    have hmem := Ideal.mem_map_of_mem mk1 hx_mem
                    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmem)
                  have hcomap_le_a : Ideal.comap mk2 (⊥ : Ideal _) ≤
                      (ps ⟨a.val + 1, by omega⟩).map mk1 := by
                    rw [hcomap_bot2]
                    exact hspan_a
                  have hcomap_le_b : Ideal.comap mk2 (⊥ : Ideal _) ≤
                      (ps ⟨b.val + 1, by omega⟩).map mk1 := by
                    rw [hcomap_bot2]
                    exact hspan_b
                  have habs_a : (ps ⟨a.val + 1, by omega⟩).map mk1 ⊔
                      Ideal.comap mk2 (⊥ : Ideal _) =
                      (ps ⟨a.val + 1, by omega⟩).map mk1 :=
                    le_antisymm (sup_le le_rfl hcomap_le_a) le_sup_left
                  have habs_b : (ps ⟨b.val + 1, by omega⟩).map mk1 ⊔
                      Ideal.comap mk2 (⊥ : Ideal _) =
                      (ps ⟨b.val + 1, by omega⟩).map mk1 :=
                    le_antisymm (sup_le le_rfl hcomap_le_b) le_sup_left
                  have hI_le : (ps ⟨b.val + 1, by omega⟩).map mk1 ≤
                      (ps ⟨a.val + 1, by omega⟩).map mk1 := by
                    have h1 : Ideal.comap mk2 (qs b) ≤
                        Ideal.comap mk2 (qs a) := hcomap2
                    rw [hcm2b, hcm2a, habs_b, habs_a] at h1
                    exact h1
                  -- comap mk1 gives ps jb ≤ ps ja, contradicting strict
                  have hcomap1 := Ideal.comap_mono (f := mk1) hI_le
                  have hcm1a : Ideal.comap mk1
                      (((ps ⟨a.val + 1, by omega⟩).map mk1)) =
                      ps ⟨a.val + 1, by omega⟩ ⊔ Ideal.comap mk1 ⊥ := by
                    rw [Ideal.comap_map_of_surjective (f := mk1) hmk1_surj]
                  have hcm1b : Ideal.comap mk1
                      (((ps ⟨b.val + 1, by omega⟩).map mk1)) =
                      ps ⟨b.val + 1, by omega⟩ ⊔ Ideal.comap mk1 ⊥ := by
                    rw [Ideal.comap_map_of_surjective (f := mk1) hmk1_surj]
                  have hcomap_bot1 : Ideal.comap mk1 (⊥ : Ideal _) = p0 := by
                    rw [← RingHom.ker_eq_comap_bot, hker1]
                  have hp0_le_a : p0 ≤ ps ⟨a.val + 1, by omega⟩ := by
                    have h0le : (⟨0, by omega⟩ : Fin (p.length + 1)) ≤
                        ⟨a.val + 1, by omega⟩ := by
                      rw [Fin.mk_le_mk]
                      omega
                    exact hlt.monotone h0le
                  have hp0_le_b : p0 ≤ ps ⟨b.val + 1, by omega⟩ := by
                    have h0le : (⟨0, by omega⟩ : Fin (p.length + 1)) ≤
                        ⟨b.val + 1, by omega⟩ := by
                      rw [Fin.mk_le_mk]
                      omega
                    exact hlt.monotone h0le
                  have hps_le : ps ⟨b.val + 1, by omega⟩ ≤
                      ps ⟨a.val + 1, by omega⟩ := by
                    have h1 : Ideal.comap mk1
                        (((ps ⟨b.val + 1, by omega⟩).map mk1)) ≤
                        Ideal.comap mk1
                          (((ps ⟨a.val + 1, by omega⟩).map mk1)) := hcomap1
                    rw [hcm1b, hcm1a] at h1
                    have habs_a' : ps ⟨a.val + 1, by omega⟩ ⊔
                        Ideal.comap mk1 (⊥ : Ideal _) =
                        ps ⟨a.val + 1, by omega⟩ := by
                      have hle_c : Ideal.comap mk1 (⊥ : Ideal _) ≤
                          ps ⟨a.val + 1, by omega⟩ := by
                        rw [hcomap_bot1]
                        exact hp0_le_a
                      exact le_antisymm (sup_le le_rfl hle_c) le_sup_left
                    have habs_b' : ps ⟨b.val + 1, by omega⟩ ⊔
                        Ideal.comap mk1 (⊥ : Ideal _) =
                        ps ⟨b.val + 1, by omega⟩ := by
                      have hle_c : Ideal.comap mk1 (⊥ : Ideal _) ≤
                          ps ⟨b.val + 1, by omega⟩ := by
                        rw [hcomap_bot1]
                        exact hp0_le_b
                      exact le_antisymm (sup_le le_rfl hle_c) le_sup_left
                    rw [habs_b', habs_a'] at h1
                    exact h1
                  exact (not_le_of_gt hps_lt) hps_le
                exact lt_of_le_not_ge hle hnge
              -- LTSeries of length p.length-1 in R'' and Krull bound
              set qser : LTSeries (PrimeSpectrum ((R ⧸ p0) ⧸ Ideal.span {x'})) :=
                idealChain_to_LTSeries qs hqs_prime hqs_lt with hqser
              have hlen_eq : qser.length = p.length - 1 := rfl
              have hbound : ((qser.length : ℕ) : WithBot ℕ∞) ≤
                  (Q''.natDegree : WithBot ℕ∞) := by
                have h1 := Order.LTSeries.length_le_krullDim qser
                have h2 := hKrullR''.krullDim_le
                exact le_trans h1 h2
              have hle_nat : qser.length ≤ Q''.natDegree := by
                exact_mod_cast hbound
              rw [hlen_eq] at hle_nat
              exact hle_nat
            omega
        exact_mod_cast hNat
      have hdim_le : OAI.Lech.dimension R ≤ P.natDegree := by
        have hcast := OAI.Lech.dimension_cast R
        have hle2 : (OAI.Lech.dimension R : WithBot ℕ∞) ≤
            (P.natDegree : WithBot ℕ∞) := by
          rw [hcast]
          exact Ring.krullDimLE_iff.mp hKrull
        exact_mod_cast hle2
      exact hdim_le

/-- Clean lower bound: Krull/Lech dimension is at most the Hilbert–Samuel degree. -/
theorem dimension_le_natDegree_of_eventual (R : Type) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] [Nontrivial R]
    (P : Polynomial ℚ)
    (hP : ∀ᶠ N in Filter.atTop,
      ((OAI.Lech.colength R N : ℕ) : ℚ) = P.eval (N : ℚ)) :
    OAI.Lech.dimension R ≤ P.natDegree :=
  dimension_le_natDegree_of_eventual_aux P.natDegree R P hP le_rfl

end DistinctDistances.AffineVariety
