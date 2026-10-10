import DistinctDistances.TrackE.Stars
import DistinctDistances.TrackE.Graph
import DistinctDistances.TrackE.Concentration
import DistinctDistances.TrackE.Contradiction

/-!
# Top level: the lower-bound clause (`introduction.tex:19-26`, `reduction.tex:10-28, 514-521`)

The paper argues along a contradiction sequence in the least failing dimension. Here the step is
a uniform single-configuration statement, `regime_excluded`: in dimension `d ≥ 3`, under IH(d),
`M > ε₀ A` once `N ≥ N₀`. A failure of the bound gives a regime sequence (the frozen framework's
`failure_gives_regime`), along which `M/A → 0` and `N → ∞`: this contradicts `regime_excluded`.
-/

open Filter
open scoped Topology

namespace DistinctDistances

noncomputable section

/-- A linear isometry preserves the distance set. -/
theorem distinctDistances_image_linearIsometryEquiv {d : ℕ} (P : Finset (RPoint d))
    (R : RPoint d ≃ₗᵢ[ℝ] RPoint d) :
    distinctDistances (P.image R) = distinctDistances P := by
  classical
  unfold distinctDistances distanceSet
  congr 1
  ext r
  simp only [Finset.mem_image, Finset.mem_offDiag, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨⟨a', ha', rfl⟩, ⟨b', hb', rfl⟩, hne⟩, rfl⟩
    exact ⟨a', b', ⟨ha', hb', fun h => hne (h ▸ rfl)⟩, (R.dist_map a' b').symm⟩
  · rintro ⟨a, b, ⟨ha, hb, hne⟩, rfl⟩
    exact ⟨R a, R b, ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, fun h => hne (R.injective h)⟩,
      R.dist_map a b⟩

/-- The star of `R b` in the transported selection is the image of the star of `b`. -/
theorem star_image_prodMap {d : ℕ} (S : Finset (RPoint d × RPoint d))
    (R : RPoint d ≃ₗᵢ[ℝ] RPoint d) (b : RPoint d) :
    star (S.image (Prod.map R R)) (R b) = (star S b).image R := by
  classical
  ext q
  constructor
  · intro hq
    simp only [star, Finset.mem_image, Finset.mem_filter] at hq ⊢
    obtain ⟨e, ⟨he, he1⟩, rfl⟩ := hq
    obtain ⟨e', he', rfl⟩ := he
    exact ⟨e'.2, ⟨e', ⟨he', R.injective he1⟩, rfl⟩, rfl⟩
  · intro hq
    simp only [star, Finset.mem_image, Finset.mem_filter] at hq ⊢
    obtain ⟨c, ⟨e, ⟨he, he1⟩, rfl⟩, rfl⟩ := hq
    exact ⟨Prod.map R R e, ⟨⟨e, he, rfl⟩, by simp [he1]⟩, rfl⟩

/-- Eventually `n^2 e^{-κ n} < 1/2`. -/
theorem exists_sq_mul_exp_neg_lt {κ : ℝ} (hκ : 0 < κ) :
    ∃ N₂ : ℕ, ∀ n : ℕ, N₂ ≤ n → (n : ℝ) ^ 2 * Real.exp (-(κ * n)) < 1 / 2 := by
  have ht : Tendsto (fun n : ℕ => (κ * n) ^ 2 * Real.exp (-(κ * n))) atTop (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop hκ)
  have hk2 : (0 : ℝ) < κ ^ 2 / 2 := by positivity
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hk2))
  refine ⟨N₂, fun n hn => ?_⟩
  have h := hN₂ n hn
  have hκ2 : 0 < κ ^ 2 := by positivity
  rw [mul_pow] at h
  have h' : κ ^ 2 * ((n : ℝ) ^ 2 * Real.exp (-(κ * n))) < κ ^ 2 * (1 / 2) := by
    rw [← mul_assoc]; linarith
  exact lt_of_mul_lt_mul_left h' hκ2.le

/-- `N^2 = A^d`. -/
theorem sq_eq_Ascale_pow {d : ℕ} (hd : 1 ≤ d) (N : ℕ) : (N : ℝ) ^ 2 = Ascale d N ^ d := by
  unfold Ascale
  rw [← Real.rpow_natCast (_ ^ _), ← Real.rpow_mul (Nat.cast_nonneg N)]
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  rw [div_mul_cancel₀ _ hd']
  norm_cast

/-- TOP.step (`reduction.tex:514-521`, assembling `red:main-contradiction` with the data built in
`reduction.tex:96-453`): in dimension `d ≥ 3`, under IH(d), the ratio `M/A` is bounded below by a
fixed `ε₀ > 0` for all large configurations. -/
theorem regime_excluded (d : ℕ) (hd : 3 ≤ d) (hIH : IH d) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ N₀ : ℕ, ∀ P : Finset (RPoint d), N₀ ≤ P.card →
      ε₀ * Ascale d P.card < Mcount P := by
  classical
  obtain ⟨c, hc, ε₁, hε₁, N₁, hstars⟩ := Reduction.exists_selection_independentStars hd hIH
  obtain ⟨c₃, C₀, ε₂, hc₃, hC₀, hε₂, hgraph⟩ := Reduction.exists_retained_graph hd c hc
  obtain ⟨c₄, hc₄, hglobal⟩ := Reduction.global_rank_lower hd
  obtain ⟨C, hC, hlocal⟩ := Reduction.local_concentration_ambient hd C₀
  set s₀ := Nat.choose d 2 with hs₀
  set C₁ : ℝ := ((1 + s₀ : ℕ) : ℝ) ^ s₀ with hC₁def
  have hC₁ : 0 < C₁ := by positivity
  set θ : ℝ := min 1 (c₄ / (4 * C₁)) with hθdef
  have hθ0 : 0 < θ := lt_min one_pos (by positivity)
  have hθ1 : θ ≤ 1 := min_le_left _ _
  have hθC : 2 * θ * C₁ < c₄ := by
    have h1 : θ ≤ c₄ / (4 * C₁) := min_le_right _ _
    have h2 : θ * C₁ ≤ c₄ / 4 := by
      calc θ * C₁ ≤ c₄ / (4 * C₁) * C₁ := by gcongr
        _ = c₄ / 4 := by field_simp
    linarith
  set κ : ℝ := θ ^ 2 * c₃ / 2 with hκdef
  have hκ : 0 < κ := by positivity
  obtain ⟨N₂, hN₂⟩ := exists_sq_mul_exp_neg_lt hκ
  set ε₀ : ℝ := min (min ε₁ ε₂) (min 1 (θ * c₃ / (4 * C))) with hε₀def
  have hε₀ : 0 < ε₀ := by
    refine lt_min (lt_min hε₁ hε₂) (lt_min one_pos ?_)
    positivity
  have hε₀₁ : ε₀ ≤ ε₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hε₀₂ : ε₀ ≤ ε₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hε₀1 : ε₀ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hε₀C : ε₀ ≤ θ * c₃ / (4 * C) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ε₀, hε₀, max (max N₁ N₂) 2, ?_⟩
  intro P hP
  by_contra hlt'
  have hlt := not_lt.mp hlt'
  have hPN₁ : N₁ ≤ P.card := (le_max_left _ _).trans ((le_max_left _ _).trans hP)
  have hPN₂ : N₂ ≤ P.card := (le_max_right _ _).trans ((le_max_left _ _).trans hP)
  have hN2 : 2 ≤ P.card := (le_max_right _ _).trans hP
  set N := P.card with hNdef
  set A := Ascale d N with hAdef
  set M := Mcount P with hMdef
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hA1 : 1 ≤ A := Real.one_le_rpow hN1 (by positivity)
  have hApos : 0 < A := lt_of_lt_of_le one_pos hA1
  have hAN : A ≤ N := Real.rpow_le_self_of_one_le hN1 (by
    rw [div_le_one hdpos]; exact_mod_cast (show 2 ≤ d by omega))
  have hM1 : 1 ≤ M := by
    simp only [hMdef, Mcount]; linarith [(Nat.cast_nonneg (distinctDistances P) : (0 : ℝ) ≤ _)]
  have hMpos : 0 < M := lt_of_lt_of_le one_pos hM1
  have hMA1 : M ≤ ε₁ * A := hlt.trans (by gcongr)
  have hMA2 : M ≤ ε₂ * A := hlt.trans (by gcongr)
  have hMA : M ≤ A := hlt.trans (by nlinarith)
  obtain ⟨S, hS, hScard, hSind⟩ := hstars P hPN₁ hMA1
  obtain ⟨R, W, adj, hWsub, hWne, hadj, hdeg, hiso⟩ := hgraph P S hS hN2 hScard hMA2
  set Q := P.image R with hQdef
  have hQcard : Q.card = N := Finset.card_image_of_injective _ R.injective
  have hMQ : Mcount Q = M := by
    simp only [hMdef, Mcount, hQdef, distinctDistances_image_linearIsometryEquiv]
  have hglob := hglobal P Q hN2 hQcard hMA (by rw [hMQ]; exact hMA) W hWsub
  set D := testDegree d N with hDdef
  have hDA : (D : ℝ) ≤ A := Nat.floor_le hApos.le
  have hloc : ∀ v ∈ W, ∀ f : MvPolynomial (SkewIdx (d + 1)) ℂ, f.totalDegree ≤ D →
      (∃ z ∈ (fun v : RPoint d × RPoint d => Reduction.pairFlat v.1 v.2) v, MvPolynomial.eval z f ≠ 0) →
      ((W.filter fun w => adj v w ∧ ∀ z ∈ (fun v : RPoint d × RPoint d => Reduction.pairFlat v.1 v.2) v ∩
          (fun v : RPoint d × RPoint d => Reduction.pairFlat v.1 v.2) w,
          MvPolynomial.eval z f = 0).card : ℝ) ≤ C * A ^ (d - 1) := by
    intro v hv f hf hnz
    obtain ⟨_, hv2⟩ := Finset.mem_product.mp (hWsub hv)
    obtain ⟨b, _, hbv⟩ := Finset.mem_image.mp hv2
    have hTQ : IndependentStar D v.2 (star (S.image (Prod.map R R)) v.2) := by
      rw [← hbv, star_image_prodMap]
      exact IndependentStar.image_linearIsometryEquiv (hSind b) R
    have h := hlocal A hA1 D hDA v.1 v.2 (star S v.1) (star (S.image (Prod.map R R)) v.2)
      (hSind v.1) hTQ (W.filter fun w => adj v w) ?_ ?_ f hf hnz
    · rwa [Finset.filter_filter] at h
    · intro y hy
      obtain ⟨_, hvy⟩ := Finset.mem_filter.mp hy
      obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hadj v y hvy
      refine ⟨?_, ?_, h3, h4⟩
      · unfold star
        exact Finset.mem_image.mpr ⟨(v.1, y.1), Finset.mem_filter.mpr ⟨h1, rfl⟩, rfl⟩
      · unfold star
        exact Finset.mem_image.mpr ⟨(v.2, y.2), Finset.mem_filter.mpr ⟨h2, rfl⟩, rfl⟩
    · intro T
      rw [Finset.filter_filter]
      exact hiso v hv T
  have hflat : ∀ v ∈ W, (restrictionRank ((fun v : RPoint d × RPoint d => Reduction.pairFlat v.1 v.2) v)
      D : ℝ) ≤ C₁ * A ^ s₀ := by
    intro v _
    have h1 := Reduction.restrictionRank_pairFlat_le v.1 v.2 D
    have h2 := Nat.choose_le_pow (D + s₀) s₀
    have h3 : ((D + s₀ : ℕ) : ℝ) ≤ ((1 + s₀ : ℕ) : ℝ) * A := by
      push_cast
      have : (s₀ : ℝ) ≤ s₀ * A := le_mul_of_one_le_right (Nat.cast_nonneg _) hA1
      nlinarith
    calc (restrictionRank (Reduction.pairFlat v.1 v.2) D : ℝ)
        ≤ ((Nat.choose (D + s₀) s₀ : ℕ) : ℝ) := by exact_mod_cast h1
      _ ≤ ((D + s₀ : ℕ) : ℝ) ^ s₀ := by exact_mod_cast h2
      _ ≤ (((1 + s₀ : ℕ) : ℝ) * A) ^ s₀ := by gcongr
      _ = C₁ * A ^ s₀ := by rw [mul_pow]
  have hNA := sq_eq_Ascale_pow (show 1 ≤ d by omega) N
  have hcap : C * A ^ (d - 1) < θ * (c₃ * (N : ℝ) ^ 2 / M) / 2 := by
    have hMle : M ≤ θ * c₃ / (4 * C) * A := hlt.trans (by gcongr)
    have hAd : A ^ d = A ^ (d - 1) * A := by
      rw [← pow_succ]; congr 1; omega
    rw [hNA, hAd]
    have hAd1 : 0 < A ^ (d - 1) := by positivity
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2), mul_div_assoc', lt_div_iff₀ hMpos]
    have h4 : 4 * C * M ≤ θ * c₃ * A := by
      have := mul_le_mul_of_nonneg_left hMle (show (0 : ℝ) ≤ 4 * C by positivity)
      calc 4 * C * M ≤ 4 * C * (θ * c₃ / (4 * C) * A) := this
        _ = θ * c₃ * A := by field_simp
    have h5 : 0 < θ * c₃ * A * A ^ (d - 1) := by positivity
    nlinarith
  have hunion : (W.card : ℝ) * Real.exp (-(θ ^ 2 * (c₃ * (N : ℝ) ^ 2 / M) / 2)) < 1 / 2 := by
    have hWcard : (W.card : ℝ) ≤ (N : ℝ) ^ 2 := by
      have := Finset.card_le_card hWsub
      rw [Finset.card_product, hQcard] at this
      exact_mod_cast (show W.card ≤ N ^ 2 by rw [sq]; exact this)
    have hexp : Real.exp (-(θ ^ 2 * (c₃ * (N : ℝ) ^ 2 / M) / 2)) ≤ Real.exp (-(κ * N)) := by
      apply Real.exp_le_exp.mpr
      have hMN : M ≤ N := hMA.trans hAN
      have : (N : ℝ) ≤ (N : ℝ) ^ 2 / M := by
        rw [le_div_iff₀ hMpos, sq]
        exact mul_le_mul_of_nonneg_left hMN hNpos.le
      have hk : κ * N ≤ θ ^ 2 * (c₃ * (N : ℝ) ^ 2 / M) / 2 := by
        rw [hκdef]
        have h0 : 0 ≤ θ ^ 2 * c₃ / 2 := by positivity
        calc θ ^ 2 * c₃ / 2 * N ≤ θ ^ 2 * c₃ / 2 * ((N : ℝ) ^ 2 / M) :=
              mul_le_mul_of_nonneg_left this h0
          _ = θ ^ 2 * (c₃ * (N : ℝ) ^ 2 / M) / 2 := by ring
      linarith
    calc (W.card : ℝ) * Real.exp (-(θ ^ 2 * (c₃ * (N : ℝ) ^ 2 / M) / 2))
        ≤ (N : ℝ) ^ 2 * Real.exp (-(κ * N)) := by
          apply mul_le_mul hWcard hexp (Real.exp_pos _).le (by positivity)
      _ < 1 / 2 := hN₂ N hPN₂
  exact Reduction.main_contradiction (fun v : RPoint d × RPoint d => Reduction.pairFlat v.1 v.2) W hWne adj
    D s₀ A c₄ C₁ (C * A ^ (d - 1)) (c₃ * (N : ℝ) ^ 2 / M) θ hApos hglob hflat hdeg hloc hθ0 hθ1
    hθC hcap hunion

/-- TOP.lower, inductive step (`reduction.tex:514-521`): IH(d) gives the bound in dimension `d`.
A failure gives a regime sequence, along which `M/A → 0` and `|P_k| → ∞`, contradicting
`regime_excluded`. -/
theorem lowerBound_of_IH (d : ℕ) (hd : 3 ≤ d) (hIH : IH d) : LowerBound d := by
  by_contra hfail
  obtain ⟨r⟩ := failure_gives_regime hd hIH hfail
  obtain ⟨ε₀, hε₀, N₀, hN₀⟩ := regime_excluded d hd hIH
  have hsmall := r.M_div_A_tendsto.eventually (gt_mem_nhds hε₀)
  have hlarge := r.card_tendsto.eventually (eventually_ge_atTop N₀)
  obtain ⟨k, hk, hkN⟩ := (hsmall.and hlarge).exists
  have hlt := hN₀ (r.P k) hkN
  have hA := r.A_pos k
  have hMA : r.M k < ε₀ * r.A k := by
    have := (div_lt_iff₀ hA).mp hk
    linarith
  have hM : Mcount (r.P k) = r.M k := by
    simp only [Mcount, Regime.M]
    ring
  have hAeq : Ascale d (r.P k).card = r.A k := rfl
  rw [hM, hAeq] at hlt
  linarith

/-- TOP.lower = `thm:main` (`introduction.tex:19-26`): the lower-bound clause of the target,
by strong induction on `d ≥ 3`. -/
theorem lower_bound : ∀ d : ℕ, 3 ≤ d →
    ∃ c : ℝ, 0 < c ∧ ∀ P : Finset (EuclideanSpace ℝ (Fin d)), 2 ≤ P.card →
      c * (P.card : ℝ) ^ ((2 : ℝ) / (d : ℝ)) ≤ (distinctDistances P : ℝ) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd
    exact lowerBound_of_IH d hd fun u hu hud => ih u hud hu

end

end DistinctDistances
