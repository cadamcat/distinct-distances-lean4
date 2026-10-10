import DistinctDistances.Main

open Filter

namespace NonVacuity

/-! Satisfiability, concrete values and two-sided growth for the distinct-distances bound. -/

/-- The Nat-valued distance counts attained by `n`-point sets in dimension `d`. -/
noncomputable def distNatSet (d n : ℕ) : Set ℕ :=
  { k : ℕ | ∃ P : Finset (EuclideanSpace ℝ (Fin d)), P.card = n ∧ distinctDistances P = k }

/-- The real-valued distance counts attained by `n`-point sets in dimension `d`. -/
noncomputable def distRealSet (d n : ℕ) : Set ℝ :=
  { r : ℝ | ∃ P : Finset (EuclideanSpace ℝ (Fin d)), P.card = n ∧ (distinctDistances P : ℝ) = r }

/-- The minimum number `g_d(n)` of distinct distances, as an `sInf` over point sets. -/
noncomputable def g (d n : ℕ) : ℝ := sInf (distRealSet d n)

/-- There are `n`-point sets in every positive dimension (line construction). -/
theorem line_points_exist (d : ℕ) (hd : 0 < d) (n : ℕ) :
    ∃ P : Finset (EuclideanSpace ℝ (Fin d)), P.card = n := by
  classical
  let i0 : Fin d := ⟨0, hd⟩
  have hfinj : Function.Injective
      (fun i : ℕ => EuclideanSpace.single i0 (i : ℝ)) := by
    intro a b hab
    have h2 := congrArg (fun x : EuclideanSpace ℝ (Fin d) => x i0) hab
    simp only [EuclideanSpace.single_apply, if_pos rfl] at h2
    exact Nat.cast_injective h2
  exact ⟨(Finset.range n).image
      (fun i : ℕ => EuclideanSpace.single i0 (i : ℝ)),
    by rw [Finset.card_image_of_injective _ hfinj, Finset.card_range]⟩

/-- The index type `Fin 3` is nonempty. -/
theorem fin_three_nonempty : Nonempty (Fin 3) :=
  ⟨0⟩

/-- The real exponent `2/d` is positive and `d` casts to a nonzero real for `d ≥ 3`. -/
theorem exponent_pos (d : ℕ) (hd : 3 ≤ d) :
    0 < (2 : ℝ) / (d : ℝ) ∧ (d : ℝ) ≠ 0 := by
  have hdR : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast (by omega : 0 < d)
  exact ⟨div_pos (by norm_num) hdR, ne_of_gt hdR⟩

/-- Real powers of `n ≥ 2` are positive. -/
theorem rpow_base_pos (d n : ℕ) (hn : 2 ≤ n) :
    0 < (n : ℝ) ^ ((2 : ℝ) / (d : ℝ)) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (by omega : 0 < n)
  exact Real.rpow_pos_of_pos hnR _

/-- A two-point set in `ℝ^3` has cardinality two. -/
theorem pair_card :
    ({0, EuclideanSpace.single (0 : Fin 3) 1} :
      Finset (EuclideanSpace ℝ (Fin 3))).card = 2 := by
  classical
  apply Finset.card_pair
  intro h
  have hz : EuclideanSpace.single (0 : Fin 3) (1 : ℝ) = 0 ↔ (1 : ℝ) = 0 := by
    simp
  have h2 : EuclideanSpace.single (0 : Fin 3) (1 : ℝ) = 0 := h.symm
  rw [hz] at h2
  norm_num at h2

/-- The off-diagonal of the two-point set has two ordered pairs. -/
theorem pair_offDiag_card :
    ({0, EuclideanSpace.single (0 : Fin 3) 1} :
      Finset (EuclideanSpace ℝ (Fin 3))).offDiag.card = 2 := by
  classical
  rw [Finset.offDiag_card, pair_card]

/-- The distance set of `{0, e₀}` in `ℝ^3` is `{1}`. -/
theorem pair_distSet :
    distanceSet ({0, EuclideanSpace.single (0 : Fin 3) 1} :
      Finset (EuclideanSpace ℝ (Fin 3))) = {1} := by
  classical
  have hne : (0 : EuclideanSpace ℝ (Fin 3)) ≠ EuclideanSpace.single 0 1 := by
    intro h
    have hz : EuclideanSpace.single (0 : Fin 3) (1 : ℝ) = 0 ↔ (1 : ℝ) = 0 := by
      simp
    have h2 : EuclideanSpace.single (0 : Fin 3) (1 : ℝ) = 0 := h.symm
    rw [hz] at h2
    norm_num at h2
  have hoff : Finset.offDiag ({0, EuclideanSpace.single (0 : Fin 3) 1} :
      Finset (EuclideanSpace ℝ (Fin 3)))
      = {(0, EuclideanSpace.single (0 : Fin 3) 1),
         (EuclideanSpace.single (0 : Fin 3) 1, 0)} := by
    rw [Finset.offDiag_insert (by simpa using hne), Finset.offDiag_singleton,
      Finset.singleton_product_singleton, Finset.singleton_product_singleton]
    simp
  have hdist : dist (0 : EuclideanSpace ℝ (Fin 3))
      (EuclideanSpace.single (0 : Fin 3) 1) = 1 := by
    rw [dist_zero_left, PiLp.norm_single, norm_one]
  have himg : (Finset.offDiag ({0, EuclideanSpace.single (0 : Fin 3) 1} :
      Finset (EuclideanSpace ℝ (Fin 3)))).image
      (fun pair : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        dist pair.1 pair.2) = {1} := by
    rw [hoff]
    ext r
    simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨p, hp, rfl⟩
      rcases hp with rfl | rfl
      · simp [hdist]
      · simp [dist_comm, hdist]
    · rintro rfl
      exact ⟨(0, EuclideanSpace.single (0 : Fin 3) 1), Or.inl rfl, hdist⟩
  unfold distanceSet
  exact himg

/-- Two points at distance one determine exactly one distinct distance. -/
theorem pair_distinct :
    distinctDistances ({0, EuclideanSpace.single (0 : Fin 3) 1} :
      Finset (EuclideanSpace ℝ (Fin 3))) = 1 := by
  classical
  unfold distinctDistances
  rw [pair_distSet, Finset.card_singleton]

/-- Three collinear points in `ℝ^3` form a three-element set. -/
theorem triple_card :
    ({0, EuclideanSpace.single (0 : Fin 3) 1,
      EuclideanSpace.single (0 : Fin 3) 2} :
      Finset (EuclideanSpace ℝ (Fin 3))).card = 3 := by
  classical
  have h01 : (0 : EuclideanSpace ℝ (Fin 3)) ≠ EuclideanSpace.single 0 1 := by
    intro h
    have hz : EuclideanSpace.single (0 : Fin 3) (1 : ℝ) = 0 ↔ (1 : ℝ) = 0 := by
      simp
    have h2 : EuclideanSpace.single (0 : Fin 3) (1 : ℝ) = 0 := h.symm
    rw [hz] at h2
    norm_num at h2
  have h02 : (0 : EuclideanSpace ℝ (Fin 3)) ≠ EuclideanSpace.single 0 2 := by
    intro h
    have hz : EuclideanSpace.single (0 : Fin 3) (2 : ℝ) = 0 ↔ (2 : ℝ) = 0 := by
      simp
    have h2 : EuclideanSpace.single (0 : Fin 3) (2 : ℝ) = 0 := h.symm
    rw [hz] at h2
    norm_num at h2
  have h12 : EuclideanSpace.single (0 : Fin 3) (1 : ℝ) ≠
      EuclideanSpace.single (0 : Fin 3) (2 : ℝ) := by
    intro h
    have h2 := congrArg
      (fun x : EuclideanSpace ℝ (Fin 3) => x (0 : Fin 3)) h
    simp only [EuclideanSpace.single_apply, if_pos rfl] at h2
    norm_num at h2
  have hmem : (0 : EuclideanSpace ℝ (Fin 3)) ∉
      ({EuclideanSpace.single (0 : Fin 3) (1 : ℝ),
        EuclideanSpace.single (0 : Fin 3) (2 : ℝ)} :
        Finset (EuclideanSpace ℝ (Fin 3))) := by
    simp [h01, h02]
  rw [Finset.card_insert_of_notMem hmem, Finset.card_pair h12]

/-- The distance set of `{0, e₀, 2e₀}` in `ℝ^3` is `{1, 2}`. -/
theorem triple_distSet :
    distanceSet ({0, EuclideanSpace.single (0 : Fin 3) 1,
      EuclideanSpace.single (0 : Fin 3) 2} :
      Finset (EuclideanSpace ℝ (Fin 3))) = {1, 2} := by
  classical
  set a : EuclideanSpace ℝ (Fin 3) := 0 with ha
  set b : EuclideanSpace ℝ (Fin 3) :=
    EuclideanSpace.single (0 : Fin 3) 1 with hb
  set c : EuclideanSpace ℝ (Fin 3) :=
    EuclideanSpace.single (0 : Fin 3) 2 with hc
  have h01 : a ≠ b := by
    intro h
    simp only [ha, hb] at h
    have hz : EuclideanSpace.single (0 : Fin 3) (1 : ℝ) = 0 ↔ (1 : ℝ) = 0 := by
      simp
    have h2 : EuclideanSpace.single (0 : Fin 3) (1 : ℝ) = 0 := h.symm
    rw [hz] at h2
    norm_num at h2
  have h02 : a ≠ c := by
    intro h
    simp only [ha, hc] at h
    have hz : EuclideanSpace.single (0 : Fin 3) (2 : ℝ) = 0 ↔ (2 : ℝ) = 0 := by
      simp
    have h2 : EuclideanSpace.single (0 : Fin 3) (2 : ℝ) = 0 := h.symm
    rw [hz] at h2
    norm_num at h2
  have h12 : b ≠ c := by
    intro h
    simp only [hb, hc] at h
    have h2 := congrArg
      (fun x : EuclideanSpace ℝ (Fin 3) => x (0 : Fin 3)) h
    simp only [EuclideanSpace.single_apply, if_pos rfl] at h2
    norm_num at h2
  have dab : dist a b = 1 := by
    simp only [ha, hb]
    rw [dist_zero_left, PiLp.norm_single, norm_one]
  have dac : dist a c = 2 := by
    simp only [ha, hc]
    rw [dist_zero_left, PiLp.norm_single]
    norm_num
  have dbc : dist b c = 1 := by
    simp only [hb, hc]
    rw [PiLp.dist_single_same, Real.dist_eq]
    norm_num
  have hP : ({a, b, c} : Finset (EuclideanSpace ℝ (Fin 3))) =
      ({0, EuclideanSpace.single (0 : Fin 3) 1,
        EuclideanSpace.single (0 : Fin 3) 2} :
        Finset (EuclideanSpace ℝ (Fin 3))) := by
    simp [ha, hb, hc]
  rw [← hP]
  ext r
  constructor
  · intro hr
    simp only [distanceSet, Finset.mem_image, Finset.mem_offDiag,
      Finset.mem_insert, Finset.mem_singleton] at hr
    obtain ⟨⟨p, q⟩, ⟨hp, hq, hne⟩, rfl⟩ := hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
    rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl
    · exact absurd rfl hne
    · rw [dab]; simp
    · rw [dac]; simp
    · rw [dist_comm, dab]; simp
    · exact absurd rfl hne
    · rw [dbc]; simp
    · rw [dist_comm, dac]; simp
    · rw [dist_comm, dbc]; simp
    · exact absurd rfl hne
  · intro hr
    simp only [Finset.mem_singleton, Finset.mem_insert] at hr
    simp only [distanceSet, Finset.mem_image, Finset.mem_offDiag,
      Finset.mem_insert, Finset.mem_singleton]
    rcases hr with rfl | rfl
    · exact ⟨(a, b), ⟨Or.inl rfl, Or.inr (Or.inl rfl), h01⟩, dab⟩
    · exact ⟨(a, c), ⟨Or.inl rfl, Or.inr (Or.inr rfl), h02⟩, dac⟩

/-- Three collinear points determine exactly two distinct distances. -/
theorem triple_distinct :
    distinctDistances ({0, EuclideanSpace.single (0 : Fin 3) 1,
      EuclideanSpace.single (0 : Fin 3) 2} :
      Finset (EuclideanSpace ℝ (Fin 3))) = 2 := by
  classical
  unfold distinctDistances
  rw [triple_distSet, Finset.card_pair (by norm_num)]

/-- The hypotheses of the final theorem hold jointly in dimension three. -/
theorem hyps_joint :
    ∃ (c C : ℝ) (P Q : Finset (EuclideanSpace ℝ (Fin 3))),
      0 < c ∧ 0 < C ∧ P.card = 2 ∧ 2 ≤ P.card ∧ Q.card = 2 ∧
      c * (P.card : ℝ) ^ ((2 : ℝ) / ((3 : ℕ) : ℝ)) ≤ (distinctDistances P : ℝ) ∧
      (distinctDistances Q : ℝ) ≤ C * (((2 : ℕ) : ℝ) ^ ((2 : ℝ) / ((3 : ℕ) : ℝ))) := by
  classical
  obtain ⟨c, C, hc, hC, hlow, hup⟩ := DistinctDistances.jsp_000900 3 le_rfl
  let P₀ : Finset (EuclideanSpace ℝ (Fin 3)) :=
    {0, EuclideanSpace.single (0 : Fin 3) 1}
  have hP₀ : P₀.card = 2 := pair_card
  have hP₂ : 2 ≤ P₀.card := by omega
  obtain ⟨Q, hQcard, hQub⟩ := hup 2 le_rfl
  exact ⟨c, C, P₀, Q, hc, hC, hP₀, hP₂, hQcard, hlow P₀ hP₂, hQub⟩

/-- The real set minimized by `g_d(n)` is nonempty for `d ≥ 3` and `n ≥ 2`. -/
theorem distRealSet_nonempty (d : ℕ) (hd : 3 ≤ d) (n : ℕ) (hn : 2 ≤ n) :
    (distRealSet d n).Nonempty := by
  classical
  obtain ⟨P, hP⟩ := line_points_exist d (by omega) n
  exact ⟨(distinctDistances P : ℝ), P, hP, rfl⟩

/-- The `sInf` defining `g_d(n)` is a genuine minimum attained by some point set. -/
theorem g_attained (d : ℕ) (hd : 3 ≤ d) (n : ℕ) (hn : 2 ≤ n) :
    ∃ P : Finset (EuclideanSpace ℝ (Fin d)),
      P.card = n ∧ (distinctDistances P : ℝ) = g d n := by
  classical
  have hneNat : (distNatSet d n).Nonempty := by
    obtain ⟨P, hP⟩ := line_points_exist d (by omega) n
    exact ⟨distinctDistances P, P, hP, rfl⟩
  have hmemNat : sInf (distNatSet d n) ∈ distNatSet d n :=
    csInf_mem hneNat
  obtain ⟨P₀, hP₀card, hP₀eq⟩ := hmemNat
  have hmemReal : ((sInf (distNatSet d n) : ℕ) : ℝ) ∈ distRealSet d n :=
    ⟨P₀, hP₀card, by rw [hP₀eq]⟩
  have hle : ∀ r ∈ distRealSet d n, ((sInf (distNatSet d n) : ℕ) : ℝ) ≤ r := by
    intro r hr
    obtain ⟨P, hPcard, hPeq⟩ := hr
    have hPmem : distinctDistances P ∈ distNatSet d n := ⟨P, hPcard, rfl⟩
    have hkle : sInf (distNatSet d n) ≤ distinctDistances P :=
      csInf_le (OrderBot.bddBelow _) hPmem
    have hcast : ((sInf (distNatSet d n) : ℕ) : ℝ) ≤ (distinctDistances P : ℝ) :=
      Nat.cast_le.mpr hkle
    rw [hPeq] at hcast
    exact hcast
  have hbdd : BddBelow (distRealSet d n) := by
    refine ⟨0, fun r hr => ?_⟩
    obtain ⟨P, _, hPeq⟩ := hr
    rw [← hPeq]
    exact Nat.cast_nonneg _
  have hneReal : (distRealSet d n).Nonempty :=
    distRealSet_nonempty d hd n hn
  have heq : g d n = ((sInf (distNatSet d n) : ℕ) : ℝ) := by
    unfold g
    exact le_antisymm (csInf_le hbdd hmemReal) (le_csInf hneReal hle)
  exact ⟨P₀, hP₀card, by rw [heq, hP₀eq]⟩

/-- The published theorem gives two-sided `Θ(n^{2/d})` bounds for the minimum `g_d(n)`. -/
theorem theta_bounds (d : ℕ) (hd : 3 ≤ d) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      (∀ n : ℕ, 2 ≤ n → c * (n : ℝ) ^ ((2 : ℝ) / (d : ℝ)) ≤ g d n) ∧
      (∀ n : ℕ, 2 ≤ n → g d n ≤ C * (n : ℝ) ^ ((2 : ℝ) / (d : ℝ))) := by
  classical
  obtain ⟨c₀, C₀, hc₀, hC₀, hlow, hup⟩ := DistinctDistances.jsp_000900 d hd
  refine ⟨min c₀ C₀, max c₀ C₀, lt_min hc₀ hC₀, min_le_max,
    fun n hn => ?_, fun n hn => ?_⟩
  · have hne : (distRealSet d n).Nonempty := distRealSet_nonempty d hd n hn
    have hnn : (0 : ℝ) ≤ (n : ℝ) ^ ((2 : ℝ) / (d : ℝ)) :=
      Real.rpow_nonneg (Nat.cast_nonneg n) _
    have hstep : min c₀ C₀ * (n : ℝ) ^ ((2 : ℝ) / (d : ℝ))
        ≤ c₀ * (n : ℝ) ^ ((2 : ℝ) / (d : ℝ)) :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) hnn
    have hlower : ∀ b ∈ distRealSet d n,
        c₀ * (n : ℝ) ^ ((2 : ℝ) / (d : ℝ)) ≤ b := by
      intro b hb
      obtain ⟨P, hPcard, hPeq⟩ := hb
      have hP₂ : 2 ≤ P.card := by omega
      have h := hlow P hP₂
      rw [hPcard] at h
      rw [hPeq] at h
      exact h
    show min c₀ C₀ * _ ≤ g d n
    unfold g
    exact le_trans hstep (le_csInf hne hlower)
  · obtain ⟨P, hPcard, hPub⟩ := hup n hn
    have hbdd : BddBelow (distRealSet d n) := by
      refine ⟨0, fun r hr => ?_⟩
      obtain ⟨Q, _, hQeq⟩ := hr
      rw [← hQeq]
      exact Nat.cast_nonneg _
    have hmem : (distinctDistances P : ℝ) ∈ distRealSet d n :=
      ⟨P, hPcard, rfl⟩
    have hnn : (0 : ℝ) ≤ (n : ℝ) ^ ((2 : ℝ) / (d : ℝ)) :=
      Real.rpow_nonneg (Nat.cast_nonneg n) _
    have hstep : C₀ * (n : ℝ) ^ ((2 : ℝ) / (d : ℝ))
        ≤ max c₀ C₀ * (n : ℝ) ^ ((2 : ℝ) / (d : ℝ)) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hnn
    show g d n ≤ max c₀ C₀ * _
    unfold g
    exact le_trans (csInf_le hbdd hmem) (le_trans hPub hstep)

/-- The published lower bound forces at least one distance for every two-point set. -/
theorem lower_forces_one (d : ℕ) (hd : 3 ≤ d)
    (P : Finset (EuclideanSpace ℝ (Fin d))) (hP : P.card = 2) :
    1 ≤ distinctDistances P := by
  classical
  obtain ⟨c, C, hc, hC, hlow, hup⟩ := DistinctDistances.jsp_000900 d hd
  have hP₂ : 2 ≤ P.card := by omega
  have h := hlow P hP₂
  rw [hP] at h
  have hexp : (0 : ℝ) < ((2 : ℕ) : ℝ) ^ ((2 : ℝ) / (d : ℝ)) := by
    have h2 : (0 : ℝ) < ((2 : ℕ) : ℝ) := by norm_num
    exact Real.rpow_pos_of_pos h2 _
  have hpos : (0 : ℝ) < c * (((2 : ℕ) : ℝ) ^ ((2 : ℝ) / (d : ℝ))) :=
    mul_pos hc hexp
  have hlt : (0 : ℝ) < (distinctDistances P : ℝ) := lt_of_lt_of_le hpos h
  have hNat : 0 < distinctDistances P := Nat.cast_pos.mp hlt
  omega

/-- The minimum `g_d(n)` grows without bound in `n` for fixed `d ≥ 3`. -/
theorem g_unbounded (d : ℕ) (hd : 3 ≤ d) :
    ∀ B : ℝ, ∃ n : ℕ, 2 ≤ n ∧ B ≤ g d n := by
  classical
  obtain ⟨c, C, hc, hle, hlow, hup⟩ := theta_bounds d hd
  have hexp : (0 : ℝ) < (2 : ℝ) / (d : ℝ) := (exponent_pos d hd).1
  have htend : Filter.Tendsto (fun n : ℕ => ((n : ℝ) ^ ((2 : ℝ) / (d : ℝ))))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hexp).comp tendsto_natCast_atTop_atTop
  intro B
  have hev : ∀ᶠ n : ℕ in Filter.atTop, B / c ≤ (n : ℝ) ^ ((2 : ℝ) / (d : ℝ)) :=
    htend.eventually (eventually_ge_atTop (B / c))
  have h2 : ∀ᶠ n : ℕ in Filter.atTop, 2 ≤ n :=
    eventually_ge_atTop 2
  obtain ⟨n, hn1, hn2⟩ := (hev.and h2).exists
  refine ⟨n, hn2, ?_⟩
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hBn : B = c * (B / c) := by field_simp
  have hmul : c * (B / c) ≤ c * ((n : ℝ) ^ ((2 : ℝ) / (d : ℝ))) :=
    mul_le_mul_of_nonneg_left hn1 (le_of_lt hc)
  rw [hBn]
  exact le_trans hmul (hlow n hn2)

#print axioms line_points_exist
#print axioms fin_three_nonempty
#print axioms exponent_pos
#print axioms rpow_base_pos
#print axioms pair_card
#print axioms pair_offDiag_card
#print axioms pair_distSet
#print axioms pair_distinct
#print axioms triple_card
#print axioms triple_distSet
#print axioms triple_distinct
#print axioms hyps_joint
#print axioms distRealSet_nonempty
#print axioms g_attained
#print axioms theta_bounds
#print axioms lower_forces_one
#print axioms g_unbounded

end NonVacuity
