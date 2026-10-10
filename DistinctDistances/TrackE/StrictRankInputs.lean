import DistinctDistances.TrackE.StrictMargins
import DistinctDistances.TrackD.Profiles.RankInduction

/-! Finite cut-cluster inputs for the direction-rank induction in
sparse-cones.tex:741–781. All rows retain the fixed physical batch. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- The cut time at the left boundary of an open positive plateau. -/
def profilePlateauLeft (S : LimitingSeparatedProfile regime) (u : ProfilePlateau S) : ℝ :=
  S.b ⟨u.val.val - 1, by have := u.val.isLt; omega⟩

/-- The strict margin budget decreases by four at each possible cut. -/
def plateauRankMargin (m : ℝ) (j : ℕ) : ℝ := m / (4 : ℝ)^j

/-- A physical target row surviving all applications of the original batch. -/
def DenseSurvivingDirectionRow {α : Type*} [Fintype α]
    {F : ConeCoverageSequence regime} {T : SelectedProfileSequence F}
    {S : LimitingSeparatedProfile regime}
    {plateau : α → ProfilePlateau S} {kind : α → DepthRateKind} {ε : α → ℝ}
    (H : ProfileDepthBatchData T S plateau kind ε)
    (i : ℕ) (p : Point d) (Q : Finset (RPoint d)) (ρ : ℝ) : Prop :=
  p ∈ (S.sequence.source i).pts.image TrackD.toC ∧ p ∉ H.batch.badCenters i ∧
    Q ⊆ (S.sequence.target i).pts ∧ (∀ q ∈ Q, TrackD.toC q ≠ p) ∧
    (∀ q ∈ Q, TrackD.toC q ∉ batchBadTargets (fun a => H.data (plateau a))
      (fun i => (S.sequence.target i).pts.image TrackD.toC) H.batch.bad i p) ∧
    ρ * (((S.sequence.target i).pts.image TrackD.toC).card : ℝ) ≤ Q.card

/-- The density quantifier follows the fixed batch, testing time and margin. -/
def DirectionRowRankMargin {α : Type*} [Fintype α]
    {F : ConeCoverageSequence regime} {T : SelectedProfileSequence F}
    {S : LimitingSeparatedProfile regime}
    {plateau : α → ProfilePlateau S} {kind : α → DepthRateKind} {ε : α → ℝ}
    (H : ProfileDepthBatchData T S plateau kind ε) (τ m : ℝ) : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ∀ᶠ i in atTop,
    ∀ p : Point d, ∀ Q : Finset (RPoint d), DenseSurvivingDirectionRow H i p Q ρ →
      profileDirectionRankTarget S i τ * Real.exp (m * (S.sequence.target i).width) ≤
        rowDirectionRank p Q
          ⌊TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ⌋₊

/-- The limiting profile is on the same closed plateau at its left boundary
and at every interior testing time. -/
theorem limiting_plateau_boundary (S : LimitingSeparatedProfile regime)
    (u : ProfilePlateau S) (τ : ℝ)
    (hτ : profilePlateauLeft S u < τ ∧ τ < S.b u.val) :
    TrackD.OnPlateau S.b u.val.val 0 (profilePlateauLeft S u) ∧
      TrackD.OnPlateau S.b u.val.val 0 τ := by
  obtain ⟨hlt, htu⟩ := hτ
  unfold profilePlateauLeft at hlt ⊢
  have hsorted := S.sorted
  constructor
  · intro i
    constructor
    · intro hi
      have hle : i ≤ (⟨u.val.val - 1, by have := u.val.isLt; omega⟩ : Fin d) :=
        Fin.mk_le_mk.mpr (by omega)
      have h := hsorted hle
      simpa using h
    · intro hi
      have hle : (⟨u.val.val - 1, by have := u.val.isLt; omega⟩ : Fin d) ≤ i :=
        Fin.mk_le_mk.mpr (by omega)
      have h := hsorted hle
      simpa using h
  · intro i
    constructor
    · intro hi
      have hle : i ≤ (⟨u.val.val - 1, by have := u.val.isLt; omega⟩ : Fin d) :=
        Fin.mk_le_mk.mpr (by omega)
      have h := hsorted hle
      simp only [add_zero] at ⊢
      linarith
    · intro hi
      have hle : u.val ≤ i := Fin.le_def.mpr hi
      have h := hsorted hle
      simp only [add_zero] at ⊢
      linarith

/-- A test just before an entire repeated-cut cluster is either initial or
in an earlier nonfinal open plateau; there is no fictitious empty plateau. -/
theorem exists_preceding_open_test (S : LimitingSeparatedProfile regime)
    (u : ProfilePlateau S) (κ : ℝ) (hκ : 0 < κ) :
    ∃ a : ℝ, a < profilePlateauLeft S u ∧ profilePlateauLeft S u - a ≤ κ ∧
      (a < S.b ⟨0, by have := regime.dimension_ge_three; omega⟩ ∨
        ∃ v : ProfilePlateau S, v.val.val < u.val.val ∧ StrictPlateauEligible S v ∧
          profilePlateauLeft S v < a ∧ a < S.b v.val) := by
  classical
  have hz_eq : profilePlateauLeft S u =
      S.b ⟨u.val.val - 1, by have := u.val.isLt; omega⟩ := rfl
  have hu_ge1 : 1 ≤ u.val.val := u.property.1
  -- Least index attaining the left value.
  let F : Finset (Fin d) := Finset.univ.filter
    (fun t => S.b t = S.b ⟨u.val.val - 1, by have := u.val.isLt; omega⟩)
  have hmem : (⟨u.val.val - 1, by have := u.val.isLt; omega⟩ : Fin d) ∈ F := by
    simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
  have hne : F.Nonempty := ⟨_, hmem⟩
  obtain ⟨j0, hj0_mem, hj0_min⟩ : ∃ j0 ∈ F, ∀ t ∈ F, j0 ≤ t :=
    ⟨F.min' hne, Finset.min'_mem F hne, fun t ht => Finset.min'_le F t ht⟩
  rw [Finset.mem_filter] at hj0_mem
  obtain ⟨_, hj0_eq⟩ := hj0_mem
  have hj0_le : j0 ≤ (⟨u.val.val - 1, by have := u.val.isLt; omega⟩ : Fin d) :=
    hj0_min _ hmem
  have hj0_val_le : j0.val ≤ u.val.val - 1 := Fin.le_def.mp hj0_le
  have hj0_lt_u : j0.val < u.val.val := by omega
  have hu_lt : u.val.val < d := u.val.isLt
  by_cases hr0 : j0.val = 0
  · -- Initial interval case.
    have hj0_eq0 : j0 = (⟨0, by have := regime.dimension_ge_three; omega⟩ : Fin d) :=
      Fin.ext hr0
    have hb0_eq : S.b ⟨0, by have := regime.dimension_ge_three; omega⟩ =
        S.b ⟨u.val.val - 1, by have := u.val.isLt; omega⟩ := by
      rw [← hj0_eq, hj0_eq0]
    refine ⟨S.b ⟨u.val.val - 1, by have := u.val.isLt; omega⟩ - κ / 2, by
      simp only [hz_eq]; linarith, by simp only [hz_eq]; linarith, ?_⟩
    left
    rw [hb0_eq]
    linarith
  · -- Earlier open plateau case.
    have hj0_ge1 : 1 ≤ j0.val := by omega
    have hprev_le : S.b ⟨j0.val - 1, by have := j0.isLt; omega⟩ ≤ S.b j0 := by
      apply S.sorted
      exact Fin.mk_le_mk.mpr (by omega)
    have hprev_lt : S.b ⟨j0.val - 1, by have := j0.isLt; omega⟩ < S.b j0 := by
      by_contra hnot
      push Not at hnot
      have heq : S.b ⟨j0.val - 1, by have := j0.isLt; omega⟩ = S.b j0 :=
        le_antisymm hprev_le hnot
      have ht_mem : (⟨j0.val - 1, by have := j0.isLt; omega⟩ : Fin d) ∈ F := by
        simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [heq, hj0_eq]
      have hle_min := hj0_min _ ht_mem
      have hval : j0.val ≤ j0.val - 1 := Fin.le_def.mp hle_min
      omega
    let v : ProfilePlateau S := ⟨j0, hj0_ge1, hprev_lt⟩
    have hv_elig : StrictPlateauEligible S v := Or.inl (by
      show v.val.val + 1 < d
      simp only [v]
      omega)
    have hbv_eq : S.b v.val =
        S.b ⟨u.val.val - 1, by have := u.val.isLt; omega⟩ := hj0_eq
    have hleftv_eq : profilePlateauLeft S v =
        S.b ⟨j0.val - 1, by have := j0.isLt; omega⟩ := rfl
    -- Choose a between max(left(v), left-κ) and left.
    let M : ℝ := max (S.b ⟨j0.val - 1, by have := j0.isLt; omega⟩)
      (S.b ⟨u.val.val - 1, by have := u.val.isLt; omega⟩ - κ)
    have hM_lt : M < S.b ⟨u.val.val - 1, by have := u.val.isLt; omega⟩ := by
      simp only [M, max_lt_iff]
      constructor
      · rw [← hj0_eq]; exact hprev_lt
      · linarith [hκ]
    let a : ℝ := (M + S.b ⟨u.val.val - 1, by have := u.val.isLt; omega⟩) / 2
    have hM_a : M < a := by simp only [a]; linarith [hM_lt]
    have ha_z : a < S.b ⟨u.val.val - 1, by have := u.val.isLt; omega⟩ := by
      simp only [a]; linarith [hM_lt]
    have hM_ge1 : S.b ⟨j0.val - 1, by have := j0.isLt; omega⟩ ≤ M := le_max_left _ _
    have hM_ge2 : S.b ⟨u.val.val - 1, by have := u.val.isLt; omega⟩ - κ ≤ M :=
      le_max_right _ _
    refine ⟨a, by simp only [hz_eq]; linarith [ha_z], by simp only [hz_eq]; linarith [hM_a, hM_ge2, hκ], ?_⟩
    right
    refine ⟨v, hj0_lt_u, hv_elig, ?_, ?_⟩
    · simp only [hleftv_eq]
      exact lt_of_le_of_lt hM_ge1 hM_a
    · simp only [hbv_eq]
      exact ha_z

/-- Equal-dimensional groups have a strict endpoint margin, uniformly in
all later rows. This is the literal e_j T^l/R bound, not a rank assumption. -/
theorem profile_same_dimension_margin (S : LimitingSeparatedProfile regime)
    (u : ProfilePlateau S) (D : TrackA.SeparatedDepthData regime u.val.val)
    (hD : DepthFromProfile S D) (kind : DepthRateKind)
    (η ε c τ : ℝ) (hη : 0 < η) (hε : 0 < ε) (hεη : ε ≤ η / 4)
    (hc : 0 < c) (hlog : profileRateEndpointLog S u kind ≤ -η)
    (hτ : profilePlateauLeft S u < τ ∧ τ < S.b u.val) :
    ∀ᶠ i in atTop,
      profileDirectionRankTarget S i τ * Real.exp ((η / 2) * (S.sequence.target i).width) ≤
        c * (D.degreeBudget i / profileDepthRate S u.val.val kind i *
          Real.exp (-ε * D.s i)) *
          (TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ)^
            (d - u.val.val) := by
  have hμ : (0 : ℝ) < η / 2 - ε := by linarith
  obtain ⟨s₀, hs₀⟩ := TrackD.RankCore.lower_constant hc hμ
  have h_abs : ∀ᶠ i in atTop,
      Real.exp (-(η / 2 - ε) * (S.sequence.target i).width) ≤ c := by
    filter_upwards [S.sequence.target_grows.eventually_ge_atTop s₀] with i hi
    exact hs₀ _ hi
  filter_upwards [h_abs] with i hi
  -- Unfold pointwise data.
  have hs_eq : D.s i = (S.sequence.target i).width := congrFun hD.1 i
  have hb_eq : D.b = S.b := hD.2.2.1
  have hs_pos : (0 : ℝ) < (S.sequence.target i).width := (S.sequence.width_pos i).2
  have hBpos : (0 : ℝ) < regime.B i := regime.B_pos i
  have hApos : (0 : ℝ) < regime.A i := regime.A_pos i
  have hB_nonneg : (0 : ℝ) ≤ regime.B i := hBpos.le
  have hs_nonneg : (0 : ℝ) ≤ (S.sequence.target i).width := hs_pos.le
  have hTτ_pos : (0 : ℝ) <
      TrackD.testDeg (regime.B i) (S.sequence.target i).width τ :=
    TrackD.RankCore.testDeg_pos hBpos _ _
  have hRpos : (0 : ℝ) < profileDepthRate S u.val.val kind i := by
    cases kind <;> simp only [profileDepthRate] <;> positivity
  -- OnPlateau at τ from the limiting boundary.
  obtain ⟨_, hb_plateau⟩ := limiting_plateau_boundary S u τ hτ
  -- Sigma equals degreeBudget times testing-degree power.
  have hsigma_eq : TrackD.sigma (regime.B i) (S.sequence.target i).width S.b τ =
      D.degreeBudget i *
        (TrackD.testDeg (regime.B i) (S.sequence.target i).width τ) ^
          (d - u.val.val) := by
    have hdeg_eq : D.degreeBudget i =
        ∏ t ∈ Finset.univ.filter (fun t : Fin d => t.val < u.val.val),
          TrackD.cutScale (regime.B i) (S.sequence.target i).width S.b t := by
      unfold TrackA.SeparatedDepthData.degreeBudget
      apply Finset.prod_congr rfl
      intro t _
      unfold TrackA.SeparatedDepthData.cutDegree TrackD.cutScale TrackD.testDeg
      rw [hb_eq, hs_eq]
    unfold TrackD.sigma
    have hsplit := Finset.prod_filter_mul_prod_filter_not Finset.univ
      (fun t : Fin d => t.val < u.val.val)
      (fun t => min (TrackD.testDeg (regime.B i) (S.sequence.target i).width τ)
        (TrackD.cutScale (regime.B i) (S.sequence.target i).width S.b t))
    have hsigma_split :
        (∏ t : Fin d, min (TrackD.testDeg (regime.B i) (S.sequence.target i).width τ)
          (TrackD.cutScale (regime.B i) (S.sequence.target i).width S.b t)) =
        (∏ t ∈ Finset.univ.filter (fun t : Fin d => t.val < u.val.val),
          min (TrackD.testDeg (regime.B i) (S.sequence.target i).width τ)
            (TrackD.cutScale (regime.B i) (S.sequence.target i).width S.b t)) *
        (∏ t ∈ Finset.univ.filter (fun t : Fin d => ¬ t.val < u.val.val),
          min (TrackD.testDeg (regime.B i) (S.sequence.target i).width τ)
            (TrackD.cutScale (regime.B i) (S.sequence.target i).width S.b t)) := by
      rw [← hsplit]
    rw [hsigma_split]
    have hfirst :
        (∏ t ∈ Finset.univ.filter (fun t : Fin d => t.val < u.val.val),
          min (TrackD.testDeg (regime.B i) (S.sequence.target i).width τ)
            (TrackD.cutScale (regime.B i) (S.sequence.target i).width S.b t)) =
        ∏ t ∈ Finset.univ.filter (fun t : Fin d => t.val < u.val.val),
          TrackD.cutScale (regime.B i) (S.sequence.target i).width S.b t := by
      apply Finset.prod_congr rfl
      intro t ht
      rw [Finset.mem_filter] at ht
      have hle : S.b t ≤ τ := by
        have h := (hb_plateau t).1 ht.2
        simpa using h
      have hDle : TrackD.cutScale (regime.B i) (S.sequence.target i).width S.b t ≤
          TrackD.testDeg (regime.B i) (S.sequence.target i).width τ := by
        unfold TrackD.cutScale
        exact TrackD.RankCore.testDeg_mono hB_nonneg hs_nonneg hle
      exact min_eq_right hDle
    have hsecond :
        (∏ t ∈ Finset.univ.filter (fun t : Fin d => ¬ t.val < u.val.val),
          min (TrackD.testDeg (regime.B i) (S.sequence.target i).width τ)
            (TrackD.cutScale (regime.B i) (S.sequence.target i).width S.b t)) =
        (TrackD.testDeg (regime.B i) (S.sequence.target i).width τ) ^
          (d - u.val.val) := by
      have hconst :
          (∏ t ∈ Finset.univ.filter (fun t : Fin d => ¬ t.val < u.val.val),
            min (TrackD.testDeg (regime.B i) (S.sequence.target i).width τ)
              (TrackD.cutScale (regime.B i) (S.sequence.target i).width S.b t)) =
          ∏ _t ∈ Finset.univ.filter (fun t : Fin d => ¬ t.val < u.val.val),
            TrackD.testDeg (regime.B i) (S.sequence.target i).width τ := by
        apply Finset.prod_congr rfl
        intro t ht
        rw [Finset.mem_filter] at ht
        have hle : τ ≤ S.b t := by
          have hnot : ¬ t.val < u.val.val := ht.2
          have hge : u.val.val ≤ t.val := by omega
          have h := (hb_plateau t).2 hge
          simpa using h
        have hTle : TrackD.testDeg (regime.B i) (S.sequence.target i).width τ ≤
            TrackD.cutScale (regime.B i) (S.sequence.target i).width S.b t := by
          unfold TrackD.cutScale
          exact TrackD.RankCore.testDeg_mono hB_nonneg hs_nonneg hle
        exact min_eq_left hTle
      rw [hconst, Finset.prod_const]
      have hcard : (Finset.univ.filter (fun t : Fin d => ¬ t.val < u.val.val)).card =
          d - u.val.val := by
        have heq : Finset.univ.filter (fun t : Fin d => ¬ t.val < u.val.val) =
            Finset.univ.filter (fun t : Fin d => u.val.val ≤ t.val) := by
          apply Finset.filter_congr
          intro t _
          simp only [not_lt]
        rw [heq]
        exact TrackD.RankCore.card_after _ (by have := u.val.isLt; omega)
      rw [hcard]
    rw [hfirst, hsecond, hdeg_eq]
  -- Rank target unfolds to degreeBudget form.
  have hrank_eq : profileDirectionRankTarget S i τ =
      D.degreeBudget i *
        (TrackD.testDeg (regime.B i) (S.sequence.target i).width τ) ^
          (d - u.val.val) *
        TrackD.testDeg (regime.B i) (S.sequence.target i).width τ /
        regime.A i := by
    unfold profileDirectionRankTarget
    rw [hsigma_eq]
  -- Testing-degree monotonicity τ ≤ b_u.
  have hτ_le : τ ≤ S.b u.val := hτ.2.le
  have hT_mono : TrackD.testDeg (regime.B i) (S.sequence.target i).width τ ≤
      TrackD.testDeg (regime.B i) (S.sequence.target i).width (S.b u.val) :=
    TrackD.RankCore.testDeg_mono hB_nonneg hs_nonneg hτ_le
  -- Endpoint identity and log bound.
  have hident := profile_rate_endpoint_identity S u kind i
  have hident' : profileDepthRate S u.val.val kind i *
      TrackD.testDeg (regime.B i) (S.sequence.target i).width (S.b u.val) /
        regime.A i =
      Real.exp (profileRateEndpointLog S u kind * (S.sequence.target i).width) :=
    hident
  have hexp_bound : profileDepthRate S u.val.val kind i *
      TrackD.testDeg (regime.B i) (S.sequence.target i).width τ / regime.A i ≤
      Real.exp (-η * (S.sequence.target i).width) := by
    have hle1 : profileDepthRate S u.val.val kind i *
        TrackD.testDeg (regime.B i) (S.sequence.target i).width τ / regime.A i ≤
        profileDepthRate S u.val.val kind i *
          TrackD.testDeg (regime.B i) (S.sequence.target i).width (S.b u.val) /
          regime.A i := by
      apply div_le_div_of_nonneg_right _ hApos.le
      exact mul_le_mul_of_nonneg_left hT_mono hRpos.le
    rw [hident'] at hle1
    have hle2 : Real.exp (profileRateEndpointLog S u kind *
        (S.sequence.target i).width) ≤
        Real.exp (-η * (S.sequence.target i).width) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right hlog hs_nonneg
    exact hle1.trans hle2
  -- Combine into the key constant bound.
  have hkey : profileDepthRate S u.val.val kind i *
      TrackD.testDeg (regime.B i) (S.sequence.target i).width τ / regime.A i *
      Real.exp ((η / 2 + ε) * (S.sequence.target i).width) ≤ c := by
    have hexp_add : Real.exp (-η * (S.sequence.target i).width) *
        Real.exp ((η / 2 + ε) * (S.sequence.target i).width) =
        Real.exp (-(η / 2 - ε) * (S.sequence.target i).width) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hle : profileDepthRate S u.val.val kind i *
        TrackD.testDeg (regime.B i) (S.sequence.target i).width τ / regime.A i *
        Real.exp ((η / 2 + ε) * (S.sequence.target i).width) ≤
        Real.exp (-η * (S.sequence.target i).width) *
          Real.exp ((η / 2 + ε) * (S.sequence.target i).width) :=
      mul_le_mul_of_nonneg_right hexp_bound (Real.exp_nonneg _)
    rw [hexp_add] at hle
    exact hle.trans hi
  -- Transfer back to the goal via positivity cancellation.
  have hEpos : (0 : ℝ) < D.degreeBudget i := by
    unfold TrackA.SeparatedDepthData.degreeBudget TrackA.SeparatedDepthData.cutDegree
    apply Finset.prod_pos
    intro t _
    rw [hb_eq, hs_eq]
    positivity
  have hPpos : (0 : ℝ) <
      (TrackD.testDeg (regime.B i) (S.sequence.target i).width τ) ^
        (d - u.val.val) :=
    pow_pos hTτ_pos _
  rw [hrank_eq]
  have hBcfg : regime.B i = TrackD.cfgB (regime.P i) := rfl
  rw [hBcfg]
  rw [hs_eq]
  have hkey2 : profileDepthRate S u.val.val kind i *
      TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ /
        regime.A i *
      Real.exp ((η / 2 + ε) * (S.sequence.target i).width) ≤ c := by
    have : profileDepthRate S u.val.val kind i *
        TrackD.testDeg (regime.B i) (S.sequence.target i).width τ / regime.A i *
        Real.exp ((η / 2 + ε) * (S.sequence.target i).width) ≤ c := hkey
    rwa [hBcfg] at this
  have hexp_add' : Real.exp ((η / 2 + ε) * (S.sequence.target i).width) =
      Real.exp ((η / 2) * (S.sequence.target i).width) *
        Real.exp (ε * (S.sequence.target i).width) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hexp_neg' : Real.exp (-ε * (S.sequence.target i).width) =
      (Real.exp (ε * (S.sequence.target i).width))⁻¹ := by
    rw [neg_mul, Real.exp_neg]
  have hRexp_pos : (0 : ℝ) < profileDepthRate S u.val.val kind i *
      Real.exp (ε * (S.sequence.target i).width) :=
    mul_pos hRpos (Real.exp_pos _)
  have hEPpos : (0 : ℝ) < D.degreeBudget i *
      (TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ) ^
        (d - u.val.val) :=
    mul_pos hEpos hPpos
  have hle_div : TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ *
      Real.exp ((η / 2) * (S.sequence.target i).width) / regime.A i ≤
      c / (profileDepthRate S u.val.val kind i *
        Real.exp (ε * (S.sequence.target i).width)) := by
    rw [le_div_iff₀ hRexp_pos]
    have heq : TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ *
        Real.exp ((η / 2) * (S.sequence.target i).width) / regime.A i *
        (profileDepthRate S u.val.val kind i *
          Real.exp (ε * (S.sequence.target i).width)) =
        profileDepthRate S u.val.val kind i *
          TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ /
          regime.A i *
          Real.exp ((η / 2 + ε) * (S.sequence.target i).width) := by
      rw [hexp_add']
      ring
    rw [heq]
    exact hkey2
  have hmul := mul_le_mul_of_nonneg_left hle_div hEPpos.le
  have hLHS_eq : D.degreeBudget i *
      (TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ) ^
        (d - u.val.val) *
      (TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ *
        Real.exp ((η / 2) * (S.sequence.target i).width) / regime.A i) =
      D.degreeBudget i *
        (TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ) ^
          (d - u.val.val) *
        TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ /
        regime.A i *
        Real.exp ((η / 2) * (S.sequence.target i).width) := by
    ring
  have hRHS_eq : D.degreeBudget i *
      (TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ) ^
        (d - u.val.val) *
      (c / (profileDepthRate S u.val.val kind i *
        Real.exp (ε * (S.sequence.target i).width))) =
      c * (D.degreeBudget i / profileDepthRate S u.val.val kind i *
        Real.exp (-ε * (S.sequence.target i).width)) *
        (TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ) ^
          (d - u.val.val) := by
    rw [hexp_neg']
    ring
  rw [hLHS_eq, hRHS_eq] at hmul
  exact hmul

/-- Absorb a fixed positive Hilbert constant using target-width growth. -/
theorem target_absorb_lower_constant (S : LimitingSeparatedProfile regime)
    (c μ : ℝ) (hc : 0 < c) (hμ : 0 < μ) :
    ∀ᶠ i in atTop, Real.exp (-μ * (S.sequence.target i).width) ≤ c := by
  obtain ⟨s₀, hs₀⟩ := TrackD.RankCore.lower_constant hc hμ
  filter_upwards [S.sequence.target_grows.eventually_ge_atTop s₀] with i hi
  exact hs₀ _ hi

/-- Each earlier index has at least four times the current margin, and
all indices through d retain the final positive common budget. -/
theorem plateau_rank_margin_bounds (m : ℝ) (hm : 0 < m) :
    (∀ j, 0 < plateauRankMargin m j ∧ plateauRankMargin m j ≤ m) ∧
    (∀ r j : ℕ, r < j → 4 * plateauRankMargin m j ≤ plateauRankMargin m r) ∧
    (∀ j : ℕ, j ≤ d → plateauRankMargin m d ≤ plateauRankMargin m j) := by
  have h4pos : (0 : ℝ) < 4 := by norm_num
  have h4ge1 : (1 : ℝ) ≤ 4 := by norm_num
  have hpow_pos : ∀ j : ℕ, (0 : ℝ) < (4 : ℝ) ^ j := fun j => pow_pos h4pos j
  have hpow_ge1 : ∀ j : ℕ, (1 : ℝ) ≤ (4 : ℝ) ^ j := fun j => one_le_pow₀ h4ge1
  have hpow_mono : ∀ a b : ℕ, a ≤ b → (4 : ℝ) ^ a ≤ (4 : ℝ) ^ b := fun a b h =>
    pow_le_pow_right₀ h4ge1 h
  refine ⟨?_, ?_, ?_⟩
  · intro j
    constructor
    · unfold plateauRankMargin
      exact div_pos hm (hpow_pos j)
    · unfold plateauRankMargin
      have h1 : m / (4 : ℝ) ^ j ≤ m / 1 :=
        div_le_div_of_nonneg_left hm.le one_pos (hpow_ge1 j)
      simpa using h1
  · intro r j hrj
    unfold plateauRankMargin
    have hpos_r := hpow_pos r
    have hpos_j := hpow_pos j
    have hle : (4 : ℝ) ^ (r + 1) ≤ (4 : ℝ) ^ j := hpow_mono _ _ (by omega)
    have hpow_succ : (4 : ℝ) ^ (r + 1) = 4 * (4 : ℝ) ^ r := by ring
    have hkey : 4 * m * (4 : ℝ) ^ r ≤ m * (4 : ℝ) ^ j := by
      calc 4 * m * (4 : ℝ) ^ r = m * (4 * (4 : ℝ) ^ r) := by ring
        _ = m * (4 : ℝ) ^ (r + 1) := by rw [hpow_succ]
        _ ≤ m * (4 : ℝ) ^ j :=
          mul_le_mul_of_nonneg_left hle hm.le
    rw [le_div_iff₀ hpos_r]
    have heq : 4 * (m / (4 : ℝ) ^ j) * (4 : ℝ) ^ r =
        (4 * m * (4 : ℝ) ^ r) / (4 : ℝ) ^ j := by field_simp
    rw [heq, div_le_iff₀ hpos_j]
    exact hkey
  · intro j hj
    unfold plateauRankMargin
    have hpos_j := hpow_pos j
    have hpos_d : (0 : ℝ) < (4 : ℝ) ^ d := hpow_pos d
    have hle : (4 : ℝ) ^ j ≤ (4 : ℝ) ^ d := hpow_mono _ _ hj
    exact div_le_div_of_nonneg_left hm.le hpos_j hle

end
end DistinctDistances.SparseCones
