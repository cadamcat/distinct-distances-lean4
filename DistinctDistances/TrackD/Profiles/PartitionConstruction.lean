import DistinctDistances.TrackD.Profiles.PartitionUniformWindows
import DistinctDistances.TrackD.Profiles.PartitionInitialEntry
import DistinctDistances.TrackD.Profiles.PartitionIterationPackages
import DistinctDistances.TrackD.Profiles.PartitionChainAssembly
import DistinctDistances.TrackD.Profiles.PartitionWindowLoss
import DistinctDistances.TrackD.Profiles.PartitionPieceTolerance
import DistinctDistances.TrackD.Profiles.PartitionSampleWidth

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section

/-- The multiscale construction with a small output tolerance. All grids,
width thresholds and sample thresholds precede the configuration. -/
theorem partition_construct_small (d : ℕ) (hd : 0 < d) (θ ξ K s₀ : ℝ)
    (hθ : 0 < θ) (hθsmall : θ ≤ 1 / 2) (hξ : 0 < ξ) (hK : 1 ≤ K) :
    ∃ η > 0, ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ P : Finset (Pt d), N₀ ≤ P.card → cfgM P ≤ η * cfgA P →
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ η → ∃ Q : Partition d, Q.Good P δ θ ξ K s₀ := by
  classical
  obtain ⟨G, hG, grid, s₁, hs₁, hgrid, hfirst, hlast, hupper, hmesh, hparameters⟩ :=
    partition_uniform_window_parameters d θ ξ K hθ hξ
  let C : ℝ := (G * d : ℕ)
  have hC : 0 ≤ C := Nat.cast_nonneg _
  obtain ⟨u₀, hu₀, hloss⟩ := partition_fixed_grid_loss C θ hC hθ
  let t : ℝ := max 1 (max s₀ (max s₁ u₀))
  have htone : 1 ≤ t := le_max_left _ _
  have ht : 0 < t := zero_lt_one.trans_le htone
  have hs₀t : s₀ ≤ t := (le_max_left _ _).trans (le_max_right _ _)
  have hs₁t : s₁ ≤ t := (le_max_left _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hu₀t : u₀ ≤ t := (le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  let η : ℝ := min (1 / 3) (θ * Real.exp (-6 * t))
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨N₀, hN₀, hsample⟩ := partition_sample_width d hd t ht
  choose weights hcontrols hgap hmult using hparameters
  refine ⟨η, hη, N₀, hN₀, ?_⟩
  intro P hP hM δ hδ hδη
  obtain ⟨hN, hB, hb⟩ := hsample P hP
  have hBpos : 0 < cfgB P := by linarith
  have hAnonneg : 0 ≤ cfgA P := by unfold cfgA; positivity
  have hMsmall : cfgM P ≤ (1 / 3) * cfgA P :=
    hM.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hAnonneg)
  let b : ℝ := Real.log (cfgB P)
  have hbt : t ≤ b := by dsimp [b]; linarith
  have hbthreshold : s₁ ≤ b := hs₁t.trans hbt
  let π : CutPath d := ⟨fun _ => 0, fun _ => 0⟩
  have hentry := partition_initial_entry P π θ ξ K hθ hK hB hMsmall
    (hcontrols b hbthreshold).multiplier
  obtain ⟨n, hterminalLow, hterminalHigh, hprevious⟩ := partition_dyadic_stop b t ht hbt
  let s : ℕ → ℝ := fun i => b / 2 ^ i
  let error : ℕ → ℝ := fun i =>
    C * Real.exp (-(s i) ^ ((1 : ℝ) / 10) / 2) +
      Real.exp (-(s i) ^ ((1 : ℝ) / 3))
  let state : ℕ → Finset (Pt d) → Prop := fun i U =>
    Nonempty (PartitionWindowEntry P U θ ξ K (s i) π)
  let good : ℕ → Piece d → Prop := fun i X => PieceGood P θ ξ K X ∧ X.width = s i
  have hsnext : ∀ i : ℕ, s (i + 1) = s i / 2 := by
    intro i
    simp only [s, pow_succ, div_div]
  have hstartState : state 0 P := by simpa [state, s] using hentry
  have hstep : ∀ i < n, ∀ U : Finset (Pt d), state i U →
      ∃ (V : Finset (Pt d)) (pl : Finset (Piece d)), state (i + 1) V ∧ V ⊆ U ∧
        (∀ X ∈ pl, good i X ∧ X.pts ⊆ U) ∧
        (pl : Set (Piece d)).PairwiseDisjoint Piece.pts ∧
        (∀ X ∈ pl, Disjoint X.pts V) ∧
        (U.card : ℝ) - V.card - (∑ X ∈ pl, (X.pts.card : ℝ)) ≤ cfgN P * error i := by
    intro i hi U hU
    obtain ⟨entry⟩ := hU
    have hwide : s₁ ≤ s i := hs₁t.trans (by have h := hprevious i hi; dsimp [s]; linarith)
    have hspos : 0 ≤ s i := (show (0 : ℝ) ≤ 1 by norm_num).trans
      (hs₁.trans hwide)
    let ε : ℝ := C * Real.exp (-(s i) ^ ((1 : ℝ) / 10) / 2)
    have hε : 0 ≤ ε := mul_nonneg hC (Real.exp_nonneg _)
    have herror : partitionEventTail
        (fun k => Real.exp (-weights (s i) hwide k / 2)) 0 ≤ ε :=
      partition_event_error_bound (weights (s i) hwide) ((s i) ^ ((1 : ℝ) / 10))
        (hcontrols (s i) hwide).weights
    have hL : 1 ≤ ⌊testDeg (cfgB P) (s i) (1 / 2)⌋₊ := by
      apply (Nat.le_floor_iff (mul_nonneg hBpos.le (Real.exp_nonneg _))).mpr
      have hexp : 1 ≤ Real.exp ((1 / 2 : ℝ) * s i) := Real.one_le_exp_iff.mpr (by positivity)
      norm_num only [Nat.cast_one]
      calc
        (1 : ℝ) ≤ cfgB P := hB.le
        _ ≤ cfgB P * Real.exp ((1 / 2 : ℝ) * s i) := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp hBpos.le
    obtain ⟨V, pl, hentryV, hVU, hgood, hdisj, hnext, hdiscard⟩ :=
      partition_window_advance P U θ ξ K (s i) ε π entry hd hθ hθsmall hξ hK hN
        ⟨i, rfl⟩ hG grid hgrid hfirst hlast hupper hmesh (weights (s i) hwide)
        (hcontrols (s i) hwide) herror hL (hgap (s i) hwide) (hmult (s i) hwide)
    refine ⟨V, pl, ?_, hVU, ?_, hdisj, hnext, ?_⟩
    · dsimp only [state]
      rw [hsnext]
      exact hentryV
    · intro X hX
      exact ⟨⟨(hgood X hX).1, (hgood X hX).2.1⟩, (hgood X hX).2.2⟩
    · have hUcard : (U.card : ℝ) ≤ cfgN P := by
        unfold cfgN
        exact_mod_cast Finset.card_le_card entry.subset
      apply hdiscard.trans
      calc
        _ ≤ ε * cfgN P + cfgN P * Real.exp (-(s i) ^ ((1 : ℝ) / 3)) :=
          add_le_add (mul_le_mul_of_nonneg_left hUcard hε) le_rfl
        _ = cfgN P * error i := by dsimp [error, ε]; ring
  obtain ⟨remaining, pieces, hstart, hfinal, hstates, hsteps⟩ :=
    partition_iterate_window_steps n P state Piece.pts good
      (fun i => cfgN P * error i) hstartState hstep
  obtain ⟨entry⟩ := hfinal
  let u : ℝ := s n
  let L : ℕ := ⌊testDeg (cfgB P) u (1 + θ / 2)⌋₊
  have hu : 0 ≤ u := ht.le.trans hterminalLow
  have htest : 0 ≤ testDeg (cfgB P) u (1 + θ / 2) := mul_nonneg hBpos.le (Real.exp_nonneg _)
  have hcore : CoreIsolated (remaining n) L := by
    apply partition_exact_isolation_core (remaining n) entry.equations L _ entry.isolate
    intro f hf
    exact (Nat.le_floor_iff htest).mpr (entry.degree f hf)
  have hLbound : (L : ℝ) ≤ cfgB P * Real.exp (3 * t) :=
    partition_final_core_degree (cfgB P) u t θ L hBpos.le hu ht.le
      hterminalHigh.le hθsmall (Nat.floor_le htest)
  have hsmall : δ * Real.exp (6 * t) ≤ θ := by
    have hδbound : δ ≤ θ * Real.exp (-6 * t) := hδη.trans (min_le_right _ _)
    calc
      _ ≤ (θ * Real.exp (-6 * t)) * Real.exp (6 * t) :=
        mul_le_mul_of_nonneg_right hδbound (Real.exp_nonneg _)
      _ = θ := by rw [mul_assoc, ← Real.exp_add]; simp
  have hdegree : δ * cfgN P / cfgA P * (L : ℝ) ^ 2 ≤ θ * cfgN P := by
    rw [partition_cfgA_eq_sq P]
    exact partition_core_energy (cfgN P) (cfgB P) δ L t θ hN.le hBpos hδ
      (Nat.cast_nonneg L) hLbound hsmall
  have herror : (∑ i ∈ Finset.range n, error i) ≤ θ := by
    simpa only [error, s] using hloss b n (hu₀t.trans hterminalLow)
  apply partition_chain_partition P n L remaining pieces error δ θ ξ K s₀ hN hstart
    (fun i hi => (hsteps i hi).1) _ (fun i hi => (hsteps i hi).2.2.1)
    (fun i hi => (hsteps i hi).2.2.2.1) hcore hdegree
    (fun i hi => (hsteps i hi).2.2.2.2) herror
  intro i hi X hX
  have hgoodX := (hsteps i hi).2.1 X hX
  refine ⟨hgoodX.1.1, ?_, hgoodX.2⟩
  rw [hgoodX.1.2]
  have h := hprevious i hi
  dsimp [s]
  linarith

/-- The exact finitary partition form, allowing every positive tolerance
by constructing at a smaller tolerance and keeping the same assignments. -/
theorem partition_construct_all (d : ℕ) (hd : 3 ≤ d) :
    ∀ θ > 0, ∀ ξ > 0, ∀ K ≥ 1, ∀ s₀ : ℝ, ∃ η > 0, ∃ N₀ : ℕ,
      ∀ P : Finset (Pt d), N₀ ≤ P.card → cfgM P ≤ η * cfgA P →
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ η → ∃ Q : Partition d, Q.Good P δ θ ξ K s₀ := by
  intro θ hθ ξ hξ K hK s₀
  let θ₁ : ℝ := min θ (1 / 4)
  have hθ₁ : 0 < θ₁ := by dsimp [θ₁]; positivity
  have hθ₁small : θ₁ ≤ 1 / 2 := (min_le_right _ _).trans (by norm_num)
  have hθ₁θ : θ₁ ≤ θ := min_le_left _ _
  obtain ⟨η, hη, N₀, hN₀, hconstruct⟩ := partition_construct_small d (by omega)
    θ₁ ξ K s₀ hθ₁ hθ₁small hξ hK
  refine ⟨η, hη, N₀, ?_⟩
  intro P hP hM δ hδ hδη
  obtain ⟨Q, hQ⟩ := hconstruct P hP hM δ hδ hδη
  have hN : 0 ≤ cfgN P := by unfold cfgN; positivity
  have hB : 1 ≤ cfgB P := by
    unfold cfgB
    apply Real.one_le_rpow
    · exact_mod_cast (show 1 ≤ P.card from (by omega))
    · positivity
  refine ⟨Q, hQ.core_subset, hQ.core_isolated, ?_, ?_, hQ.pieces_disjoint,
    hQ.core_disjoint, ?_⟩
  · exact hQ.core_degree.trans (mul_le_mul_of_nonneg_right hθ₁θ hN)
  · intro X hX
    obtain ⟨hgood, hwidth⟩ := hQ.pieces_good X hX
    have hs : 0 ≤ X.width := by
      obtain ⟨a, ha⟩ := hgood.width_dyadic
      rw [ha]
      exact div_nonneg (Real.log_nonneg hB) (by positivity)
    exact ⟨dprofiles2_pieceGood_mono P X hθ₁θ hs hgood, hwidth⟩
  · exact hQ.discard.trans (mul_le_mul_of_nonneg_right hθ₁θ hN)

end
end DistinctDistances.TrackD
