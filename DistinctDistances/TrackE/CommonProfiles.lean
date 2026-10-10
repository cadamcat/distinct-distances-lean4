import DistinctDistances.TrackE.CommonProfileInputs

/-! Limiting common-window and outer-pool profiles retain their literal
selected graphs, cone families, partitions and global terminal assignments
(`sc:selection.common-profile`, sparse-cones.tex:44–52, 340–350). -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- One limiting profile for the two actual selected pools. This record is
indexed by the original selection, so its incidence graph and terminal map
remain available without any replacement or physical role exchange. -/
structure CommonPoolProfile {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) where
  s : ℕ → ℝ
  width : ∀ i, ∀ X ∈ T.sources i ∪ T.targets i, X.width = s i
  width_pos : ∀ i, 0 < s i
  width_grows : Tendsto s atTop atTop
  b : Fin d → ℝ
  limit : ∀ ρ : ℝ, 0 < ρ → ∀ᶠ i in atTop,
    ∀ X ∈ T.sources i ∪ T.targets i, ∀ a, |X.path.time a - b a| ≤ ρ
  good : ∀ θ : ℝ, 0 < θ → ∀ ξ : ℝ, 0 < ξ → ∀ K : ℝ, 1 ≤ K →
    ∀ ρ : ℝ, 0 < ρ → ∀ᶠ i in atTop,
      TrackD.PoolGood (regime.P i) θ ξ K ρ (T.sources i) (s i) b ∧
      TrackD.PoolGood (regime.P i) θ ξ K ρ (T.targets i) (s i) b
  sorted : Monotone b
  sum_zero : ∑ a, b a = 0
  balance : ∃ c : ℝ, 0 < c ∧
    b ⟨0, by have := regime.dimension_ge_three; omega⟩ ≤ -c ∧
    c ≤ b ⟨d - 1, by have := regime.dimension_ge_three; omega⟩ ∧
    b ⟨0, by have := regime.dimension_ge_three; omega⟩ +
      b ⟨1, by have := regime.dimension_ge_three; omega⟩ ≤ -c
  source_size : Framework.ExpEquivalent (fun _ => Unit)
    (fun i _ => ((TrackD.poolPts (T.sources i)).card : ℝ)) (fun i _ => regime.N i) s
  target_size : Framework.ExpEquivalent (fun _ => Unit)
    (fun i _ => ((TrackD.poolPts (T.targets i)).card : ℝ)) (fun i _ => regime.N i) s

/-- `sc:selection.common-profile`: compactness for literal equal-width
selected pools, including the outermost pool. Width separation is not a premise.
The returned selection is exactly the common reindexing of all original data. -/
theorem selected_common_pool_profile {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F)
    (hwidth : ∀ i, ∃ s : ℝ, ∀ X ∈ T.sources i ∪ T.targets i, X.width = s) :
    ∃ (φ : ℕ → ℕ) (hφ : StrictMono φ),
      Nonempty (CommonPoolProfile (T.comp φ hφ)) := by
  choose s hwidth using hwidth
  choose X hX using fun i => (T.certificate i).targets_nonempty
  have hmem (i : ℕ) : X i ∈ T.sources i ∪ T.targets i :=
    Finset.mem_union_right _ (hX i)
  have hdata (i : ℕ) :
      TrackD.PieceGood (regime.P i) (selectionTolerance (T.precision i))
        (selectionTolerance (T.precision i)) (selectionScale (T.precision i)) (X i) ∧
      selectionScale (T.precision i) ≤ (X i).width :=
    (T.certificate i).good.pieces_good (X i)
      ((T.certificate i).targets_subset (hX i))
  have hspos (i : ℕ) : 0 < s i := by
    rw [← hwidth i (X i) (hmem i)]
    have hscale : 0 < selectionScale (T.precision i) := by
      unfold selectionScale
      positivity
    exact hscale.trans_le (hdata i).2
  have hngrows : Tendsto (fun i => (T.precision i : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp T.precision_grows
  have hsgrows : Tendsto s atTop atTop := by
    apply Filter.tendsto_atTop_mono _ hngrows
    intro i
    have h := (hdata i).2
    rw [hwidth i (X i) (hmem i)] at h
    unfold selectionScale at h
    linarith
  have hbase (i : ℕ) : TrackD.PieceGood (regime.P i) 1 1 1 (X i) := by
    have hn : 0 ≤ (T.precision i : ℝ) := Nat.cast_nonneg _
    have htol : selectionTolerance (T.precision i) ≤ 1 := by
      unfold selectionTolerance
      apply (div_le_one₀ (by positivity)).mpr
      linarith
    have hscale : 1 ≤ selectionScale (T.precision i) := by
      unfold selectionScale
      linarith
    have hw : 0 ≤ (X i).width := by
      rw [hwidth i (X i) (hmem i)]
      exact (hspos i).le
    exact selection_piece_good_weaken _ _ hw htol htol hscale (hdata i).1
  have hbounded : ∀ᶠ i in atTop, ∀ a, -1 ≤ (X i).path.time a ∧
      (X i).path.time a ≤ 2 :=
    Eventually.of_forall fun i a => by
      have h := (hbase i).time_range a
      exact ⟨h.1, by linarith [h.2]⟩
  obtain ⟨φ, hφ, b, hlim⟩ := Framework.exists_profile_subsequence
    (fun i => (X i).path.time) (-1) 2 hbounded
  let T' := T.comp φ hφ
  let X' : ℕ → TrackD.Piece d := fun i => X (φ i)
  let s' : ℕ → ℝ := fun i => s (φ i)
  have hmem' (i : ℕ) : X' i ∈ T'.sources i ∪ T'.targets i := hmem (φ i)
  have hwidth' (i : ℕ) : ∀ Y ∈ T'.sources i ∪ T'.targets i, Y.width = s' i :=
    hwidth (φ i)
  have hspos' (i : ℕ) : 0 < s' i := hspos (φ i)
  have hlim' : Framework.ProfileConverges (fun i => (X' i).path.time) b := hlim
  obtain ⟨hsorted, hsum, hbalance⟩ := selected_piece_budget_limits T' X' hmem' b hlim'
  have hclose := selected_uniform_profile_limit T' X' hmem' b hlim'
  have htol' := selection_tolerance_tendsto_zero T'.precision T'.precision_grows
  have hgood : ∀ θ : ℝ, 0 < θ → ∀ ξ : ℝ, 0 < ξ → ∀ K : ℝ, 1 ≤ K →
      ∀ ρ : ℝ, 0 < ρ → ∀ᶠ i in atTop,
        TrackD.PoolGood ((regime.comp φ hφ).P i) θ ξ K ρ (T'.sources i) (s' i) b ∧
        TrackD.PoolGood ((regime.comp φ hφ).P i) θ ξ K ρ (T'.targets i) (s' i) b := by
    intro θ hθ ξ hξ K hK ρ hρ
    filter_upwards [selected_piece_good_eventually T' θ hθ ξ hξ K hK,
      hclose ρ hρ, htol'.eventually (Iio_mem_nhds hθ)] with i hpieces hclosei hθi
    have one (pl : Finset (TrackD.Piece d))
        (hsub : pl ⊆ (T'.partition i).pieces)
        (hunion : pl ⊆ T'.sources i ∪ T'.targets i) :
        TrackD.PoolGood ((regime.comp φ hφ).P i) θ ξ K ρ pl (s' i) b := by
      have hpool := pool_good_of_partition ((regime.comp φ hφ).P i) (T'.partition i)
        ((F.comp φ hφ).delta i) (selectionTolerance (T'.precision i))
        (selectionTolerance (T'.precision i)) (selectionScale (T'.precision i))
        (selectionScale (T'.precision i)) ρ (s' i) b
        ((regime.comp φ hφ).N_pos i) (T'.certificate i).good pl hsub
        (fun Y hY => hwidth' i Y (hunion hY))
        (fun Y hY => hclosei Y (hunion hY))
      refine ⟨fun Y hY => hpieces Y (hunion hY), hpool.width,
        hpool.close, ?_, hpool.disjoint⟩
      exact hpool.count.trans (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right hθi.le (hspos' i).le))
    exact ⟨one (T'.sources i) (T'.certificate i).sources_subset
        (Finset.subset_union_left),
      one (T'.targets i) (T'.certificate i).targets_subset
        (Finset.subset_union_right)⟩
  obtain ⟨hsourceSize, htargetSize⟩ := selected_pool_mass_equivalent T' s' hspos' hwidth'
  refine ⟨φ, hφ, ⟨{
    s := s'
    width := hwidth'
    width_pos := hspos'
    width_grows := hsgrows.comp hφ.tendsto_atTop
    b := b
    limit := hclose
    good := hgood
    sorted := hsorted
    sum_zero := hsum
    balance := hbalance
    source_size := hsourceSize
    target_size := htargetSize }⟩⟩

end
end DistinctDistances.SparseCones
