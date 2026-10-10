import DistinctDistances.TrackE.CommonPhysicalInputs
import DistinctDistances.TrackD.Profiles.RegularityChosenNonreal

/-! Fix physical equations and original supported owners before later
graphs and image subfamilies, sparse-cones.tex:99–141. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- `sc:retained-products.points.tests`: common union regularity and
nonreal-flat removal at each prescribed finite loss. -/
theorem selected_common_physical_tests {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (M : CommonPoolProfile T)
    (j : ℕ) (hj : j < d) (τ ξ : ℝ) (hτ : -1 < τ) (hξ : 0 < ξ)
    (hplateau : TrackD.OnPlateau M.b j ξ τ) (θ : ℝ) (hθ : 0 < θ) :
    ∀ᶠ i in atTop, Nonempty (CommonPhysicalTests T M j τ i θ) := by
  have hgood : ∀ θ' > 0, ∀ η > 0, ∀ ρ > 0, ∀ᶠ i in atTop,
      TrackD.PoolGood (regime.P i) θ' η 1 ρ
        (T.sources i ∪ T.targets i) (M.s i) M.b := by
    intro θ' hθ' η hη ρ hρ
    exact selected_common_union_good M θ' η ρ hθ' hη hρ
  have hJac := TrackD.regularity_jacobian_sequence d regime.dimension_ge_three
    regime.P (fun i => T.sources i ∪ T.targets i) M.s M.b hgood M.width_grows
    (θ / 2) ξ (by positivity) hξ
  obtain ⟨θ₁, hθ₁, η, hη, hηξ, s₁, hnonreal⟩ :=
    TrackD.prof_regularity_nonreal_with_margin d
      regime.dimension_ge_three (θ / 2) (by positivity) (ξ / 2) (by positivity)
  filter_upwards [hJac, hgood θ₁ hθ₁ η hη (ξ / 4) (by positivity),
    common_physical_test_degree_one M τ hτ, M.width_grows.eventually_ge_atTop s₁]
    with i hJ hpool hT hs
  obtain ⟨E, g, hE, hg, hcarrier, hrank, hloss⟩ := hJ j hj τ hplateau hT
  refine ⟨{
    equations := E
    minor := g
    equations_degree := hE
    minor_degree := hg
    carrier_equations := hcarrier
    minor_rank := hrank
    regularity_loss := hloss
    nonreal_loss := ?_ }⟩
  intro X hX
  have hw := hpool.width X hX
  have hbX : TrackD.OnPlateau X.path.time j (ξ / 2) τ := by
    intro a
    obtain ⟨hpre, hpost⟩ := hplateau a
    obtain ⟨hlo, hhi⟩ := abs_le.mp (hpool.close X hX a)
    constructor
    · intro ha
      have h := hpre ha
      linarith
    · intro ha
      have h := hpost ha
      linarith
  exact hnonreal (regime.P i) X (hpool.pieces X hX)
    (by simpa only [hw] using hs) j hj
    ⟨τ, hbX, by simpa only [hw] using hT⟩

/-- `sc:retained-products.points`: one slow choice of physical tests gives
negligible omissions in both original roles. The single supported owner
map and its global terminal overrides precede every later graph. -/
theorem selected_common_physical_retention {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (M : CommonPoolProfile T)
    (j : ℕ) (hj : j < d) (τ ξ : ℝ) (hτ : -1 < τ) (hξ : 0 < ξ)
    (hplateau : TrackD.OnPlateau M.b j ξ τ) :
    Nonempty (CommonPhysicalSequence T M j τ) := by
  obtain ⟨α, hα, hterminal⟩ := exists_selected_common_owner T j hj
  let Q : ℕ → ℕ → Prop := fun n i =>
    Nonempty (CommonPhysicalTests T M j τ i (selectionTolerance n))
  have hQ (n : ℕ) : ∀ᶠ i in atTop, Q n i :=
    selected_common_physical_tests T M j hj τ ξ hτ hξ hplateau
      (selectionTolerance n) (by unfold selectionTolerance; positivity)
  obtain ⟨a, _, hagrows, hdiag⟩ := Framework.exists_slow_diagonal Q hQ
  have hchosen : ∀ᶠ i in atTop,
      Nonempty (CommonPhysicalTests T M j τ i (selectionTolerance (a i))) :=
    hdiag.mono fun i hi => hi (a i) le_rfl
  let E : ℕ → Finset (Poly d) := fun i =>
    if hi : Nonempty (CommonPhysicalTests T M j τ i (selectionTolerance (a i)))
      then (Classical.choice hi).equations else ∅
  let g : ℕ → Poly d := fun i =>
    if hi : Nonempty (CommonPhysicalTests T M j τ i (selectionTolerance (a i)))
      then (Classical.choice hi).minor else 0
  have htests : ∀ᶠ i in atTop,
      (∀ f ∈ E i, (f.totalDegree : ℝ) ≤
        TrackD.testDeg (TrackD.cfgB (regime.P i)) (M.s i) τ) ∧
      (g i).totalDegree ≤ ⌊TrackD.testDeg (TrackD.cfgB (regime.P i)) (M.s i) τ⌋₊ ∧
      (∀ Z, TrackD.PoolCarrier (T.sources i ∪ T.targets i) j Z →
        ∀ f ∈ E i, f ∈ Z.ideal) ∧
      (∀ y : Point d, MvPolynomial.eval y (g i) ≠ 0 →
        Module.finrank ℂ (TrackD.jacKer (E i) y) + j ≤ d) := by
    filter_upwards [hchosen] with i hi
    let D := Classical.choice hi
    have hE : E i = D.equations := by simp only [E, dif_pos hi]; rfl
    have hg : g i = D.minor := by simp only [g, dif_pos hi]; rfl
    rw [hE, hg]
    have hT : 0 ≤ TrackD.testDeg (TrackD.cfgB (regime.P i)) (M.s i) τ :=
      (Nat.cast_nonneg D.minor.totalDegree).trans D.minor_degree
    exact ⟨D.equations_degree, (Nat.le_floor_iff hT).mpr D.minor_degree,
      D.carrier_equations, D.minor_rank⟩
  have htolerance := selection_tolerance_tendsto_zero a hagrows
  have hone (pl : ℕ → Finset (TrackD.Piece d))
      (hsub : ∀ i, pl i ⊆ T.sources i ∪ T.targets i)
      (hdis : ∀ i, (pl i : Set (TrackD.Piece d)).PairwiseDisjoint TrackD.Piece.pts) :
      Framework.LittleO
        (fun i => (((TrackD.poolPts (pl i)) \ retainedCommonPool (pl i)
          (T.sources i ∪ T.targets i) j (E i) (g i) (α i)).card : ℝ))
        (fun i => ((TrackD.poolPts (pl i)).card : ℝ)) := by
    apply Asymptotics.IsLittleO.of_bound
    intro c hc
    filter_upwards [hchosen, htolerance.eventually (Iio_mem_nhds hc)] with i hi hci
    let D := Classical.choice hi
    have hE : E i = D.equations := by simp only [E, dif_pos hi]; rfl
    have hg : g i = D.minor := by simp only [g, dif_pos hi]; rfl
    have hb := common_physical_omissions_card (pl i) (T.sources i ∪ T.targets i)
      (hsub i) (hdis i) j (E i) (g i) (α i) (hα i) (selectionTolerance (a i))
      (by
        intro X hX
        rw [hE, hg]
        exact D.regularity_loss X (hsub i hX))
      (fun X hX => D.nonreal_loss X (hsub i hX))
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)]
    exact hb.trans (mul_le_mul_of_nonneg_right hci.le (Nat.cast_nonneg _))
  refine ⟨{
    equations := E
    minor := g
    owner := α
    supported := hα
    terminal := hterminal
    tests := htests
    source_omissions := hone T.sources (fun i => Finset.subset_union_left)
      (fun i => (T.certificate i).good.pieces_disjoint.subset
        (Finset.coe_subset.mpr (T.certificate i).sources_subset))
    target_omissions := hone T.targets (fun i => Finset.subset_union_right)
      (fun i => (T.certificate i).good.pieces_disjoint.subset
        (Finset.coe_subset.mpr (T.certificate i).targets_subset)) }⟩

end
end DistinctDistances.SparseCones
