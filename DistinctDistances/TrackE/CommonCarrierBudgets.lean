import DistinctDistances.TrackE.CommonCarrierInputs
import DistinctDistances.TrackE.NarrowScale

/-! Pooled budgets from each original physical piece,
`sc:retained-carrier-weights`, sparse-cones.tex:127–141. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- Original piece budgets expressed in the one limiting profile. -/
theorem common_piece_limiting_budgets {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} (M : CommonPoolProfile T) (j : ℕ) (hj : j ≤ d) :
    ∀ η : ℝ, 0 < η → ∀ᶠ i in atTop, ∀ X ∈ T.sources i ∪ T.targets i,
      (∑ Z ∈ TrackD.pieceCarrierFamily X j, (Z.degree : ℝ)) ≤
        commonCarrierScale M j i * Real.exp (η * M.s i) ∧
      (∀ Z, X.path.IsCarrier j Z → (∃ q ∈ X.pts, TrackD.toC q ∈ Z) →
        ((X.pts.filter (fun q => TrackD.toC q ∈ Z)).card : ℝ) ≤
          (Z.degree : ℝ) * (regime.N i / commonCarrierScale M j i) *
            Real.exp (η * M.s i)) := by
  intro η hη
  have hd : 0 < (d : ℝ) := by exact_mod_cast (by have := regime.dimension_ge_three; omega : 0 < d)
  let γ : ℝ := η / 2
  let ρ : ℝ := η / (2 * (d : ℝ))
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  obtain ⟨θ, hθ, hbez⟩ := TrackD.prof_budget_bezout d regime.dimension_ge_three γ hγ
  filter_upwards [M.good θ hθ 1 (by norm_num) 1 le_rfl ρ hρ,
    M.limit ρ hρ] with i hgood hclose
  intro X hX
  have hpiece : TrackD.PieceGood (regime.P i) θ 1 1 X := by
    rcases Finset.mem_union.mp hX with h | h
    · exact hgood.1.pieces X h
    · exact hgood.2.pieces X h
  have hw : X.width = M.s i := M.width i X hX
  have hs : 0 ≤ X.width := by rw [hw]; exact (M.width_pos i).le
  have hscale := common_scale_closeness (regime.B i) (regime.N i) (M.s i) ρ
    M.b X.path.time (regime.B_pos i) (M.width_pos i).le hρ.le M.sum_zero
    (regime_B_pow_dimension regime i) (hclose X hX) j
  have hscale' :
      TrackD.eScale (TrackD.cfgB (regime.P i)) X.width X.path.time j ≤
        commonCarrierScale M j i * Real.exp ((d : ℝ) * ρ * M.s i) ∧
      TrackD.tailScale (TrackD.cfgB (regime.P i)) X.width X.path.time j ≤
        (regime.N i / commonCarrierScale M j i) *
          Real.exp ((d : ℝ) * ρ * M.s i) := by
    simpa only [hw, TrackD.cfgB, Regime.B, Regime.N, commonCarrierScale] using hscale
  have hexp : Real.exp ((d : ℝ) * ρ * M.s i) * Real.exp (γ * X.width) =
      Real.exp (η * M.s i) := by
    rw [hw, ← Real.exp_add]
    congr 1
    dsimp [ρ, γ]
    field_simp [hd.ne']
    ring
  have hfamily : ∀ Z ∈ TrackD.pieceCarrierFamily X j,
      X.path.IsCarrier j Z ∧ ∃ q ∈ X.pts, TrackD.toC q ∈ Z :=
    fun Z hZ => (TrackD.mem_pieceCarrierFamily X j Z).mp hZ
  have hbudget := hbez (regime.P i) X 1 1 hpiece hs j hj
    (TrackD.pieceCarrierFamily X j) hfamily
  constructor
  · calc
      (∑ Z ∈ TrackD.pieceCarrierFamily X j, (Z.degree : ℝ)) ≤
          TrackD.eScale (TrackD.cfgB (regime.P i)) X.width X.path.time j *
            Real.exp (γ * X.width) := hbudget.1
      _ ≤ (commonCarrierScale M j i * Real.exp ((d : ℝ) * ρ * M.s i)) *
          Real.exp (γ * X.width) :=
        mul_le_mul_of_nonneg_right hscale'.1 (Real.exp_pos _).le
      _ = commonCarrierScale M j i * Real.exp (η * M.s i) := by
        rw [mul_assoc, hexp]
  · intro Z hZ hpoint
    have hsingle : ∀ W ∈ ({Z} : Finset (AffineVariety d)),
        X.path.IsCarrier j W ∧ ∃ q ∈ X.pts, TrackD.toC q ∈ W := by
      intro W hW
      simpa only [Finset.mem_singleton.mp hW] using And.intro hZ hpoint
    have hcap := (hbez (regime.P i) X 1 1 hpiece hs j hj {Z} hsingle).2
    simp only [Finset.sum_singleton, Finset.mem_singleton, exists_eq_left] at hcap
    obtain ⟨q, hq, hqZ⟩ := hpoint
    have hZi := (TrackD.prof_partition_pure X q hq (hpiece.vanish q hq)
      (hpiece.proper q hq) j hj Z ⟨hZ, hqZ⟩).1
    have hdeg : 0 ≤ (Z.degree : ℝ) := by
      exact_mod_cast (show (0 : ℚ) ≤ Z.degree from
        (by norm_num : (0 : ℚ) ≤ 1).trans (AffineVariety.one_le_degree Z hZi.ne_top))
    calc
      ((X.pts.filter (fun q => TrackD.toC q ∈ Z)).card : ℝ) ≤
          (Z.degree : ℝ) * TrackD.tailScale (TrackD.cfgB (regime.P i))
            X.width X.path.time j * Real.exp (γ * X.width) := hcap
      _ ≤ (Z.degree : ℝ) * ((regime.N i / commonCarrierScale M j i) *
          Real.exp ((d : ℝ) * ρ * M.s i)) * Real.exp (γ * X.width) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscale'.2 hdeg)
          (Real.exp_pos _).le
      _ = (Z.degree : ℝ) * (regime.N i / commonCarrierScale M j i) *
          Real.exp (η * M.s i) := by rw [mul_assoc, mul_assoc, hexp]; ring

/-- Both literal retained role families have the degree and normalized mass
budgets at every fixed tolerance, before any carrier-pair deletion. -/
theorem selected_common_carrier_budgets {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} {M : CommonPoolProfile T} {j : ℕ} {τ : ℝ}
    (W : CommonPhysicalSequence T M j τ) (hj : j ≤ d) :
    ∀ η : ℝ, 0 < η → ∀ᶠ i in atTop, CommonCarrierBudgets W i η := by
  intro η hη
  let γ : ℝ := η / 4
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have he (i : ℕ) : 0 < commonCarrierScale M j i := by
    unfold commonCarrierScale TrackD.eScale TrackD.cutScale TrackD.testDeg
    exact Finset.prod_pos fun _ _ => mul_pos (regime.B_pos i) (Real.exp_pos _)
  filter_upwards [common_piece_limiting_budgets M j hj γ hγ,
    M.good γ hγ 1 (by norm_num) 1 le_rfl 1 (by norm_num),
    common_retained_mass_lower W γ hγ] with i hpiece hgood hmass
  have hstructure := common_retained_carrier_structure W hj i
  have hone (pl : Finset (TrackD.Piece d)) (S : Finset (RPoint d))
      (hsub : pl ⊆ T.sources i ∪ T.targets i)
      (hS : S ⊆ TrackD.poolPts pl)
      (hcount : (pl.card : ℝ) ≤ Real.exp (γ * M.s i))
      (hSsize : regime.N i * Real.exp (-γ * M.s i) ≤ (S.card : ℝ))
      (hpureS : AffineFamily.IsPure (commonOwnerFamily S (W.owner i)) (d - j)) :
      (∑ Z ∈ commonOwnerFamily S (W.owner i), (Z.degree : ℝ)) ≤
        commonCarrierScale M j i * Real.exp (η * M.s i) ∧
      ∀ Z ∈ commonOwnerFamily S (W.owner i),
        ((commonOwnerFiber S (W.owner i) Z).card : ℝ) ≤
          (S.card : ℝ) * (Z.degree : ℝ) / commonCarrierScale M j i *
            Real.exp (η * M.s i) := by
    have hei : 0 < commonCarrierScale M j i := he i
    have hα : TrackD.CarrierAssignment pl j (W.owner i) := by
      intro X hX q hq
      exact W.supported i X (hsub hX) q hq
    have hpure : ∀ X ∈ pl, ∀ Z ∈ TrackD.pieceCarrierFamily X j, Z.IsIrreducible := by
      intro X hX Z hZ
      have hXpart : X ∈ (T.partition i).pieces := by
        rcases Finset.mem_union.mp (hsub hX) with h | h
        · exact (T.certificate i).sources_subset h
        · exact (T.certificate i).targets_subset h
      have hXgood := ((T.certificate i).good.pieces_good X hXpart).1
      obtain ⟨hc, q, hq, hqZ⟩ := (TrackD.mem_pieceCarrierFamily X j Z).mp hZ
      exact (TrackD.prof_partition_pure X q hq (hXgood.vanish q hq)
        (hXgood.proper q hq) j hj Z ⟨hc, hqZ⟩).1
    have hpool := common_owner_pooled_bounds pl S (W.owner i) j hS hα hpure
      (commonCarrierScale M j i * Real.exp (γ * M.s i))
      ((regime.N i / commonCarrierScale M j i) * Real.exp (γ * M.s i))
      (mul_nonneg hei.le (Real.exp_pos _).le)
      (mul_nonneg (div_nonneg (regime.N_pos i).le hei.le) (Real.exp_pos _).le)
      (fun X hX => (hpiece X (hsub hX)).1)
      (fun X hX Z hZ hpoint => by
        simpa only [mul_assoc] using (hpiece X (hsub hX)).2 Z hZ hpoint)
    have h2γ : Real.exp (γ * M.s i) * Real.exp (γ * M.s i) =
        Real.exp ((2 * γ) * M.s i) := by rw [← Real.exp_add]; congr 1; ring
    have h3γ : Real.exp (γ * M.s i) * Real.exp ((2 * γ) * M.s i) =
        Real.exp ((3 * γ) * M.s i) := by rw [← Real.exp_add]; congr 1; ring
    have h2le : Real.exp ((2 * γ) * M.s i) ≤ Real.exp (η * M.s i) := by
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_right _ (M.width_pos i).le
      dsimp [γ]
      linarith
    have h3le : Real.exp ((3 * γ) * M.s i) ≤ Real.exp (η * M.s i) := by
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_right _ (M.width_pos i).le
      dsimp [γ]
      linarith
    have hN : regime.N i ≤ (S.card : ℝ) * Real.exp (γ * M.s i) := by
      have h := mul_le_mul_of_nonneg_right hSsize (Real.exp_pos (γ * M.s i)).le
      have hexp : Real.exp (-γ * M.s i) * Real.exp (γ * M.s i) = 1 := by
        rw [← Real.exp_add]
        have hz : -γ * M.s i + γ * M.s i = 0 := by ring
        rw [hz, Real.exp_zero]
      simpa only [mul_assoc, hexp, mul_one] using h
    constructor
    · calc
        _ ≤ (pl.card : ℝ) * (commonCarrierScale M j i * Real.exp (γ * M.s i)) := hpool.1
        _ ≤ Real.exp (γ * M.s i) *
            (commonCarrierScale M j i * Real.exp (γ * M.s i)) :=
          mul_le_mul_of_nonneg_right hcount (by positivity)
        _ = commonCarrierScale M j i * Real.exp ((2 * γ) * M.s i) := by
          rw [← h2γ]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h2le (he i).le
    · intro Z hZ
      have hdeg : 0 ≤ (Z.degree : ℝ) := by
        exact_mod_cast (show (0 : ℚ) ≤ Z.degree from
          (by norm_num : (0 : ℚ) ≤ 1).trans
            (AffineVariety.one_le_degree Z (hpureS Z hZ).1.ne_top))
      calc
        _ ≤ (pl.card : ℝ) * (Z.degree : ℝ) *
            ((regime.N i / commonCarrierScale M j i) * Real.exp (γ * M.s i)) := hpool.2 Z hZ
        _ ≤ Real.exp (γ * M.s i) * (Z.degree : ℝ) *
            ((regime.N i / commonCarrierScale M j i) * Real.exp (γ * M.s i)) := by
          apply mul_le_mul_of_nonneg_right
          · exact mul_le_mul_of_nonneg_right hcount hdeg
          · exact mul_nonneg (div_nonneg (regime.N_pos i).le hei.le) (Real.exp_pos _).le
        _ = (Z.degree : ℝ) / commonCarrierScale M j i * regime.N i *
            Real.exp ((2 * γ) * M.s i) := by
          rw [← h2γ]; ring
        _ ≤ (Z.degree : ℝ) / commonCarrierScale M j i *
            ((S.card : ℝ) * Real.exp (γ * M.s i)) * Real.exp ((2 * γ) * M.s i) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hN (div_nonneg hdeg (he i).le)) (Real.exp_pos _).le
        _ = (S.card : ℝ) * (Z.degree : ℝ) / commonCarrierScale M j i *
            Real.exp ((3 * γ) * M.s i) := by
          rw [← h3γ]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h3le (by positivity)
  have hs : W.sources i ⊆ TrackD.poolPts (T.sources i) := by
    exact Finset.filter_subset _ _
  have ht : W.targets i ⊆ TrackD.poolPts (T.targets i) := by
    exact Finset.filter_subset _ _
  have hsource := hone (T.sources i) (W.sources i) Finset.subset_union_left
    hs hgood.1.count hmass.1 hstructure.1
  have htarget := hone (T.targets i) (W.targets i) Finset.subset_union_right
    ht hgood.2.count hmass.2 hstructure.2.1
  exact ⟨hsource.1, htarget.1, hsource.2, htarget.2⟩

end
end DistinctDistances.SparseCones
