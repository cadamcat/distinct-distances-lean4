import DistinctDistances.TrackE.FinalRegularityInputs
import DistinctDistances.TrackD.Profiles.RegularityChosenCuts

/-! Proper homogeneous minor cuts on the original assigned physical carriers,
sparse-cones.tex:908–918. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d}

/-- sc:u-final-curve.minor-cuts: every later homogeneous minor of A's explicit
degree has only negligible proper zero mass on the original owners. The final
physical cut plateau is tested at the reserved later time, uniformly in the
center, the physical row, and the polynomial chosen after the common batch. -/
theorem final_homogeneous_minor_zeros_small (S : LimitingSeparatedProfile regime)
    (u : ProfilePlateau S) (D : TrackA.SeparatedDepthData regime u.val.val)
    (hD : DepthFromProfile S D) (τ_eq τ_test : ℝ) (heq : τ_eq ≤ τ_test)
    (hτ : profilePlateauLeft S u < τ_test ∧ τ_test < S.b u.val) :
    ∀ ρ : ℝ, 0 < ρ → ∀ᶠ i in atTop,
      ∀ p : Point d, ∀ Q : Finset (RPoint d), Q ⊆ (S.sequence.target i).pts →
      ∀ g : Poly d,
        g.IsHomogeneous ((d - 2) *
          (⌊TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ_eq⌋₊ - 1)) →
        ((properMinorZeroTargets D i p Q g).card : ℝ) ≤
          ρ * (S.sequence.target i).pts.card := by
  classical
  intro ρ hρ
  obtain ⟨ξ, hξ, hplateau⟩ := target_plateau_margin S u τ_test (by
    simpa only [profilePlateauLeft] using hτ)
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast (by have := regime.dimension_ge_three; omega : 1 ≤ d)
  obtain ⟨θ₁, hθ₁, η, hη, hηξ, s₁, hcuts⟩ := TrackD.prof_regularity_cuts_with_margin d
    regime.dimension_ge_three ρ hρ ξ hξ (d : ℝ) hd
  filter_upwards [S.sequence.good θ₁ hθ₁ η hη 1 le_rfl,
    hplateau, S.sequence.target_grows.eventually_ge_atTop s₁, target_test_degree S τ_test]
    with i hgood hplateaui hwidth htest
  intro p Q hQ g hg
  let L : ℕ := ⌊TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ_eq⌋₊
  let r : ℕ := (d - 2) * (L - 1)
  have hminor : r ≤ d * L := Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
  have hfloor : (L : ℝ) ≤ TrackD.testDeg (TrackD.cfgB (regime.P i))
      (S.sequence.target i).width τ_eq := Nat.floor_le (by
    unfold TrackD.testDeg TrackD.cfgB
    positivity)
  have hmono : TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ_eq ≤
      TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ_test :=
    TrackD.RankCore.testDeg_mono (by unfold TrackD.cfgB; positivity)
      (S.sequence.width_pos i).2.le heq
  have hchoices : ∀ Y : AffineVariety d, ∃ f : Poly d,
      f.totalDegree ≤ r ∧
      (g ∉ (radialImage p Y).ideal → f ∉ Y.ideal) ∧
      ∀ x : Point d, MvPolynomial.eval x f = MvPolynomial.eval (x - p) g :=
    fun Y => Request.bounded_radial_pullback p Y g hg
  choose f hfdegree hfproper hfeval using hchoices
  have hdegree : ∀ Y : AffineVariety d, ((f Y).totalDegree : ℝ) ≤
      (d : ℝ) * TrackD.testDeg (TrackD.cfgB (regime.P i)) (S.sequence.target i).width τ_test := by
    intro Y
    have hnat : ((f Y).totalDegree : ℝ) ≤ (d : ℝ) * (L : ℝ) := by
      exact_mod_cast (hfdegree Y).trans hminor
    exact hnat.trans (mul_le_mul_of_nonneg_left (hfloor.trans hmono) (Nat.cast_nonneg d))
  have hcap := hcuts (regime.P i) (S.sequence.target i) hgood.2 hwidth
    u.val.val u.val.isLt τ_test hplateaui htest f hdegree
  have hsub : properMinorZeroTargets D i p Q g ⊆
      (S.sequence.target i).pts.filter (fun q =>
        ∃ Y ∈ (S.sequence.target i).path.localCarriers u.val.val (TrackD.toC q),
          f Y ∉ Y.ideal ∧ MvPolynomial.eval (TrackD.toC q) (f Y) = 0) := by
    intro q hq
    obtain ⟨hqQ, hproper, hzero⟩ := Finset.mem_filter.mp hq
    have hqTarget := hQ hqQ
    have hqD : TrackD.toC q ∈ D.targets i := by
      rw [(hD.2.2.2 i).2.1]
      exact Finset.mem_image.mpr ⟨q, hqTarget, rfl⟩
    have hlocal : D.owner i (TrackD.toC q) ∈
        (S.sequence.target i).path.localCarriers u.val.val (TrackD.toC q) :=
      ⟨(hD.2.2.2 i).2.2.2.1 q hqTarget, D.owner_contains i _ hqD⟩
    exact Finset.mem_filter.mpr ⟨hqTarget, D.owner i (TrackD.toC q), hlocal,
      hfproper _ hproper, by rw [hfeval]; exact hzero⟩
  have hcard : ((properMinorZeroTargets D i p Q g).card : ℝ) ≤
      (((S.sequence.target i).pts.filter (fun q =>
        ∃ Y ∈ (S.sequence.target i).path.localCarriers u.val.val (TrackD.toC q),
          f Y ∉ Y.ideal ∧ MvPolynomial.eval (TrackD.toC q) (f Y) = 0)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  exact hcard.trans hcap

end
end DistinctDistances.SparseCones
