import DistinctDistances.TrackE.ProfileBudgets
import DistinctDistances.TrackE.WideSource
import DistinctDistances.TrackD.Profiles.RegularityChosenNonreal

/-! Fixed physical source carriers and nonreal-flat deletions for the wide
branch (`depth.tex:222–260`). The original source becomes the target of a
second coherent depth object, so its existing degree and mass budgets apply. -/

namespace DistinctDistances.SparseCones

open Filter
open scoped Topology BigOperators Classical

noncomputable section

namespace SeparatedProfileSequence

/-- Exchange the two physical pieces without changing the underlying regime. -/
def swap {d : ℕ} {regime : Regime d} (S : SeparatedProfileSequence regime) :
    SeparatedProfileSequence regime := {
  source := S.target
  target := S.source
  base_good := fun i => (S.base_good i).symm
  good := fun θ hθ ξ hξ K hK => (S.good θ hθ ξ hξ K hK).mono fun _ h => h.symm
  width_pos := fun i => (S.width_pos i).symm
  source_grows := S.target_grows
  target_grows := S.source_grows
  source_small := S.target_small
  target_small := S.source_small
  separated := S.separated.symm
  times_close := fun t => by
    simpa only [neg_sub, neg_zero] using (S.times_close t).neg }

end SeparatedProfileSequence

namespace LimitingSeparatedProfile

/-- The same limiting profile controls the exchanged piece sequence. -/
def swap {d : ℕ} {regime : Regime d} (S : LimitingSeparatedProfile regime) :
    LimitingSeparatedProfile regime := {
  sequence := S.sequence.swap
  b := S.b
  source_limit := S.target_limit
  target_limit := S.source_limit
  sorted := S.sorted
  sum_zero := S.sum_zero
  balance := S.balance }

end LimitingSeparatedProfile

namespace PositiveSourcePlateau

/-- Plateau margins depend only on the shared limiting profile. -/
def swap {d j : ℕ} {regime : Regime d} {S : LimitingSeparatedProfile regime}
    (A : PositiveSourcePlateau S j) : PositiveSourcePlateau S.swap j := {
  r := A.r
  r_pos := A.r_pos
  r_le_j := A.r_le_j
  τ := A.τ
  ξ := A.ξ
  τ_pos := A.τ_pos
  ξ_pos := A.ξ_pos
  plateau := A.plateau
  prefix_nonpos := A.prefix_nonpos }

end PositiveSourcePlateau

/-- One carrier through each physical source point, fixed independently of
all later lists and tests. This is the source version of G5.owners. -/
theorem source_carrier_owners {d : ℕ} {regime : Regime d}
    (S : LimitingSeparatedProfile regime) (r : ℕ) (hr : r ≤ d) :
    ∃ owner : ℕ → RPoint d → AffineVariety d,
      ∀ i, TrackD.CarrierAssignment {S.sequence.source i} r (owner i) := by
  have hexists (i : ℕ) (p : RPoint d) : ∃ Z : AffineVariety d,
      p ∈ (S.sequence.source i).pts →
        (S.sequence.source i).path.IsCarrier r Z ∧ TrackD.toC p ∈ Z := by
    by_cases hp : p ∈ (S.sequence.source i).pts
    · have hvan (k : Fin d) : MvPolynomial.eval (TrackD.toC p) ((S.sequence.source i).path.cut k) = 0 :=
        (S.sequence.base_good i).1.vanish p hp k
      have hsys : (S.sequence.source i).path.system r ≤ MvPolynomial.vanishingIdeal ℂ {TrackD.toC p} := by
        apply Ideal.span_le.mpr
        rintro f ⟨k, hk, rfl⟩
        change (S.sequence.source i).path.cut k ∈ MvPolynomial.vanishingIdeal ℂ {TrackD.toC p}
        rw [MvPolynomial.mem_vanishingIdeal_iff]
        intro y hy
        have hyx : y = TrackD.toC p := Set.mem_singleton_iff.mp hy
        subst y
        exact hvan k
      obtain ⟨I, hI, hIx⟩ := Ideal.exists_minimalPrimes_le hsys
      let Z : AffineVariety d := ⟨I, hI.isPrime.isRadical⟩
      refine ⟨Z, fun _ => ⟨hI, ?_⟩⟩
      intro f hf
      exact MvPolynomial.mem_vanishingIdeal_iff.mp (hIx hf) (TrackD.toC p) (Set.mem_singleton _)
    · exact ⟨AffineVariety.whole, fun hp' => (hp hp').elim⟩
  choose owner howner using hexists
  refine ⟨owner, fun i X hX p hp => ?_⟩
  have hX_eq : X = S.sequence.source i := Finset.mem_singleton.mp hX
  subst hX_eq
  exact howner i p hp

/-- The source family is an actual owner image. Its degree and uniform
subfamily mass bounds use the same profile as the original target family. -/
structure WideSourceCarriers {d j : ℕ} {regime : Regime d}
    (S : LimitingSeparatedProfile regime) (A : PositiveSourcePlateau S j) where
  data : TrackA.SeparatedDepthData regime A.r.val
  s_eq : data.s = fun i => (S.sequence.source i).width
  v_eq : data.v = fun i => (S.sequence.target i).width
  b_eq : data.b = S.b
  centers_eq : ∀ i, data.centers i = (S.sequence.target i).pts.image TrackD.toC
  targets_eq : ∀ i, data.targets i = (S.sequence.source i).pts.image TrackD.toC
  carriers_eq : ∀ i, data.carriers i = (data.targets i).image (data.owner i)
  carrier_path : ∀ i q, q ∈ (S.sequence.source i).pts →
    (S.sequence.source i).path.IsCarrier A.r.val (data.owner i (TrackD.toC q))
  budgets : data.DegreeBudgets

/-- `G5.wide.carriers`: construct the fixed source assignment and its full
profile budgets before choosing generic lists or any actual center. -/
theorem profile_wide_source_carriers {d j : ℕ} {regime : Regime d}
    (S : LimitingSeparatedProfile regime) (A : PositiveSourcePlateau S j) :
    Nonempty (WideSourceCarriers S A) := by
  obtain ⟨owner, howner⟩ := source_carrier_owners S A.r.val A.r.isLt.le
  obtain ⟨E, hE, _⟩ := separated_depth_data_core S.swap A.r.val
    (by have := A.r_pos; omega) A.r.isLt owner howner
  have hbudgets := profile_depth_budgets_core S.swap E hE.1 hE.2.2.1
    (fun i => (hE.2.2.2 i).2.1)
    (fun i => (hE.2.2.2 i).2.2.1)
    (fun i => (hE.2.2.2 i).2.2.2.1)
  exact ⟨{
    data := E
    s_eq := hE.1
    v_eq := hE.2.1
    b_eq := hE.2.2.1
    centers_eq := fun i => (hE.2.2.2 i).1
    targets_eq := fun i => (hE.2.2.2 i).2.1
    carriers_eq := fun i => (hE.2.2.2 i).2.2.1
    carrier_path := fun i => (hE.2.2.2 i).2.2.2.1
    budgets := hbudgets }⟩

/-- `G5.wide.source-nonreal`: all source points touching any nonreal flat
carrier on the selected positive plateau form a negligible set. -/
theorem source_nonreal_negligible {d j : ℕ} {regime : Regime d}
    (S : LimitingSeparatedProfile regime) (A : PositiveSourcePlateau S j) :
    Framework.LittleO
      (fun i => (((S.sequence.source i).pts.filter (fun x =>
        ∃ Z ∈ (S.sequence.source i).path.localCarriers A.r.val (TrackD.toC x),
          TrackD.IsFlat Z ∧ ¬ TrackD.IsRealFlat Z)).card : ℝ))
      (fun i => ((S.sequence.source i).pts.card : ℝ)) := by
  have hξ := A.ξ_pos
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  obtain ⟨θ, hθ, η, hη, hηξ, v₀, hregularity⟩ :=
    TrackD.prof_regularity_nonreal_with_margin d
      regime.dimension_ge_three ε hε A.ξ A.ξ_pos
  filter_upwards [S.sequence.good θ hθ η hη 1 le_rfl,
    S.sequence.source_grows.eventually_ge_atTop v₀, source_plateau_eventually S A,
    source_positive_test_degree S A] with i hi hwidth hplateau htest
  have h := hregularity (regime.P i) (S.sequence.source i) hi.1 hwidth
    A.r.val A.r.isLt ⟨A.τ, hplateau, htest⟩
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  exact h

/-- `G5.wide.equal-target-nonreal`: in the equal-dimension case the first
positive source index is also the target index, so target deletion is valid.
The strict-dimension case does not consume this statement. -/
theorem target_nonreal_negligible_of_first_positive {d j : ℕ} {regime : Regime d}
    (S : LimitingSeparatedProfile regime) (A : PositiveSourcePlateau S j)
    (heq : A.r.val = j) :
    Framework.LittleO
      (fun i => (((S.sequence.target i).pts.filter (fun x =>
        ∃ Z ∈ (S.sequence.target i).path.localCarriers j (TrackD.toC x),
          TrackD.IsFlat Z ∧ ¬ TrackD.IsRealFlat Z)).card : ℝ))
      (fun i => ((S.sequence.target i).pts.card : ℝ)) := by
  have h := source_nonreal_negligible S.swap A.swap
  change Framework.LittleO
    (fun i => (((S.sequence.target i).pts.filter (fun x =>
      ∃ Z ∈ (S.sequence.target i).path.localCarriers A.r.val (TrackD.toC x),
        TrackD.IsFlat Z ∧ ¬ TrackD.IsRealFlat Z)).card : ℝ))
    (fun i => ((S.sequence.target i).pts.card : ℝ)) at h
  simpa only [heq] using h

end

end DistinctDistances.SparseCones
