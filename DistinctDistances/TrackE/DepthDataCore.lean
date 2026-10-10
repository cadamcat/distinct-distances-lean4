import DistinctDistances.TrackE.DepthProfile

/-! Construction of the coherent actual samples and persistent carrier assignment
for `G5.data` (`depth.tex:4–16`, profiles.tex:448–451). -/

namespace DistinctDistances.SparseCones

open Filter
open scoped Topology BigOperators

noncomputable section

/-- Complexification preserves the actual point labels. -/
theorem profile_toC_injective {d : ℕ} : Function.Injective (TrackD.toC (d := d)) := by
  intro x y h
  ext t
  exact Complex.ofReal_injective (congrFun h t)

open Classical in
/-- A piece's lower size bound at every fixed slack and its literal inclusion
in the configuration give both signed exponential size bounds. -/
theorem profile_sample_size {d : ℕ} {regime : Regime d}
    (X : ℕ → TrackD.Piece d)
    (hsub : ∀ i, (X i).pts ⊆ regime.P i) (hwidth : ∀ i, 0 < (X i).width)
    (hsize : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop,
      regime.N i * Real.exp (-ε * (X i).width) ≤ ((X i).pts.card : ℝ)) :
    Framework.ExpEquivalent (fun _ => Unit)
      (fun i _ => (((X i).pts.image TrackD.toC).card : ℝ))
      (fun i _ => regime.N i) (fun i => (X i).width) := by
  have hcard : ∀ i, ((X i).pts.image TrackD.toC).card = (X i).pts.card :=
    fun i => Finset.card_image_of_injective _ profile_toC_injective
  constructor
  · intro ε hε
    filter_upwards [hsize ε hε] with i hi
    intro u
    simpa only [hcard i] using hi
  · intro ε hε
    exact Eventually.of_forall fun i u => by
      have hN : (((X i).pts.image TrackD.toC).card : ℝ) ≤ regime.N i := by
        rw [hcard i]
        change ((X i).pts.card : ℝ) ≤ ((regime.P i).card : ℝ)
        exact_mod_cast Finset.card_le_card (hsub i)
      have he : 1 ≤ Real.exp (ε * (X i).width) :=
        Real.one_le_exp_iff.mpr (mul_nonneg hε.le (hwidth i).le)
      exact hN.trans (by simpa using mul_le_mul_of_nonneg_left he (regime.N_pos i).le)

open Classical in
/-- The explicit equality bundle unfolds to `DepthFromProfile` in the frozen
wrapper. The fixed real owner map is extended along injective complexification. -/
theorem separated_depth_data_core {d : ℕ} {regime : Regime d}
    (S : LimitingSeparatedProfile regime) (j : ℕ) (hj₀ : 1 ≤ j) (hjd : j < d)
    (owner : ℕ → RPoint d → AffineVariety d)
    (howner : ∀ i, TrackD.CarrierAssignment {S.sequence.target i} j (owner i)) :
    ∃ D : TrackA.SeparatedDepthData regime j,
      (D.s = (fun i => (S.sequence.target i).width) ∧
        D.v = (fun i => (S.sequence.source i).width) ∧ D.b = S.b ∧
        ∀ i,
          D.centers i = (S.sequence.source i).pts.image TrackD.toC ∧
          D.targets i = (S.sequence.target i).pts.image TrackD.toC ∧
          D.carriers i = (D.targets i).image (D.owner i) ∧
          (∀ q ∈ (S.sequence.target i).pts,
            (S.sequence.target i).path.IsCarrier j (D.owner i (TrackD.toC q))) ∧
          D.pathEquations i =
            (Finset.univ.filter (fun t : Fin d => t.val < j)).image
              (S.sequence.target i).path.cut) ∧
      ∀ i q, q ∈ (S.sequence.target i).pts → D.owner i (TrackD.toC q) = owner i q := by
  classical
  let own : ℕ → Point d → AffineVariety d := fun i =>
    Function.extend TrackD.toC (owner i) (fun _ => AffineVariety.whole)
  have hown : ∀ i q, own i (TrackD.toC q) = owner i q :=
    fun i q => profile_toC_injective.extend_apply (owner i) (fun _ => AffineVariety.whole) q
  let centers := fun i => (S.sequence.source i).pts.image TrackD.toC
  let targets := fun i => (S.sequence.target i).pts.image TrackD.toC
  let carriers := fun i => (targets i).image (own i)
  let equations := fun i =>
    (Finset.univ.filter (fun t : Fin d => t.val < j)).image (S.sequence.target i).path.cut
  have hphysical : ∀ i q, q ∈ (S.sequence.target i).pts →
      (S.sequence.target i).path.IsCarrier j (own i (TrackD.toC q)) ∧
        TrackD.toC q ∈ own i (TrackD.toC q) := by
    intro i q hq
    rw [hown]
    exact howner i (S.sequence.target i) (Finset.mem_singleton_self _) q hq
  have hspan : ∀ i, Ideal.span (equations i : Set (Poly d)) =
      (S.sequence.target i).path.system j := by
    intro i
    have hset : (equations i : Set (Poly d)) =
        {f | ∃ t : Fin d, t.val < j ∧ (S.sequence.target i).path.cut t = f} := by
      ext f
      simp [equations]
    change Ideal.span (equations i : Set (Poly d)) = Ideal.span _
    rw [hset]
  have hpure : ∀ i, AffineFamily.IsPure (carriers i) (d - j) := by
    intro i Y hY
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hY
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
    have hgood := (S.sequence.base_good i).2
    exact TrackD.prof_partition_pure (S.sequence.target i) x hx
      (hgood.vanish x hx) (hgood.proper x hx) j hjd.le
      (own i (TrackD.toC x)) (hphysical i x hx)
  have hcomponent : ∀ i Y, Y ∈ carriers i →
      Y.IsComponentOf (Ideal.span (equations i : Set (Poly d))) := by
    intro i Y hY
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hY
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
    rw [hspan i]
    exact (hphysical i x hx).1
  have hdegree : ∃ C : ℝ, 0 < C ∧ ∀ᶠ i in atTop,
      ∀ f ∈ equations i, (f.totalDegree : ℝ) ≤
        regime.B i * Real.exp (C * (S.sequence.target i).width) := by
    refine ⟨3, by norm_num, Eventually.of_forall ?_⟩
    intro i f hf
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hf
    have hgood := (S.sequence.base_good i).2
    have htest : (((S.sequence.target i).path.cut t).totalDegree : ℝ) ≤
        regime.B i * Real.exp (((S.sequence.target i).path.time t + 1) *
          (S.sequence.target i).width) := by
      simpa only [TrackD.testDeg, TrackD.cfgB, Regime.B, Regime.N] using hgood.degree t
    apply htest.trans
    apply mul_le_mul_of_nonneg_left _ (regime.B_pos i).le
    apply Real.exp_le_exp.mpr
    have htime := (hgood.time_range t).2
    have hw := (S.sequence.width_pos i).2
    nlinarith
  have hsourceSize := profile_sample_size (regime := regime) S.sequence.source
    (fun i => (S.sequence.base_good i).1.subset)
    (fun i => (S.sequence.width_pos i).1) (fun ε hε => by
      filter_upwards [S.sequence.good ε hε 1 (by norm_num) 1 le_rfl] with i hi
      exact hi.1.size)
  have htargetSize := profile_sample_size (regime := regime) S.sequence.target
    (fun i => (S.sequence.base_good i).2.subset)
    (fun i => (S.sequence.width_pos i).2) (fun ε hε => by
      filter_upwards [S.sequence.good ε hε 1 (by norm_num) 1 le_rfl] with i hi
      exact hi.2.size)
  let D : TrackA.SeparatedDepthData regime j := {
    j_pos := hj₀
    j_lt := hjd
    s := fun i => (S.sequence.target i).width
    v := fun i => (S.sequence.source i).width
    s_grows := S.sequence.target_grows
    v_grows := S.sequence.source_grows
    s_small := S.sequence.target_small
    v_small := S.sequence.source_small
    separated := S.sequence.separated
    b := S.b
    b_sorted := S.sorted
    b_sum := S.sum_zero
    centers := centers
    targets := targets
    centers_subsample := fun i => Finset.image_subset_image (S.sequence.base_good i).1.subset
    targets_subsample := fun i => Finset.image_subset_image (S.sequence.base_good i).2.subset
    carriers := carriers
    carrier_pure := hpure
    owner := own
    owner_member := fun i q hq => Finset.mem_image.mpr ⟨q, hq, rfl⟩
    owner_contains := by
      intro i q hq
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
      exact (hphysical i x hx).2
    pathEquations := equations
    path_component := hcomponent
    path_degree := hdegree
    source_size := hsourceSize
    target_size := htargetSize }
  refine ⟨D, ⟨rfl, rfl, rfl, ?_⟩, ?_⟩
  · intro i
    exact ⟨rfl, rfl, rfl, fun q hq => (hphysical i q hq).1, rfl⟩
  · intro i q hq
    exact hown i q

end

end DistinctDistances.SparseCones
