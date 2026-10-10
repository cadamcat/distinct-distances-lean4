import DistinctDistances.TrackE.WideCarriers
import DistinctDistances.TrackE.RequestsWide
import DistinctDistances.TrackE.RequestsWideFlat
import DistinctDistances.TrackE.FlatCaps
import DistinctDistances.TrackD.PairGenericity

/-! Fixed surviving physical assignments for wide-window generic lists
(`depth.tex:235–281`). All families and fibers are specified before lists,
centers, component tests, and later incidence deletions are chosen. -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section

variable {d j : ℕ} {regime : Regime d}

/-- Exact target-profile identities consumed by the finite assignment bridge.
The frozen DepthFromProfile wrapper constructs this record directly. -/
structure WideTargetProfile (S : LimitingSeparatedProfile regime)
    (D : TrackA.SeparatedDepthData regime j) where
  s_eq : D.s = fun i => (S.sequence.target i).width
  v_eq : D.v = fun i => (S.sequence.source i).width
  b_eq : D.b = S.b
  centers_eq : ∀ i, D.centers i = (S.sequence.source i).pts.image TrackD.toC
  targets_eq : ∀ i, D.targets i = (S.sequence.target i).pts.image TrackD.toC
  carriers_eq : ∀ i, D.carriers i = (D.targets i).image (D.owner i)
  carrier_path : ∀ i q, q ∈ (S.sequence.target i).pts →
    (S.sequence.target i).path.IsCarrier j (D.owner i (TrackD.toC q))
  budgets : D.DegreeBudgets

/-- Keep every nonlinear carrier and every real flat carrier. -/
def keepRealCarrier (Z : AffineVariety d) : Prop :=
  TrackD.IsFlat Z → TrackD.IsRealFlat Z

namespace WideSourceCarriers
variable {S : LimitingSeparatedProfile regime} {A : PositiveSourcePlateau S j}
    (W : WideSourceCarriers S A)

/-- Distinct surviving source values of the original fixed owner map. -/
def survivingSources (i : ℕ) : AffineFamily.Family d :=
  (W.data.carriers i).filter keepRealCarrier

/-- Ignore precisely the actual source assignments to nonreal flat members. -/
def ignoredSources (i : ℕ) : Finset (Point d) :=
  (W.data.targets i).filter (fun p => ¬ keepRealCarrier (W.data.owner i p))

/-- Real sample labels are preserved within each fixed source owner fiber. -/
def sourceAssigned (i : ℕ) (X : AffineVariety d) : Finset (RPoint d) :=
  (S.sequence.source i).pts.filter (fun p => W.data.owner i (TrackD.toC p) = X)

end WideSourceCarriers

/-- The equal-dimensional case omits nonreal target flats. In the strict
case the target family is unchanged, using the separate generic-depth input. -/
def wideSurvivingTargets (D : TrackA.SeparatedDepthData regime j)
    {S : LimitingSeparatedProfile regime} (A : PositiveSourcePlateau S j)
    (i : ℕ) : AffineFamily.Family d :=
  if A.r.val = j then (D.carriers i).filter keepRealCarrier else D.carriers i

/-- The target sets are fibers of the earlier physical assignment. -/
def wideTargetAssigned (S : LimitingSeparatedProfile regime)
    (D : TrackA.SeparatedDepthData regime j) (i : ℕ) (Y : AffineVariety d) :
    Finset (RPoint d) :=
  (S.sequence.target i).pts.filter (fun p => D.owner i (TrackD.toC p) = Y)

/-- Finite assignment facts; no asymptotic generic-list property is a field. -/
structure WideFiniteFacts (S : LimitingSeparatedProfile regime)
    (D : TrackA.SeparatedDepthData regime j) (A : PositiveSourcePlateau S j)
    (W : WideSourceCarriers S A) : Prop where
  source_pure : ∀ i, AffineFamily.IsPure (W.survivingSources i) (d - A.r.val)
  targets_subset : ∀ i, wideSurvivingTargets D A i ⊆ D.carriers i
  source_assignment : ∀ i, TrackD.Assignment (regime.P i)
    (W.survivingSources i) (W.sourceAssigned i)
  target_assignment : ∀ i, TrackD.Assignment (regime.P i)
    (wideSurvivingTargets D A i) (wideTargetAssigned S D i)
  ignored_subset : ∀ i, W.ignoredSources i ⊆ D.centers i
  source_owner : ∀ i p, p ∈ D.centers i → p ∉ W.ignoredSources i →
    W.data.owner i p ∈ W.survivingSources i ∧
    (S.sequence.source i).path.IsCarrier A.r.val (W.data.owner i p) ∧
    p ∈ W.data.owner i p
  flat_real : A.r.val = j → ∀ i Z,
    Z ∈ W.survivingSources i ∪ wideSurvivingTargets D A i →
    TrackD.IsFlat Z → TrackD.IsRealFlat Z
  source_mass_le : ∀ i, TrackD.famMass (W.survivingSources i) (W.sourceAssigned i) ≤
    ((D.centers i).card : ℝ)
  target_mass_le : ∀ i, TrackD.famMass (wideSurvivingTargets D A i)
    (wideTargetAssigned S D i) ≤ ((D.targets i).card : ℝ)
  centers_pos : ∀ i, 0 < ((D.centers i).card : ℝ)
  targets_pos : ∀ i, 0 < ((D.targets i).card : ℝ)

/-- `G5.wide.fibers`: finite owner-fiber and physical-assignment facts. -/
theorem wide_finite_assignment_facts (S : LimitingSeparatedProfile regime)
    (D : TrackA.SeparatedDepthData regime j) (T : WideTargetProfile S D)
    (A : PositiveSourcePlateau S j) (W : WideSourceCarriers S A) :
    WideFiniteFacts S D A W := by
  have htargets_eq (i : ℕ) : W.data.targets i = D.centers i := by
    rw [W.targets_eq i, T.centers_eq i]
  have hsource_card (i : ℕ) : (D.centers i).card = (S.sequence.source i).pts.card := by
    rw [T.centers_eq i, Finset.card_image_of_injective _ profile_toC_injective]
  have htarget_card (i : ℕ) : (D.targets i).card = (S.sequence.target i).pts.card := by
    rw [T.targets_eq i, Finset.card_image_of_injective _ profile_toC_injective]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i X hX
    have hX_mem : X ∈ W.data.carriers i := (Finset.mem_filter.mp hX).1
    exact W.data.carrier_pure i X hX_mem
  · intro i
    dsimp [wideSurvivingTargets]
    split_ifs
    · exact Finset.filter_subset _ _
    · exact Finset.Subset.refl _
  · intro i
    refine ⟨?_, ?_, ?_⟩
    · intro X hX q hq
      have hq_pts : q ∈ (S.sequence.source i).pts := (Finset.mem_filter.mp hq).1
      exact (S.sequence.base_good i).1.subset hq_pts
    · intro X hX q hq
      have hq_filter := Finset.mem_filter.mp hq
      have hq_pts : q ∈ (S.sequence.source i).pts := hq_filter.1
      have hq_owner : W.data.owner i (TrackD.toC q) = X := hq_filter.2
      have hq_target : TrackD.toC q ∈ W.data.targets i := by
        rw [W.targets_eq i]
        exact Finset.mem_image_of_mem _ hq_pts
      have hcontains := W.data.owner_contains i (TrackD.toC q) hq_target
      rw [hq_owner] at hcontains
      exact hcontains
    · intro X hX Y hY hXY
      dsimp [Function.onFun]
      rw [Finset.disjoint_left]
      intro q hqX hqY
      have h1 := (Finset.mem_filter.mp hqX).2
      have h2 := (Finset.mem_filter.mp hqY).2
      exact hXY (h1.symm.trans h2)
  · intro i
    refine ⟨?_, ?_, ?_⟩
    · intro Y hY q hq
      have hq_pts : q ∈ (S.sequence.target i).pts := (Finset.mem_filter.mp hq).1
      exact (S.sequence.base_good i).2.subset hq_pts
    · intro Y hY q hq
      have hq_filter := Finset.mem_filter.mp hq
      have hq_pts : q ∈ (S.sequence.target i).pts := hq_filter.1
      have hq_owner : D.owner i (TrackD.toC q) = Y := hq_filter.2
      have hq_target : TrackD.toC q ∈ D.targets i := by
        rw [T.targets_eq i]
        exact Finset.mem_image_of_mem _ hq_pts
      have hcontains := D.owner_contains i (TrackD.toC q) hq_target
      rw [hq_owner] at hcontains
      exact hcontains
    · intro X hX Y hY hXY
      dsimp [Function.onFun]
      rw [Finset.disjoint_left]
      intro q hqX hqY
      have h1 := (Finset.mem_filter.mp hqX).2
      have h2 := (Finset.mem_filter.mp hqY).2
      exact hXY (h1.symm.trans h2)
  · intro i p hp
    have hmem : p ∈ W.data.targets i := (Finset.mem_filter.mp hp).1
    rwa [htargets_eq i] at hmem
  · intro i p hp hnot
    have hp_target : p ∈ W.data.targets i := by rwa [htargets_eq i]
    have hnot_keep : keepRealCarrier (W.data.owner i p) := by
      by_contra hc
      have : p ∈ W.ignoredSources i := by
        rw [WideSourceCarriers.ignoredSources, Finset.mem_filter]
        exact ⟨hp_target, hc⟩
      exact hnot this
    have howner_mem : W.data.owner i p ∈ W.data.carriers i :=
      W.data.owner_member i p hp_target
    have hsurv : W.data.owner i p ∈ W.survivingSources i := by
      rw [WideSourceCarriers.survivingSources, Finset.mem_filter]
      exact ⟨howner_mem, hnot_keep⟩
    have hpath : (S.sequence.source i).path.IsCarrier A.r.val (W.data.owner i p) := by
      rw [T.centers_eq i] at hp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      exact W.carrier_path i q hq
    have hcontains : p ∈ W.data.owner i p :=
      W.data.owner_contains i p hp_target
    exact ⟨hsurv, hpath, hcontains⟩
  · intro heq i Z hZ hflat
    rcases Finset.mem_union.mp hZ with hZ_src | hZ_tgt
    · have hkeep := (Finset.mem_filter.mp hZ_src).2
      exact hkeep hflat
    · dsimp [wideSurvivingTargets] at hZ_tgt
      rw [if_pos heq] at hZ_tgt
      have hkeep := (Finset.mem_filter.mp hZ_tgt).2
      exact hkeep hflat
  · intro i
    dsimp [TrackD.famMass]
    have hfiber := Finset.sum_card_fiberwise_eq_card_filter
      (S.sequence.source i).pts (W.survivingSources i)
      (fun p => W.data.owner i (TrackD.toC p))
    have hle : (∑ X ∈ W.survivingSources i, (W.sourceAssigned i X).card) ≤ (D.centers i).card := by
      calc
        (∑ X ∈ W.survivingSources i, (W.sourceAssigned i X).card) =
            ((S.sequence.source i).pts.filter (fun p =>
              W.data.owner i (TrackD.toC p) ∈ W.survivingSources i)).card := by
          dsimp [WideSourceCarriers.sourceAssigned]
          rw [hfiber]
        _ ≤ (S.sequence.source i).pts.card := Finset.card_filter_le _ _
        _ = (D.centers i).card := (hsource_card i).symm
    exact_mod_cast hle
  · intro i
    dsimp [TrackD.famMass]
    have hfiber := Finset.sum_card_fiberwise_eq_card_filter
      (S.sequence.target i).pts (wideSurvivingTargets D A i)
      (fun p => D.owner i (TrackD.toC p))
    have hle : (∑ Y ∈ wideSurvivingTargets D A i, (wideTargetAssigned S D i Y).card) ≤ (D.targets i).card := by
      calc
        (∑ Y ∈ wideSurvivingTargets D A i, (wideTargetAssigned S D i Y).card) =
            ((S.sequence.target i).pts.filter (fun p =>
              D.owner i (TrackD.toC p) ∈ wideSurvivingTargets D A i)).card := by
          dsimp [wideTargetAssigned]
          rw [hfiber]
        _ ≤ (S.sequence.target i).pts.card := Finset.card_filter_le _ _
        _ = (D.targets i).card := (htarget_card i).symm
    exact_mod_cast hle
  · intro i
    rw [hsource_card i]
    have hsize := (S.sequence.base_good i).1.size
    have hNpos : 0 < (regime.P i).card := by
      have := regime.card_ge_two i
      omega
    have hexp : 0 < Real.exp (-1 * (S.sequence.source i).width) := by positivity
    have hpos : 0 < TrackD.cfgN (regime.P i) * Real.exp (-1 * (S.sequence.source i).width) := by
      dsimp [TrackD.cfgN]
      positivity
    have hpts_pos : 0 < ((S.sequence.source i).pts.card : ℝ) := hpos.trans_le hsize
    exact hpts_pos
  · intro i
    rw [htarget_card i]
    have hsize := (S.sequence.base_good i).2.size
    have hNpos : 0 < (regime.P i).card := by
      have := regime.card_ge_two i
      omega
    have hexp : 0 < Real.exp (-1 * (S.sequence.target i).width) := by positivity
    have hpos : 0 < TrackD.cfgN (regime.P i) * Real.exp (-1 * (S.sequence.target i).width) := by
      dsimp [TrackD.cfgN]
      positivity
    have hpts_pos : 0 < ((S.sequence.target i).pts.card : ℝ) := hpos.trans_le hsize
    exact hpts_pos

/-- `G5.wide.omissions`: both fixed assignment omissions are negligible
relative to their literal samples, with target deletion needed only when r=j. -/
theorem wide_omission_negligible (S : LimitingSeparatedProfile regime)
    (D : TrackA.SeparatedDepthData regime j) (T : WideTargetProfile S D)
    (A : PositiveSourcePlateau S j) (W : WideSourceCarriers S A) :
    Framework.LittleO (fun i => ((W.ignoredSources i).card : ℝ))
      (fun i => ((D.centers i).card : ℝ)) ∧
    Framework.LittleO (fun i => D.submass i (D.carriers i \ wideSurvivingTargets D A i))
      (fun i => ((D.targets i).card : ℝ)) := by
  have hcenters_card (i : ℕ) : (D.centers i).card = (S.sequence.source i).pts.card := by
    rw [T.centers_eq i, Finset.card_image_of_injective _ profile_toC_injective]
  have htargets_card (i : ℕ) : (D.targets i).card = (S.sequence.target i).pts.card := by
    rw [T.targets_eq i, Finset.card_image_of_injective _ profile_toC_injective]
  constructor
  · have hsource_o := source_nonreal_negligible S A
    apply Asymptotics.IsLittleO.of_bound
    intro ε hε
    filter_upwards [hsource_o.def hε] with i hi
    let bad := (S.sequence.source i).pts.filter (fun x =>
      ∃ Z ∈ (S.sequence.source i).path.localCarriers A.r.val (TrackD.toC x),
        TrackD.IsFlat Z ∧ ¬ TrackD.IsRealFlat Z)
    have hsub : W.ignoredSources i ⊆ bad.image TrackD.toC := by
      intro p hp
      have hp_filter := Finset.mem_filter.mp hp
      have hp_target : p ∈ W.data.targets i := hp_filter.1
      have hp_not : ¬ keepRealCarrier (W.data.owner i p) := hp_filter.2
      rw [W.targets_eq i] at hp_target
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp_target
      apply Finset.mem_image_of_mem
      rw [Finset.mem_filter]
      have hcontains := W.data.owner_contains i (TrackD.toC x) (by
        rw [W.targets_eq i]
        exact Finset.mem_image_of_mem _ hx)
      have hloc : W.data.owner i (TrackD.toC x) ∈
          (S.sequence.source i).path.localCarriers A.r.val (TrackD.toC x) :=
        ⟨W.carrier_path i x hx, hcontains⟩
      have hp_flat : TrackD.IsFlat (W.data.owner i (TrackD.toC x)) := by
        by_contra hnot
        apply hp_not
        intro h
        exact (hnot h).elim
      have hp_nonreal : ¬ TrackD.IsRealFlat (W.data.owner i (TrackD.toC x)) := by
        intro hreal
        apply hp_not
        intro _
        exact hreal
      exact ⟨hx, ⟨W.data.owner i (TrackD.toC x), hloc, hp_flat, hp_nonreal⟩⟩
    have hcard : (W.ignoredSources i).card ≤ bad.card := by
      calc
        (W.ignoredSources i).card ≤ (bad.image TrackD.toC).card := Finset.card_le_card hsub
        _ ≤ bad.card := Finset.card_image_le
    have hnorm_bad : ‖(bad.card : ℝ)‖ = (bad.card : ℝ) := Real.norm_of_nonneg (by positivity)
    have hnorm_source : ‖((S.sequence.source i).pts.card : ℝ)‖ = ((S.sequence.source i).pts.card : ℝ) :=
      Real.norm_of_nonneg (by positivity)
    rw [hnorm_bad, hnorm_source] at hi
    have hnorm_ign : ‖((W.ignoredSources i).card : ℝ)‖ = ((W.ignoredSources i).card : ℝ) :=
      Real.norm_of_nonneg (by positivity)
    have hnorm_cent : ‖((D.centers i).card : ℝ)‖ = ((D.centers i).card : ℝ) :=
      Real.norm_of_nonneg (by positivity)
    rw [hnorm_ign, hnorm_cent, hcenters_card i]
    exact (Nat.cast_le.mpr hcard).trans hi
  · by_cases heq : A.r.val = j
    · have htarget_o := target_nonreal_negligible_of_first_positive S A heq
      apply Asymptotics.IsLittleO.of_bound
      intro ε hε
      filter_upwards [htarget_o.def hε] with i hi
      let bad := (S.sequence.target i).pts.filter (fun x =>
        ∃ Z ∈ (S.sequence.target i).path.localCarriers j (TrackD.toC x),
          TrackD.IsFlat Z ∧ ¬ TrackD.IsRealFlat Z)
      have hsurv_eq : wideSurvivingTargets D A i = (D.carriers i).filter keepRealCarrier := by
        dsimp [wideSurvivingTargets]
        rw [if_pos heq]
      have hdiff_eq : D.carriers i \ wideSurvivingTargets D A i =
          (D.carriers i).filter (fun Y => ¬ keepRealCarrier Y) := by
        rw [hsurv_eq]
        ext Y
        simp only [Finset.mem_sdiff, Finset.mem_filter]
        tauto
      have hsubmass : D.submass i (D.carriers i \ wideSurvivingTargets D A i) =
          (((D.targets i).filter (fun q => D.owner i q ∈
            (D.carriers i \ wideSurvivingTargets D A i))).card : ℝ) := by
        dsimp [TrackA.SeparatedDepthData.submass, TrackA.SeparatedDepthData.mass]
        exact_mod_cast Finset.sum_card_fiberwise_eq_card_filter
          (D.targets i) (D.carriers i \ wideSurvivingTargets D A i) (D.owner i)
      have hsub : (D.targets i).filter (fun q => D.owner i q ∈
          (D.carriers i \ wideSurvivingTargets D A i)) ⊆ bad.image TrackD.toC := by
        intro q hq
        have hq_filter := Finset.mem_filter.mp hq
        have hq_target : q ∈ D.targets i := hq_filter.1
        have hq_J : D.owner i q ∈ D.carriers i \ wideSurvivingTargets D A i := hq_filter.2
        rw [hdiff_eq, Finset.mem_filter] at hq_J
        have hp_not := hq_J.2
        rw [T.targets_eq i] at hq_target
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hq_target
        apply Finset.mem_image_of_mem
        rw [Finset.mem_filter]
        have hcontains := D.owner_contains i (TrackD.toC y) (by
          rw [T.targets_eq i]
          exact Finset.mem_image_of_mem _ hy)
        have hloc : D.owner i (TrackD.toC y) ∈
            (S.sequence.target i).path.localCarriers j (TrackD.toC y) :=
          ⟨T.carrier_path i y hy, hcontains⟩
        have hY_flat : TrackD.IsFlat (D.owner i (TrackD.toC y)) := by
          by_contra hnot
          apply hp_not
          intro h
          exact (hnot h).elim
        have hY_nonreal : ¬ TrackD.IsRealFlat (D.owner i (TrackD.toC y)) := by
          intro hreal
          apply hp_not
          intro _
          exact hreal
        exact ⟨hy, ⟨D.owner i (TrackD.toC y), hloc, hY_flat, hY_nonreal⟩⟩
      have hcard : ((D.targets i).filter (fun q => D.owner i q ∈
          (D.carriers i \ wideSurvivingTargets D A i))).card ≤ bad.card := by
        calc
          ((D.targets i).filter (fun q => D.owner i q ∈
              (D.carriers i \ wideSurvivingTargets D A i))).card ≤ (bad.image TrackD.toC).card :=
            Finset.card_le_card hsub
          _ ≤ bad.card := Finset.card_image_le
      have hnorm_bad : ‖(bad.card : ℝ)‖ = (bad.card : ℝ) := Real.norm_of_nonneg (by positivity)
      have hnorm_target : ‖((S.sequence.target i).pts.card : ℝ)‖ = ((S.sequence.target i).pts.card : ℝ) :=
        Real.norm_of_nonneg (by positivity)
      rw [hnorm_bad, hnorm_target] at hi
      have hnonneg_mass : 0 ≤ D.submass i (D.carriers i \ wideSurvivingTargets D A i) := by
        rw [hsubmass]
        exact Nat.cast_nonneg _
      have hnorm_sub : ‖D.submass i (D.carriers i \ wideSurvivingTargets D A i)‖ =
          D.submass i (D.carriers i \ wideSurvivingTargets D A i) := Real.norm_of_nonneg hnonneg_mass
      have hnorm_tgt : ‖((D.targets i).card : ℝ)‖ = ((D.targets i).card : ℝ) :=
        Real.norm_of_nonneg (by positivity)
      rw [hnorm_sub, hnorm_tgt, htargets_card i, hsubmass]
      exact (Nat.cast_le.mpr hcard).trans hi
    · apply Asymptotics.IsLittleO.of_bound
      intro ε hε
      apply Eventually.of_forall
      intro i
      have hsurv_eq : wideSurvivingTargets D A i = D.carriers i := by
        dsimp [wideSurvivingTargets]
        rw [if_neg heq]
      have hdiff_empty : D.carriers i \ wideSurvivingTargets D A i = ∅ := by
        rw [hsurv_eq, Finset.sdiff_self]
      have hzero : D.submass i (D.carriers i \ wideSurvivingTargets D A i) = 0 := by
        dsimp [TrackA.SeparatedDepthData.submass]
        rw [hdiff_empty, Finset.sum_empty]
      rw [hzero, norm_zero]
      exact mul_nonneg hε.le (norm_nonneg _)

lemma wide_source_mass_add_ignored (S : LimitingSeparatedProfile regime)
    (D : TrackA.SeparatedDepthData regime j) (T : WideTargetProfile S D)
    (A : PositiveSourcePlateau S j) (W : WideSourceCarriers S A) (i : ℕ) :
    TrackD.famMass (W.survivingSources i) (W.sourceAssigned i) + ((W.ignoredSources i).card : ℝ) =
      ((D.centers i).card : ℝ) := by
  have hfiber := Finset.sum_card_fiberwise_eq_card_filter
    (S.sequence.source i).pts (W.survivingSources i)
    (fun p => W.data.owner i (TrackD.toC p))
  have hmass : TrackD.famMass (W.survivingSources i) (W.sourceAssigned i) =
      (((S.sequence.source i).pts.filter (fun p =>
        W.data.owner i (TrackD.toC p) ∈ W.survivingSources i)).card : ℝ) := by
    dsimp [TrackD.famMass, WideSourceCarriers.sourceAssigned]
    exact_mod_cast hfiber
  have hsurv_filter : (S.sequence.source i).pts.filter (fun p =>
      W.data.owner i (TrackD.toC p) ∈ W.survivingSources i) =
    (S.sequence.source i).pts.filter (fun p =>
      keepRealCarrier (W.data.owner i (TrackD.toC p))) := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · intro ⟨hp, hmem⟩
      have := (Finset.mem_filter.mp hmem).2
      exact ⟨hp, this⟩
    · intro ⟨hp, hkeep⟩
      refine ⟨hp, ?_⟩
      rw [WideSourceCarriers.survivingSources, Finset.mem_filter]
      have htarget : TrackD.toC p ∈ W.data.targets i := by
        rw [W.targets_eq i]
        exact Finset.mem_image_of_mem _ hp
      exact ⟨W.data.owner_member i (TrackD.toC p) htarget, hkeep⟩
  have hign_filter : (W.ignoredSources i).card =
      ((S.sequence.source i).pts.filter (fun p =>
        ¬ keepRealCarrier (W.data.owner i (TrackD.toC p)))).card := by
    dsimp [WideSourceCarriers.ignoredSources]
    rw [W.targets_eq i]
    have hfeq : ((S.sequence.source i).pts.image TrackD.toC).filter
        (fun q => ¬ keepRealCarrier (W.data.owner i q)) =
      ((S.sequence.source i).pts.filter
        (fun p => ¬ keepRealCarrier (W.data.owner i (TrackD.toC p)))).image TrackD.toC := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨p, hp, rfl⟩, hnot⟩
        exact ⟨p, ⟨hp, hnot⟩, rfl⟩
      · rintro ⟨p, ⟨hp, hnot⟩, rfl⟩
        exact ⟨⟨p, hp, rfl⟩, hnot⟩
    rw [hfeq, Finset.card_image_of_injective _ profile_toC_injective]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (S.sequence.source i).pts) (fun p => keepRealCarrier (W.data.owner i (TrackD.toC p)))
  have hcenters_card : (D.centers i).card = (S.sequence.source i).pts.card := by
    rw [T.centers_eq i, Finset.card_image_of_injective _ profile_toC_injective]
  rw [hmass, hsurv_filter, hign_filter, hcenters_card]
  exact_mod_cast hsplit

lemma wide_target_mass_add_omitted (S : LimitingSeparatedProfile regime)
    (D : TrackA.SeparatedDepthData regime j) (T : WideTargetProfile S D)
    (A : PositiveSourcePlateau S j) (i : ℕ) :
    TrackD.famMass (wideSurvivingTargets D A i) (wideTargetAssigned S D i) +
      D.submass i (D.carriers i \ wideSurvivingTargets D A i) =
        ((D.targets i).card : ℝ) := by
  have hfiber := Finset.sum_card_fiberwise_eq_card_filter
    (S.sequence.target i).pts (wideSurvivingTargets D A i)
    (fun p => D.owner i (TrackD.toC p))
  have hmass : TrackD.famMass (wideSurvivingTargets D A i) (wideTargetAssigned S D i) =
      (((S.sequence.target i).pts.filter (fun p =>
        D.owner i (TrackD.toC p) ∈ wideSurvivingTargets D A i)).card : ℝ) := by
    dsimp [TrackD.famMass, wideTargetAssigned]
    exact_mod_cast hfiber
  have hsubmass : D.submass i (D.carriers i \ wideSurvivingTargets D A i) =
      (((D.targets i).filter (fun q => D.owner i q ∈
        (D.carriers i \ wideSurvivingTargets D A i))).card : ℝ) := by
    dsimp [TrackA.SeparatedDepthData.submass, TrackA.SeparatedDepthData.mass]
    exact_mod_cast Finset.sum_card_fiberwise_eq_card_filter
      (D.targets i) (D.carriers i \ wideSurvivingTargets D A i) (D.owner i)
  have hsub_filter : ((D.targets i).filter (fun q => D.owner i q ∈
        (D.carriers i \ wideSurvivingTargets D A i))).card =
      ((S.sequence.target i).pts.filter (fun p =>
        D.owner i (TrackD.toC p) ∈ (D.carriers i \ wideSurvivingTargets D A i))).card := by
    rw [T.targets_eq i]
    have hfeq : ((S.sequence.target i).pts.image TrackD.toC).filter
        (fun q => D.owner i q ∈ (D.carriers i \ wideSurvivingTargets D A i)) =
      ((S.sequence.target i).pts.filter
        (fun p => D.owner i (TrackD.toC p) ∈ (D.carriers i \ wideSurvivingTargets D A i))).image TrackD.toC := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨p, hp, rfl⟩, hmem⟩
        exact ⟨p, ⟨hp, hmem⟩, rfl⟩
      · rintro ⟨p, ⟨hp, hmem⟩, rfl⟩
        exact ⟨⟨p, hp, rfl⟩, hmem⟩
    rw [hfeq, Finset.card_image_of_injective _ profile_toC_injective]
  have hcompl : (S.sequence.target i).pts.filter (fun p =>
      D.owner i (TrackD.toC p) ∈ (D.carriers i \ wideSurvivingTargets D A i)) =
    (S.sequence.target i).pts.filter (fun p =>
      D.owner i (TrackD.toC p) ∉ wideSurvivingTargets D A i) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · intro ⟨hp, hmem, hnot⟩
      exact ⟨hp, hnot⟩
    · intro ⟨hp, hnot⟩
      have htarget : TrackD.toC p ∈ D.targets i := by
        rw [T.targets_eq i]
        exact Finset.mem_image_of_mem _ hp
      exact ⟨hp, D.owner_member i (TrackD.toC p) htarget, hnot⟩
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (S.sequence.target i).pts) (fun p => D.owner i (TrackD.toC p) ∈ wideSurvivingTargets D A i)
  have htargets_card : (D.targets i).card = (S.sequence.target i).pts.card := by
    rw [T.targets_eq i, Finset.card_image_of_injective _ profile_toC_injective]
  rw [hmass, hsubmass, hsub_filter, hcompl, htargets_card]
  exact_mod_cast hsplit

/-- `G5.wide.subpower-masses`: fixed surviving samples retain N exp(-o(log B)). -/
theorem wide_surviving_mass_lower (S : LimitingSeparatedProfile regime)
    (D : TrackA.SeparatedDepthData regime j) (T : WideTargetProfile S D)
    (A : PositiveSourcePlateau S j) (W : WideSourceCarriers S A) :
    ∀ θ : ℝ, 0 < θ → ∀ᶠ i in atTop,
      regime.N i * Real.exp (-θ * Real.log (regime.B i)) ≤
        TrackD.famMass (W.survivingSources i) (W.sourceAssigned i) ∧
      regime.N i * Real.exp (-θ * Real.log (regime.B i)) ≤
        TrackD.famMass (wideSurvivingTargets D A i) (wideTargetAssigned S D i) := by
  intro θ hθ
  have homission := wide_omission_negligible S D T A W
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hsource_o := homission.1.def hhalf
  have htarget_o := homission.2.def hhalf
  have hsource_exp := D.source_size.1 1 (by norm_num : (0 : ℝ) < 1)
  have htarget_exp := D.target_size.1 1 (by norm_num : (0 : ℝ) < 1)
  have htheta2 : 0 < θ / 2 := by linarith
  have hv_small := D.v_small.def htheta2
  have hs_small := D.s_small.def htheta2
  have hlog : Tendsto (fun i => Real.log (regime.B i)) atTop atTop :=
    Real.tendsto_log_atTop.comp regime.B_tendsto
  have hB_large : ∀ᶠ i in atTop, (2 * Real.log 2) / θ ≤ Real.log (regime.B i) :=
    hlog.eventually_ge_atTop ((2 * Real.log 2) / θ)
  have hB_ge_one : ∀ᶠ i in atTop, 1 ≤ regime.B i :=
    regime.B_tendsto.eventually_ge_atTop 1
  filter_upwards [hsource_o, htarget_o, hsource_exp, htarget_exp,
    hv_small, hs_small, hB_large, hB_ge_one] with i
    hign_o hsub_o hsrc_size htgt_size hv_o hs_o hlarge hB1
  have hlogB_nonneg : 0 ≤ Real.log (regime.B i) := Real.log_nonneg hB1
  have hnorm_logB : ‖Real.log (regime.B i)‖ = Real.log (regime.B i) :=
    Real.norm_of_nonneg hlogB_nonneg
  rw [hnorm_logB] at hv_o hs_o
  have hv_le : D.v i ≤ (θ / 2) * Real.log (regime.B i) :=
    (le_abs_self (D.v i)).trans hv_o
  have hs_le : D.s i ≤ (θ / 2) * Real.log (regime.B i) :=
    (le_abs_self (D.s i)).trans hs_o
  have hlog2_le : Real.log 2 ≤ (θ / 2) * Real.log (regime.B i) := by
    have hmul := mul_le_mul_of_nonneg_left hlarge (by linarith : 0 ≤ θ / 2)
    have heq : (θ / 2) * ((2 * Real.log 2) / θ) = Real.log 2 := by
      field_simp
    rwa [heq] at hmul
  have hexp_half : Real.exp (- (θ / 2) * Real.log (regime.B i)) ≤ 1 / 2 := by
    have hneg : - (θ / 2) * Real.log (regime.B i) ≤ - Real.log 2 := by linarith
    have h := Real.exp_le_exp.mpr hneg
    have h2pos : (0 : ℝ) < 2 := by norm_num
    have hlog2 : Real.exp (- Real.log 2) = 1 / 2 := by
      rw [Real.exp_neg, Real.exp_log h2pos]
      norm_num
    rwa [hlog2] at h
  have hfactor : -θ * Real.log (regime.B i) =
      - (θ / 2) * Real.log (regime.B i) + - (θ / 2) * Real.log (regime.B i) := by ring
  have hexp_factor : Real.exp (-θ * Real.log (regime.B i)) =
      Real.exp (- (θ / 2) * Real.log (regime.B i)) * Real.exp (- (θ / 2) * Real.log (regime.B i)) := by
    rw [hfactor, Real.exp_add]
  have hexp_le : Real.exp (-θ * Real.log (regime.B i)) ≤
      (1 / 2) * Real.exp (- (θ / 2) * Real.log (regime.B i)) := by
    rw [hexp_factor]
    have hnonneg : 0 ≤ Real.exp (- (θ / 2) * Real.log (regime.B i)) := by positivity
    nlinarith
  have hN_nonneg : 0 ≤ regime.N i := Nat.cast_nonneg _
  have hN_exp_le : regime.N i * Real.exp (-θ * Real.log (regime.B i)) ≤
      (1 / 2) * (regime.N i * Real.exp (- (θ / 2) * Real.log (regime.B i))) := by
    calc regime.N i * Real.exp (-θ * Real.log (regime.B i))
      _ ≤ regime.N i * ((1 / 2) * Real.exp (- (θ / 2) * Real.log (regime.B i))) :=
        mul_le_mul_of_nonneg_left hexp_le hN_nonneg
      _ = (1 / 2) * (regime.N i * Real.exp (- (θ / 2) * Real.log (regime.B i))) := by ring
  have hsrc_size_unit := hsrc_size ()
  have hsrc_v : regime.N i * Real.exp (- (θ / 2) * Real.log (regime.B i)) ≤
      ((D.centers i).card : ℝ) := by
    have hneg_v : - (θ / 2) * Real.log (regime.B i) ≤ - D.v i := by linarith
    have hle_exp : Real.exp (- (θ / 2) * Real.log (regime.B i)) ≤ Real.exp (- D.v i) :=
      Real.exp_le_exp.mpr hneg_v
    have hmul : regime.N i * Real.exp (- (θ / 2) * Real.log (regime.B i)) ≤
        regime.N i * Real.exp (- D.v i) := mul_le_mul_of_nonneg_left hle_exp hN_nonneg
    have h1v : -1 * D.v i = - D.v i := by ring
    rw [h1v] at hsrc_size_unit
    exact hmul.trans hsrc_size_unit
  have hsrc_half : (1 / 2) * (regime.N i * Real.exp (- (θ / 2) * Real.log (regime.B i))) ≤
      (1 / 2) * ((D.centers i).card : ℝ) := mul_le_mul_of_nonneg_left hsrc_v (by norm_num)
  have hnorm_ign : ‖((W.ignoredSources i).card : ℝ)‖ = ((W.ignoredSources i).card : ℝ) :=
    Real.norm_of_nonneg (by positivity)
  have hnorm_cent : ‖((D.centers i).card : ℝ)‖ = ((D.centers i).card : ℝ) :=
    Real.norm_of_nonneg (by positivity)
  rw [hnorm_ign, hnorm_cent] at hign_o
  have hsrc_mass_eq := wide_source_mass_add_ignored S D T A W i
  have hsrc_surv_ge : (1 / 2) * ((D.centers i).card : ℝ) ≤
      TrackD.famMass (W.survivingSources i) (W.sourceAssigned i) := by
    linarith [hsrc_mass_eq, hign_o]
  have htgt_size_unit := htgt_size ()
  have htgt_s : regime.N i * Real.exp (- (θ / 2) * Real.log (regime.B i)) ≤
      ((D.targets i).card : ℝ) := by
    have hneg_s : - (θ / 2) * Real.log (regime.B i) ≤ - D.s i := by linarith
    have hle_exp : Real.exp (- (θ / 2) * Real.log (regime.B i)) ≤ Real.exp (- D.s i) :=
      Real.exp_le_exp.mpr hneg_s
    have hmul : regime.N i * Real.exp (- (θ / 2) * Real.log (regime.B i)) ≤
        regime.N i * Real.exp (- D.s i) := mul_le_mul_of_nonneg_left hle_exp hN_nonneg
    have h1s : -1 * D.s i = - D.s i := by ring
    rw [h1s] at htgt_size_unit
    exact hmul.trans htgt_size_unit
  have htgt_half : (1 / 2) * (regime.N i * Real.exp (- (θ / 2) * Real.log (regime.B i))) ≤
      (1 / 2) * ((D.targets i).card : ℝ) := mul_le_mul_of_nonneg_left htgt_s (by norm_num)
  have hsubmass_nonneg : 0 ≤ D.submass i (D.carriers i \ wideSurvivingTargets D A i) := by
    dsimp [TrackA.SeparatedDepthData.submass, TrackA.SeparatedDepthData.mass]
    exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hnorm_sub : ‖D.submass i (D.carriers i \ wideSurvivingTargets D A i)‖ =
      D.submass i (D.carriers i \ wideSurvivingTargets D A i) :=
    Real.norm_of_nonneg hsubmass_nonneg
  have hnorm_tgt : ‖((D.targets i).card : ℝ)‖ = ((D.targets i).card : ℝ) :=
    Real.norm_of_nonneg (by positivity)
  rw [hnorm_sub, hnorm_tgt] at hsub_o
  have htgt_mass_eq := wide_target_mass_add_omitted S D T A i
  have htgt_surv_ge : (1 / 2) * ((D.targets i).card : ℝ) ≤
      TrackD.famMass (wideSurvivingTargets D A i) (wideTargetAssigned S D i) := by
    linarith [htgt_mass_eq, hsub_o]
  constructor
  · exact hN_exp_le.trans (hsrc_half.trans hsrc_surv_ge)
  · exact hN_exp_le.trans (htgt_half.trans htgt_surv_ge)

/-- Equal-dimensional flat count and individual assigned-weight bounds,
with the paper's e=B^j and literal surviving masses. -/
def WideFlatBounds (S : LimitingSeparatedProfile regime)
    (D : TrackA.SeparatedDepthData regime j) (A : PositiveSourcePlateau S j)
    (W : WideSourceCarriers S A) (θ : ℝ) (i : ℕ) : Prop :=
  (((W.survivingSources i).filter TrackD.IsFlat).card : ℝ) ≤
      regime.B i ^ (j : ℝ) * Real.exp (θ * Real.log (regime.B i)) ∧
  (((wideSurvivingTargets D A i).filter TrackD.IsFlat).card : ℝ) ≤
      regime.B i ^ (j : ℝ) * Real.exp (θ * Real.log (regime.B i)) ∧
  (∀ X ∈ W.survivingSources i, TrackD.IsFlat X →
    ((W.sourceAssigned i X).card : ℝ) ≤
      TrackD.famMass (W.survivingSources i) (W.sourceAssigned i) *
        (regime.B i ^ (j : ℝ))⁻¹ * Real.exp (θ * Real.log (regime.B i))) ∧
  (∀ Y ∈ wideSurvivingTargets D A i, TrackD.IsFlat Y →
    ((wideTargetAssigned S D i Y).card : ℝ) ≤
      TrackD.famMass (wideSurvivingTargets D A i) (wideTargetAssigned S D i) *
        (regime.B i ^ (j : ℝ))⁻¹ * Real.exp (θ * Real.log (regime.B i)))

lemma card_filter_fin_val_lt {d j : ℕ} (hj : j ≤ d) :
    (Finset.univ.filter (fun t : Fin d => t.val < j)).card = j := by
  have hbij : Finset.univ.filter (fun t : Fin d => t.val < j) =
      (Finset.range j).attach.image (fun ⟨x, hx⟩ => ⟨x, (Finset.mem_range.mp hx).trans_le hj⟩) := by
    ext ⟨t, ht⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_attach,
      Subtype.exists, true_and, Finset.mem_range]
    constructor
    · intro h
      exact ⟨t, h, rfl⟩
    · rintro ⟨x, hx, hEq⟩
      injection hEq with hEq'
      omega
  rw [hbij, Finset.card_image_of_injective]
  · rw [Finset.card_attach, Finset.card_range]
  · intro ⟨x, hx⟩ ⟨y, hy⟩ h
    injection h with h'
    exact Subtype.ext h'

theorem balanced_cut_product_aux {d j : ℕ} {regime : Regime d}
    (D : TrackA.SeparatedDepthData regime j) (i : ℕ) :
    (∏ t : Fin d, D.cutDegree i t) = regime.N i := by
  simp only [TrackA.SeparatedDepthData.cutDegree]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hd : (d : ℝ) ≠ 0 := by
    exact_mod_cast (show d ≠ 0 by have := regime.dimension_ge_three; omega)
  have hBN : regime.B i ^ d = regime.N i := by
    rw [Regime.B, ← Real.rpow_natCast, ← Real.rpow_mul (regime.N_pos i).le,
      one_div_mul_cancel hd, Real.rpow_one]
  rw [← Real.exp_sum, ← Finset.sum_mul, D.b_sum, zero_mul, Real.exp_zero, mul_one]
  exact hBN

theorem degreeBudget_mul_tailBudget_aux {d j : ℕ} {regime : Regime d}
    (D : TrackA.SeparatedDepthData regime j) (i : ℕ) :
    D.degreeBudget i * D.tailBudget i = regime.N i := by
  have h := Finset.prod_filter_mul_prod_filter_not Finset.univ
    (fun t : Fin d => t.val < j) (D.cutDegree i)
  have heq : D.degreeBudget i * D.tailBudget i = ∏ t : Fin d, D.cutDegree i t := by
    simpa only [TrackA.SeparatedDepthData.degreeBudget,
      TrackA.SeparatedDepthData.tailBudget, not_lt] using h
  exact heq.trans (balanced_cut_product_aux D i)

theorem degreeBudget_eq_prod_exp {d j : ℕ} {regime : Regime d}
    (D : TrackA.SeparatedDepthData regime j) (i : ℕ) :
    D.degreeBudget i = regime.B i ^ j * Real.exp ((∑ t ∈ Finset.univ.filter (fun t : Fin d => t.val < j), D.b t) * D.s i) := by
  dsimp [TrackA.SeparatedDepthData.degreeBudget, TrackA.SeparatedDepthData.cutDegree]
  rw [Finset.prod_mul_distrib, Finset.prod_const, card_filter_fin_val_lt D.j_lt.le,
    ← Real.exp_sum, ← Finset.sum_mul]

set_option maxHeartbeats 800000 in
theorem wide_equal_flat_budgets (S : LimitingSeparatedProfile regime)
    (D : TrackA.SeparatedDepthData regime j) (T : WideTargetProfile S D)
    (A : PositiveSourcePlateau S j) (W : WideSourceCarriers S A)
    (heq : A.r.val = j) :
    ∀ θ : ℝ, 0 < θ → ∀ᶠ i in atTop, WideFlatBounds S D A W θ i := by
  intro θ hθ
  have F := wide_finite_assignment_facts S D T A W
  have htheta2 : 0 < θ / 2 := by linarith
  have hsurv_mass := wide_surviving_mass_lower S D T A W (θ / 2) htheta2
  have hW_budget1 := W.budgets.1 1 (by norm_num : (0 : ℝ) < 1)
  have hT_budget1 := T.budgets.1 1 (by norm_num : (0 : ℝ) < 1)
  have hW_budget2 := W.budgets.2 1 (by norm_num : (0 : ℝ) < 1)
  have hT_budget2 := T.budgets.2 1 (by norm_num : (0 : ℝ) < 1)
  let Bsum := ∑ t ∈ Finset.univ.filter (fun t : Fin d => t.val < j), S.b t
  have hBsum_nonpos : Bsum ≤ 0 := by
    dsimp [Bsum]
    apply Finset.sum_nonpos
    intro t ht
    have hlt : t.val < A.r.val := by
      have := (Finset.mem_filter.mp ht).2
      omega
    exact A.prefix_nonpos t hlt
  let C_b : ℝ := max (1 - Bsum) 1
  have hCb_pos : 0 < C_b := by
    dsimp [C_b]
    linarith [le_max_right (1 - Bsum) 1]
  have hCb_ge1 : 1 ≤ C_b := le_max_right _ _
  have hCb_ge_sub : 1 - Bsum ≤ C_b := le_max_left _ _
  let ε_w : ℝ := (θ / 2) / C_b
  have hεw_pos : 0 < ε_w := div_pos htheta2 hCb_pos
  have hW_s_small := W.data.s_small.def hεw_pos
  have hD_s_small := D.s_small.def hεw_pos
  have hB_ge_one : ∀ᶠ i in atTop, 1 ≤ regime.B i :=
    regime.B_tendsto.eventually_ge_atTop 1
  filter_upwards [hsurv_mass, hW_budget1, hT_budget1, hW_budget2, hT_budget2,
    hW_s_small, hD_s_small, hB_ge_one] with i
    hsurv hWb1 hTb1 hWb2 hTb2 hWs hDs hB1
  have hlogB_nonneg : 0 ≤ Real.log (regime.B i) := Real.log_nonneg hB1
  have hnorm_logB : ‖Real.log (regime.B i)‖ = Real.log (regime.B i) :=
    Real.norm_of_nonneg hlogB_nonneg
  rw [hnorm_logB] at hWs hDs
  have hWs_le : W.data.s i ≤ ε_w * Real.log (regime.B i) := (le_abs_self _).trans hWs
  have hDs_le : D.s i ≤ ε_w * Real.log (regime.B i) := (le_abs_self _).trans hDs
  have hWs_nonneg : 0 ≤ W.data.s i := by
    rw [W.s_eq]
    exact (S.sequence.width_pos i).1.le
  have hDs_nonneg : 0 ≤ D.s i := by
    rw [T.s_eq]
    exact (S.sequence.width_pos i).2.le
  have hWs_bound : (1 - Bsum) * W.data.s i ≤ (θ / 2) * Real.log (regime.B i) := by
    calc (1 - Bsum) * W.data.s i
      _ ≤ C_b * W.data.s i := mul_le_mul_of_nonneg_right hCb_ge_sub hWs_nonneg
      _ ≤ C_b * (ε_w * Real.log (regime.B i)) := mul_le_mul_of_nonneg_left hWs_le hCb_pos.le
      _ = (θ / 2) * Real.log (regime.B i) := by
        dsimp [ε_w]
        rw [← mul_assoc, mul_div_cancel₀ _ hCb_pos.ne']
  have hDs_bound : (1 - Bsum) * D.s i ≤ (θ / 2) * Real.log (regime.B i) := by
    calc (1 - Bsum) * D.s i
      _ ≤ C_b * D.s i := mul_le_mul_of_nonneg_right hCb_ge_sub hDs_nonneg
      _ ≤ C_b * (ε_w * Real.log (regime.B i)) := mul_le_mul_of_nonneg_left hDs_le hCb_pos.le
      _ = (θ / 2) * Real.log (regime.B i) := by
        dsimp [ε_w]
        rw [← mul_assoc, mul_div_cancel₀ _ hCb_pos.ne']
  have hWs_theta : W.data.s i ≤ θ * Real.log (regime.B i) := by
    calc W.data.s i
      _ = 1 * W.data.s i := by ring
      _ ≤ C_b * W.data.s i := mul_le_mul_of_nonneg_right hCb_ge1 hWs_nonneg
      _ ≤ (θ / 2) * Real.log (regime.B i) := by
        calc C_b * W.data.s i
          _ ≤ C_b * (ε_w * Real.log (regime.B i)) := mul_le_mul_of_nonneg_left hWs_le hCb_pos.le
          _ = (θ / 2) * Real.log (regime.B i) := by
            dsimp [ε_w]
            rw [← mul_assoc, mul_div_cancel₀ _ hCb_pos.ne']
      _ ≤ θ * Real.log (regime.B i) := by
        have : θ / 2 ≤ θ := by linarith
        exact mul_le_mul_of_nonneg_right this hlogB_nonneg
  have hDs_theta : D.s i ≤ θ * Real.log (regime.B i) := by
    calc D.s i
      _ = 1 * D.s i := by ring
      _ ≤ C_b * D.s i := mul_le_mul_of_nonneg_right hCb_ge1 hDs_nonneg
      _ ≤ (θ / 2) * Real.log (regime.B i) := by
        calc C_b * D.s i
          _ ≤ C_b * (ε_w * Real.log (regime.B i)) := mul_le_mul_of_nonneg_left hDs_le hCb_pos.le
          _ = (θ / 2) * Real.log (regime.B i) := by
            dsimp [ε_w]
            rw [← mul_assoc, mul_div_cancel₀ _ hCb_pos.ne']
      _ ≤ θ * Real.log (regime.B i) := by
        have : θ / 2 ≤ θ := by linarith
        exact mul_le_mul_of_nonneg_right this hlogB_nonneg
  have hB_pow : regime.B i ^ j = regime.B i ^ (j : ℝ) :=
    (Real.rpow_natCast (regime.B i) j).symm
  have hdeg_eq_D := degreeBudget_eq_prod_exp D i
  have hb_eq_D : (∑ t ∈ Finset.univ.filter (fun t : Fin d => t.val < j), D.b t) = Bsum := by
    apply Finset.sum_congr rfl
    intro t _
    exact congr_fun T.b_eq t
  rw [hb_eq_D] at hdeg_eq_D
  have hmul_nonpos_D : Bsum * D.s i ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hBsum_nonpos hDs_nonneg
  have hexp_le1_D : Real.exp (Bsum * D.s i) ≤ 1 := by
    have := Real.exp_le_exp.mpr hmul_nonpos_D
    rwa [Real.exp_zero] at this
  have hdeg_le_D : D.degreeBudget i ≤ regime.B i ^ (j : ℝ) := by
    rw [hdeg_eq_D]
    have hB_nonneg : 0 ≤ regime.B i ^ j := by positivity
    calc regime.B i ^ j * Real.exp (Bsum * D.s i)
      _ ≤ regime.B i ^ j * 1 := mul_le_mul_of_nonneg_left hexp_le1_D hB_nonneg
      _ = regime.B i ^ j := mul_one _
      _ = regime.B i ^ (j : ℝ) := hB_pow
  have heq_rhs_W : regime.B i ^ A.r.val * Real.exp ((∑ t ∈ Finset.univ.filter (fun t : Fin d => t.val < A.r.val), W.data.b t) * W.data.s i) =
      regime.B i ^ j * Real.exp (Bsum * W.data.s i) := by
    have hset : (Finset.univ.filter (fun t : Fin d => t.val < A.r.val) : Finset (Fin d)) =
        Finset.univ.filter (fun t : Fin d => t.val < j) := by rw [heq]
    have hb_eq_W : (∑ t ∈ Finset.univ.filter (fun t : Fin d => t.val < A.r.val), W.data.b t) = Bsum := by
      calc ∑ t ∈ Finset.univ.filter (fun t : Fin d => t.val < A.r.val), W.data.b t
        _ = ∑ t ∈ Finset.univ.filter (fun t : Fin d => t.val < j), W.data.b t := by rw [hset]
        _ = ∑ t ∈ Finset.univ.filter (fun t : Fin d => t.val < j), S.b t := by
            apply Finset.sum_congr rfl
            intro t _
            exact congr_fun W.b_eq t
        _ = Bsum := rfl
    have hB : regime.B i ^ A.r.val = regime.B i ^ j := by rw [heq]
    rw [hb_eq_W, hB]
  have hdeg_eq_W := (degreeBudget_eq_prod_exp W.data i).trans heq_rhs_W
  have hmul_nonpos_W : Bsum * W.data.s i ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hBsum_nonpos hWs_nonneg
  have hexp_le1_W : Real.exp (Bsum * W.data.s i) ≤ 1 := by
    have := Real.exp_le_exp.mpr hmul_nonpos_W
    rwa [Real.exp_zero] at this
  have hdeg_le_W : W.data.degreeBudget i ≤ regime.B i ^ (j : ℝ) := by
    rw [hdeg_eq_W]
    have hB_nonneg : 0 ≤ regime.B i ^ j := by positivity
    calc regime.B i ^ j * Real.exp (Bsum * W.data.s i)
      _ ≤ regime.B i ^ j * 1 := mul_le_mul_of_nonneg_left hexp_le1_W hB_nonneg
      _ = regime.B i ^ j := mul_one _
      _ = regime.B i ^ (j : ℝ) := hB_pow
  have hpos_deg_D : 0 < D.degreeBudget i := by
    dsimp [TrackA.SeparatedDepthData.degreeBudget, TrackA.SeparatedDepthData.cutDegree]
    exact Finset.prod_pos fun t _ => mul_pos (regime.B_pos i) (Real.exp_pos _)
  have hpos_deg_W : 0 < W.data.degreeBudget i := by
    dsimp [TrackA.SeparatedDepthData.degreeBudget, TrackA.SeparatedDepthData.cutDegree]
    exact Finset.prod_pos fun t _ => mul_pos (regime.B_pos i) (Real.exp_pos _)
  have htail_D : D.tailBudget i = regime.N i / D.degreeBudget i := by
    have hmul := degreeBudget_mul_tailBudget_aux D i
    rw [← hmul, mul_div_cancel_left₀ _ hpos_deg_D.ne']
  have htail_W : W.data.tailBudget i = regime.N i / W.data.degreeBudget i := by
    have hmul := degreeBudget_mul_tailBudget_aux W.data i
    rw [← hmul, mul_div_cancel_left₀ _ hpos_deg_W.ne']
  have hdiv_helper (a b c : ℝ) : a / (b * c) = a * b⁻¹ * c⁻¹ := by
    rw [div_eq_mul_inv, mul_inv, mul_assoc]
  have htail_exp_D : D.tailBudget i =
      regime.N i * (regime.B i ^ (j : ℝ))⁻¹ * Real.exp (- Bsum * D.s i) := by
    rw [htail_D, hdeg_eq_D, hB_pow, hdiv_helper, ← Real.exp_neg, neg_mul_eq_neg_mul]
  have htail_exp_W : W.data.tailBudget i =
      regime.N i * (regime.B i ^ (j : ℝ))⁻¹ * Real.exp (- Bsum * W.data.s i) := by
    rw [htail_W, hdeg_eq_W, hB_pow, hdiv_helper, ← Real.exp_neg, neg_mul_eq_neg_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hflat1 : (((W.survivingSources i).filter TrackD.IsFlat).card : ℝ) ≤
        (AffineFamily.degree (W.data.carriers i) : ℝ) := by
      calc (((W.survivingSources i).filter TrackD.IsFlat).card : ℝ)
        = ∑ X ∈ (W.survivingSources i).filter TrackD.IsFlat, (1 : ℝ) := by simp
        _ = ∑ X ∈ (W.survivingSources i).filter TrackD.IsFlat, (X.degree : ℝ) := by
            apply Finset.sum_congr rfl
            intro X hX
            have hX_filter := Finset.mem_filter.mp hX
            have hX_surv := hX_filter.1
            have hX_flat := hX_filter.2
            have hX_mem : X ∈ W.data.carriers i := (Finset.mem_filter.mp hX_surv).1
            have hX_irred := (W.data.carrier_pure i X hX_mem).1
            have hdeg := Request.affine_flat_degree_one X hX_irred hX_flat
            rw [hdeg]
            norm_num
        _ ≤ ∑ X ∈ W.data.carriers i, (X.degree : ℝ) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro X hX
              have hX_surv := (Finset.mem_filter.mp hX).1
              exact (Finset.mem_filter.mp hX_surv).1
            · intro X hX _
              have hX_irred := (W.data.carrier_pure i X hX).1
              have hle := AffineVariety.one_le_degree X hX_irred.ne_top
              exact_mod_cast (by linarith : 0 ≤ X.degree)
        _ = (AffineFamily.degree (W.data.carriers i) : ℝ) := by
            simp only [AffineFamily.degree, Rat.cast_sum]
    have hdeg_b1 := hWb1 ()
    rw [one_mul] at hdeg_b1
    have hstep1 := hflat1.trans hdeg_b1
    have hstep2 : W.data.degreeBudget i * Real.exp (W.data.s i) ≤
        regime.B i ^ (j : ℝ) * Real.exp (θ * Real.log (regime.B i)) := by
      have hexp_le : Real.exp (W.data.s i) ≤ Real.exp (θ * Real.log (regime.B i)) :=
        Real.exp_le_exp.mpr hWs_theta
      exact mul_le_mul hdeg_le_W hexp_le (Real.exp_pos _).le (Real.rpow_nonneg (regime.B_pos i).le _)
    exact hstep1.trans hstep2
  · have hflat2 : (((wideSurvivingTargets D A i).filter TrackD.IsFlat).card : ℝ) ≤
        (AffineFamily.degree (D.carriers i) : ℝ) := by
      calc (((wideSurvivingTargets D A i).filter TrackD.IsFlat).card : ℝ)
        = ∑ Y ∈ (wideSurvivingTargets D A i).filter TrackD.IsFlat, (1 : ℝ) := by simp
        _ = ∑ Y ∈ (wideSurvivingTargets D A i).filter TrackD.IsFlat, (Y.degree : ℝ) := by
            apply Finset.sum_congr rfl
            intro Y hY
            have hY_filter := Finset.mem_filter.mp hY
            have hY_surv := hY_filter.1
            have hY_flat := hY_filter.2
            have hY_mem : Y ∈ D.carriers i := F.targets_subset i hY_surv
            have hY_irred := (D.carrier_pure i Y hY_mem).1
            have hdeg := Request.affine_flat_degree_one Y hY_irred hY_flat
            rw [hdeg]
            norm_num
        _ ≤ ∑ Y ∈ D.carriers i, (Y.degree : ℝ) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro Y hY
              have hY_surv := (Finset.mem_filter.mp hY).1
              exact F.targets_subset i hY_surv
            · intro Y hY _
              have hY_irred := (D.carrier_pure i Y hY).1
              have hle := AffineVariety.one_le_degree Y hY_irred.ne_top
              exact_mod_cast (by linarith : 0 ≤ Y.degree)
        _ = (AffineFamily.degree (D.carriers i) : ℝ) := by
            simp only [AffineFamily.degree, Rat.cast_sum]
    have hdeg_b2 := hTb1 ()
    rw [one_mul] at hdeg_b2
    have hstep1 := hflat2.trans hdeg_b2
    have hstep2 : D.degreeBudget i * Real.exp (D.s i) ≤
        regime.B i ^ (j : ℝ) * Real.exp (θ * Real.log (regime.B i)) := by
      have hexp_le : Real.exp (D.s i) ≤ Real.exp (θ * Real.log (regime.B i)) :=
        Real.exp_le_exp.mpr hDs_theta
      exact mul_le_mul hdeg_le_D hexp_le (Real.exp_pos _).le (Real.rpow_nonneg (regime.B_pos i).le _)
    exact hstep1.trans hstep2
  · intro X hX hflat
    have hX_mem : X ∈ W.data.carriers i := (Finset.mem_filter.mp hX).1
    have hsub : ({X} : AffineFamily.Family d) ⊆ W.data.carriers i :=
      Finset.singleton_subset_iff.mpr hX_mem
    have hbudget := hWb2 ⟨{X}, hsub⟩
    dsimp at hbudget
    have hsubmass_eq : W.data.submass i {X} = ((W.sourceAssigned i X).card : ℝ) := by
      dsimp [TrackA.SeparatedDepthData.submass]
      rw [Finset.sum_singleton]
      dsimp [TrackA.SeparatedDepthData.mass, WideSourceCarriers.sourceAssigned]
      rw [W.targets_eq i]
      have hfeq : ((S.sequence.source i).pts.image TrackD.toC).filter
          (fun q => W.data.owner i q = X) =
        ((S.sequence.source i).pts.filter
          (fun p => W.data.owner i (TrackD.toC p) = X)).image TrackD.toC := by
        ext q; simp only [Finset.mem_filter, Finset.mem_image]
        constructor
        · rintro ⟨⟨p, hp, rfl⟩, ho⟩; exact ⟨p, ⟨hp, ho⟩, rfl⟩
        · rintro ⟨p, ⟨hp, ho⟩, rfl⟩; exact ⟨⟨p, hp, rfl⟩, ho⟩
      rw [hfeq, Finset.card_image_of_injective _ profile_toC_injective]
    have hdeg_sing : (AffineFamily.degree {X} : ℝ) = 1 := by
      dsimp [AffineFamily.degree]
      rw [Finset.sum_singleton]
      have hX_irred := (W.data.carrier_pure i X hX_mem).1
      have hdeg := Request.affine_flat_degree_one X hX_irred hflat
      rw [hdeg]
      norm_num
    rw [hsubmass_eq, hdeg_sing, one_mul, one_mul] at hbudget
    rw [htail_exp_W] at hbudget
    have hexp_comb : Real.exp (- Bsum * W.data.s i) * Real.exp (W.data.s i) =
        Real.exp ((1 - Bsum) * W.data.s i) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have htail_re : regime.N i * (regime.B i ^ (j : ℝ))⁻¹ * Real.exp (- Bsum * W.data.s i) * Real.exp (W.data.s i) =
        regime.N i * (regime.B i ^ (j : ℝ))⁻¹ * Real.exp ((1 - Bsum) * W.data.s i) := by
      rw [mul_assoc, hexp_comb]
    rw [htail_re] at hbudget
    have hN_le : regime.N i ≤ TrackD.famMass (W.survivingSources i) (W.sourceAssigned i) *
        Real.exp ((θ / 2) * Real.log (regime.B i)) := by
      have hpos : 0 < Real.exp ((θ / 2) * Real.log (regime.B i)) := Real.exp_pos _
      have hmul := mul_le_mul_of_nonneg_right hsurv.1 hpos.le
      have heq_cancel : regime.N i * Real.exp (- (θ / 2) * Real.log (regime.B i)) *
          Real.exp ((θ / 2) * Real.log (regime.B i)) = regime.N i := by
        rw [mul_assoc, ← Real.exp_add]
        have : - (θ / 2) * Real.log (regime.B i) + (θ / 2) * Real.log (regime.B i) = 0 := by ring
        rw [this, Real.exp_zero, mul_one]
      rwa [heq_cancel] at hmul
    have hconj3_calc : regime.N i * (regime.B i ^ (j : ℝ))⁻¹ * Real.exp ((1 - Bsum) * W.data.s i) ≤
        TrackD.famMass (W.survivingSources i) (W.sourceAssigned i) * (regime.B i ^ (j : ℝ))⁻¹ *
          Real.exp (θ * Real.log (regime.B i)) := by
      have hB_inv_nonneg : 0 ≤ (regime.B i ^ (j : ℝ))⁻¹ := inv_nonneg.mpr (by positivity)
      have hexp_s_nonneg : 0 ≤ Real.exp ((1 - Bsum) * W.data.s i) := by positivity
      have h1 : regime.N i * (regime.B i ^ (j : ℝ))⁻¹ * Real.exp ((1 - Bsum) * W.data.s i) ≤
          (TrackD.famMass (W.survivingSources i) (W.sourceAssigned i) * Real.exp ((θ / 2) * Real.log (regime.B i))) *
          (regime.B i ^ (j : ℝ))⁻¹ * Real.exp ((1 - Bsum) * W.data.s i) := by
        apply mul_le_mul_of_nonneg_right _ hexp_s_nonneg
        apply mul_le_mul_of_nonneg_right hN_le hB_inv_nonneg
      have h2 : (TrackD.famMass (W.survivingSources i) (W.sourceAssigned i) * Real.exp ((θ / 2) * Real.log (regime.B i))) *
          (regime.B i ^ (j : ℝ))⁻¹ * Real.exp ((1 - Bsum) * W.data.s i) =
          TrackD.famMass (W.survivingSources i) (W.sourceAssigned i) * (regime.B i ^ (j : ℝ))⁻¹ *
          (Real.exp ((θ / 2) * Real.log (regime.B i)) * Real.exp ((1 - Bsum) * W.data.s i)) := by ring
      rw [h2] at h1
      have h3 : Real.exp ((θ / 2) * Real.log (regime.B i)) * Real.exp ((1 - Bsum) * W.data.s i) ≤
          Real.exp (θ * Real.log (regime.B i)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        linarith
      have hmass_nonneg : 0 ≤ TrackD.famMass (W.survivingSources i) (W.sourceAssigned i) := by
        dsimp [TrackD.famMass]
        exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
      have hpref_nonneg : 0 ≤ TrackD.famMass (W.survivingSources i) (W.sourceAssigned i) * (regime.B i ^ (j : ℝ))⁻¹ :=
        mul_nonneg hmass_nonneg hB_inv_nonneg
      exact h1.trans (mul_le_mul_of_nonneg_left h3 hpref_nonneg)
    exact hbudget.trans hconj3_calc
  · intro Y hY hflat
    have hY_mem : Y ∈ D.carriers i := F.targets_subset i hY
    have hsub : ({Y} : AffineFamily.Family d) ⊆ D.carriers i :=
      Finset.singleton_subset_iff.mpr hY_mem
    have hbudget := hTb2 ⟨{Y}, hsub⟩
    dsimp at hbudget
    have hsubmass_eq : D.submass i {Y} = ((wideTargetAssigned S D i Y).card : ℝ) := by
      dsimp [TrackA.SeparatedDepthData.submass]
      rw [Finset.sum_singleton]
      dsimp [TrackA.SeparatedDepthData.mass, wideTargetAssigned]
      rw [T.targets_eq i]
      have hfeq : ((S.sequence.target i).pts.image TrackD.toC).filter
          (fun q => D.owner i q = Y) =
        ((S.sequence.target i).pts.filter
          (fun p => D.owner i (TrackD.toC p) = Y)).image TrackD.toC := by
        ext q; simp only [Finset.mem_filter, Finset.mem_image]
        constructor
        · rintro ⟨⟨p, hp, rfl⟩, ho⟩; exact ⟨p, ⟨hp, ho⟩, rfl⟩
        · rintro ⟨p, ⟨hp, ho⟩, rfl⟩; exact ⟨⟨p, hp, rfl⟩, ho⟩
      rw [hfeq, Finset.card_image_of_injective _ profile_toC_injective]
    have hdeg_sing : (AffineFamily.degree {Y} : ℝ) = 1 := by
      dsimp [AffineFamily.degree]
      rw [Finset.sum_singleton]
      have hY_irred := (D.carrier_pure i Y hY_mem).1
      have hdeg := Request.affine_flat_degree_one Y hY_irred hflat
      rw [hdeg]
      norm_num
    rw [hsubmass_eq, hdeg_sing, one_mul, one_mul] at hbudget
    rw [htail_exp_D] at hbudget
    have hexp_comb : Real.exp (- Bsum * D.s i) * Real.exp (D.s i) =
        Real.exp ((1 - Bsum) * D.s i) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have htail_re : regime.N i * (regime.B i ^ (j : ℝ))⁻¹ * Real.exp (- Bsum * D.s i) * Real.exp (D.s i) =
        regime.N i * (regime.B i ^ (j : ℝ))⁻¹ * Real.exp ((1 - Bsum) * D.s i) := by
      rw [mul_assoc, hexp_comb]
    rw [htail_re] at hbudget
    have hN_le : regime.N i ≤ TrackD.famMass (wideSurvivingTargets D A i) (wideTargetAssigned S D i) *
        Real.exp ((θ / 2) * Real.log (regime.B i)) := by
      have hpos : 0 < Real.exp ((θ / 2) * Real.log (regime.B i)) := Real.exp_pos _
      have hmul := mul_le_mul_of_nonneg_right hsurv.2 hpos.le
      have heq_cancel : regime.N i * Real.exp (- (θ / 2) * Real.log (regime.B i)) *
          Real.exp ((θ / 2) * Real.log (regime.B i)) = regime.N i := by
        rw [mul_assoc, ← Real.exp_add]
        have : - (θ / 2) * Real.log (regime.B i) + (θ / 2) * Real.log (regime.B i) = 0 := by ring
        rw [this, Real.exp_zero, mul_one]
      rwa [heq_cancel] at hmul
    have hconj4_calc : regime.N i * (regime.B i ^ (j : ℝ))⁻¹ * Real.exp ((1 - Bsum) * D.s i) ≤
        TrackD.famMass (wideSurvivingTargets D A i) (wideTargetAssigned S D i) * (regime.B i ^ (j : ℝ))⁻¹ *
          Real.exp (θ * Real.log (regime.B i)) := by
      have hB_inv_nonneg : 0 ≤ (regime.B i ^ (j : ℝ))⁻¹ := inv_nonneg.mpr (by positivity)
      have hexp_s_nonneg : 0 ≤ Real.exp ((1 - Bsum) * D.s i) := by positivity
      have h1 : regime.N i * (regime.B i ^ (j : ℝ))⁻¹ * Real.exp ((1 - Bsum) * D.s i) ≤
          (TrackD.famMass (wideSurvivingTargets D A i) (wideTargetAssigned S D i) * Real.exp ((θ / 2) * Real.log (regime.B i))) *
          (regime.B i ^ (j : ℝ))⁻¹ * Real.exp ((1 - Bsum) * D.s i) := by
        apply mul_le_mul_of_nonneg_right _ hexp_s_nonneg
        apply mul_le_mul_of_nonneg_right hN_le hB_inv_nonneg
      have h2 : (TrackD.famMass (wideSurvivingTargets D A i) (wideTargetAssigned S D i) * Real.exp ((θ / 2) * Real.log (regime.B i))) *
          (regime.B i ^ (j : ℝ))⁻¹ * Real.exp ((1 - Bsum) * D.s i) =
          TrackD.famMass (wideSurvivingTargets D A i) (wideTargetAssigned S D i) * (regime.B i ^ (j : ℝ))⁻¹ *
          (Real.exp ((θ / 2) * Real.log (regime.B i)) * Real.exp ((1 - Bsum) * D.s i)) := by ring
      rw [h2] at h1
      have h3 : Real.exp ((θ / 2) * Real.log (regime.B i)) * Real.exp ((1 - Bsum) * D.s i) ≤
          Real.exp (θ * Real.log (regime.B i)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        linarith
      have hmass_nonneg : 0 ≤ TrackD.famMass (wideSurvivingTargets D A i) (wideTargetAssigned S D i) := by
        dsimp [TrackD.famMass]
        exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
      have hpref_nonneg : 0 ≤ TrackD.famMass (wideSurvivingTargets D A i) (wideTargetAssigned S D i) * (regime.B i ^ (j : ℝ))⁻¹ :=
        mul_nonneg hmass_nonneg hB_inv_nonneg
      exact h1.trans (mul_le_mul_of_nonneg_left h3 hpref_nonneg)
    exact hbudget.trans hconj4_calc

/-- `G5.wide.rounding`: leave exponential room between B^(1/4) and the
natural floor of sqrt B, uniformly before choosing lists. -/
theorem wide_root_cap (regime : Regime d) :
    ∀ᶠ i in atTop, Real.exp ((1 / 4 : ℝ) * Real.log (regime.B i)) ≤
      (⌊regime.B i ^ (1 / 2 : ℝ)⌋₊ : ℝ) := by
  have hlog : Tendsto (fun i => Real.log (regime.B i)) atTop atTop :=
    Real.tendsto_log_atTop.comp regime.B_tendsto
  filter_upwards [hlog.eventually_ge_atTop (4 * Real.log 2)] with i hi
  have hBpos : 0 < regime.B i := regime.B_pos i
  let x := (1 / 4 : ℝ) * Real.log (regime.B i)
  let y := Real.exp x
  have hx : Real.log 2 ≤ x := by
    dsimp [x]
    linarith
  have hy2 : (2 : ℝ) ≤ y := by
    have h := Real.exp_le_exp.mpr hx
    rwa [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
  have hy_sq : y + 1 ≤ y ^ 2 := by
    nlinarith
  have hy2_eq : y ^ 2 = regime.B i ^ (1 / 2 : ℝ) := by
    dsimp [y, x]
    rw [sq, ← Real.exp_add]
    have h2x : (1 / 4 : ℝ) * Real.log (regime.B i) + (1 / 4 : ℝ) * Real.log (regime.B i) =
        Real.log (regime.B i) * (1 / 2 : ℝ) := by ring
    rw [h2x, ← Real.rpow_def_of_pos hBpos]
  have hfloor := Nat.lt_floor_add_one (regime.B i ^ (1 / 2 : ℝ))
  have hlt : y + 1 < (⌊regime.B i ^ (1 / 2 : ℝ)⌋₊ : ℝ) + 1 := by
    calc
      y + 1 ≤ y ^ 2 := hy_sq
      _ = regime.B i ^ (1 / 2 : ℝ) := hy2_eq
      _ < (⌊regime.B i ^ (1 / 2 : ℝ)⌋₊ : ℝ) + 1 := hfloor
  linarith

/-- `G5.wide.root-coordinates`: reindex the actual principal-open polynomial
and restrict the moving-root set from D's convention to A's convention. -/
theorem generic_moving_root_bound_of_pair (X Y : AffineVariety d)
    (J : AffineFamily.Family d) (q : ℕ)
    (h : TrackD.ForGeneralPair X Y (fun x y =>
      y - x ∉ X.tangentSpace x ∧ (TrackD.movingRoots J x y).Finite ∧
      ((TrackD.movingRoots J x y).ncard : ℝ) ≤ (q : ℝ))) :
    TrackA.GenericMovingRootBound X Y J q := by
  classical
  rcases h with ⟨g, ⟨x₀, hx₀, y₀, hy₀, hg₀⟩, hpair⟩
  let H : Poly (d + d) := MvPolynomial.rename finSumFinEquiv g
  have hcoords (x y : Point d) : Fin.append x y ∘ finSumFinEquiv = TrackD.pairPt x y := by
    funext i
    cases i with
    | inl i => simp [TrackD.pairPt]
    | inr i => exact Fin.append_right x y i
  have heval (x y : Point d) :
      MvPolynomial.eval (Fin.append x y) H = MvPolynomial.eval (TrackD.pairPt x y) g := by
    change MvPolynomial.eval (Fin.append x y) (MvPolynomial.rename finSumFinEquiv g) = _
    rw [MvPolynomial.eval_rename, hcoords]
  have hroots (x y : Point d) :
      TrackA.movingRoots x y J ⊆ TrackD.movingRoots J x y := by
    intro z hz
    rcases hz with ⟨hzJ, hzline, hzx, _⟩
    rw [AffineFamily.points_locus] at hzJ
    rcases Set.mem_iUnion.mp hzJ with ⟨Z, hzJ⟩
    rcases Set.mem_iUnion.mp hzJ with ⟨hZ, hzZ⟩
    refine ⟨⟨Z, hZ, hzZ⟩, hzx, ?_⟩
    rcases hzline with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [hc]
    abel
  refine ⟨H, ?_, ?_⟩
  · refine ⟨x₀, hx₀, y₀, hy₀, ?_⟩
    rw [heval]
    exact hg₀
  · intro x hx y hy hH
    have hg : MvPolynomial.eval (TrackD.pairPt x y) g ≠ 0 := by
      rw [← heval x y]
      exact hH
    have hgeom := hpair x hx y hy hg
    have hxy : x ≠ y := by
      intro hxy
      subst y
      apply hgeom.1
      simpa using (Submodule.zero_mem (X.tangentSpace x))
    have hfinite : (TrackA.movingRoots x y J).Finite :=
      hgeom.2.1.subset (hroots x y)
    have hncard := Set.ncard_le_ncard (hroots x y) hgeom.2.1
    have hncardReal : ((TrackA.movingRoots x y J).ncard : ℝ) ≤
        ((TrackD.movingRoots J x y).ncard : ℝ) := by
      exact_mod_cast hncard
    have hboundReal : ((TrackA.movingRoots x y J).ncard : ℝ) ≤ (q : ℝ) :=
      hncardReal.trans hgeom.2.2
    have hbound : (TrackA.movingRoots x y J).ncard ≤ q := by
      exact_mod_cast hboundReal
    exact ⟨hxy, hfinite, hbound⟩

/-- `G5.wide.flat-cap`: the contradiction regime eventually satisfies the
uniform proper real-flat bound at exponent 1/3 from the planar shortcut. -/
theorem wide_regime_flat_cap (regime : Regime d) :
    ∀ᶠ i in atTop, TrackD.RealFlatCap (regime.P i) (1 / 3 : ℝ) := by
  obtain ⟨ε₀, hε₀, N₀, hcap⟩ := Reduction.card_inter_proper_flat_le
    regime.dimension_ge_three regime.inductionHypothesis
  have hM_div_A : Tendsto (fun i => regime.M i / regime.A i) atTop (𝓝 0) :=
    regime.M_div_A_tendsto
  have hratio : ∀ᶠ i in atTop, regime.M i / regime.A i ≤ ε₀ :=
    hM_div_A.eventually (ge_mem_nhds hε₀)
  have hN : ∀ᶠ i in atTop, N₀ ≤ (regime.P i).card :=
    regime.card_tendsto.eventually_ge_atTop N₀
  filter_upwards [hratio, hN] with i hi_ratio hi_N
  intro F hF
  have hM_le : Mcount (regime.P i) ≤ ε₀ * Ascale d (regime.P i).card := by
    have hM_eq : Mcount (regime.P i) = regime.M i := by dsimp [Mcount, Regime.M]; ring
    have hA_eq : Ascale d (regime.P i).card = regime.A i := rfl
    rw [hM_eq, hA_eq]
    rw [← div_le_iff₀ (regime.A_pos i)]
    exact hi_ratio
  have h := hcap (regime.P i) hi_N hM_le F hF
  exact h

/-- A list certificate contains actual generic geometry and a weighted
component-pair loss, before any actual center is selected. -/
def WideListCertificate (S : LimitingSeparatedProfile regime)
    (D : TrackA.SeparatedDepthData regime j) (A : PositiveSourcePlateau S j)
    (W : WideSourceCarriers S A) (i : ℕ) (δ : ℝ)
    (L : AffineVariety d → AffineFamily.Family d) : Prop :=
  (∀ X ∈ W.survivingSources i, L X ⊆ wideSurvivingTargets D A i) ∧
  (∑ X ∈ W.survivingSources i, ∑ Y ∈ wideSurvivingTargets D A i \ L X,
    ((W.sourceAssigned i X).card : ℝ) * (wideTargetAssigned S D i Y).card) ≤
      δ * TrackD.famMass (W.survivingSources i) (W.sourceAssigned i) *
        TrackD.famMass (wideSurvivingTargets D A i) (wideTargetAssigned S D i) ∧
  ∀ X ∈ W.survivingSources i, ∀ Y ∈ L X,
    TrackA.GenericMovingRootBound X Y (L X) ⌊regime.B i ^ (1 / 2 : ℝ)⌋₊

lemma mass_eq_wideTargetAssigned_card (S : LimitingSeparatedProfile regime)
    (D : TrackA.SeparatedDepthData regime j) (T : WideTargetProfile S D)
    (i : ℕ) (Y : AffineVariety d) :
    D.mass i Y = (wideTargetAssigned S D i Y).card := by
  dsimp [TrackA.SeparatedDepthData.mass, wideTargetAssigned]
  rw [T.targets_eq i]
  have hfeq : ((S.sequence.target i).pts.image TrackD.toC).filter
      (fun q => D.owner i q = Y) =
    ((S.sequence.target i).pts.filter
      (fun p => D.owner i (TrackD.toC p) = Y)).image TrackD.toC := by
    ext q; simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨p, hp, rfl⟩, ho⟩; exact ⟨p, ⟨hp, ho⟩, rfl⟩
    · rintro ⟨p, ⟨hp, ho⟩, rfl⟩; exact ⟨⟨p, hp, rfl⟩, ho⟩
  rw [hfeq, Finset.card_image_of_injective _ profile_toC_injective]

lemma sum_mass_carriers_eq_targets_card (D : TrackA.SeparatedDepthData regime j) (i : ℕ) :
    ∑ Y ∈ D.carriers i, (D.mass i Y : ℝ) = ((D.targets i).card : ℝ) := by
  have hmaps : ∀ q ∈ D.targets i, D.owner i q ∈ D.carriers i :=
    fun q hq => D.owner_member i q hq
  have h := (Finset.card_eq_sum_card_fiberwise (s := D.targets i) (t := D.carriers i)
    (f := D.owner i) hmaps).symm
  dsimp [TrackA.SeparatedDepthData.mass]
  exact_mod_cast h

lemma centers_fiber_card_le_sourceAssigned_card (S : LimitingSeparatedProfile regime)
    (D : TrackA.SeparatedDepthData regime j) (T : WideTargetProfile S D)
    (A : PositiveSourcePlateau S j) (W : WideSourceCarriers S A)
    (i : ℕ) (X : AffineVariety d) :
    (((D.centers i \ W.ignoredSources i).filter (fun p => W.data.owner i p = X)).card : ℝ) ≤
      ((W.sourceAssigned i X).card : ℝ) := by
  have hsub : (D.centers i \ W.ignoredSources i).filter (fun p => W.data.owner i p = X) ⊆
      (D.centers i).filter (fun p => W.data.owner i p = X) := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hp'.1).1, hp'.2⟩
  have hcard_le := Finset.card_le_card hsub
  have heq : ((D.centers i).filter (fun p => W.data.owner i p = X)).card = (W.sourceAssigned i X).card := by
    rw [T.centers_eq i]
    have hfeq : ((S.sequence.source i).pts.image TrackD.toC).filter
        (fun p => W.data.owner i p = X) =
      ((S.sequence.source i).pts.filter
        (fun p => W.data.owner i (TrackD.toC p) = X)).image TrackD.toC := by
      ext q; simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨p, hp, rfl⟩, ho⟩; exact ⟨p, ⟨hp, ho⟩, rfl⟩
      · rintro ⟨p, ⟨hp, ho⟩, rfl⟩; exact ⟨⟨p, hp, rfl⟩, ho⟩
    rw [hfeq, Finset.card_image_of_injective _ profile_toC_injective]
    rfl
  exact_mod_cast hcard_le.trans heq.le

lemma carriers_filter_not_mem_L_eq {d : ℕ} (K T L_X : Finset (AffineVariety d))
    (hL : L_X ⊆ T) (hT : T ⊆ K) :
    K.filter (fun Y => Y ∉ L_X) = (K \ T) ∪ (T \ L_X) := by
  ext Y
  simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff]
  constructor
  · rintro ⟨hYK, hYnL⟩
    by_cases hYT : Y ∈ T
    · exact Or.inr ⟨hYT, hYnL⟩
    · exact Or.inl ⟨hYK, hYT⟩
  · rintro (⟨hYK, hYnT⟩ | ⟨hYT, hYnL⟩)
    · exact ⟨hYK, fun hYL => hYnT (hL hYL)⟩
    · exact ⟨hT hYT, hYnL⟩

lemma disjoint_sdiff_sdiff {d : ℕ} (K T L_X : Finset (AffineVariety d)) :
    Disjoint (K \ T) (T \ L_X) := by
  rw [Finset.disjoint_iff_ne]
  rintro a ha b hb rfl
  have ha' := (Finset.mem_sdiff.mp ha).2
  have hb' := (Finset.mem_sdiff.mp hb).1
  exact ha' hb'

lemma unign_loss_sum_le (S : LimitingSeparatedProfile regime)
    (D : TrackA.SeparatedDepthData regime j) (T : WideTargetProfile S D)
    (A : PositiveSourcePlateau S j) (W : WideSourceCarriers S A) (i : ℕ)
    (L : AffineVariety d → AffineFamily.Family d) :
    ∑ p ∈ (D.centers i \ W.ignoredSources i),
      ∑ Y ∈ wideSurvivingTargets D A i \ L (W.data.owner i p), (D.mass i Y : ℝ) ≤
    ∑ X ∈ W.survivingSources i,
      ∑ Y ∈ wideSurvivingTargets D A i \ L X,
        ((W.sourceAssigned i X).card : ℝ) * (wideTargetAssigned S D i Y).card := by
  have F := wide_finite_assignment_facts S D T A W
  have hmaps : ∀ p ∈ D.centers i \ W.ignoredSources i, W.data.owner i p ∈ W.survivingSources i := by
    intro p hp; exact (F.source_owner i p (Finset.mem_sdiff.mp hp).1 (Finset.mem_sdiff.mp hp).2).1
  calc ∑ p ∈ (D.centers i \ W.ignoredSources i),
        ∑ Y ∈ wideSurvivingTargets D A i \ L (W.data.owner i p), (D.mass i Y : ℝ)
    _ = ∑ X ∈ W.survivingSources i,
          ∑ p ∈ (D.centers i \ W.ignoredSources i).filter (fun p => W.data.owner i p = X),
            ∑ Y ∈ wideSurvivingTargets D A i \ L (W.data.owner i p), (D.mass i Y : ℝ) := by
        rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    _ = ∑ X ∈ W.survivingSources i,
          ∑ p ∈ (D.centers i \ W.ignoredSources i).filter (fun p => W.data.owner i p = X),
            ∑ Y ∈ wideSurvivingTargets D A i \ L X, (D.mass i Y : ℝ) := by
        apply Finset.sum_congr rfl
        intro X hX
        apply Finset.sum_congr rfl
        intro p hp
        have hpX : W.data.owner i p = X := (Finset.mem_filter.mp hp).2
        rw [hpX]
    _ = ∑ X ∈ W.survivingSources i,
          (((D.centers i \ W.ignoredSources i).filter (fun p => W.data.owner i p = X)).card : ℝ) *
            ∑ Y ∈ wideSurvivingTargets D A i \ L X, (D.mass i Y : ℝ) := by
        apply Finset.sum_congr rfl
        intro X hX
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ X ∈ W.survivingSources i,
          ((W.sourceAssigned i X).card : ℝ) *
            ∑ Y ∈ wideSurvivingTargets D A i \ L X, ((wideTargetAssigned S D i Y).card : ℝ) := by
        apply Finset.sum_le_sum
        intro X hX
        have hcard_le := centers_fiber_card_le_sourceAssigned_card S D T A W i X
        have hmass_eq (Y : AffineVariety d) : (D.mass i Y : ℝ) = ((wideTargetAssigned S D i Y).card : ℝ) :=
          congr_arg Nat.cast (mass_eq_wideTargetAssigned_card S D T i Y)
        have hsum_eq : (∑ Y ∈ wideSurvivingTargets D A i \ L X, (D.mass i Y : ℝ)) =
            ∑ Y ∈ wideSurvivingTargets D A i \ L X, ((wideTargetAssigned S D i Y).card : ℝ) := by
          apply Finset.sum_congr rfl
          intro Y hY
          exact hmass_eq Y
        rw [hsum_eq]
        have hmass_nonneg : 0 ≤ ∑ Y ∈ wideSurvivingTargets D A i \ L X, ((wideTargetAssigned S D i Y).card : ℝ) := by
          apply Finset.sum_nonneg
          intro _ _
          exact Nat.cast_nonneg _
        exact mul_le_mul_of_nonneg_right hcard_le hmass_nonneg
    _ = ∑ X ∈ W.survivingSources i,
          ∑ Y ∈ wideSurvivingTargets D A i \ L X,
            ((W.sourceAssigned i X).card : ℝ) * (wideTargetAssigned S D i Y).card := by
        apply Finset.sum_congr rfl
        intro X hX
        rw [Finset.mul_sum]

/-- `G5.wide.incidence-normalization`: fixed source/target omissions plus
component product loss control the actual persistent incidence normalization. -/
theorem wide_incidence_bound (S : LimitingSeparatedProfile regime)
    (D : TrackA.SeparatedDepthData regime j) (T : WideTargetProfile S D)
    (A : PositiveSourcePlateau S j) (W : WideSourceCarriers S A) (i : ℕ)
    (δ : ℝ) (hδ : 0 ≤ δ) (L : AffineVariety d → AffineFamily.Family d)
    (hsub : ∀ X ∈ W.survivingSources i, L X ⊆ wideSurvivingTargets D A i)
    (hloss : (∑ X ∈ W.survivingSources i,
      ∑ Y ∈ wideSurvivingTargets D A i \ L X,
        ((W.sourceAssigned i X).card : ℝ) * (wideTargetAssigned S D i Y).card) ≤
      δ * TrackD.famMass (W.survivingSources i) (W.sourceAssigned i) *
        TrackD.famMass (wideSurvivingTargets D A i) (wideTargetAssigned S D i)) :
    D.incidenceMass i (((D.centers i).product (D.carriers i)).filter
      (fun a => a.1 ∈ W.ignoredSources i ∨ a.2 ∉ L (W.data.owner i a.1))) ≤
      ((W.ignoredSources i).card : ℝ) / (D.centers i).card +
        D.submass i (D.carriers i \ wideSurvivingTargets D A i) / (D.targets i).card + δ := by
  have F := wide_finite_assignment_facts S D T A W
  let bad := ((D.centers i).product (D.carriers i)).filter
    (fun a => a.1 ∈ W.ignoredSources i ∨ a.2 ∉ L (W.data.owner i a.1))
  have hbad_sum : (∑ a ∈ bad, (D.mass i a.2 : ℝ)) =
      ∑ p ∈ D.centers i,
        ∑ Y ∈ (D.carriers i).filter (fun Y => p ∈ W.ignoredSources i ∨ Y ∉ L (W.data.owner i p)),
          (D.mass i Y : ℝ) := by
    dsimp [bad]
    rw [Finset.sum_filter, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_filter]
  let unign := D.centers i \ W.ignoredSources i
  have hsplit_centers : D.centers i = W.ignoredSources i ∪ unign := by
    change D.centers i = W.ignoredSources i ∪ (D.centers i \ W.ignoredSources i)
    rw [Finset.union_comm, Finset.sdiff_union_of_subset (F.ignored_subset i)]
  have hdisj_centers : Disjoint (W.ignoredSources i) unign := by
    rw [Finset.disjoint_iff_ne]
    rintro a ha _ hb rfl
    exact (Finset.mem_sdiff.mp hb).2 ha
  have houter_sum : (∑ p ∈ D.centers i,
      ∑ Y ∈ (D.carriers i).filter (fun Y => p ∈ W.ignoredSources i ∨ Y ∉ L (W.data.owner i p)),
        (D.mass i Y : ℝ)) =
      (∑ p ∈ W.ignoredSources i,
        ∑ Y ∈ (D.carriers i).filter (fun Y => p ∈ W.ignoredSources i ∨ Y ∉ L (W.data.owner i p)),
          (D.mass i Y : ℝ)) +
      (∑ p ∈ unign,
        ∑ Y ∈ (D.carriers i).filter (fun Y => p ∈ W.ignoredSources i ∨ Y ∉ L (W.data.owner i p)),
          (D.mass i Y : ℝ)) := by
    rw [hsplit_centers, Finset.sum_union hdisj_centers]
  have hign_term : (∑ p ∈ W.ignoredSources i,
      ∑ Y ∈ (D.carriers i).filter (fun Y => p ∈ W.ignoredSources i ∨ Y ∉ L (W.data.owner i p)),
        (D.mass i Y : ℝ)) = ((W.ignoredSources i).card : ℝ) * (D.targets i).card := by
    have hinner (p : Point d) (hp : p ∈ W.ignoredSources i) :
        (∑ Y ∈ (D.carriers i).filter (fun Y => p ∈ W.ignoredSources i ∨ Y ∉ L (W.data.owner i p)),
          (D.mass i Y : ℝ)) = ((D.targets i).card : ℝ) := by
      have hext : (D.carriers i).filter (fun Y => p ∈ W.ignoredSources i ∨ Y ∉ L (W.data.owner i p)) =
          D.carriers i := by
        ext Y
        simp only [Finset.mem_filter]
        exact ⟨fun h => h.1, fun h => ⟨h, Or.inl hp⟩⟩
      rw [hext, sum_mass_carriers_eq_targets_card]
    calc ∑ p ∈ W.ignoredSources i,
          ∑ Y ∈ (D.carriers i).filter (fun Y => p ∈ W.ignoredSources i ∨ Y ∉ L (W.data.owner i p)),
            (D.mass i Y : ℝ)
      _ = ∑ p ∈ W.ignoredSources i, ((D.targets i).card : ℝ) := by
          apply Finset.sum_congr rfl
          intro p hp
          exact hinner p hp
      _ = ((W.ignoredSources i).card : ℝ) * (D.targets i).card := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hunign_term : (∑ p ∈ unign,
      ∑ Y ∈ (D.carriers i).filter (fun Y => p ∈ W.ignoredSources i ∨ Y ∉ L (W.data.owner i p)),
        (D.mass i Y : ℝ)) ≤
      ((D.centers i).card : ℝ) * D.submass i (D.carriers i \ wideSurvivingTargets D A i) +
      δ * ((D.centers i).card : ℝ) * (D.targets i).card := by
    have hinner (p : Point d) (hp : p ∈ unign) :
        (∑ Y ∈ (D.carriers i).filter (fun Y => p ∈ W.ignoredSources i ∨ Y ∉ L (W.data.owner i p)),
          (D.mass i Y : ℝ)) =
        D.submass i (D.carriers i \ wideSurvivingTargets D A i) +
        ∑ Y ∈ wideSurvivingTargets D A i \ L (W.data.owner i p), (D.mass i Y : ℝ) := by
      have hp_not_ign : p ∉ W.ignoredSources i := (Finset.mem_sdiff.mp hp).2
      have hp_cent : p ∈ D.centers i := (Finset.mem_sdiff.mp hp).1
      have hX_surv : W.data.owner i p ∈ W.survivingSources i :=
        (F.source_owner i p hp_cent hp_not_ign).1
      have hext : (D.carriers i).filter (fun Y => p ∈ W.ignoredSources i ∨ Y ∉ L (W.data.owner i p)) =
          (D.carriers i \ wideSurvivingTargets D A i) ∪
          (wideSurvivingTargets D A i \ L (W.data.owner i p)) := by
        have hext1 : (D.carriers i).filter (fun Y => p ∈ W.ignoredSources i ∨ Y ∉ L (W.data.owner i p)) =
            (D.carriers i).filter (fun Y => Y ∉ L (W.data.owner i p)) := by
          ext Y; simp only [Finset.mem_filter]; tauto
        rw [hext1, carriers_filter_not_mem_L_eq _ _ _ (hsub _ hX_surv) (F.targets_subset i)]
      rw [hext, Finset.sum_union (disjoint_sdiff_sdiff _ _ _)]
      rfl
    have hsum_split : (∑ p ∈ unign,
        ∑ Y ∈ (D.carriers i).filter (fun Y => p ∈ W.ignoredSources i ∨ Y ∉ L (W.data.owner i p)),
          (D.mass i Y : ℝ)) =
        (∑ p ∈ unign, D.submass i (D.carriers i \ wideSurvivingTargets D A i)) +
        ∑ p ∈ unign, ∑ Y ∈ wideSurvivingTargets D A i \ L (W.data.owner i p), (D.mass i Y : ℝ) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      exact hinner p hp
    rw [hsum_split]
    have hpart1 : (∑ p ∈ unign, D.submass i (D.carriers i \ wideSurvivingTargets D A i)) ≤
        ((D.centers i).card : ℝ) * D.submass i (D.carriers i \ wideSurvivingTargets D A i) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      have hcard_le : (unign.card : ℝ) ≤ ((D.centers i).card : ℝ) := by
        exact_mod_cast (Finset.card_le_card (Finset.sdiff_subset : unign ⊆ D.centers i))
      have hsub_nonneg : 0 ≤ D.submass i (D.carriers i \ wideSurvivingTargets D A i) := by
        dsimp [TrackA.SeparatedDepthData.submass]
        exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
      exact mul_le_mul_of_nonneg_right hcard_le hsub_nonneg
    have hpart2 : (∑ p ∈ unign, ∑ Y ∈ wideSurvivingTargets D A i \ L (W.data.owner i p), (D.mass i Y : ℝ)) ≤
        δ * ((D.centers i).card : ℝ) * (D.targets i).card := by
      have hloss_sum := unign_loss_sum_le S D T A W i L
      have hloss_trans := hloss_sum.trans hloss
      have hmass_source := F.source_mass_le i
      have hmass_target := F.target_mass_le i
      have h1 : δ * TrackD.famMass (W.survivingSources i) (W.sourceAssigned i) *
          TrackD.famMass (wideSurvivingTargets D A i) (wideTargetAssigned S D i) ≤
          δ * ((D.centers i).card : ℝ) * (D.targets i).card := by
        have hpos1 : 0 ≤ δ * TrackD.famMass (W.survivingSources i) (W.sourceAssigned i) := by
          have hmass_pos : 0 ≤ TrackD.famMass (W.survivingSources i) (W.sourceAssigned i) := by
            dsimp [TrackD.famMass]
            exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
          exact mul_nonneg hδ hmass_pos
        have hstep1 := mul_le_mul_of_nonneg_left hmass_target hpos1
        have hstep2 : δ * TrackD.famMass (W.survivingSources i) (W.sourceAssigned i) * (D.targets i).card ≤
            δ * ((D.centers i).card : ℝ) * (D.targets i).card := by
          have hpos_T : 0 ≤ ((D.targets i).card : ℝ) := Nat.cast_nonneg _
          have hstep_inner := mul_le_mul_of_nonneg_left hmass_source hδ
          exact mul_le_mul_of_nonneg_right hstep_inner hpos_T
        exact hstep1.trans hstep2
      exact hloss_trans.trans h1
    exact add_le_add hpart1 hpart2
  have htotal_sum_le : (∑ a ∈ bad, (D.mass i a.2 : ℝ)) ≤
      ((W.ignoredSources i).card : ℝ) * (D.targets i).card +
      ((D.centers i).card : ℝ) * D.submass i (D.carriers i \ wideSurvivingTargets D A i) +
      δ * ((D.centers i).card : ℝ) * (D.targets i).card := by
    rw [hbad_sum, houter_sum, hign_term]
    have := add_le_add_left hunign_term (((W.ignoredSources i).card : ℝ) * (D.targets i).card)
    linarith
  dsimp [TrackA.SeparatedDepthData.incidenceMass]
  have hNC_pos : 0 < ((D.centers i).card : ℝ) := F.centers_pos i
  have hNT_pos : 0 < ((D.targets i).card : ℝ) := F.targets_pos i
  have hprod_pos : 0 < ((D.centers i).card : ℝ) * ((D.targets i).card : ℝ) :=
    mul_pos hNC_pos hNT_pos
  let NC := ((D.centers i).card : ℝ)
  let NT := ((D.targets i).card : ℝ)
  have hdiv_le := div_le_div_of_nonneg_right htotal_sum_le hprod_pos.le
  have hdiv_eq : (((W.ignoredSources i).card : ℝ) * NT +
      NC * D.submass i (D.carriers i \ wideSurvivingTargets D A i) +
      δ * NC * NT) / (NC * NT) =
      ((W.ignoredSources i).card : ℝ) / NC +
      D.submass i (D.carriers i \ wideSurvivingTargets D A i) / NT + δ := by
    have hNC_ne : NC ≠ 0 := hNC_pos.ne'
    have hNT_ne : NT ≠ 0 := hNT_pos.ne'
    have hNCNT_ne : NC * NT ≠ 0 := hprod_pos.ne'
    rw [add_div, add_div]
    have h1 : (((W.ignoredSources i).card : ℝ) * NT) / (NC * NT) = ((W.ignoredSources i).card : ℝ) / NC := by
      rw [mul_comm ((W.ignoredSources i).card : ℝ) NT, mul_comm NC NT]
      exact mul_div_mul_left _ _ hNT_ne
    have h2 : (NC * D.submass i (D.carriers i \ wideSurvivingTargets D A i)) / (NC * NT) =
        D.submass i (D.carriers i \ wideSurvivingTargets D A i) / NT := by
      exact mul_div_mul_left _ _ hNC_ne
    have h3 : (δ * NC * NT) / (NC * NT) = δ := by
      rw [mul_assoc δ, mul_div_cancel_right₀ _ hNCNT_ne]
    rw [h1, h2, h3]
  exact hdiv_le.trans (le_of_eq hdiv_eq)

/-- `G5.wide.fixed-lists`: one fixed error gives eventual list certificates,
using the correct generic-depth dimension branch. -/
theorem wide_fixed_error_lists (S : LimitingSeparatedProfile regime)
    (D : TrackA.SeparatedDepthData regime j) (T : WideTargetProfile S D)
    (A : PositiveSourcePlateau S j) (W : WideSourceCarriers S A)
    (hk : d - j < d - 1) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ i in atTop, ∃ L : AffineVariety d → AffineFamily.Family d,
      WideListCertificate S D A W i δ L := by
  have F := wide_finite_assignment_facts S D T A W
  have hrj := A.r_le_j
  have hjlt := D.j_lt
  have hrlt := A.r.isLt
  have hrpos := A.r_pos
  have hkl : d - j ≤ d - A.r.val := by omega
  have hlpos : 1 ≤ d - j := by omega
  have hkd : d - A.r.val < d := by omega
  have hld : d - j + 1 < d := by omega
  have htarget (i : ℕ) : ∀ Y ∈ wideSurvivingTargets D A i,
      Y.IsIrreducible ∧ Y.dimension = d - j := by
    intro Y hY
    exact D.carrier_pure i Y (F.targets_subset i hY)
  have hlog : Tendsto (fun i => Real.log (regime.B i)) atTop atTop :=
    Real.tendsto_log_atTop.comp regime.B_tendsto
  by_cases heq : A.r.val = j
  · obtain ⟨θ, hθ, w₀, hgeo⟩ := TrackD.geo_generic_depth d
      regime.dimension_ge_three (1 / 3) (by norm_num)
      (1 / 4) (by norm_num) δ hδ
    filter_upwards [wide_surviving_mass_lower S D T A W θ hθ,
      wide_equal_flat_budgets S D T A W heq θ hθ,
      wide_regime_flat_cap regime, hlog.eventually_ge_atTop w₀,
      wide_root_cap regime] with i hmass hflat hcap hwidth hround
    obtain ⟨L, hsub, hloss, hgeometry⟩ := hgeo (regime.P i)
      (Real.log (regime.B i)) (regime.B i ^ (j : ℝ)) hwidth le_rfl
      (Real.rpow_pos_of_pos (regime.B_pos i) _) hcap
      (d - A.r.val) (d - j) hkl hlpos hkd hld
      (W.survivingSources i) (wideSurvivingTargets D A i)
      (W.sourceAssigned i) (wideTargetAssigned S D i)
      (F.source_pure i) (htarget i) (F.source_assignment i) (F.target_assignment i)
      (F.flat_real heq i) hmass.1 hmass.2 (fun _ => hflat)
    refine ⟨L, hsub, hloss, ?_⟩
    intro X hX Y hY
    apply generic_moving_root_bound_of_pair X Y (L X)
    exact (hgeometry X hX Y hY).mono fun x hx y hy h =>
      ⟨h.1, h.2.2.1, h.2.2.2.trans hround⟩
  · have hlk : d - j < d - A.r.val := by omega
    obtain ⟨θ, hθ, w₀, hgeo⟩ := Request.generic_depth_strict_dimension d
      regime.dimension_ge_three (1 / 3) (by norm_num)
      (1 / 4) (by norm_num) δ hδ
    filter_upwards [wide_surviving_mass_lower S D T A W θ hθ,
      wide_regime_flat_cap regime, hlog.eventually_ge_atTop w₀,
      wide_root_cap regime] with i hmass hcap hwidth hround
    obtain ⟨L, hsub, hloss, hgeometry⟩ := hgeo (regime.P i)
      (Real.log (regime.B i)) hwidth le_rfl hcap
      (d - A.r.val) (d - j) hlk hlpos hkd hld
      (W.survivingSources i) (wideSurvivingTargets D A i)
      (W.sourceAssigned i) (wideTargetAssigned S D i)
      (F.source_pure i) (htarget i) (F.source_assignment i) (F.target_assignment i)
      hmass.1 hmass.2
    refine ⟨L, hsub, hloss, ?_⟩
    intro X hX Y hY
    apply generic_moving_root_bound_of_pair X Y (L X)
    exact (hgeometry X hX Y hY).mono fun x hx y hy h =>
      ⟨h.1, h.2.2.1, h.2.2.2.trans hround⟩

/-- `G5.wide.core`: select lists at slowly vanishing error on the fixed
source carriers, normalize all omissions, and attach uniform component tests. -/
theorem profile_wide_core (S : LimitingSeparatedProfile regime)
    (D : TrackA.SeparatedDepthData regime j) (T : WideTargetProfile S D)
    (A : PositiveSourcePlateau S j) (W : WideSourceCarriers S A)
    (hwide : Tendsto (fun i => D.s i / D.v i) atTop (𝓝 0))
    (hk : d - j < d - 1) : D.WideInput := by
  have F := wide_finite_assignment_facts S D T A W
  obtain ⟨hignored, htargets⟩ := wide_omission_negligible S D T A W
  let δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hδpos (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  let Q : ℕ → ℕ → Prop := fun n i =>
    ∃ L : AffineVariety d → AffineFamily.Family d,
      WideListCertificate S D A W i (δ n) L
  have hQ (n : ℕ) : ∀ᶠ i in atTop, Q n i :=
    wide_fixed_error_lists S D T A W hk (δ n) (hδpos n)
  obtain ⟨a, _, hagrows, hchoice⟩ := Framework.exists_slow_diagonal Q hQ
  let lists : ℕ → AffineVariety d → AffineFamily.Family d := fun i =>
    if h : Q (a i) i then h.choose else fun _ => ∅
  have hlist (i : ℕ) (hi : Q (a i) i) :
      WideListCertificate S D A W i (δ (a i)) (lists i) := by
    simpa only [lists, dif_pos hi] using hi.choose_spec
  have hchosen : ∀ᶠ i in atTop,
      WideListCertificate S D A W i (δ (a i)) (lists i) := by
    filter_upwards [hchoice] with i hi
    exact hlist i (hi (a i) le_rfl)
  have hsub : ∀ i X, X ∈ W.survivingSources i → lists i X ⊆ D.carriers i := by
    intro i X hX
    by_cases hi : Q (a i) i
    · exact ((hlist i hi).1 X hX).trans (F.targets_subset i)
    · simp only [lists, dif_neg hi]
      exact Finset.empty_subset _
  have hsourceRatio : Tendsto
      (fun i => ((W.ignoredSources i).card : ℝ) / (D.centers i).card) atTop (𝓝 0) :=
    (Framework.littleO_iff_ratio
      (Eventually.of_forall fun i => (F.centers_pos i).ne')).mp hignored
  have htargetRatio : Tendsto
      (fun i => D.submass i (D.carriers i \ wideSurvivingTargets D A i) /
        (D.targets i).card) atTop (𝓝 0) :=
    (Framework.littleO_iff_ratio
      (Eventually.of_forall fun i => (F.targets_pos i).ne')).mp htargets
  have hδlim : Tendsto (fun i => δ (a i)) atTop (𝓝 0) := by
    simpa only [δ, Function.comp_def] using
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hagrows
  let R : ℕ → ℝ := fun i =>
    ((W.ignoredSources i).card : ℝ) / (D.centers i).card +
      D.submass i (D.carriers i \ wideSurvivingTargets D A i) / (D.targets i).card + δ (a i)
  have hRlim : Tendsto R atTop (𝓝 0) := by
    simpa only [zero_add, add_zero] using (hsourceRatio.add htargetRatio).add hδlim
  have hRsmall : Framework.LittleO R (fun _ => 1) :=
    (Asymptotics.isLittleO_one_iff ℝ).mpr hRlim
  have hmass : Framework.LittleO
      (fun i => D.incidenceMass i (((D.centers i).product (D.carriers i)).filter
        (fun p => p.1 ∈ W.ignoredSources i ∨ p.2 ∉ lists i (W.data.owner i p.1))))
      (fun _ => 1) := by
    apply Asymptotics.IsLittleO.of_bound
    intro ε hε
    filter_upwards [hchosen, hRsmall.def hε] with i hi hRi
    have hRupper : R i ≤ ε := (le_abs_self (R i)).trans (by
      simpa only [Real.norm_eq_abs, abs_one, mul_one] using hRi)
    have hbound := wide_incidence_bound S D T A W i (δ (a i))
      (hδpos (a i)).le (lists i) hi.1 hi.2.1
    have hnonneg : 0 ≤ D.incidenceMass i
        (((D.centers i).product (D.carriers i)).filter
          (fun p => p.1 ∈ W.ignoredSources i ∨ p.2 ∉ lists i (W.data.owner i p.1))) := by
      unfold TrackA.SeparatedDepthData.incidenceMass
      positivity
    simp only [Real.norm_eq_abs, abs_one, mul_one]
    rw [abs_of_nonneg hnonneg]
    exact hbound.trans hRupper
  have hrj := A.r_le_j
  have hrpos := A.r_pos
  have hrlt := A.r.isLt
  refine ⟨d - A.r.val, W.survivingSources, W.data.owner, lists, W.ignoredSources,
    by omega, by omega, F.source_pure, F.ignored_subset, hignored, ?_, hsub,
    hchosen.mono (fun _ hi => hi.2.2), hmass, ?_⟩
  · intro i p hp hnot
    have h := F.source_owner i p hp hnot
    exact ⟨h.1, h.2.2⟩
  · exact profile_source_component_tests S D T.s_eq T.v_eq T.centers_eq hwide A
      W.survivingSources W.data.owner W.ignoredSources F.source_owner

end
end DistinctDistances.SparseCones
