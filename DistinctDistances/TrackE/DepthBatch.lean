import DistinctDistances.TrackE.DepthBatchInputs

/-! Simultaneous actual-center projected-degree interfaces for the finite batch
of plateaux, depth denominators and logarithmic tolerances used in separated
rank propagation (sparse-cones.tex:668–691). -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d} {α : Type*} [Fintype α]

/-- All batch deletions are fixed before any later center, envelope or positive
target-density choice. Each application keeps its original plateau assignment. -/
structure DepthBatchData (j : α → ℕ)
    (D : (a : α) → TrackA.SeparatedDepthData regime (j a))
    (centers targets : ℕ → Finset (Point d))
    (R : α → ℕ → ℝ) (ε : α → ℝ) where
  bad : α → ℕ → Finset (Point d × AffineVariety d)
  bad_subset : ∀ a i, bad a i ⊆ centers i ×ˢ (D a).carriers i
  badCenters : ℕ → Finset (Point d)
  badCenters_subset : ∀ i, badCenters i ⊆ centers i
  incidence_small : Framework.LittleO
    (fun i => ((batchBadPairs D centers targets bad i).card : ℝ))
    (fun i => (centers i).card * (targets i).card)
  centers_small : Framework.LittleO (fun i => ((badCenters i).card : ℝ))
    (fun i => (centers i).card)
  row_small : Framework.UniformLittleO
    (fun i => {p : Point d // p ∈ centers i ∧ p ∉ badCenters i})
    (fun i p => ((batchBadTargets D targets bad i p.val).card : ℝ))
    (fun i _ => (targets i).card)
  owner_retained : ∀ i p q, q ∈ targets i →
    q ∉ batchBadTargets D targets bad i p →
    ∀ a, (D a).owner i q ∈ (D a).retained i (bad a i) p
  dimension : ∀ᶠ i in atTop, ∀ a, ∀ p ∈ centers i, p ∉ badCenters i →
    ∀ Y ∈ (D a).retained i (bad a i) p, (radialImage p Y).dimension = d - j a
  degree : ∀ ρ : ℝ, 0 < ρ → ∀ᶠ i in atTop,
    ∀ a, ∀ p ∈ centers i, p ∉ badCenters i →
    ∀ J : AffineFamily.Family d, J ⊆ (D a).retained i (bad a i) p →
      ρ * ((targets i).card : ℝ) ≤ (D a).submass i J →
      (D a).degreeBudget i / R a i * Real.exp (-ε a * (D a).s i) ≤
        (ProjectiveFamily.degree (TrackA.projectedFamily p J) : ℝ)

/-- `sc:u-typical.batch`: combine A's conclusions for a fixed finite batch on
the same actual point sets. One row Markov is applied to their physical union;
the resulting typical centers serve every later fixed positive density at once. -/
theorem projected_degree_batch (j : α → ℕ)
    (D : (a : α) → TrackA.SeparatedDepthData regime (j a))
    (centers targets : ℕ → Finset (Point d))
    (R : α → ℕ → ℝ) (ε : α → ℝ)
    (hcenters : ∀ a i, (D a).centers i = centers i)
    (htargets : ∀ a i, (D a).targets i = targets i)
    (hconclusion : ∀ a, (D a).ProjectedDegreeConclusion (R a) (ε a)) :
    Nonempty (DepthBatchData j D centers targets R ε) := by
  classical
  unfold TrackA.SeparatedDepthData.ProjectedDegreeConclusion at hconclusion
  choose bad originalCenters hsubset hinc hcenterSmall _hrows hdimension hdegree
    using hconclusion
  have hbadSub : ∀ a i, bad a i ⊆ centers i ×ˢ (D a).carriers i := by
    intro a i
    simpa only [hcenters a i, Finset.product_eq_sprod] using (hsubset a i).1
  have hcenterSub : ∀ a i, originalCenters a i ⊆ centers i := by
    intro a i
    simpa only [hcenters a i] using (hsubset a i).2
  have hpairSub : ∀ i, batchBadPairs D centers targets bad i ⊆ centers i ×ˢ targets i :=
    fun i => Finset.filter_subset _ _
  have hpairSmall := batch_incidence_small D centers targets bad
    hcenters htargets hbadSub hinc
  obtain ⟨markovCenters, hmarkovSub, hmarkovSmall, hmarkovRows⟩ :=
    finite_incidence_row_deletion centers targets
      (batchBadPairs D centers targets bad) hpairSub hpairSmall
  let originalUnion : ℕ → Finset (Point d) := fun i =>
    (Finset.univ : Finset α).biUnion (fun a => originalCenters a i)
  let commonCenters : ℕ → Finset (Point d) := fun i => markovCenters i ∪ originalUnion i
  have hunionSub : ∀ i, originalUnion i ⊆ centers i := by
    intro i p hp
    obtain ⟨a, _, ha⟩ := Finset.mem_biUnion.mp hp
    exact hcenterSub a i ha
  have hcommonSub : ∀ i, commonCenters i ⊆ centers i :=
    fun i => Finset.union_subset (hmarkovSub i) (hunionSub i)
  have havoid : ∀ i p, p ∉ commonCenters i →
      p ∉ markovCenters i ∧ ∀ a, p ∉ originalCenters a i := by
    intro i p hp
    constructor
    · intro hm
      exact hp (Finset.mem_union_left _ hm)
    · intro a ha
      exact hp (Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ a, ha⟩))
  have horiginalSmall : ∀ a, Framework.LittleO
      (fun i => ((originalCenters a i).card : ℝ)) (fun i => (centers i).card) := by
    intro a
    simpa only [hcenters] using hcenterSmall a
  have hunionSmall : Framework.LittleO
      (fun i => ((originalUnion i).card : ℝ)) (fun i => (centers i).card) :=
    finite_center_union_small centers originalCenters horiginalSmall
  have hsumSmall := hmarkovSmall.add hunionSmall
  have hcommonSmall : Framework.LittleO
      (fun i => ((commonCenters i).card : ℝ)) (fun i => (centers i).card) := by
    apply Asymptotics.IsLittleO.of_bound
    intro δ hδ
    filter_upwards [hsumSmall.def hδ] with i hi
    have hcard : ((commonCenters i).card : ℝ) ≤
        (markovCenters i).card + (originalUnion i).card := by
      exact_mod_cast Finset.card_union_le (markovCenters i) (originalUnion i)
    calc
      ‖((commonCenters i).card : ℝ)‖ = ((commonCenters i).card : ℝ) :=
        Real.norm_of_nonneg (by positivity)
      _ ≤ (markovCenters i).card + (originalUnion i).card := hcard
      _ = ‖((markovCenters i).card : ℝ) + (originalUnion i).card‖ :=
        (Real.norm_of_nonneg (by positivity)).symm
      _ ≤ δ * ‖((centers i).card : ℝ)‖ := hi
  have hrowSmall : Framework.UniformLittleO
      (fun i => {p : Point d // p ∈ centers i ∧ p ∉ commonCenters i})
      (fun i p => ((batchBadTargets D targets bad i p.val).card : ℝ))
      (fun i _ => (targets i).card) := by
    intro δ hδ
    filter_upwards [hmarkovRows δ hδ] with i hi
    intro p
    have hnot := (havoid i p.val p.property.2).1
    have heq : batchBadTargets D targets bad i p.val =
        (targets i).filter (fun q => (p.val, q) ∈ batchBadPairs D centers targets bad i) := by
      ext q
      simp [batchBadTargets, batchBadPairs, p.property.1]
    rw [heq]
    exact hi ⟨p.val, p.property.1, hnot⟩
  have hfinite {Q : α → ℕ → Prop} (hQ : ∀ a, ∀ᶠ i in atTop, Q a i) :
      ∀ᶠ i in atTop, ∀ a, Q a i := by
    simpa only [Finset.mem_univ, forall_const] using
      Framework.eventually_finite (Finset.univ : Finset α) Q (fun a _ => hQ a)
  have hdim : ∀ᶠ i in atTop, ∀ a, ∀ p ∈ centers i, p ∉ commonCenters i →
      ∀ Y ∈ (D a).retained i (bad a i) p, (radialImage p Y).dimension = d - j a := by
    filter_upwards [hfinite hdimension] with i hi
    intro a p hp hnot Y hY
    have hpD : p ∈ (D a).centers i := by simpa only [hcenters a i] using hp
    exact hi a p hpD ((havoid i p hnot).2 a) Y hY
  have hdeg : ∀ ρ : ℝ, 0 < ρ → ∀ᶠ i in atTop,
      ∀ a, ∀ p ∈ centers i, p ∉ commonCenters i →
      ∀ J : AffineFamily.Family d, J ⊆ (D a).retained i (bad a i) p →
        ρ * ((targets i).card : ℝ) ≤ (D a).submass i J →
        (D a).degreeBudget i / R a i * Real.exp (-ε a * (D a).s i) ≤
          (ProjectiveFamily.degree (TrackA.projectedFamily p J) : ℝ) := by
    intro ρ hρ
    filter_upwards [hfinite (fun a => hdegree a ρ hρ)] with i hi
    intro a p hp hnot J hJ hmass
    have hpD : p ∈ (D a).centers i := by simpa only [hcenters a i] using hp
    have hmassD : ρ * (((D a).targets i).card : ℝ) ≤ (D a).submass i J := by
      simpa only [htargets a i] using hmass
    exact hi a p hpD ((havoid i p hnot).2 a) J hJ hmassD
  exact ⟨{
    bad := bad
    bad_subset := hbadSub
    badCenters := commonCenters
    badCenters_subset := hcommonSub
    incidence_small := hpairSmall
    centers_small := hcommonSmall
    row_small := hrowSmall
    owner_retained := fun i p q hq hnot =>
      batch_owner_retained D targets bad htargets i p q hq hnot
    dimension := hdim
    degree := hdeg }⟩

end
end DistinctDistances.SparseCones
