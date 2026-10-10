import DistinctDistances.TrackE.ProfileDepthBatch

/-! Retain the literal selected graph after the fixed batch deletions
(`sc:u-typical.graph`, sparse-cones.tex:668–678, 795–928). -/
namespace DistinctDistances.SparseCones
open Filter
open scoped Topology BigOperators Classical
noncomputable section
variable {d : ℕ} {regime : Regime d} {α : Type*} [Fintype α]

/-- Delete only the fixed batch incidence union and the common atypical rows
from the original terminal-selected physical graph. -/
def profileBatchGraph {F : ConeCoverageSequence regime}
    {T : SelectedProfileSequence F} {S : LimitingSeparatedProfile regime}
    {plateau : α → ProfilePlateau S} {kind : α → DepthRateKind} {ε : α → ℝ}
    (H : ProfileDepthBatchData T S plateau kind ε) (i : ℕ) :
    Finset (RPoint d × RPoint d) :=
  (terminalSelectedGraph T i).filter (fun pq =>
    TrackD.toC pq.1 ∉ H.batch.badCenters i ∧
    (TrackD.toC pq.1, TrackD.toC pq.2) ∉ batchBadPairs
      (fun a => H.data (plateau a))
      (fun i => (S.sequence.source i).pts.image TrackD.toC)
      (fun i => (S.sequence.target i).pts.image TrackD.toC) H.batch.bad i)

/-- Injective complexification transfers the negligible complex pair/row
deletions to every dense physical graph on the same actual point sets. -/
theorem finite_graph_survives_complex_deletion (X Y : ℕ → Finset (RPoint d))
    (Γ : ℕ → Finset (RPoint d × RPoint d))
    (hΓ : ∀ i, Γ i ⊆ X i ×ˢ Y i)
    (badCenters : ℕ → Finset (Point d))
    (badPairs : ℕ → Finset (Point d × Point d))
    (hcenters : Framework.LittleO (fun i => ((badCenters i).card : ℝ))
      (fun i => ((X i).image TrackD.toC).card))
    (hpairs : Framework.LittleO (fun i => ((badPairs i).card : ℝ))
      (fun i => ((X i).image TrackD.toC).card * ((Y i).image TrackD.toC).card))
    (c : ℝ) (hc : 0 < c)
    (hdense : ∀ᶠ i in atTop, c * ((X i).image TrackD.toC).card *
      ((Y i).image TrackD.toC).card ≤ (Γ i).card) :
    ∀ᶠ i in atTop, (c / 2) * ((X i).image TrackD.toC).card *
      ((Y i).image TrackD.toC).card ≤
      (((Γ i).filter (fun pq => TrackD.toC pq.1 ∉ badCenters i ∧
        (TrackD.toC pq.1, TrackD.toC pq.2) ∉ badPairs i)).card : ℝ) := by
  have htoCInj : Function.Injective (TrackD.toC (d := d)) := by
    intro x y h
    ext k
    have hk : TrackD.toC x k = TrackD.toC y k := by rw [h]
    dsimp [TrackD.toC] at hk
    exact Complex.ofReal_injective hk
  let f : RPoint d × RPoint d → Point d × Point d :=
    fun pq => (TrackD.toC pq.1, TrackD.toC pq.2)
  have hfInj : Function.Injective f := by
    intro pq₁ pq₂ h
    dsimp [f] at h
    rcases Prod.ext_iff.mp h with ⟨h1, h2⟩
    exact Prod.ext (htoCInj h1) (htoCInj h2)
  have hc4 : 0 < c / 4 := by linarith
  have hcen := hcenters.def hc4
  have hpr := hpairs.def hc4
  filter_upwards [hdense, hcen, hpr] with i hi hcenBound hprBound
  let NX : ℝ := ((X i).image TrackD.toC).card
  let NY : ℝ := ((Y i).image TrackD.toC).card
  let Γ' := (Γ i).filter (fun pq => TrackD.toC pq.1 ∉ badCenters i ∧
    (TrackD.toC pq.1, TrackD.toC pq.2) ∉ badPairs i)
  let B₁ := (Γ i).filter (fun pq => TrackD.toC pq.1 ∈ badCenters i)
  let B₂ := (Γ i).filter (fun pq => (TrackD.toC pq.1, TrackD.toC pq.2) ∈ badPairs i)
  have hdiffSub : Γ i \ Γ' ⊆ B₁ ∪ B₂ := by
    intro pq hpq
    rw [Finset.mem_sdiff] at hpq
    have hq := hpq.1
    have hnot := hpq.2
    have hdisj : TrackD.toC pq.1 ∈ badCenters i ∨ (TrackD.toC pq.1, TrackD.toC pq.2) ∈ badPairs i := by
      by_contra hneg
      push_neg at hneg
      apply hnot
      rw [Finset.mem_filter]
      exact ⟨hq, hneg.1, hneg.2⟩
    rw [Finset.mem_union]
    cases hdisj with
    | inl h1 => left; exact Finset.mem_filter.mpr ⟨hq, h1⟩
    | inr h2 => right; exact Finset.mem_filter.mpr ⟨hq, h2⟩
  have hcardDiff : ((Γ i \ Γ').card : ℝ) ≤ (B₁.card : ℝ) + (B₂.card : ℝ) := by
    have h1 := Finset.card_le_card hdiffSub
    have h2 := Finset.card_union_le B₁ B₂
    exact_mod_cast h1.trans h2
  have hB₁Sub : B₁ ⊆ ((X i).filter (fun p => TrackD.toC p ∈ badCenters i)) ×ˢ (Y i) := by
    intro pq hpq
    rw [Finset.mem_filter] at hpq
    have hsub := hΓ i hpq.1
    rw [Finset.mem_product] at hsub
    rw [Finset.mem_product, Finset.mem_filter]
    exact ⟨⟨hsub.1, hpq.2⟩, hsub.2⟩
  have hB₁Card : (B₁.card : ℝ) ≤ ((badCenters i).card : ℝ) * NY := by
    have hsubCard : B₁.card ≤ (((X i).filter (fun p => TrackD.toC p ∈ badCenters i)) ×ˢ (Y i)).card :=
      Finset.card_le_card hB₁Sub
    rw [Finset.card_product] at hsubCard
    have hcenSub : (((X i).filter (fun p => TrackD.toC p ∈ badCenters i)).image TrackD.toC) ⊆ badCenters i := by
      intro z hz
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
      rw [Finset.mem_filter] at hp
      exact hp.2
    have hcenCard : ((X i).filter (fun p => TrackD.toC p ∈ badCenters i)).card ≤ (badCenters i).card := by
      rw [← Finset.card_image_of_injective _ htoCInj]
      exact Finset.card_le_card hcenSub
    have hYcard : (Y i).card = ((Y i).image TrackD.toC).card :=
      (Finset.card_image_of_injective (Y i) htoCInj).symm
    have hB1le : B₁.card ≤ (badCenters i).card * ((Y i).image TrackD.toC).card := by
      calc
        B₁.card ≤ ((X i).filter (fun p => TrackD.toC p ∈ badCenters i)).card * (Y i).card := hsubCard
        _ ≤ (badCenters i).card * (Y i).card := Nat.mul_le_mul_right _ hcenCard
        _ = (badCenters i).card * ((Y i).image TrackD.toC).card := by rw [hYcard]
    have hcast : (B₁.card : ℝ) ≤ ((badCenters i).card : ℝ) * (((Y i).image TrackD.toC).card : ℝ) := by
      exact_mod_cast hB1le
    exact hcast
  have hB₂Card : (B₂.card : ℝ) ≤ ((badPairs i).card : ℝ) := by
    have himageSub : B₂.image f ⊆ badPairs i := by
      intro z hz
      obtain ⟨pq, hpq, rfl⟩ := Finset.mem_image.mp hz
      rw [Finset.mem_filter] at hpq
      exact hpq.2
    have hcardEq : (B₂.image f).card = B₂.card :=
      Finset.card_image_of_injective B₂ hfInj
    rw [← hcardEq]
    exact_mod_cast Finset.card_le_card himageSub
  have hB₁Bound : (B₁.card : ℝ) ≤ (c / 4) * NX * NY := by
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)] at hcenBound
    calc
      (B₁.card : ℝ) ≤ ((badCenters i).card : ℝ) * NY := hB₁Card
      _ ≤ ((c / 4) * NX) * NY := mul_le_mul_of_nonneg_right hcenBound (by positivity)
      _ = (c / 4) * NX * NY := by ring
  have hB₂Bound : (B₂.card : ℝ) ≤ (c / 4) * NX * NY := by
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)] at hprBound
    calc
      (B₂.card : ℝ) ≤ ((badPairs i).card : ℝ) := hB₂Card
      _ ≤ (c / 4) * (NX * NY) := hprBound
      _ = (c / 4) * NX * NY := by ring
  have hΓ'Lower : ((Γ i).card : ℝ) - ((B₁.card : ℝ) + (B₂.card : ℝ)) ≤ (Γ'.card : ℝ) := by
    have hPartition : (Γ i \ Γ').card + Γ'.card = (Γ i).card :=
      Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)
    have hPartitionR : ((Γ i \ Γ').card : ℝ) + (Γ'.card : ℝ) = ((Γ i).card : ℝ) := by
      exact_mod_cast hPartition
    linarith [hcardDiff, hPartitionR]
  calc
    (c / 2) * NX * NY = c * NX * NY - ((c / 4) * NX * NY + (c / 4) * NX * NY) := by ring
    _ ≤ (Γ i).card - ((B₁.card : ℝ) + (B₂.card : ℝ)) := by linarith [hi, hB₁Bound, hB₂Bound]
    _ ≤ (Γ'.card : ℝ) := hΓ'Lower

/-- `sc:u-typical.graph`: retain density at least 1/8, common typical centers,
all original plateau owners and the original terminal exclusion. -/
theorem selected_profile_batch_graph {F : ConeCoverageSequence regime}
    (T : SelectedProfileSequence F) (S : LimitingSeparatedProfile regime)
    (hsource : ∀ i, T.sources i = {S.sequence.source i})
    (htarget : ∀ i, T.targets i = {S.sequence.target i})
    {plateau : α → ProfilePlateau S} {kind : α → DepthRateKind} {ε : α → ℝ}
    (H : ProfileDepthBatchData T S plateau kind ε) :
    (∀ᶠ i in atTop, (1 / 8 : ℝ) * ((S.sequence.source i).pts.image TrackD.toC).card *
      ((S.sequence.target i).pts.image TrackD.toC).card ≤ (profileBatchGraph H i).card) ∧
    (∀ i p q, (p, q) ∈ profileBatchGraph H i →
      TrackD.toC p ∉ H.batch.badCenters i ∧ ∀ a,
        (H.data (plateau a)).owner i (TrackD.toC q) ∈
          (H.data (plateau a)).retained i (H.batch.bad a i) (TrackD.toC p)) ∧
    (∀ u, u.val.val = d - 1 → ∀ i p q, (p, q) ∈ profileBatchGraph H i →
      ¬ TrackD.ProjectsInto (F.family i p) p ((H.data u).owner i (TrackD.toC q))) := by
  classical
  let X : ℕ → Finset (RPoint d) := fun i => (S.sequence.source i).pts
  let Y : ℕ → Finset (RPoint d) := fun i => (S.sequence.target i).pts
  have hsourcePool (i : ℕ) : TrackD.poolPts (T.sources i) = X i := by
    rw [hsource i]
    simp [TrackD.poolPts, X]
  have htargetPool (i : ℕ) : TrackD.poolPts (T.targets i) = Y i := by
    rw [htarget i]
    simp [TrackD.poolPts, Y]
  have hsub : ∀ i, terminalSelectedGraph T i ⊆ X i ×ˢ Y i := by
    intro i pq hpq
    obtain ⟨hp, hq, _, _, _⟩ := (mem_terminalSelectedGraph T i pq.1 pq.2).mp hpq
    exact Finset.mem_product.mpr
      ⟨by simpa only [hsourcePool] using hp, by simpa only [htargetPool] using hq⟩
  have hXcard (i : ℕ) : ((X i).image TrackD.toC).card = (X i).card :=
    Finset.card_image_of_injective _ profile_toC_injective
  have hYcard (i : ℕ) : ((Y i).image TrackD.toC).card = (Y i).card :=
    Finset.card_image_of_injective _ profile_toC_injective
  have hdense : ∀ᶠ i in atTop, (1 / 4 : ℝ) * ((X i).image TrackD.toC).card *
      ((Y i).image TrackD.toC).card ≤ (terminalSelectedGraph T i).card := by
    simpa only [hXcard, hYcard, hsourcePool, htargetPool] using
      selected_terminal_graph_dense T
  have hgraphDense := finite_graph_survives_complex_deletion X Y
    (terminalSelectedGraph T) hsub H.batch.badCenters
    (batchBadPairs (fun a => H.data (plateau a))
      (fun i => (X i).image TrackD.toC) (fun i => (Y i).image TrackD.toC) H.batch.bad)
    H.batch.centers_small H.batch.incidence_small (1 / 4) (by norm_num) hdense
  have hretainedDense : ∀ᶠ i in atTop,
      (1 / 8 : ℝ) * ((S.sequence.source i).pts.image TrackD.toC).card *
        ((S.sequence.target i).pts.image TrackD.toC).card ≤ (profileBatchGraph H i).card := by
    simpa only [profileBatchGraph, show ((1 / 4 : ℝ) / 2) = 1 / 8 by norm_num] using
      hgraphDense
  refine ⟨hretainedDense, ?_, ?_⟩
  · intro i p q hpq
    obtain ⟨hterminal, htypical, hpair⟩ := Finset.mem_filter.mp hpq
    obtain ⟨hp, hq, _, _, _⟩ := (mem_terminalSelectedGraph T i p q).mp hterminal
    have hpC : TrackD.toC p ∈ (S.sequence.source i).pts.image TrackD.toC := by
      apply Finset.mem_image.mpr
      exact ⟨p, by simpa only [hsourcePool] using hp, rfl⟩
    have hqC : TrackD.toC q ∈ (S.sequence.target i).pts.image TrackD.toC := by
      apply Finset.mem_image.mpr
      exact ⟨q, by simpa only [htargetPool] using hq, rfl⟩
    have hqNot : TrackD.toC q ∉ batchBadTargets (fun a => H.data (plateau a))
        (fun i => (S.sequence.target i).pts.image TrackD.toC) H.batch.bad i (TrackD.toC p) := by
      intro hbad
      apply hpair
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hpC, hqC⟩, (Finset.mem_filter.mp hbad).2⟩
    exact ⟨htypical, H.batch.owner_retained i (TrackD.toC p) (TrackD.toC q) hqC hqNot⟩
  · intro u hlast i p q hpq
    exact H.terminal_excluded u hlast i p q (Finset.mem_filter.mp hpq).1

end
end DistinctDistances.SparseCones
