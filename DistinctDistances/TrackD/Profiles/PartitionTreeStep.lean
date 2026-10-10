import DistinctDistances.TrackD.Profiles.PartitionTreeBase

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section
variable {d G : ℕ}

structure PartitionPreparedForest (grid : Fin G → ℝ) (L : Fin G → ℕ)
    (s u : ℝ) (a : Fin (G * d) → ℝ) (r : Fin G) (π : CutPath d) (j : ℕ)
    (S T : Finset (Pt d)) (loss : ℝ) (pl : Finset (Piece d)) : Prop where
  subset : ∀ X ∈ pl, X.pts ⊆ T
  disjoint : (pl : Set (Piece d)).PairwiseDisjoint Piece.pts
  leaf : ∀ X ∈ pl, PartitionGridLeaf grid L r π j S s X ∧
    (S.card : ℝ) * Real.exp (-partitionEventTail a (r.val * d + j)) ≤ X.pts.card ∧
    PartitionGridTests grid L r u X
  discard : (T.card : ℝ) - ∑ X ∈ pl, (X.pts.card : ℝ) ≤ T.card * loss

/-- The nonterminal event in the finite tree: extract proper cuts, advance a
large residual, and sum losses against the original disjoint parent masses. -/
theorem partition_grid_forest_step (grid : Fin G → ℝ) (hgrid : StrictMono grid)
    (L : Fin G → ℕ) (s u : ℝ) (hu : 0 < u) (a : Fin (G * d) → ℝ)
    (ha : ∀ i, u ≤ a i)
    (htail : ∀ i, (∑ k ∈ Finset.univ.filter (fun k : Fin (G * d) => i < k), a k) ≤ a i / 9)
    (r : Fin G) (π : CutPath d) (j : ℕ) (hj : j < d) (hnext : r.val + 1 < G)
    (S S₀ : Finset (Pt d)) (hne : S.Nonempty) (hsubset : S ⊆ S₀)
    (hvan : ∀ x ∈ S, ∀ i : Fin d, i.val < j → MvPolynomial.eval (toC x) (π.cut i) = 0)
    (hproper : ∀ x ∈ S, ∀ i : Fin d, i.val < j →
      ∀ Z ∈ π.localCarriers i.val (toC x), π.cut i ∉ Z.ideal)
    (hmono : ∀ i k : Fin d, i.val < j → k.val < j → i ≤ k → π.time i ≤ π.time k)
    (hfinal : ∀ i : Fin d, i.val < j → π.time i ≤ grid r)
    (hrec : ∀ (r' : Fin G) (π' : CutPath d) (j' : ℕ) (T : Finset (Pt d)),
      r.val * d + j < r'.val * d + j' → j' ≤ d → T ⊆ S₀ →
      (∀ x ∈ T, ∀ i : Fin d, i.val < j' → MvPolynomial.eval (toC x) (π'.cut i) = 0) →
      (∀ x ∈ T, ∀ i : Fin d, i.val < j' →
        ∀ Z ∈ π'.localCarriers i.val (toC x), π'.cut i ∉ Z.ideal) →
      (∀ i k : Fin d, i.val < j' → k.val < j' → i ≤ k → π'.time i ≤ π'.time k) →
      (∀ i : Fin d, i.val < j' → π'.time i ≤ grid r') →
      Nonempty (PartitionGridForest grid L s u a r' π' j' T)) :
    Nonempty (PartitionGridForest grid L s u a r π j S) := by
  classical
  letI : DecidableEq (Pt d) := fun x y => Classical.propDecidable (x = y)
  have ha0 : ∀ i, 0 ≤ a i := fun i => hu.le.trans (ha i)
  let qn : ℕ := r.val * d + j
  have hq : qn < G * d := by
    have hmul := Nat.mul_le_mul_right d (Nat.succ_le_of_lt r.isLt)
    dsimp [qn]
    nlinarith
  let q : Fin (G * d) := ⟨qn, hq⟩
  let m : ℝ := S.card
  have hm : 0 < m := by
    dsimp [m]
    exact_mod_cast Finset.card_pos.mpr hne
  let w : Fin (G * d) → ℝ := fun i => Real.exp (-a i / 2)
  let loss : ℝ := partitionEventTail w (qn + 1)
  have hloss : 0 ≤ loss := partition_event_tail_nonneg w (fun i => Real.exp_nonneg _) _
  obtain ⟨bs, hbs, hdisj, hsat, hcount⟩ :=
    partition_greedy_captures π j (L r) S (m * Real.exp (-a q)) (by positivity)
  let R : Finset (Pt d) := S \ bs.biUnion id
  have hcover := partition_greedy_residual S bs (fun T hT => (hbs T hT).1) hdisj
  have hRsub : R ⊆ S := by simpa [R] using hcover.1
  have hRdisj : ∀ T ∈ bs, Disjoint T R := by simpa [R] using hcover.2.1
  have hcoverCard : (∑ T ∈ bs, (T.card : ℝ)) + (R.card : ℝ) = m := by
    simpa [R, m] using hcover.2.2.1
  have hRnot : R.Nonempty → R ∉ bs := by simpa [R] using hcover.2.2.2
  have hextracted : ∀ T ∈ bs, ∃ pl : Finset (Piece d),
      PartitionPreparedForest grid L s u a r π j S T loss pl := by
    intro T hT
    obtain ⟨hTS, hmass, g, hg, hcap⟩ := hbs T hT
    obtain ⟨π', hkeep, hcut, htime, hvan', hproper', hmono', hfinal'⟩ :=
      partition_extend_prefix π j hj S T g (grid r) hcap hvan hproper hmono hfinal
    obtain ⟨f⟩ := hrec r π' (j + 1) T (by omega) (by omega) (hTS.trans hsubset)
      hvan' hproper' hmono' hfinal'
    refine ⟨f.pieces, ?_⟩
    refine ⟨(fun X hX => (f.leaf X hX).1.subset), f.disjoint, ?_, ?_⟩
    · intro X hX
      obtain ⟨hgeo, hsize, htests⟩ := f.leaf X hX
      have hroot : PartitionGridLeaf grid L r π j S s X := by
        apply hgeo.compose grid L r r π π' j (j + 1) S T s X hTS (by omega) le_rfl hkeep
        intro i hi hi'
        have hieq : i = (⟨j, hj⟩ : Fin d) := Fin.ext (by change i.val = j; omega)
        rw [hieq]
        exact ⟨r, le_rfl, hcut ▸ hg, htime⟩
      have hsize' : (T.card : ℝ) * Real.exp (-partitionEventTail a (qn + 1)) ≤ X.pts.card := by
        simpa [qn, Nat.add_assoc] using hsize
      have hrootSize : m * Real.exp (-partitionEventTail a qn) ≤ X.pts.card :=
        (partition_event_child_mass a qn hq m (T.card : ℝ) hmass).trans hsize'
      exact ⟨hroot, hrootSize, htests⟩
    · simpa [loss, w, qn, Nat.add_assoc] using f.discard
  let rn : Fin G := ⟨r.val + 1, hnext⟩
  have hrrn : r < rn := by change r.val < r.val + 1; omega
  have hqn : qn + 1 ≤ rn.val * d + j := by
    have hd : 0 < d := by omega
    dsimp [qn, rn]
    simp only [Nat.add_mul, one_mul]
    omega
  have htailq : partitionEventTail a (qn + 1) ≤ a q / 9 := by
    have h := htail q
    have hfilter : Finset.univ.filter (fun k : Fin (G * d) => q < k) =
        Finset.univ.filter (fun k : Fin (G * d) => qn + 1 ≤ k.val) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]
      change (qn < k.val) ↔ qn + 1 ≤ k.val
      omega
    rw [hfilter] at h
    exact h
  by_cases hlarge : m * Real.exp (-a q / 2) ≤ (R.card : ℝ)
  · have hRne : R.Nonempty := by
      apply Finset.card_pos.mp
      have hpos : (0 : ℝ) < R.card := lt_of_lt_of_le (by positivity) hlarge
      exact_mod_cast hpos
    obtain ⟨fR⟩ := hrec rn π j R (by omega) (by omega) (hRsub.trans hsubset)
      (fun x hx i hi => hvan x (hRsub hx) i hi)
      (fun x hx i hi Z hZ => hproper x (hRsub hx) i hi Z hZ)
      hmono (fun i hi => (hfinal i hi).trans (hgrid.monotone hrrn.le))
    have hresidual : PartitionPreparedForest grid L s u a r π j S R loss fR.pieces := by
      refine ⟨(fun X hX => (fR.leaf X hX).1.subset), fR.disjoint, ?_, ?_⟩
      · intro X hX
        obtain ⟨hgeo, hsize, htests⟩ := fR.leaf X hX
        have hroot : PartitionGridLeaf grid L r π j S s X := by
          apply hgeo.compose grid L r rn π π j j S R s X hRsub le_rfl hrrn.le
            (fun i hi => ⟨rfl, rfl⟩)
          intro i hi hi'
          omega
        have hsizeHalf : m * Real.exp (-a q / 2 - partitionEventTail a (qn + 1)) ≤ X.pts.card :=
          partition_event_residual_mass a ha0 qn (rn.val * d + j) hq hqn m (R.card : ℝ)
            (X.pts.card : ℝ) (by positivity) hlarge hsize
        have hrootSize : m * Real.exp (-partitionEventTail a qn) ≤ X.pts.card := by
          rw [partition_event_tail_succ a qn hq]
          apply le_trans _ hsizeHalf
          apply mul_le_mul_of_nonneg_left _ hm.le
          apply Real.exp_le_exp.mpr
          have hapos := ha0 q
          change -(a q + partitionEventTail a (qn + 1)) ≤
            -a q / 2 - partitionEventTail a (qn + 1)
          linarith
        have hrootTests : PartitionGridTests grid L r u X := by
          intro k hrk ℓ hℓ hp g hg
          by_cases hkr : k = r
          · subst k
            exact hgeo.residual_capture_bound grid L hgrid r rn hrrn π j R s X hfinal
              m (a q) (partitionEventTail a (qn + 1)) u (ha q) htailq hsizeHalf
              (fun g hg => by
                convert (hsat g hg).le using 1
                congr 2
                ext x
                simp [CutPath.captured, R]) ℓ hℓ hp g hg
          · have hrnk : rn ≤ k := by
              change r.val + 1 ≤ k.val
              have hval : r.val ≠ k.val := by intro heq; exact hkr (Fin.ext heq.symm)
              change r.val ≤ k.val at hrk
              omega
            exact htests k hrnk ℓ hℓ hp g hg
        exact ⟨hroot, hrootSize, hrootTests⟩
      · have htailLoss : partitionEventTail w (rn.val * d + j) ≤ loss :=
          partition_event_tail_antitone w (fun i => Real.exp_nonneg _) (qn + 1) _ hqn
        exact fR.discard.trans (mul_le_mul_of_nonneg_left htailLoss (Nat.cast_nonneg R.card))
    let parents := insert R bs
    have hparents : (parents : Set (Finset (Pt d))).PairwiseDisjoint id := by
      dsimp [parents]
      rw [Finset.coe_insert, Set.pairwiseDisjoint_insert]
      exact ⟨hdisj, fun T hT hne => (hRdisj T hT).symm⟩
    have hparentSub : ∀ T ∈ parents, T ⊆ S := by
      intro T hT
      rcases Finset.mem_insert.mp hT with rfl | hT
      · exact hRsub
      · exact (hbs T hT).1
    have hprepared : ∀ T ∈ parents, ∃ pl,
        PartitionPreparedForest grid L s u a r π j S T loss pl := by
      intro T hT
      rcases Finset.mem_insert.mp hT with rfl | hT
      · exact ⟨fR.pieces, hresidual⟩
      · exact hextracted T hT
    have hforall : ∀ T, ∃ pl : Finset (Piece d), T ∈ parents →
        PartitionPreparedForest grid L s u a r π j S T loss pl := by
      intro T
      by_cases hT : T ∈ parents
      · obtain ⟨pl, hpl⟩ := hprepared T hT
        exact ⟨pl, fun _ => hpl⟩
      · exact ⟨∅, fun h => (hT h).elim⟩
    choose children hchildren using hforall
    have hmissing : m - (∑ T ∈ parents, (T.card : ℝ)) ≤ m * 0 := by
      dsimp [parents]
      rw [Finset.sum_insert (hRnot hRne)]
      linarith [hcoverCard]
    have hbudget : loss + 0 ≤ partitionEventTail w qn := by
      rw [partition_event_tail_succ w qn hq]
      dsimp [loss]
      have hpos := Real.exp_nonneg (-a q / 2)
      change partitionEventTail w (qn + 1) + 0 ≤
        Real.exp (-a q / 2) + partitionEventTail w (qn + 1)
      linarith
    exact partition_join_grid_forests grid L s u a r π j S parents children hparents hparentSub
      (fun T hT => (hchildren T hT).subset) (fun T hT => (hchildren T hT).disjoint)
      (fun T hT => (hchildren T hT).leaf) loss 0 hloss
      (fun T hT => (hchildren T hT).discard) hmissing hbudget
  · have hprepared : ∀ T, ∃ pl : Finset (Piece d), T ∈ bs →
        PartitionPreparedForest grid L s u a r π j S T loss pl := by
      intro T
      by_cases hT : T ∈ bs
      · obtain ⟨pl, hpl⟩ := hextracted T hT
        exact ⟨pl, fun _ => hpl⟩
      · exact ⟨∅, fun h => (hT h).elim⟩
    choose children hchildren using hprepared
    have hmissing : m - (∑ T ∈ bs, (T.card : ℝ)) ≤ m * Real.exp (-a q / 2) := by
      have hRsmall := (lt_of_not_ge hlarge).le
      linarith [hcoverCard]
    have hbudget : loss + Real.exp (-a q / 2) ≤ partitionEventTail w qn := by
      rw [partition_event_tail_succ w qn hq]
      change partitionEventTail w (qn + 1) + Real.exp (-a q / 2) ≤
        Real.exp (-a q / 2) + partitionEventTail w (qn + 1)
      linarith
    exact partition_join_grid_forests grid L s u a r π j S bs children hdisj
      (fun T hT => (hbs T hT).1)
      (fun T hT => (hchildren T hT).subset) (fun T hT => (hchildren T hT).disjoint)
      (fun T hT => (hchildren T hT).leaf) loss (Real.exp (-a q / 2)) hloss
      (fun T hT => (hchildren T hT).discard) hmissing hbudget

end
end DistinctDistances.TrackD
