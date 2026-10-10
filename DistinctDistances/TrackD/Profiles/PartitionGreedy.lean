import DistinctDistances.TrackD.Profiles.Defs

/-! Finite greedy extraction for the two window operations and the regularization
trees, `profiles.tex:92–116, 141–154`. The threshold is fixed from the original
node mass; it is not recomputed after each extraction. -/

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section

/-- Saturated disjoint extraction of admissible batches from a finite node. -/
theorem partition_greedy_batches {α : Type*} (S : Finset α)
    (admissible : Finset α → Prop) (m : ℝ) (hm : 0 < m)
    (hsize : ∀ T, admissible T → m ≤ (T.card : ℝ)) :
    ∃ batches : Finset (Finset α),
      (∀ T ∈ batches, T ⊆ S ∧ admissible T) ∧
      (batches : Set (Finset α)).PairwiseDisjoint id ∧
      (∀ T, T ⊆ S \ batches.biUnion id → ¬ admissible T) ∧
      m * batches.card ≤ S.card := by
  classical
  have main : ∀ n : ℕ, ∀ S : Finset α, S.card = n →
      ∃ batches : Finset (Finset α),
        (∀ T ∈ batches, T ⊆ S ∧ admissible T) ∧
        (batches : Set (Finset α)).PairwiseDisjoint id ∧
        (∀ T, T ⊆ S \ batches.biUnion id → ¬ admissible T) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro S hn
        by_cases hex : ∃ T, T ⊆ S ∧ admissible T
        · obtain ⟨T, hTS, hT⟩ := hex
          have hTne : T.Nonempty := by
            by_contra h
            have hzero := Finset.not_nonempty_iff_eq_empty.mp h
            have hmass := hsize T hT
            simp only [hzero, Finset.card_empty, Nat.cast_zero] at hmass
            linarith
          have hsmall : (S \ T).card < n := by
            rw [← hn, Finset.card_sdiff_of_subset hTS]
            have hpos := Finset.card_pos.mpr hTne
            have hle := Finset.card_le_card hTS
            omega
          obtain ⟨bs, hbs, hdisj, hsat⟩ := ih _ hsmall (S \ T) rfl
          refine ⟨insert T bs, ?_, ?_, ?_⟩
          · intro U hU
            rcases Finset.mem_insert.mp hU with rfl | hU
            · exact ⟨hTS, hT⟩
            · exact ⟨(hbs U hU).1.trans Finset.sdiff_subset, (hbs U hU).2⟩
          · rw [Finset.coe_insert, Set.pairwiseDisjoint_insert]
            refine ⟨hdisj, ?_⟩
            intro U hU hne
            apply Finset.disjoint_left.mpr
            intro x hxT hxU
            exact (Finset.mem_sdiff.mp ((hbs U hU).1 hxU)).2 hxT
          · intro U hU
            apply hsat U
            intro x hx
            have hxS := (Finset.mem_sdiff.mp (hU hx)).1
            have hxout := (Finset.mem_sdiff.mp (hU hx)).2
            have hxT : x ∉ T := by
              intro h
              exact hxout (Finset.mem_biUnion.mpr ⟨T, Finset.mem_insert_self _ _, h⟩)
            have hxbs : x ∉ bs.biUnion id := by
              intro h
              obtain ⟨V, hV, hxV⟩ := Finset.mem_biUnion.mp h
              exact hxout (Finset.mem_biUnion.mpr ⟨V, Finset.mem_insert_of_mem hV, hxV⟩)
            exact Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hxS, hxT⟩, hxbs⟩
        · refine ⟨∅, by simp, by simp, ?_⟩
          intro T hTS hT
          exact hex ⟨T, by simpa using hTS, hT⟩
  obtain ⟨bs, hbs, hdisj, hsat⟩ := main S.card S rfl
  refine ⟨bs, hbs, hdisj, hsat, ?_⟩
  calc
    m * bs.card = ∑ T ∈ bs, m := by simp [mul_comm]
    _ ≤ ∑ T ∈ bs, (T.card : ℝ) :=
      Finset.sum_le_sum (fun T hT => hsize T (hbs T hT).2)
    _ = ((bs.biUnion id).card : ℝ) := by
      norm_cast
      exact (Finset.card_biUnion hdisj).symm
    _ ≤ S.card := by
      exact_mod_cast Finset.card_le_card (Finset.biUnion_subset.mpr (fun T hT => (hbs T hT).1))

/-- One regularization event. Every extracted batch has a bounded proper-cut
certificate; every bounded proper test captures less than the fixed threshold
on the residual. -/
theorem partition_greedy_captures {d : ℕ} (π : CutPath d) (j D : ℕ)
    (S : Finset (Pt d)) (m : ℝ) (hm : 0 < m) :
    ∃ batches : Finset (Finset (Pt d)),
      (∀ T ∈ batches, T ⊆ S ∧ m ≤ (T.card : ℝ) ∧
        ∃ g : Poly d, g.totalDegree ≤ D ∧ T ⊆ π.captured j S g) ∧
      (batches : Set (Finset (Pt d))).PairwiseDisjoint id ∧
      (∀ g : Poly d, g.totalDegree ≤ D →
        ((π.captured j (S \ batches.biUnion id) g).card : ℝ) < m) ∧
      m * batches.card ≤ S.card := by
  classical
  let admissible : Finset (Pt d) → Prop := fun T =>
    m ≤ (T.card : ℝ) ∧ ∃ g : Poly d, g.totalDegree ≤ D ∧ T ⊆ π.captured j S g
  obtain ⟨bs, hbs, hdisj, hsat, hcount⟩ :=
    partition_greedy_batches S admissible m hm (fun T hT => hT.1)
  refine ⟨bs, (fun T hT => ⟨(hbs T hT).1, (hbs T hT).2⟩), hdisj, ?_, hcount⟩
  intro g hg
  let R := S \ bs.biUnion id
  by_contra hn
  have hcard : m ≤ ((π.captured j R g).card : ℝ) := le_of_not_gt hn
  have hsub : π.captured j R g ⊆ π.captured j S g := by
    intro x hx
    obtain ⟨hxR, hxg⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.sdiff_subset hxR, hxg⟩
  exact hsat (π.captured j R g) (by
    intro x hx
    simpa [R] using (Finset.mem_filter.mp hx).1) ⟨hcard, g, hg, hsub⟩

/-- Capture is inherited by restriction to a descendant without changing the
carrier system or its original certificate. -/
theorem partition_capture_subset {d : ℕ} (π : CutPath d) (j : ℕ)
    (S T : Finset (Pt d)) (hTS : T ⊆ S) (g : Poly d) :
    π.captured j T g ⊆ π.captured j S g := by
  classical
  intro x hx
  obtain ⟨hxT, hxg⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨hTS hxT, hxg⟩

end
end DistinctDistances.TrackD
