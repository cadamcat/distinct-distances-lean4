import DistinctDistances.TrackD.Profiles.PartitionChain

namespace DistinctDistances.TrackD

open scoped BigOperators Classical
noncomputable section

/-- `profiles.tex:81–116`: iterate a finite sequence of already supplied
window operations. Each chosen output is kept once, together with all its
certificates; the mass errors are those of the individual windows. -/
theorem partition_iterate_window_steps {α β : Type*} (n : ℕ) (initial : Finset α)
    (state : ℕ → Finset α → Prop) (pts : β → Finset α)
    (good : ℕ → β → Prop) (error : ℕ → ℝ)
    (hstart : state 0 initial)
    (hstep : ∀ i < n, ∀ U : Finset α, state i U →
      ∃ (V : Finset α) (pl : Finset β), state (i + 1) V ∧ V ⊆ U ∧
        (∀ X ∈ pl, good i X ∧ pts X ⊆ U) ∧
        (pl : Set β).PairwiseDisjoint pts ∧ (∀ X ∈ pl, Disjoint (pts X) V) ∧
        (U.card : ℝ) - V.card - (∑ X ∈ pl, ((pts X).card : ℝ)) ≤ error i) :
    ∃ (remaining : ℕ → Finset α) (pieces : ℕ → Finset β),
      remaining 0 = initial ∧ state n (remaining n) ∧
      (∀ i < n, state i (remaining i)) ∧
      ∀ i < n, remaining (i + 1) ⊆ remaining i ∧
        (∀ X ∈ pieces i, good i X ∧ pts X ⊆ remaining i) ∧
        (pieces i : Set β).PairwiseDisjoint pts ∧
        (∀ X ∈ pieces i, Disjoint (pts X) (remaining (i + 1))) ∧
        ((remaining i).card : ℝ) - (remaining (i + 1)).card -
          (∑ X ∈ pieces i, ((pts X).card : ℝ)) ≤ error i := by
  classical
  revert initial hstart hstep
  induction n with
  | zero =>
    intro initial hstart _hstep
    exact ⟨fun _ => initial, fun _ => ∅, rfl, hstart,
      fun i hi => absurd hi (Nat.not_lt_zero i),
      fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ n ih =>
    intro initial hstart hstep
    have hstep_n : ∀ i < n, ∀ U : Finset α, state i U →
        ∃ (V : Finset α) (pl : Finset β), state (i + 1) V ∧ V ⊆ U ∧
          (∀ X ∈ pl, good i X ∧ pts X ⊆ U) ∧
          (pl : Set β).PairwiseDisjoint pts ∧ (∀ X ∈ pl, Disjoint (pts X) V) ∧
          (U.card : ℝ) - V.card - (∑ X ∈ pl, ((pts X).card : ℝ)) ≤ error i :=
      fun i hi U hU => hstep i (by omega) U hU
    obtain ⟨remaining, pieces, h0, hn, hstate, hprop⟩ :=
      ih initial hstart hstep_n
    obtain ⟨V, pl, hVstate, hVsub, hgood, hdisj, hdisjV, herr⟩ :=
      hstep n (Nat.lt_succ_self n) (remaining n) hn
    let remaining' : ℕ → Finset α := fun j => if j = n + 1 then V else remaining j
    let pieces' : ℕ → Finset β := fun j => if j = n then pl else pieces j
    have hrem_succ : remaining' (n + 1) = V := by simp [remaining']
    have hrem_n : remaining' n = remaining n := by
      simp only [remaining']
      rw [if_neg (by omega : ¬ n = n + 1)]
    have hpc_n : pieces' n = pl := by simp [pieces']
    refine ⟨remaining', pieces', ?_, ?_, ?_, ?_⟩
    · show remaining' 0 = initial
      have : (0 : ℕ) ≠ n + 1 := by omega
      simp only [remaining', if_neg this]
      exact h0
    · show state (n + 1) (remaining' (n + 1))
      rw [hrem_succ]
      exact hVstate
    · intro i hi
      by_cases hieq : i = n
      · rw [hieq, hrem_n]
        exact hn
      · have hlt : i < n := by omega
        have : remaining' i = remaining i := by
          simp only [remaining']
          rw [if_neg (by omega : ¬ i = n + 1)]
        rw [this]
        exact hstate i hlt
    · intro i hi
      by_cases hieq : i = n
      · rw [hieq]
        have hr1 : remaining' (n + 1) = V := hrem_succ
        have hr0 : remaining' n = remaining n := hrem_n
        have hp0 : pieces' n = pl := hpc_n
        rw [hr1, hr0, hp0]
        refine ⟨hVsub, ?_, hdisj, ?_, herr⟩
        · intro X hX
          obtain ⟨hg, hpts⟩ := hgood X hX
          exact ⟨hg, hpts⟩
        · intro X hX
          have hXdisj := hdisjV X hX
          simpa [hr1] using hXdisj
      · have hlt : i < n := by omega
        obtain ⟨hsub0, hgood0, hdisj0, hdisjV0, herr0⟩ := hprop i hlt
        have hr1 : remaining' (i + 1) = remaining (i + 1) := by
          simp only [remaining']
          rw [if_neg (by omega : ¬ i + 1 = n + 1)]
        have hr0 : remaining' i = remaining i := by
          simp only [remaining']
          rw [if_neg (by omega : ¬ i = n + 1)]
        have hp0 : pieces' i = pieces i := by
          simp only [pieces']
          rw [if_neg hieq]
        rw [hr1, hr0, hp0]
        exact ⟨hsub0, hgood0, hdisj0, hdisjV0, herr0⟩

end
end DistinctDistances.TrackD
