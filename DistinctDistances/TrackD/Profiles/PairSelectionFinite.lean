import DistinctDistances.TrackD.Profiles.PairSelectionFinitePackages
import DistinctDistances.TrackD.Profiles.PairSelectionThresholds

namespace DistinctDistances.TrackD
open scoped BigOperators Classical
noncomputable section

/-- Assemble the outer-mass dichotomy after a single global deletion. -/
theorem pair_selection_finite (d : ℕ) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ a > 0, ∀ (P : Finset (Pt d)) (Q : Partition d) (δ θ ξ K s : ℝ)
      (R : Pt d → Pt d → Prop),
      0 < cfgN P → 0 < δ → δ ≤ a → θ ≤ 1 → 1 ≤ s → Q.Good P δ θ ξ K s →
      cfgN P / 2 ≤ (poolPts Q.pieces).card →
      (((P ×ˢ P).filter (fun pq => ¬ R pq.1 pq.2 ∧ ¬ R pq.2 pq.1)).card : ℝ) ≤
        a * cfgN P ^ 2 →
      ∃ (plx ply : Finset (Piece d)) (t : Fin d → ℝ),
        plx ⊆ Q.pieces ∧ ply ⊆ Q.pieces ∧ plx.Nonempty ∧ ply.Nonempty ∧
        (∀ X ∈ plx ∪ ply, ∀ i, |X.path.time i - t i| ≤ ρ) ∧
        WindowAlternative P δ ρ plx ply ∧
        (1 / 2 - ρ) * (poolPts plx).card * (poolPts ply).card ≤
          (((poolPts plx ×ˢ poolPts ply).filter (fun pq => R pq.1 pq.2)).card : ℝ) := by
  obtain ⟨ao, hao, hout⟩ := pair_selection_outer_pool d ρ hρ
  obtain ⟨ai, hai, hin⟩ := pair_selection_inner_pieces d ρ hρ
  refine ⟨min ao ai, lt_min hao hai, ?_⟩
  intro P Q δ θ ξ K s R hN hδ hδa hθ hs hQ hmass hbad
  let outer := Q.pieces.filter (fun X => X.width = Real.log (cfgB P))
  let inner := Q.pieces.filter (fun X => X.width ≠ Real.log (cfgB P))
  have houter : outer ⊆ Q.pieces := Finset.filter_subset _ _
  have hinner : inner ⊆ Q.pieces := Finset.filter_subset _ _
  have hsub : ∀ X ∈ Q.pieces, X.pts ⊆ P := fun X hX => (hQ.pieces_good X hX).1.subset
  have htime : ∀ X ∈ Q.pieces, ∀ i, -1 ≤ X.path.time i ∧ X.path.time i ≤ 2 := by
    intro X hX i
    obtain ⟨hlo, hhi⟩ := (hQ.pieces_good X hX).1.time_range i
    exact ⟨hlo, hhi.trans (by linarith)⟩
  have hdisj (pl : Finset (Piece d)) (hpl : pl ⊆ Q.pieces) :
      (pl : Set (Piece d)).PairwiseDisjoint Piece.pts := by
    intro X hX Y hY hXY
    exact hQ.pieces_disjoint (hpl hX) (hpl hY) hXY
  by_cases hm : cfgN P / 4 ≤ (poolPts outer).card
  · obtain ⟨pool, t, hpool, hne, hclose, hsize, hsel⟩ := hout P outer δ R hN hδ
      (hδa.trans (min_le_left _ _)) (fun X hX => hsub X (houter hX))
      (hdisj outer houter) (fun X hX => htime X (houter hX))
      (fun X hX => (Finset.mem_filter.mp hX).2) hm
      (hbad.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)))
    refine ⟨pool, pool, t, hpool.trans houter, hpool.trans houter, hne, hne, ?_,
      Or.inr (Or.inr ⟨rfl, ?_, hsize⟩), hsel⟩
    · simpa only [Finset.union_self] using hclose
    · intro X hX
      exact (Finset.mem_filter.mp (hpool hX)).2
  · have hunion : poolPts outer ∪ poolPts inner = poolPts Q.pieces := by
      ext x
      simp only [poolPts, Finset.mem_union, Finset.mem_biUnion,
        outer, inner, Finset.mem_filter]
      constructor
      · rintro (⟨X, ⟨hX, _⟩, hx⟩ | ⟨X, ⟨hX, _⟩, hx⟩)
        all_goals exact ⟨X, hX, hx⟩
      · rintro ⟨X, hX, hx⟩
        by_cases h : X.width = Real.log (cfgB P)
        · exact Or.inl ⟨X, ⟨hX, h⟩, hx⟩
        · exact Or.inr ⟨X, ⟨hX, h⟩, hx⟩
    have hcard : ((poolPts Q.pieces).card : ℝ) ≤
        (poolPts outer).card + (poolPts inner).card := by
      rw [← hunion]
      exact_mod_cast Finset.card_union_le (poolPts outer) (poolPts inner)
    have hinnerMass : cfgN P / 4 ≤ (poolPts inner).card := by
      have hm' := lt_of_not_ge hm
      linarith
    have hwidth : ∀ X ∈ inner, 0 < X.width ∧ X.width < Real.log (cfgB P) ∧
        ∃ i : ℕ, X.width = Real.log (cfgB P) / 2 ^ i := by
      intro X hX
      obtain ⟨hgood, hXs⟩ := hQ.pieces_good X (hinner hX)
      have hXp : 0 < X.width := by linarith
      obtain ⟨i, hi⟩ := hgood.width_dyadic
      have hden : (0 : ℝ) < 2 ^ i := by positivity
      have hlog : 0 < Real.log (cfgB P) := by
        rw [hi] at hXp
        exact (div_pos_iff.mp hXp).elim (fun h => h.1) (fun h => by linarith)
      have hle : X.width ≤ Real.log (cfgB P) := by
        rw [hi]
        exact div_le_self hlog.le (one_le_pow₀ (by norm_num))
      exact ⟨hXp, lt_of_le_of_ne hle (Finset.mem_filter.mp hX).2, i, hi⟩
    obtain ⟨X, hX, Y, hY, t, hclose, hwindow, hsel⟩ := hin P inner R hN
      (fun X hX => hsub X (hinner hX)) (hdisj inner hinner)
      (fun X hX => htime X (hinner hX)) hwidth hinnerMass
      (hbad.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)))
    refine ⟨{X}, {Y}, t, Finset.singleton_subset_iff.mpr (hinner hX),
      Finset.singleton_subset_iff.mpr (hinner hY), Finset.singleton_nonempty _,
      Finset.singleton_nonempty _, ?_, ?_, ?_⟩
    · intro Z hZ i
      simp only [Finset.mem_union, Finset.mem_singleton] at hZ
      rcases hZ with rfl | rfl
      · exact (hclose i).1
      · exact (hclose i).2
    · rcases hwindow with hcommon | hsep
      · exact Or.inl ⟨X, Y, rfl, rfl, hcommon⟩
      · exact Or.inr (Or.inl ⟨X, Y, rfl, rfl, hsep⟩)
    · simpa [poolPts] using hsel

end
end DistinctDistances.TrackD
